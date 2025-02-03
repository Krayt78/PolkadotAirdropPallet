//! A shell pallet built with [`frame`].
//!
//! To get started with this pallet, try implementing the guide in
//! <https://paritytech.github.io/polkadot-sdk/master/polkadot_sdk_docs/guides/your_first_pallet/index.html>

#![cfg_attr(not(feature = "std"), no_std)]

use polkadot_sdk::polkadot_sdk_frame as frame;

// Re-export all pallet parts, this is needed to properly import the pallet into the runtime.
pub use pallet::*;

use codec::{Decode, Encode, MaxEncodedLen};
use frame::deps::frame_support::PalletId;
use frame::deps::sp_io::{crypto::secp256k1_ecdsa_recover, hashing::keccak_256};
use frame::deps::sp_runtime;
use frame::derive::{RuntimeDebug, TypeInfo};
use frame::testing_prelude::*;
use frame::traits::{AccountIdConversion, CheckedSub, Currency, ExistenceRequirement, Get};
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

type BalanceOf<T> =
    <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

pub trait WeightInfo {
    fn claim() -> Weight;
    fn register_claim() -> Weight;
    fn move_claim() -> Weight;
}

pub struct TestWeightInfo;
impl WeightInfo for TestWeightInfo {
    fn claim() -> Weight {
        Weight::zero()
    }
    fn register_claim() -> Weight {
        Weight::zero()
    }
    fn move_claim() -> Weight {
        Weight::zero()
    }
}

#[derive(
    Clone, Copy, PartialEq, Eq, Encode, Decode, Default, RuntimeDebug, TypeInfo, MaxEncodedLen,
)]
pub struct EthereumAddress([u8; 20]);

impl Serialize for EthereumAddress {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let hex: String = rustc_hex::ToHex::to_hex(&self.0[..]);
        serializer.serialize_str(&format!("0x{}", hex))
    }
}

impl<'de> Deserialize<'de> for EthereumAddress {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let base_string = String::deserialize(deserializer)?;
        let offset = if base_string.starts_with("0x") { 2 } else { 0 };
        let s = &base_string[offset..];
        if s.len() != 40 {
            Err(serde::de::Error::custom(
                "Bad length of Ethereum address (should be 42 including '0x')",
            ))?;
        }
        let raw: Vec<u8> = rustc_hex::FromHex::from_hex(s)
            .map_err(|e| serde::de::Error::custom(format!("{:?}", e)))?;
        let mut r = Self::default();
        r.0.copy_from_slice(&raw);
        Ok(r)
    }
}

#[derive(Encode, Decode, Clone, TypeInfo, MaxEncodedLen)]
pub struct EcdsaSignature(pub [u8; 65]);

impl PartialEq for EcdsaSignature {
    fn eq(&self, other: &Self) -> bool {
        &self.0[..] == &other.0[..]
    }
}

impl core::fmt::Debug for EcdsaSignature {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "EcdsaSignature({:?})", &self.0[..])
    }
}

#[frame::pallet]
pub mod pallet {
    use super::*;

    pub const PALLET_ID: PalletId = PalletId(*b"airdrop!");

    #[pallet::config]
    pub trait Config: polkadot_sdk::frame_system::Config {
        /// The currency mechanism.
        type Currency: Currency<Self::AccountId>;

        /// The origin which may forcibly move a claim from one account to another.
        type MoveClaimOrigin: EnsureOrigin<Self::RuntimeOrigin>;

        /// Weight information for extrinsics in this pallet.
        type WeightInfo: WeightInfo;

        /// The prefix used in signed messages
        #[pallet::constant]
        type Prefix: Get<&'static [u8]>;
    }

    #[pallet::error]
    pub enum Error<T> {
        /// Invalid Ethereum signature.
        InvalidEthereumSignature,
        /// Ethereum address has no claim.
        SignerHasNoClaim,
        /// Account ID sending transaction has no claim.
        SenderHasNoClaim,
        /// There's not enough in the pot to pay out some unvested amount. Generally implies a
        /// logic error.
        PotUnderflow,
        /// Not enough balance in pallet account
        InsufficientPalletBalance,
    }

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::storage]
    pub type Claims<T: Config> = StorageMap<_, Identity, EthereumAddress, BalanceOf<T>>;

    #[pallet::storage]
    pub type Total<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    #[pallet::storage]
    pub(super) type Preclaims<T: Config> = StorageMap<_, Identity, T::AccountId, EthereumAddress>;

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Make a claim to collect your tokens.
        ///
        /// The dispatch origin for this call must be _None_.
        ///
        /// Unsigned Validation:
        /// A call to claim is deemed valid if the signature provided matches
        /// the expected signed message of:
        ///
        /// > Ethereum Signed Message:
        /// > (configured prefix string)(address)
        ///
        /// and `address` matches the `dest` account.
        ///
        /// Parameters:
        /// - `dest`: The destination account to payout the claim.
        /// - `ethereum_signature`: The signature of an ethereum signed message matching the format
        ///   described above.
        ///
        /// <weight>
        /// The weight of this call is invariant over the input parameters.
        /// Weight includes logic to validate unsigned `claim` call.
        ///
        /// Total Complexity: O(1)
        /// </weight>
        #[pallet::call_index(0)]
        #[pallet::weight(T::WeightInfo::claim())]
        pub fn claim(
            origin: OriginFor<T>,
            dest: T::AccountId,
            ethereum_signature: EcdsaSignature,
        ) -> DispatchResult {
            ensure_none(origin)?;

            let data = dest.using_encoded(to_ascii_hex);
            let signer = Self::eth_recover(&ethereum_signature, &data, &[][..])
                .ok_or(Error::<T>::InvalidEthereumSignature)?;

            Self::process_claim(signer, dest)?;
            Ok(())
        }

        /// Register a new claim to collect tokens from the pallet account.
        ///
        /// The dispatch origin for this call must be _Root_.
        ///
        /// Parameters:
        /// - `who`: The Ethereum address allowed to collect this claim.
        /// - `value`: The number of tokens that will be claimed.
        #[pallet::call_index(1)]
        #[pallet::weight(T::WeightInfo::register_claim())]
        pub fn register_claim(
            origin: OriginFor<T>,
            who: EthereumAddress,
            value: BalanceOf<T>,
        ) -> DispatchResult {
            ensure_root(origin)?;

            // Check if pallet account has enough balance
            let pallet_account = Self::account_id();
            ensure!(
                T::Currency::free_balance(&pallet_account) >= value,
                Error::<T>::InsufficientPalletBalance
            );

            Total::<T>::mutate(|t| *t += value);
            Claims::<T>::insert(who, value);
            Ok(())
        }

        #[pallet::call_index(2)]
        #[pallet::weight(T::WeightInfo::move_claim())]
        pub fn move_claim(
            origin: OriginFor<T>,
            old: EthereumAddress,
            new: EthereumAddress,
            maybe_preclaim: Option<T::AccountId>,
        ) -> DispatchResultWithPostInfo {
            T::MoveClaimOrigin::try_origin(origin)
                .map(|_| ())
                .or_else(ensure_root)?;

            Claims::<T>::take(&old).map(|c| Claims::<T>::insert(&new, c));
            maybe_preclaim.map(|preclaim| {
                Preclaims::<T>::mutate(&preclaim, |maybe_o| {
                    if maybe_o.as_ref().map_or(false, |o| o == &old) {
                        *maybe_o = Some(new)
                    }
                })
            });
            Ok(Pays::No.into())
        }
    }

    impl<T: Config> Pallet<T> {
        /// The account ID of the pallet.
        pub fn account_id() -> T::AccountId {
            PALLET_ID.into_account_truncating()
        }

        /// Constructs the message that Ethereum RPC's `personal_sign` and `eth_sign` would sign.
        fn ethereum_signable_message(what: &[u8], extra: &[u8]) -> Vec<u8> {
            let prefix = T::Prefix::get();
            let mut l = prefix.len() + what.len() + extra.len();
            let mut rev = Vec::new();
            while l > 0 {
                rev.push(b'0' + (l % 10) as u8);
                l /= 10;
            }
            let mut v = b"\x19Ethereum Signed Message:\n".to_vec();
            v.extend(rev.into_iter().rev());
            v.extend_from_slice(prefix);
            v.extend_from_slice(what);
            v.extend_from_slice(extra);
            v
        }

        // Attempts to recover the Ethereum address from a message signature signed by using
        // the Ethereum RPC's `personal_sign` and `eth_sign`.
        fn eth_recover(s: &EcdsaSignature, what: &[u8], extra: &[u8]) -> Option<EthereumAddress> {
            let msg = keccak_256(&Self::ethereum_signable_message(what, extra));
            let mut res = EthereumAddress::default();
            res.0
                .copy_from_slice(&keccak_256(&secp256k1_ecdsa_recover(&s.0, &msg).ok()?[..])[12..]);
            Some(res)
        }

        fn process_claim(
            signer: EthereumAddress,
            dest: T::AccountId,
        ) -> sp_runtime::DispatchResult {
            let balance_due = Claims::<T>::get(&signer).ok_or(Error::<T>::SignerHasNoClaim)?;

            let new_total = Total::<T>::get()
                .checked_sub(&balance_due)
                .ok_or(Error::<T>::PotUnderflow)?;

            // Transfer tokens from pallet account to the destination account
            let pallet_account = Self::account_id();
            T::Currency::transfer(
                &pallet_account,
                &dest,
                balance_due,
                ExistenceRequirement::KeepAlive,
            )?;

            Total::<T>::put(new_total);
            Claims::<T>::remove(&signer);

            Ok(())
        }
    }
}

/// Converts the given binary data into ASCII-encoded hex. It will be twice the length.
fn to_ascii_hex(data: &[u8]) -> Vec<u8> {
    let mut r = Vec::with_capacity(data.len() * 2);
    let mut push_nibble = |n| r.push(if n < 10 { b'0' + n } else { b'a' - 10 + n });
    for &b in data.iter() {
        push_nibble(b / 16);
        push_nibble(b % 16);
    }
    r
}
