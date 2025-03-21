#![cfg_attr(not(feature = "std"), no_std)]

use polkadot_sdk::{
    frame_support::{
        self,
   
        pallet_prelude::Weight,
        traits::{Currency, ExistenceRequirement, Get},
        PalletId,
    },
    frame_system,
    sp_io::{crypto::secp256k1_ecdsa_recover, hashing::keccak_256},
    sp_runtime::{
        self,
        traits::{AccountIdConversion, CheckedSub, ValidateUnsigned},
        transaction_validity::{
            InvalidTransaction, TransactionLongevity, TransactionSource,
            ValidTransaction,
        },
        RuntimeDebug, Saturating,
    },
};

use polkadot_primitives::ValidityError;

//use frame::prelude::*;
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::prelude::{format, string::String, vec::Vec};
use scale_info::TypeInfo;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

// Re-export all pallet parts, this is needed to properly import the pallet into the runtime.
pub use pallet::*;

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
pub struct EthereumAddress(pub [u8; 20]);

impl AsRef<[u8]> for EthereumAddress {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

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
        self.0[..] == other.0[..]
    }
}

impl core::fmt::Debug for EcdsaSignature {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "EcdsaSignature({:?})", &self.0[..])
    }
}

#[frame_support::pallet]
pub mod pallet {
    use super::*;
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;
    use scale_info::prelude::vec;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: polkadot_sdk::frame_system::Config {
        /// The overarching event type.
        type RuntimeEvent: From<Event<Self>>
            + IsType<<Self as polkadot_sdk::frame_system::Config>::RuntimeEvent>;

        /// The currency mechanism.
        type Currency: Currency<Self::AccountId>;

        /// The prefix used in signed messages.
        type Prefix: Get<&'static [u8]>;

        /// The origin which may forcibly move a claim.
        type MoveClaimOrigin: EnsureOrigin<Self::RuntimeOrigin>;

        /// Treasury account Id
        #[pallet::constant]
        type PotId: Get<PalletId>;

        /// The weight info for the pallet.
        type WeightInfo: WeightInfo;
    }

    #[pallet::storage]
    #[pallet::getter(fn claims)]
    pub type Claims<T: Config> = StorageMap<_, Blake2_128Concat, EthereumAddress, BalanceOf<T>>;

    #[pallet::storage]
    #[pallet::getter(fn total)]
    pub type Total<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Someone claimed some tokens. [who, ethereum_address, amount]
        Claimed {
            who: T::AccountId,
            ethereum_address: EthereumAddress,
            amount: BalanceOf<T>,
        },
        /// Someone's claim was moved to a new address. [old, new]
        ClaimMoved {
            old: EthereumAddress,
            new: EthereumAddress,
        },
    }

    #[pallet::error]
    pub enum Error<T> {
        /// Invalid Ethereum signature.
        InvalidEthereumSignature,
        /// Ethereum address has no claim.
        SignerHasNoClaim,
        /// There's not enough in the pot to pay out some unvested amount. Generally implies a logic error.
        InsufficientPalletBalance,
    }

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
        #[pallet::weight(10_000 + T::DbWeight::get().reads_writes(1,1).ref_time())]
        pub fn register_claim(
            origin: OriginFor<T>,
            who: EthereumAddress,
            value: BalanceOf<T>,
        ) -> DispatchResult {
            ensure_root(origin)?;

            ensure!(
                T::Currency::free_balance(&Self::account_id()) >= value,
                Error::<T>::InsufficientPalletBalance
            );

            Claims::<T>::insert(who, value);
            Total::<T>::mutate(|t| *t = t.saturating_add(value));

            Ok(())
        }

        /// Move a claim to a new address.
        ///
        /// The dispatch origin for this call must be _Root_.
        ///
        /// Parameters:
        /// - `old`: The old Ethereum address.
        /// - `new`: The new Ethereum address.
        #[pallet::call_index(2)]
        #[pallet::weight(10_000 + T::DbWeight::get().reads_writes(1,1).ref_time())]
        pub fn move_claim(
            origin: OriginFor<T>,
            old: EthereumAddress,
            new: EthereumAddress,
        ) -> DispatchResultWithPostInfo {
            T::MoveClaimOrigin::try_origin(origin)
                .map(|_| ())
                .or_else(ensure_root)?;

            Claims::<T>::take(&old).map(|c| Claims::<T>::insert(&new, c));

            Self::deposit_event(Event::ClaimMoved { old, new });
            Ok(Pays::No.into())
        }
    }

    #[pallet::validate_unsigned]
    impl<T: Config> ValidateUnsigned for Pallet<T> {
        type Call = Call<T>;

        fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
            const PRIORITY: u64 = 100;

            match call {
                Call::claim { dest, ethereum_signature } => {
                    let data = dest.using_encoded(to_ascii_hex);
                    let signer = Self::eth_recover(ethereum_signature, &data, &[][..])
                        .ok_or(InvalidTransaction::Custom(
                            ValidityError::InvalidEthereumSignature.into()
                        ))?;

                    // Check if this signer has a claim
                    let _balance = Claims::<T>::get(&signer)
                        .ok_or(InvalidTransaction::Custom(ValidityError::SignerHasNoClaim.into()))?;

                    Ok(ValidTransaction {
                        priority: PRIORITY,
                        requires: vec![],
                        provides: vec![(signer, dest.clone()).encode()],
                        longevity: TransactionLongevity::max_value(),
                        propagate: true,
                    })
                }
                _ => Err(InvalidTransaction::Call.into()),
            }
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

impl<T: Config> Pallet<T> {
    /// The account ID of the pallet.
    pub fn account_id() -> T::AccountId {
        T::PotId::get().into_account_truncating()
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

    fn process_claim(signer: EthereumAddress, dest: T::AccountId) -> sp_runtime::DispatchResult {
        let balance_due = Claims::<T>::get(&signer).ok_or(Error::<T>::SignerHasNoClaim)?;

        let new_total = Total::<T>::get()
            .checked_sub(&balance_due)
            .ok_or(Error::<T>::InsufficientPalletBalance)?;

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

        Self::deposit_event(Event::Claimed {
            who: dest,
            ethereum_address: signer,
            amount: balance_due,
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use codec::Encode;
    use frame_support::{
        assert_noop, assert_ok, parameter_types,
        traits::{Currency, ExistenceRequirement},
    };
    use frame_system::mocking::MockBlock;
    use hex_literal::hex;
    use polkadot_sdk::{frame_support, frame_system, pallet_balances, sp_core, sp_io};
    use sp_runtime::{
        self,
        traits::{BadOrigin, BlakeTwo256},
        BuildStorage, TokenError,
    };

    type Block = MockBlock<Test>;

    frame_support::construct_runtime!(
        pub enum Test
        {
            System: frame_system,
            Balances: pallet_balances,
            Claims: crate,
        }
    );

    parameter_types! {
        pub const BlockHashCount: u64 = 250;
        pub const SS58Prefix: u8 = 42;
    }

    impl frame_system::Config for Test {
        type BaseCallFilter = frame_support::traits::Everything;
        type BlockWeights = ();
        type BlockLength = ();
        type RuntimeOrigin = RuntimeOrigin;
        type RuntimeCall = RuntimeCall;
        type Nonce = u64;
        type Hash = sp_core::H256;
        type Hashing = BlakeTwo256;
        type AccountId = u64;
        type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
        type Block = Block;
        type RuntimeEvent = RuntimeEvent;
        type BlockHashCount = BlockHashCount;
        type DbWeight = ();
        type Version = ();
        type PalletInfo = PalletInfo;
        type AccountData = pallet_balances::AccountData<u64>;
        type OnNewAccount = ();
        type OnKilledAccount = ();
        type SystemWeightInfo = ();
        type SS58Prefix = SS58Prefix;
        type OnSetCode = ();
        type MaxConsumers = frame_support::traits::ConstU32<16>;
        type PreInherents = ();
        type SingleBlockMigrations = ();
        type PostInherents = ();
        type PostTransactions = ();
        type RuntimeTask = ();
        type MultiBlockMigrator = ();
    }

    parameter_types! {
        pub const ExistentialDeposit: u64 = 1;
        pub const MaxLocks: u32 = 50;
        pub const MaxReserves: u32 = 50;
        pub const MaxFreezes: u32 = 50;
    }

    impl pallet_balances::Config for Test {
        type Balance = u64;
        type DustRemoval = ();
        type RuntimeEvent = RuntimeEvent;
        type ExistentialDeposit = ExistentialDeposit;
        type AccountStore = System;
        type WeightInfo = ();
        type MaxLocks = MaxLocks;
        type MaxReserves = MaxReserves;
        type ReserveIdentifier = [u8; 8];
        type RuntimeHoldReason = RuntimeHoldReason;
        type RuntimeFreezeReason = RuntimeFreezeReason;
        type FreezeIdentifier = ();
        type MaxFreezes = MaxFreezes;
    }

    parameter_types! {
        pub Prefix: &'static [u8] = b"Pay RUSTs to the TEST account:";
        pub const PotId: PalletId = PalletId(*b"airdrop!");
    }

    impl Config for Test {
        type RuntimeEvent = RuntimeEvent;
        type Currency = Balances;
        type WeightInfo = TestWeightInfo;
        type PotId = PotId;
        type Prefix = Prefix;
        type MoveClaimOrigin = frame_system::EnsureRoot<u64>;
    }

    pub struct TestWeightInfo;
    impl WeightInfo for TestWeightInfo {
        fn claim() -> Weight {
            Weight::from_parts(0, 0)
        }
        fn register_claim() -> Weight {
            Weight::from_parts(0, 0)
        }
        fn move_claim() -> Weight {
            Weight::from_parts(0, 0)
        }
    }

    // Helper functions for generating test accounts and signatures
    fn alice() -> libsecp256k1::SecretKey {
        libsecp256k1::SecretKey::parse(&keccak_256(b"Alice")).unwrap()
    }

    fn bob() -> libsecp256k1::SecretKey {
        libsecp256k1::SecretKey::parse(&keccak_256(b"Bob")).unwrap()
    }

    fn eth(secret: &libsecp256k1::SecretKey) -> EthereumAddress {
        let mut res = EthereumAddress::default();
        let pk = libsecp256k1::PublicKey::from_secret_key(secret);
        res.0
            .copy_from_slice(&keccak_256(&pk.serialize()[1..65])[12..]);
        res
    }

    fn sig<T: Config>(
        secret: &libsecp256k1::SecretKey,
        what: &[u8],
        extra: &[u8],
    ) -> EcdsaSignature {
        let msg = keccak_256(&Pallet::<T>::ethereum_signable_message(
            &to_ascii_hex(what)[..],
            extra,
        ));
        let (sig, recovery_id) = libsecp256k1::sign(&libsecp256k1::Message::parse(&msg), secret);
        let mut r = [0u8; 65];
        r[0..64].copy_from_slice(&sig.serialize()[..]);
        r[64] = recovery_id.serialize();
        EcdsaSignature(r)
    }

    pub fn new_test_ext() -> sp_io::TestExternalities {
        let mut t = frame_system::GenesisConfig::<Test>::default()
            .build_storage()
            .unwrap();

        let initial_balance = 1_000_000;
        pallet_balances::GenesisConfig::<Test> {
            balances: vec![(Claims::account_id(), initial_balance)],
        }
        .assimilate_storage(&mut t)
        .unwrap();

        t.into()
    }

    #[test]
    fn basic_setup_works() {
        new_test_ext().execute_with(|| {
            assert_eq!(
                pallet_balances::Pallet::<Test>::free_balance(&Claims::account_id()),
                1_000_000
            );
            assert_eq!(Claims::claims(&eth(&alice())), None);
            assert_eq!(Claims::total(), 0);
        });
    }

    #[test]
    fn register_claim_works() {
        new_test_ext().execute_with(|| {
            let claim_amount = 100;
            let eth_address = eth(&alice());

            // Register a claim
            assert_ok!(Claims::register_claim(
                RuntimeOrigin::root(),
                eth_address,
                claim_amount
            ));

            // Check state after registration
            assert_eq!(Claims::claims(&eth_address), Some(claim_amount));
            assert_eq!(Claims::total(), claim_amount);
        });
    }

    #[test]
    fn claim_works() {
        new_test_ext().execute_with(|| {
            assert_eq!(Balances::free_balance(42), 0);
            let claim_amount = 100;
            let dest_account = 42u64;
            let eth_address = eth(&alice());

            println!("eth_address: {:?}", eth_address);

            // Register a claim
            assert_ok!(Claims::register_claim(
                RuntimeOrigin::root(),
                eth_address,
                claim_amount
            ));

            // Check initial state
            assert_eq!(Claims::claims(&eth_address), Some(claim_amount));
            assert_eq!(Claims::total(), claim_amount);
            assert_eq!(
                pallet_balances::Pallet::<Test>::free_balance(&dest_account),
                0
            );

            let signature = sig::<Test>(&alice(), &dest_account.encode(), &[][..]);

            // Log the signature with println!
            println!("{:?}", signature.0);

            // Claim tokens
            assert_ok!(Claims::claim(
                RuntimeOrigin::none(),
                dest_account,
                signature
            ));

            // Check final state
            assert_eq!(
                pallet_balances::Pallet::<Test>::free_balance(&dest_account),
                claim_amount
            );
            assert_eq!(Claims::claims(&eth_address), None);
            assert_eq!(Claims::total(), 0);
        });
    }

    #[test]
    fn claim_fails_if_no_claim() {
        new_test_ext().execute_with(|| {
            let dest_account = 42;

            assert_noop!(
                Claims::claim(
                    RuntimeOrigin::none(),
                    dest_account,
                    sig::<Test>(&alice(), &dest_account.encode(), &[][..])
                ),
                Error::<Test>::SignerHasNoClaim
            );
        });
    }

    #[test]
    fn non_root_cannot_register_claim() {
        new_test_ext().execute_with(|| {
            assert_noop!(
                Claims::register_claim(RuntimeOrigin::signed(42), eth(&alice()), 100),
                BadOrigin
            );
        });
    }

    #[test]
    fn claim_fails_if_insufficient_pallet_balance() {
        new_test_ext().execute_with(|| {
            let claim_amount = 100;
            let eth_address = eth(&alice());

            // Register a claim
            assert_ok!(Claims::register_claim(
                RuntimeOrigin::root(),
                eth_address,
                claim_amount
            ));

            // Drain the pallet account
            let pallet_account = Claims::account_id();
            let _ = pallet_balances::Pallet::<Test>::transfer(
                &pallet_account,
                &42,
                1_000_000,
                ExistenceRequirement::AllowDeath,
            );

            // Try to claim
            assert_noop!(
                Claims::claim(
                    RuntimeOrigin::none(),
                    42,
                    sig::<Test>(&alice(), &42u64.encode(), &[][..])
                ),
                TokenError::FundsUnavailable //(could also be Error::<Test>::InsufficientPalletBalance but FundsUnavailable triggers first)
            );
        });
    }

    #[test]
    fn move_claim_works() {
        new_test_ext().execute_with(|| {
            let claim_amount = 100;
            let old_eth = eth(&alice());
            let new_eth = eth(&bob());

            // Register a claim for Alice
            assert_ok!(Claims::register_claim(
                RuntimeOrigin::root(),
                old_eth,
                claim_amount
            ));

            // Move claim from Alice to Bob
            assert_ok!(Claims::move_claim(
                RuntimeOrigin::root(),
                old_eth,
                new_eth
            ));

            // Check that the claim has been moved
            assert_eq!(Claims::claims(&old_eth), None);
            assert_eq!(Claims::claims(&new_eth), Some(claim_amount));

            // Bob should now be able to claim
            let dest_account = 42;
            assert_ok!(Claims::claim(
                RuntimeOrigin::none(),
                dest_account,
                sig::<Test>(&bob(), &dest_account.encode(), &[][..])
            ));

            // Check final state
            assert_eq!(
                pallet_balances::Pallet::<Test>::free_balance(&dest_account),
                claim_amount
            );
            assert_eq!(Claims::claims(&new_eth), None);
            assert_eq!(Claims::total(), 0);
        });
    }

    #[test]
    fn real_eth_sig_works() {
        new_test_ext().execute_with(|| {
                // "Pay RUSTs to the TEST account:2a00000000000000"
                let sig = hex!["444023e89b67e67c0562ed0305d252a5dd12b2af5ac51d6d3cb69a0b486bc4b3191401802dc29d26d586221f7256cd3329fe82174bdf659baea149a40e1c495d1c"];
                let sig = EcdsaSignature(sig);
                let who = 42u64.using_encoded(to_ascii_hex);
                let signer = Pallet::<Test>::eth_recover(&sig, &who, &[][..]).unwrap();
                assert_eq!(signer.0, hex!["6d31165d5d932d571f3b44695653b46dcc327e84"]);
            });
    }

    #[test]
    fn real_eth_sig_hex_works() {
        new_test_ext().execute_with(|| {
                //Signature is "0xa14a1de114061d347702e0002c0a863d774c3ca1df83008a47c47b391c368b097191ff2107352954f4d43d01fed02384abf315ee861d91dd41c869cd4501546b00"
                //The address is "0x79933Da2de793DFC61c90017884C253B9BDF8B90"
                let sig = hex!["a14a1de114061d347702e0002c0a863d774c3ca1df83008a47c47b391c368b097191ff2107352954f4d43d01fed02384abf315ee861d91dd41c869cd4501546b00"];
                let sig = EcdsaSignature(sig);
                let who = 42u64.using_encoded(to_ascii_hex);
                let signer = Pallet::<Test>::eth_recover(&sig, &who, &[][..]).unwrap();
                assert_eq!(signer.0, hex!["79933Da2de793DFC61c90017884C253B9BDF8B90"]);
            });
    }

    #[test]
    fn custom_signature_test() {
        new_test_ext().execute_with(|| {
                assert_eq!(Balances::free_balance(42), 0);
                let claim_amount = 100;
                let dest_account = 42u64;
                
                // Parse the private key directly without hashing
                let private_key = hex::decode("9116d6c6a9c830c06af62af6d4101b566e2466d88510b6c11d655545c74790a4").unwrap();
                let mut private_key_bytes = [0u8; 32];
                private_key_bytes.copy_from_slice(&private_key);
                let eth_test_account = libsecp256k1::SecretKey::parse(&private_key_bytes).unwrap();
                let eth_address = eth(&eth_test_account);

                println!("Ethereum address: 0x{}", hex::encode(eth_address.as_ref()));

                // Register a claim
                assert_ok!(Claims::register_claim(
                    RuntimeOrigin::root(),
                    eth_address,
                    claim_amount
                ));

                // Check initial state
                assert_eq!(Claims::claims(&eth_address), Some(claim_amount));
                assert_eq!(Claims::total(), claim_amount);
                assert_eq!(
                    pallet_balances::Pallet::<Test>::free_balance(&dest_account),
                    0
                );

                let signature = sig::<Test>(&eth_test_account, &dest_account.encode(), &[][..]);

                // Log dest_account
                println!("dest_account : {:?}", dest_account);  
                // Log the signature with println!
                println!("signature bytes: {:?}", signature.0);
                // Log the signature with println! in hex
                println!("signature hex : {:?}", hex::encode(signature.0));

                // Claim tokens
                assert_ok!(Claims::claim(
                    RuntimeOrigin::none(),
                    dest_account,
                    signature
                ));

                // Check final state
                assert_eq!(
                    pallet_balances::Pallet::<Test>::free_balance(&dest_account),
                    claim_amount
                );
                assert_eq!(Claims::claims(&eth_address), None);
                assert_eq!(Claims::total(), 0);
            });
    }

    #[test]
    fn full_test() {
        new_test_ext().execute_with(|| {
                assert_eq!(Balances::free_balance(42), 0);
                let claim_amount = 100;
                let dest_account = 42u64;

                let eth_hex_address = hex!["79933Da2de793DFC61c90017884C253B9BDF8B90"];
                let eth_address = EthereumAddress(eth_hex_address);
                println!("Ethereum address: 0x{}", hex::encode(eth_address.as_ref()));

                // Register a claim
                assert_ok!(Claims::register_claim(
                    RuntimeOrigin::root(),
                    eth_address,
                    claim_amount
                ));

                // Check initial state
                assert_eq!(Claims::claims(&eth_address), Some(claim_amount));
                assert_eq!(Claims::total(), claim_amount);
                assert_eq!(
                    pallet_balances::Pallet::<Test>::free_balance(&dest_account),
                    0
                );

                let signature_hex = hex!["a14a1de114061d347702e0002c0a863d774c3ca1df83008a47c47b391c368b097191ff2107352954f4d43d01fed02384abf315ee861d91dd41c869cd4501546b00"];
                let signature = EcdsaSignature(signature_hex);  

                // Log dest_account
                println!("dest_account : {:?}", dest_account);  
                // Log the signature with println!
                println!("signature bytes: {:?}", signature.0);
                // Log the signature with println! in hex
                println!("signature hex : {:?}", signature_hex);

                // Claim tokens
                assert_ok!(Claims::claim(
                    RuntimeOrigin::none(),
                    dest_account,
                    signature
                ));

                // Check final state
                assert_eq!(
                    pallet_balances::Pallet::<Test>::free_balance(&dest_account),
                    claim_amount
                );
                assert_eq!(Claims::claims(&eth_address), None);
                assert_eq!(Claims::total(), 0);
            });
    }
}
