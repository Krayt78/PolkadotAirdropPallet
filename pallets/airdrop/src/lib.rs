#![cfg_attr(not(feature = "std"), no_std)]

use polkadot_sdk::{
    frame_support::{
        self,
        pallet_prelude::*,
        traits::{Currency, ExistenceRequirement, Get},
        PalletId,
    },
    frame_system::{
        pallet_prelude::*,
    },
    sp_io::{crypto::secp256k1_ecdsa_recover, hashing::keccak_256},
    sp_runtime::{
        self,
        Saturating,
        traits::{AccountIdConversion, CheckedSub},
        RuntimeDebug,
    },
};

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};

// Re-export all pallet parts, this is needed to properly import the pallet into the runtime.
pub use pallet::*;

type BalanceOf<T> =
    <<T as Config>::Currency as Currency<<T as polkadot_sdk::frame_system::Config>::AccountId>>::Balance;

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

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: polkadot_sdk::frame_system::Config {
        /// The overarching event type.
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as polkadot_sdk::frame_system::Config>::RuntimeEvent>;

        /// The currency mechanism.
        type Currency: Currency<Self::AccountId>;

        /// The prefix used in signed messages.
        type Prefix: Get<&'static [u8]>;

        /// The origin which may forcibly move a claim.
        type MoveClaimOrigin: EnsureOrigin<Self::RuntimeOrigin>;

        /// Weight information for extrinsics in this pallet.
        type WeightInfo: WeightInfo;
    }

    #[pallet::storage]
    #[pallet::getter(fn claims)]
    pub type Claims<T: Config> = StorageMap<_, Blake2_128Concat, EthereumAddress, BalanceOf<T>>;

    #[pallet::storage]
    #[pallet::getter(fn total)]
    pub type Total<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    #[pallet::storage]
    #[pallet::getter(fn preclaims)]
    pub(super) type Preclaims<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, EthereumAddress>;

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

            println!("{:?}", signer);

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
        /// - `maybe_preclaim`: The account that should be allowed to claim the tokens.
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
            if let Some(p) = maybe_preclaim {
                Preclaims::<T>::insert(p, new);
            }

            Self::deposit_event(Event::ClaimMoved { old, new });
            Ok(Pays::No.into())
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
        PalletId(*b"airdrop!").into_account_truncating()
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

        Self::deposit_event(Event::Claimed { who: dest, ethereum_address: signer, amount: balance_due });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use codec::Encode;
    use hex_literal::hex;
    use frame_support::{
        assert_noop, assert_ok,
        traits::{Currency, ExistenceRequirement},
        parameter_types,
    };
    use sp_runtime::{
        traits::{BlakeTwo256, BadOrigin},
        BuildStorage,
    };
    use frame_system::mocking::MockBlock;
    use polkadot_sdk::{
        sp_io,
        sp_core,
        frame_support,
        frame_system,
        pallet_balances,
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
    }

    impl Config for Test {
        type RuntimeEvent = RuntimeEvent;
        type Currency = Balances;
        type WeightInfo = TestWeightInfo;
        type Prefix = Prefix;
        type MoveClaimOrigin = frame_system::EnsureRoot<u64>;
    }

    pub struct TestWeightInfo;
    impl WeightInfo for TestWeightInfo {
        fn claim() -> Weight { Weight::from_parts(0, 0) }
        fn register_claim() -> Weight { Weight::from_parts(0, 0) }
        fn move_claim() -> Weight { Weight::from_parts(0, 0) }
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
        res.0.copy_from_slice(&keccak_256(&pk.serialize()[1..65])[12..]);
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
            assert_eq!(pallet_balances::Pallet::<Test>::free_balance(&Claims::account_id()), 1_000_000);
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
            assert_ok!(Claims::register_claim(RuntimeOrigin::root(), eth_address, claim_amount));

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
            assert_ok!(Claims::register_claim(RuntimeOrigin::root(), eth_address, claim_amount));

            // Check initial state
            assert_eq!(Claims::claims(&eth_address), Some(claim_amount));
            assert_eq!(Claims::total(), claim_amount);
            assert_eq!(pallet_balances::Pallet::<Test>::free_balance(&dest_account), 0);

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
            assert_eq!(pallet_balances::Pallet::<Test>::free_balance(&dest_account), claim_amount);
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
            assert_ok!(Claims::register_claim(RuntimeOrigin::root(), eth_address, claim_amount));

            // Drain the pallet account
            let pallet_account = Claims::account_id();
            let _ = pallet_balances::Pallet::<Test>::transfer(
                &pallet_account,
                &42,
                1_000_000,
                ExistenceRequirement::AllowDeath
            );

            // Try to claim
            assert_noop!(
                Claims::claim(
                    RuntimeOrigin::none(),
                    42,
                    sig::<Test>(&alice(), &42u64.encode(), &[][..])
                ),
                Error::<Test>::InsufficientPalletBalance
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
            assert_ok!(Claims::register_claim(RuntimeOrigin::root(), old_eth, claim_amount));

            // Move claim from Alice to Bob
            assert_ok!(Claims::move_claim(RuntimeOrigin::root(), old_eth, new_eth, None));

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
            assert_eq!(pallet_balances::Pallet::<Test>::free_balance(&dest_account), claim_amount);
            assert_eq!(Claims::claims(&new_eth), None);
            assert_eq!(Claims::total(), 0);
        });
    }

    #[test]
    fn real_eth_sig_works() {
        new_test_ext().execute_with(|| {
            // "Pay RUSTs to the TEST account:2a00000000000000"
            let sig = hex!("583d568a6fb8340bdaa270773c2f63843141baeea20a6ca5ab4433c74636b4746b2cf570f07ea80f973e836ac3976778e0d3c624a9799835fefa666bfacb891c1c");
            let sig = EcdsaSignature(sig);
            let dest = 42u64.encode();
            let addr = hex!("c29aab429a74f28b5e0952e2a07142a50dfa17e4");
            let addr = EthereumAddress(addr);
            let claim_amount = 100;

            assert_ok!(Claims::register_claim(RuntimeOrigin::root(), addr, claim_amount));
            assert_ok!(Claims::claim(RuntimeOrigin::none(), 42, sig));
        });
    }
}