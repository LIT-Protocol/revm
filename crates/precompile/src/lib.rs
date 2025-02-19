//! # revm-precompile
//!
//! Implementations of EVM precompiled contracts.
#![cfg_attr(not(test), warn(unused_crate_dependencies))]
#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
#[cfg(not(feature = "std"))]
extern crate alloc as std;

pub mod blake2;
#[cfg(feature = "blst")]
pub mod bls12_381;
pub mod bn128;
pub mod fatal_precompile;
pub mod hash;
pub mod identity;
#[cfg(any(feature = "c-kzg", feature = "kzg-rs"))]
pub mod kzg_point_evaluation;
pub mod modexp;
pub mod secp256k1;
#[cfg(feature = "secp256r1")]
pub mod secp256r1;
pub mod utilities;

// Lit Protocol Precompile Additions
pub mod cait_sith_key_deriver;
pub mod ec_ops;

pub use fatal_precompile::fatal_precompile;

#[cfg(all(feature = "c-kzg", feature = "kzg-rs"))]
// silence kzg-rs lint as c-kzg will be used as default if both are enabled.
use kzg_rs as _;
pub use primitives::{
    precompile::{PrecompileError as Error, *},
    Address, Bytes, HashMap, HashSet, Log, B256,
};
#[doc(hidden)]
pub use revm_primitives as primitives;

use cfg_if::cfg_if;
use core::hash::Hash;
use once_cell::race::OnceBox;
use std::{boxed::Box, vec::Vec};

/// The base cost of the operation.
pub(crate) const IDENTITY_BASE: u64 = 15;
/// The cost per word.
pub(crate) const IDENTITY_PER_WORD: u64 = 3;

pub fn calc_linear_cost_u32(len: usize, base: u64, word: u64) -> u64 {
    (len as u64).div_ceil(32) * word + base
}

#[derive(Clone, Default, Debug)]
pub struct Precompiles {
    /// Precompiles.
    inner: HashMap<Address, Precompile>,
    /// Addresses of precompile.
    addresses: HashSet<Address>,
}

impl Precompiles {
    /// Returns the precompiles for the given spec.
    pub fn new(spec: PrecompileSpecId) -> &'static Self {
        match spec {
            PrecompileSpecId::HOMESTEAD => Self::homestead(),
            PrecompileSpecId::BYZANTIUM => Self::byzantium(),
            PrecompileSpecId::ISTANBUL => Self::istanbul(),
            PrecompileSpecId::BERLIN => Self::berlin(),
            PrecompileSpecId::CANCUN => Self::cancun(),
            PrecompileSpecId::PRAGUE => Self::prague(),
            PrecompileSpecId::LATEST => Self::latest(),
        }
    }

    /// Returns precompiles for Homestead spec.
    pub fn homestead() -> &'static Self {
        static INSTANCE: OnceBox<Precompiles> = OnceBox::new();
        INSTANCE.get_or_init(|| {
            let mut precompiles = Precompiles::default();
            precompiles.extend([
                secp256k1::ECRECOVER,
                hash::SHA256,
                hash::RIPEMD160,
                identity::FUN,
                cait_sith_key_deriver::DERIVE_CAIT_SITH_PUBKEY,
                ec_ops::EC_OPERATION,
            ]);
            Box::new(precompiles)
        })
    }

    /// Returns inner HashMap of precompiles.
    pub fn inner(&self) -> &HashMap<Address, Precompile> {
        &self.inner
    }

    /// Returns precompiles for Byzantium spec.
    pub fn byzantium() -> &'static Self {
        static INSTANCE: OnceBox<Precompiles> = OnceBox::new();
        INSTANCE.get_or_init(|| {
            let mut precompiles = Self::homestead().clone();
            precompiles.extend([
                // EIP-196: Precompiled contracts for addition and scalar multiplication on the elliptic curve alt_bn128.
                // EIP-197: Precompiled contracts for optimal ate pairing check on the elliptic curve alt_bn128.
                bn128::add::BYZANTIUM,
                bn128::mul::BYZANTIUM,
                bn128::pair::BYZANTIUM,
                // EIP-198: Big integer modular exponentiation.
                modexp::BYZANTIUM,
            ]);
            Box::new(precompiles)
        })
    }

    /// Returns precompiles for Istanbul spec.
    pub fn istanbul() -> &'static Self {
        static INSTANCE: OnceBox<Precompiles> = OnceBox::new();
        INSTANCE.get_or_init(|| {
            let mut precompiles = Self::byzantium().clone();
            precompiles.extend([
                // EIP-1108: Reduce alt_bn128 precompile gas costs.
                bn128::add::ISTANBUL,
                bn128::mul::ISTANBUL,
                bn128::pair::ISTANBUL,
                // EIP-152: Add BLAKE2 compression function `F` precompile.
                blake2::FUN,
            ]);
            Box::new(precompiles)
        })
    }

    /// Returns precompiles for Berlin spec.
    pub fn berlin() -> &'static Self {
        static INSTANCE: OnceBox<Precompiles> = OnceBox::new();
        INSTANCE.get_or_init(|| {
            let mut precompiles = Self::istanbul().clone();
            precompiles.extend([
                // EIP-2565: ModExp Gas Cost.
                modexp::BERLIN,
            ]);
            Box::new(precompiles)
        })
    }

    /// Returns precompiles for Cancun spec.
    ///
    /// If the `c-kzg` feature is not enabled KZG Point Evaluation precompile will not be included,
    /// effectively making this the same as Berlin.
    pub fn cancun() -> &'static Self {
        static INSTANCE: OnceBox<Precompiles> = OnceBox::new();
        INSTANCE.get_or_init(|| {
            let mut precompiles = Self::berlin().clone();

            // EIP-4844: Shard Blob Transactions
            cfg_if! {
                if #[cfg(any(feature = "c-kzg", feature = "kzg-rs"))] {
                    let precompile = kzg_point_evaluation::POINT_EVALUATION.clone();
                } else {
                    // TODO move constants to separate file.
                    let precompile = fatal_precompile(u64_to_address(0x0A), "c-kzg feature is not enabled".into());
                }
            }

            precompiles.extend([
                precompile,
            ]);

            Box::new(precompiles)
        })
    }

    /// Returns precompiles for Prague spec.
    pub fn prague() -> &'static Self {
        static INSTANCE: OnceBox<Precompiles> = OnceBox::new();
        INSTANCE.get_or_init(|| {
            let precompiles = Self::cancun().clone();

            // Don't include BLS12-381 precompiles in no_std builds.
            #[cfg(feature = "blst")]
            let precompiles = {
                let mut precompiles = precompiles;
                precompiles.extend(bls12_381::precompiles());
                precompiles
            };

            Box::new(precompiles)
        })
    }

    /// Returns the precompiles for the latest spec.
    pub fn latest() -> &'static Self {
        Self::prague()
    }

    /// Returns an iterator over the precompiles addresses.
    #[inline]
    pub fn addresses(&self) -> impl ExactSizeIterator<Item = &Address> {
        self.inner.keys()
    }

    /// Consumes the type and returns all precompile addresses.
    #[inline]
    pub fn into_addresses(self) -> impl ExactSizeIterator<Item = Address> {
        self.inner.into_keys()
    }

    /// Is the given address a precompile.
    #[inline]
    pub fn contains(&self, address: &Address) -> bool {
        self.inner.contains_key(address)
    }

    /// Returns the precompile for the given address.
    #[inline]
    pub fn get(&self, address: &Address) -> Option<&Precompile> {
        self.inner.get(address)
    }

    /// Returns the precompile for the given address.
    #[inline]
    pub fn get_mut(&mut self, address: &Address) -> Option<&mut Precompile> {
        self.inner.get_mut(address)
    }

    /// Is the precompiles list empty.
    pub fn is_empty(&self) -> bool {
        self.inner.len() == 0
    }

    /// Returns the number of precompiles.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns the precompiles addresses as a set.
    pub fn addresses_set(&self) -> &HashSet<Address> {
        &self.addresses
    }

    /// Extends the precompiles with the given precompiles.
    ///
    /// Other precompiles with overwrite existing precompiles.
    #[inline]
    pub fn extend(&mut self, other: impl IntoIterator<Item = PrecompileWithAddress>) {
        let items = other.into_iter().collect::<Vec<_>>();
        self.addresses.extend(items.iter().map(|p| *p.address()));
        self.inner.extend(items.into_iter().map(Into::into));
    }
}

#[derive(Clone, Debug)]
pub struct PrecompileWithAddress(pub Address, pub Precompile);

impl From<(Address, Precompile)> for PrecompileWithAddress {
    fn from(value: (Address, Precompile)) -> Self {
        PrecompileWithAddress(value.0, value.1)
    }
}

impl From<PrecompileWithAddress> for (Address, Precompile) {
    fn from(value: PrecompileWithAddress) -> Self {
        (value.0, value.1)
    }
}

impl PrecompileWithAddress {
    /// Returns reference of address.
    #[inline]
    pub fn address(&self) -> &Address {
        &self.0
    }

    /// Returns reference of precompile.
    #[inline]
    pub fn precompile(&self) -> &Precompile {
        &self.1
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum PrecompileSpecId {
    HOMESTEAD,
    BYZANTIUM,
    ISTANBUL,
    BERLIN,
    CANCUN,
    PRAGUE,
    LATEST,
}

impl PrecompileSpecId {
    /// Returns the appropriate precompile Spec for the primitive [SpecId](revm_primitives::SpecId)
    pub const fn from_spec_id(spec_id: revm_primitives::SpecId) -> Self {
        use revm_primitives::SpecId::*;
        match spec_id {
            FRONTIER | FRONTIER_THAWING | HOMESTEAD | DAO_FORK | TANGERINE | SPURIOUS_DRAGON => {
                Self::HOMESTEAD
            }
            BYZANTIUM | CONSTANTINOPLE | PETERSBURG => Self::BYZANTIUM,
            ISTANBUL | MUIR_GLACIER => Self::ISTANBUL,
            BERLIN | LONDON | ARROW_GLACIER | GRAY_GLACIER | MERGE | SHANGHAI => Self::BERLIN,
            CANCUN => Self::CANCUN,
            PRAGUE | OSAKA => Self::PRAGUE,
            LATEST => Self::LATEST,
            #[cfg(feature = "optimism")]
            BEDROCK | REGOLITH | CANYON => Self::BERLIN,
            #[cfg(feature = "optimism")]
            ECOTONE | FJORD | GRANITE | HOLOCENE | ISTHMUS => Self::CANCUN,
        }
    }
}

/// Const function for making an address by concatenating the bytes from two given numbers.
///
/// Note that 32 + 128 = 160 = 20 bytes (the length of an address). This function is used
/// as a convenience for specifying the addresses of the various precompiles.
#[inline]
pub const fn u64_to_address(x: u64) -> Address {
    let x = x.to_be_bytes();
    Address::new([
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7],
    ])
}

pub(crate) fn bytes_to_projective_point<C>(data: &[u8]) -> Option<C::ProjectivePoint>
where
    C: elliptic_curve::hash2curve::GroupDigest,
    <C as elliptic_curve::CurveArithmetic>::ProjectivePoint:
        elliptic_curve::group::cofactor::CofactorGroup,
    <C as elliptic_curve::CurveArithmetic>::AffinePoint: elliptic_curve::sec1::FromEncodedPoint<C>,
    <C as elliptic_curve::CurveArithmetic>::Scalar: elliptic_curve::hash2curve::FromOkm,
    <C as elliptic_curve::Curve>::FieldBytesSize: elliptic_curve::sec1::ModulusSize,
{
    let encoded_point = elliptic_curve::sec1::EncodedPoint::<C>::from_bytes(data).ok()?;
    let point = <C::AffinePoint as elliptic_curve::sec1::FromEncodedPoint<C>>::from_encoded_point(
        &encoded_point,
    )
    .map(C::ProjectivePoint::from);
    Option::<C::ProjectivePoint>::from(point)
}
pub(crate) fn extract_points<C>(
    data: &[u8],
    pks_cnt: usize,
) -> Result<Vec<C::ProjectivePoint>, String>
where
    C: elliptic_curve::hash2curve::GroupDigest,
    <C as elliptic_curve::CurveArithmetic>::ProjectivePoint:
        elliptic_curve::group::cofactor::CofactorGroup,
    <C as elliptic_curve::CurveArithmetic>::AffinePoint: elliptic_curve::sec1::FromEncodedPoint<C>,
    <C as elliptic_curve::CurveArithmetic>::Scalar: elliptic_curve::hash2curve::FromOkm,
    <C as elliptic_curve::Curve>::FieldBytesSize: elliptic_curve::sec1::ModulusSize,
{
    let mut offset = 0;
    let mut points = Vec::with_capacity(pks_cnt);
    while offset < data.len() && points.len() < pks_cnt {
        let point = match data[offset] {
            0x04 => {
                // Uncompressed form
                if offset + 65 > data.len() {
                    return Err(format!(
                        "invalid length for uncompressed point: {}",
                        data.len()
                    ));
                }
                let point = bytes_to_projective_point::<C>(&data[offset..offset + 65]);
                offset += 65;
                point
            }
            0x03 | 0x02 => {
                // Compressed form
                if offset + 33 > data.len() {
                    return Err(format!(
                        "invalid length for compressed point: {}",
                        data.len()
                    ));
                }
                let point = bytes_to_projective_point::<C>(&data[offset..offset + 33]);
                offset += 33;
                point
            }
            _ => {
                if offset + 64 > data.len() {
                    return Err(format!("invalid length for hybrid point: {}", data.len()));
                }
                let mut tmp = [4u8; 65];
                tmp[1..].copy_from_slice(&data[offset..offset + 64]);
                let point = bytes_to_projective_point::<C>(&tmp[..]);
                offset += 64;
                point
            }
        };
        if point.is_none() {
            return Err(format!("invalid point at offset {}", offset));
        }
        points.push(point.unwrap());
    }
    Ok(points)
}
