use super::{calc_linear_cost_u32, extract_points, IDENTITY_BASE, IDENTITY_PER_WORD};
use crate::ec_ops::*;
use crate::{Error, Precompile, PrecompileAddress, PrecompileResult, StandardPrecompileFn, Vec};
use elliptic_curve::{
    group::cofactor::CofactorGroup,
    hash2curve::{FromOkm, GroupDigest},
    sec1::{FromEncodedPoint, ModulusSize},
    Curve, CurveArithmetic,
};
use hd_keys_curves::*;

pub const DERIVE_CAIT_SITH_PUBKEY: PrecompileAddress = PrecompileAddress(
    crate::u64_to_b160(245),
    Precompile::Standard(derive_cait_sith_pubkey as StandardPrecompileFn),
);

/// The minimum length of the input.
const MIN_LENGTH: usize = 81;

#[repr(u8)]
pub enum CurveType {
    P256 = 0,
    K256 = 1,
    P384 = 2,
    Ed25519 = 3,
    Ed448 = 4,
    Jubjub = 5,
    Bls12381G1 = 6,
    Bls12381G2 = 7,
    Ristretto25519 = 8,
}

impl TryFrom<u8> for CurveType {
    type Error = String;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::P256),
            1 => Ok(Self::K256),
            2 => Ok(Self::P384),
            3 => Ok(Self::Ed25519),
            4 => Ok(Self::Ed448),
            5 => Ok(Self::Jubjub),
            6 => Ok(Self::Bls12381G1),
            7 => Ok(Self::Bls12381G2),
            8 => Ok(Self::Ristretto25519),
            _ => Err("invalid curve".to_string()),
        }
    }
}

fn derive_cait_sith_pubkey(input: &[u8], gas_limit: u64) -> PrecompileResult {
    println!("Lit Precompile: derive_cait_sith_pubkey");
    let gas_used = calc_linear_cost_u32(input.len(), IDENTITY_BASE, IDENTITY_PER_WORD);
    if gas_used > gas_limit {
        return Err(Error::OutOfGas);
    }

    for i in 0..input.len() {
        if let Ok(params) = DeriveParamCnt::try_from(&input[i..]) {
            return params.derive_public_key().map(|pk| (gas_used, pk));
        }
        if input.len() - i < MIN_LENGTH {
            break;
        }
    }
    Err(Error::OutOfGas)
}

struct DeriveParamCnt<'a> {
    curve_type: CurveType,
    id: &'a [u8],
    cxt: &'a [u8],
    buffer: &'a [u8],
    public_key_count: usize,
}

impl<'a> TryFrom<&'a [u8]> for DeriveParamCnt<'a> {
    type Error = String;

    fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
        let err = Err(format!("invalid length for derive params: {}", value.len()));
        if value.len() < MIN_LENGTH {
            return err;
        }
        let curve_type = CurveType::try_from(value[0])?;

        let mut offset = 1;
        if offset + 4 > value.len() {
            return err;
        }
        let id_len = u32::from_be_bytes([
            value[offset],
            value[offset + 1],
            value[offset + 2],
            value[offset + 3],
        ]) as usize;
        offset += 4;
        if offset + id_len > value.len() || id_len == 0 {
            return err;
        }
        let id = &value[offset..offset + id_len];
        offset += id_len;
        if offset + 4 > value.len() {
            return err;
        }
        let cxt_len = u32::from_be_bytes([
            value[offset],
            value[offset + 1],
            value[offset + 2],
            value[offset + 3],
        ]) as usize;
        offset += 4;
        if offset + cxt_len > value.len() || cxt_len == 0 {
            return err;
        }
        let cxt = &value[offset..offset + cxt_len];
        offset += cxt_len;
        let pks_cnt = u32::from_be_bytes([
            value[offset],
            value[offset + 1],
            value[offset + 2],
            value[offset + 3],
        ]) as usize;
        if pks_cnt < 2 {
            return Err(format!("Insufficient public key count: {}", pks_cnt));
        }
        offset += 4;
        Ok(Self {
            curve_type,
            id,
            cxt,
            buffer: &value[offset..],
            public_key_count: pks_cnt,
        })
    }
}

impl<'a> DeriveParamCnt<'a> {
    pub fn derive_public_key(&self) -> Result<Vec<u8>, Error> {
        match self.curve_type {
            CurveType::P256 => {
                self.compute_new_public_key::<p256::ProjectivePoint, p256::Scalar, _, _>(
                    prime256v1_points,
                    prime256v1_point_out,
                )
            },
            CurveType::K256 => {
                self.compute_new_public_key::<k256::ProjectivePoint, k256::Scalar, _, _>(
                    secp256k1_points,
                    secp256k1_point_out,
                )
            },
            CurveType::P384 => {
                self.compute_new_public_key::<p384::ProjectivePoint, p384::Scalar, _, _>(
                    secp384r1_points,
                    secp384r1_point_out,
                )
            },
            CurveType::Ed25519 => {
                self.compute_new_public_key::<curve25519_dalek::EdwardsPoint, curve25519_dalek::Scalar, _, _>(
                    curve25519_points,
                    curve25519_point_out
                )
            },
            CurveType::Ed448 => {
                self.compute_new_public_key::<ed448_goldilocks_plus::EdwardsPoint, ed448_goldilocks_plus::Scalar, _, _>(
                    curve448_points,
                    curve448_point_out,
                )
            },
            CurveType::Jubjub => {
                self.compute_new_public_key::<jubjub::SubgroupPoint, jubjub::Scalar, _, _>(
                    jubjub_points,
                    jubjub_point_out,
                )
            },
            CurveType::Bls12381G1 => {
                self.compute_new_public_key::<blsful::inner_types::G1Projective, blsful::inner_types::Scalar, _, _>(
                    bls12381g1_points,
                    |pk| pk.to_uncompressed().to_vec()
                )
            },
            CurveType::Bls12381G2 => {
                self.compute_new_public_key::<blsful::inner_types::G2Projective, blsful::inner_types::Scalar, _, _>(
                    bls12381g2_points,
                    |pk| pk.to_uncompressed().to_vec()
                )
            },
            CurveType::Ristretto25519 => {
                self.compute_new_public_key::<curve25519_dalek::RistrettoPoint, curve25519_dalek::Scalar, _, _>(
                    ristretto25519_points,
                    ristretto25519_point_out
                )
            }
        }
    }

    fn compute_new_public_key<B, D, F, O>(
        &self,
        convert_points: F,
        out_point: O,
    ) -> Result<Vec<u8>, Error>
    where
        B: HDDerivable<Scalar = D>,
        D: HDDeriver,
        F: Fn(&[u8], usize) -> Result<(&[u8], Vec<B>), Error>,
        O: Fn(&B) -> Vec<u8>,
    {
        let (_, public_keys) = convert_points(self.buffer, self.public_key_count)?;
        let tweak = D::create(self.id, self.cxt);
        let pk = tweak.hd_derive_public_key(&public_keys);
        Ok(out_point(&pk))
    }
}

#[deprecated(since = "2.0.3", note = "Please use DeriveParamsCnt instead")]
struct DeriveParams<C>
where
    C: GroupDigest,
    <C as CurveArithmetic>::ProjectivePoint: CofactorGroup,
    <C as CurveArithmetic>::AffinePoint: FromEncodedPoint<C>,
    <C as CurveArithmetic>::Scalar: FromOkm,
    <C as Curve>::FieldBytesSize: ModulusSize,
{
    id: Vec<u8>,
    cxt: Vec<u8>,
    root_hd_keys: Vec<C::ProjectivePoint>,
}

impl<C> TryFrom<&[u8]> for DeriveParams<C>
where
    C: GroupDigest,
    <C as CurveArithmetic>::ProjectivePoint: CofactorGroup,
    <C as CurveArithmetic>::AffinePoint: FromEncodedPoint<C>,
    <C as CurveArithmetic>::Scalar: FromOkm,
    <C as Curve>::FieldBytesSize: ModulusSize,
{
    type Error = String;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let err = Err(format!("invalid length for derive params: {}", value.len()));
        if value.len() < MIN_LENGTH {
            return err;
        }

        let mut offset = 0;
        if offset + 4 > value.len() {
            return err;
        }
        let id_len = u32::from_be_bytes([
            value[offset],
            value[offset + 1],
            value[offset + 2],
            value[offset + 3],
        ]) as usize;
        offset += 4;
        if offset + id_len > value.len() || id_len == 0 {
            return err;
        }
        let id = value[offset..offset + id_len].to_vec();
        offset += id_len;
        if offset + 4 > value.len() {
            return err;
        }
        let cxt_len = u32::from_be_bytes([
            value[offset],
            value[offset + 1],
            value[offset + 2],
            value[offset + 3],
        ]) as usize;
        offset += 4;
        if offset + cxt_len > value.len() || cxt_len == 0 {
            return err;
        }
        let cxt = value[offset..offset + cxt_len].to_vec();
        offset += cxt_len;
        let pks_cnt = u32::from_be_bytes([
            value[offset],
            value[offset + 1],
            value[offset + 2],
            value[offset + 3],
        ]) as usize;

        if pks_cnt < 2 || (offset + pks_cnt * 33) > value.len() {
            return err;
        }

        offset += 4;
        let root_hd_keys = extract_points::<C>(&value[offset..], pks_cnt)?;
        Ok(DeriveParams {
            id,
            cxt,
            root_hd_keys,
        })
    }
}

#[test]
fn derive_precompile_works() {
    use crate::bytes_to_projective_point;

    let k256_vectors = TestVector {
        tweaks: vec![
            scalar_from_hex::<k256::Scalar>(
                "80efe4d28a41cf962133bfcaa2807d38a7f5cec16941cc6d6eec8e76185d2a43",
            ),
            scalar_from_hex::<k256::Scalar>(
                "5afd988c6086d335f892a43ccf943d3973814eadd315adc04bb12808f1c1ac4e",
            ),
            scalar_from_hex::<k256::Scalar>(
                "666f2ce0352e74402c16c02df1b8c29334898e89792eb3ccea54172289c8683b",
            ),
            scalar_from_hex::<k256::Scalar>(
                "d8d9ab7eb84354614b196236009e60f10f28c1c389013c53c907d203f69c9dcf",
            ),
            scalar_from_hex::<k256::Scalar>(
                "8be371c633650ced7b804f127f7c657ec555abc9b9388bdaff3768089e35f1e7",
            ),
        ],
        derived_secret_keys: vec![
            scalar_from_hex::<k256::Scalar>(
                "028b65b2be48d4995b4605fd15d9fe84a8a2aa2844413144e7fd639f02cb3cec",
            ),
            scalar_from_hex::<k256::Scalar>(
                "5afd988c6086d335f892a43ccf943d3973814eadd315adc04bb12808f1c1ac4e",
            ),
            scalar_from_hex::<k256::Scalar>(
                "666f2ce0352e74402c16c02df1b8c29334898e89792eb3ccea54172289c8683b",
            ),
            scalar_from_hex::<k256::Scalar>(
                "d8d9ab7eb84354614b196236009e60f10f28c1c389013c53c907d203f69c9dcf",
            ),
            scalar_from_hex::<k256::Scalar>(
                "8be371c633650ced7b804f127f7c657ec555abc9b9388bdaff3768089e35f1e7",
            ),
        ],
        derived_public_keys: vec![
            bytes_to_projective_point::<k256::Secp256k1>(
                &hex::decode("03da91c23e934cfa868670f46f8e984c6ab6b2f72177917ab30f34f842a0e26bd5")
                    .unwrap(),
            )
            .unwrap(),
            bytes_to_projective_point::<k256::Secp256k1>(
                &hex::decode("038a4f4d11de67b125728db83c8c8d08e62dd4c9af93d8697e3c540287c2775a74")
                    .unwrap(),
            )
            .unwrap(),
            bytes_to_projective_point::<k256::Secp256k1>(
                &hex::decode("028debebba9542d40dae7845fc063176dce0743bff37dca74ce452952b7ec62f55")
                    .unwrap(),
            )
            .unwrap(),
            bytes_to_projective_point::<k256::Secp256k1>(
                &hex::decode("038bd9b34d3be3ac6000a29d3ead1010d1017a69f85a11057bfaa6912e8f0f5fdd")
                    .unwrap(),
            )
            .unwrap(),
            bytes_to_projective_point::<k256::Secp256k1>(
                &hex::decode("03f57045f267f445992a0f03f6fe7f558e0196ce29f625ba729c98ee2893694ab9")
                    .unwrap(),
            )
            .unwrap(),
        ],
    };

    compute_key_test_vectors::<k256::Secp256k1>(k256_vectors);
}

#[test]
fn run_test_k256() {
    let input = hex::decode("0100000020b6b29bd7863f9d949c1352e0f3cf4b4cc194846e6b5dda28bda465b79e1d83630000002b4c49545f48445f4b45595f49445f4b3235365f584d443a5348412d3235365f535357555f524f5f4e554c5f00000002706ed9fbf152fcc24fa744f727fb3f1e309344f458f6f1ce5ac395785c40b758d1708a19d70e9eb8f04dded74302e302230ca839d9b0a6b512ebaf6180c397ae48a534627a648dc2f3a555ae215d887a38d1983b962a32215a4c8ab01817aed0405f2ebd4571adc68aab5d1be4193d2bedf2d7ec3c0d5623374509efc16a5aac").unwrap();
    let temp = hex::decode(&input).unwrap();
    let res = derive_cait_sith_pubkey(&temp, 1000000000000000000);
    assert!(res.is_ok());
}

#[cfg(test)]
fn scalar_from_hex<F: elliptic_curve::PrimeField>(s: &str) -> F {
    scalar_from_bytes::<F>(&hex::decode(s).unwrap())
}

#[cfg(test)]
fn scalar_from_bytes<F: elliptic_curve::PrimeField>(s: &[u8]) -> F {
    let mut repr = F::Repr::default();
    repr.as_mut().copy_from_slice(s);
    F::from_repr(repr).unwrap()
}

#[cfg(test)]
fn compute_key_test_vectors<C>(test_vectors: TestVector<C>)
where
    C: GroupDigest,
    <C as CurveArithmetic>::ProjectivePoint: CofactorGroup,
    <C as CurveArithmetic>::AffinePoint: FromEncodedPoint<C>,
    <C as CurveArithmetic>::Scalar: FromOkm,
    <C as Curve>::FieldBytesSize: ModulusSize,
{
    let root_secret_keys = [
        scalar_from_bytes::<k256::Scalar>(&[
            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3,
        ]),
        scalar_from_bytes::<k256::Scalar>(&[
            5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
            5, 5, 5,
        ]),
        scalar_from_bytes::<k256::Scalar>(&[
            7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
            7, 7, 7,
        ]),
        scalar_from_bytes::<k256::Scalar>(&[
            11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
            11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
        ]),
        scalar_from_bytes::<k256::Scalar>(&[
            13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
            13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
        ]),
    ];
    let root_public_keys = [
        k256::ProjectivePoint::GENERATOR * root_secret_keys[0],
        k256::ProjectivePoint::GENERATOR * root_secret_keys[1],
        k256::ProjectivePoint::GENERATOR * root_secret_keys[2],
        k256::ProjectivePoint::GENERATOR * root_secret_keys[3],
        k256::ProjectivePoint::GENERATOR * root_secret_keys[4],
    ];
    // let ids: [&'static [u8]] = [
    //     b"",
    //     b"abc",
    //     b"abcdef0123456789",
    //     b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
    //     b"a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    // ];
}

#[cfg(test)]
struct TestVector<C>
where
    C: GroupDigest,
    <C as CurveArithmetic>::ProjectivePoint: CofactorGroup,
    <C as CurveArithmetic>::AffinePoint: FromEncodedPoint<C>,
    <C as CurveArithmetic>::Scalar: FromOkm,
    <C as Curve>::FieldBytesSize: ModulusSize,
{
    tweaks: Vec<C::Scalar>,
    derived_secret_keys: Vec<C::Scalar>,
    derived_public_keys: Vec<C::ProjectivePoint>,
}
