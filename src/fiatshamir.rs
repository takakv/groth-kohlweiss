use std::io::Read;

use p384::elliptic_curve::sec1::ToEncodedPoint;
use p384::elliptic_curve::PrimeField;
use p384::{ProjectivePoint, Scalar};
use sha3::digest::{ExtendableOutput, Update};
use sha3::Shake128;

use crate::proof::ProofCommitment;

const BUFFER_SIZE: usize = (Scalar::NUM_BITS / 8) as usize;

pub fn compute_challenge(
    ck: ProjectivePoint,
    commitments: &[ProjectivePoint],
    proof_commitment: &ProofCommitment,
) -> Scalar {
    let mut hasher = Shake128::default();

    hasher.update(ck.to_affine().to_encoded_point(false).as_bytes());

    for c in commitments {
        hasher.update(c.to_affine().to_encoded_point(false).as_bytes());
    }

    let ProofCommitment { c_l, c_a, c_b, c_d } = proof_commitment;
    for j in 0..c_l.len() {
        hasher.update(c_l[j].to_affine().to_encoded_point(false).as_bytes());
        hasher.update(c_a[j].to_affine().to_encoded_point(false).as_bytes());
        hasher.update(c_b[j].to_affine().to_encoded_point(false).as_bytes());
        hasher.update(c_d[j].to_affine().to_encoded_point(false).as_bytes());
    }

    let mut reader = hasher.finalize_xof();
    let mut buf = [0u8; BUFFER_SIZE];

    loop {
        reader.read_exact(&mut buf).unwrap();

        let Ok(scalar) = Scalar::from_slice(&buf) else {
            continue;
        };

        return scalar;
    }
}
