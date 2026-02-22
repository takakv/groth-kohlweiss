use p384::{ProjectivePoint, Scalar};

use crate::crypto::commit;
use crate::proof::{Parameters, Transcript};

#[derive(Debug)]
pub enum VerificationError {
    InconsistentTranscript,
    LoopCheckFailed,
    ProductCheckFailed,
}

fn compute_f_j_ij_product(f: &[Scalar], x: Scalar, i: usize) -> Scalar {
    let mut result = Scalar::ONE;
    let mut mask = 1;

    for f_j in f {
        result *= if (i & mask) != 0 { *f_j } else { x - f_j };
        mask <<= 1;
    }

    result
}

fn compute_c_d_product(c_d: &[ProjectivePoint], x: Scalar) -> (ProjectivePoint, Scalar) {
    let mut result = ProjectivePoint::IDENTITY;
    let mut x_neg_exp = -Scalar::ONE;

    for c_d_k in c_d {
        result += c_d_k * &x_neg_exp;
        x_neg_exp *= x;
    }

    (result, -x_neg_exp)
}

fn all_equal_to(n: usize, lengths: &[usize]) -> bool {
    lengths.iter().all(|&len| len == n)
}

fn validate_transcript_structure(
    params: &Parameters,
    transcript: &Transcript,
) -> Result<(), VerificationError> {
    if !all_equal_to(
        params.n,
        &[
            transcript.commitment.c_l.len(),
            transcript.commitment.c_a.len(),
            transcript.commitment.c_b.len(),
            transcript.commitment.c_d.len(),
            transcript.response.f.len(),
            transcript.response.z_a.len(),
            transcript.response.z_b.len(),
        ],
    ) {
        return Err(VerificationError::InconsistentTranscript);
    }

    Ok(())
}

fn verify_loop(ck: ProjectivePoint, transcript: &Transcript) -> bool {
    let commitments = &transcript.commitment;
    let x = transcript.challenge;
    let response = &transcript.response;

    let c_l = &commitments.c_l;
    let c_a = &commitments.c_a;
    let c_b = &commitments.c_b;

    let f = &response.f;
    let z_a = &response.z_a;
    let z_b = &response.z_b;

    for j in 0..f.len() {
        let c_l_j = c_l[j];

        let lhs = (c_l_j * x) + c_a[j];
        let rhs = commit(ck, f[j], z_a[j]);
        if lhs != rhs {
            return false;
        }

        let lhs = (c_l_j * (x - f[j])) + c_b[j];
        let rhs = commit(ck, Scalar::ZERO, z_b[j]);
        if lhs != rhs {
            return false;
        }
    }

    true
}

pub fn verify_commitment_to_0(
    ck: ProjectivePoint,
    commitments: &[ProjectivePoint],
    params: &Parameters,
    transcript: &Transcript,
) -> Result<(), VerificationError> {
    validate_transcript_structure(params, transcript)?;

    if !verify_loop(ck, transcript) {
        return Err(VerificationError::LoopCheckFailed);
    }

    let c_d = &transcript.commitment.c_d;
    let x = transcript.challenge;
    let f = &transcript.response.f;
    let z_d = transcript.response.z_d;

    let (prod_c_d, _) = compute_c_d_product(c_d, x);
    let mut prod_c_i = ProjectivePoint::IDENTITY;

    for i in 0..params.cap {
        let prod_f_j = compute_f_j_ij_product(f, x, i);
        prod_c_i += commitments[i] * prod_f_j;
    }

    let lhs = prod_c_i + prod_c_d;
    let rhs = commit(ck, Scalar::ZERO, z_d);

    if lhs != rhs {
        return Err(VerificationError::ProductCheckFailed);
    }

    Ok(())
}

pub fn verify_membership(
    ck: ProjectivePoint,
    allowed_values: &[Scalar],
    commitment: ProjectivePoint,
    params: &Parameters,
    transcript: &Transcript,
) -> Result<(), VerificationError> {
    validate_transcript_structure(params, transcript)?;

    if !verify_loop(ck, transcript) {
        return Err(VerificationError::LoopCheckFailed);
    }

    let c_d = &transcript.commitment.c_d;
    let x = transcript.challenge;
    let f = &transcript.response.f;
    let z_d = transcript.response.z_d;

    let (prod_c_d, x_exp_n) = compute_c_d_product(c_d, x);

    let lambda = allowed_values;
    let mut sum_lambda_p = Scalar::ZERO;

    for i in 0..params.cap {
        let prod_f_j = compute_f_j_ij_product(f, x, i);
        sum_lambda_p += lambda[i] * prod_f_j;
    }

    let prod_c_i = (commitment * x_exp_n) + commit(ck, -sum_lambda_p, Scalar::ZERO);

    let lhs = prod_c_i + prod_c_d;
    let rhs = commit(ck, Scalar::ZERO, z_d);

    if lhs != rhs {
        return Err(VerificationError::ProductCheckFailed);
    }

    Ok(())
}
