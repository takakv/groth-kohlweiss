use p384::{ProjectivePoint, Scalar};

use crate::crypto::commit;
use crate::proof::{Parameters, Transcript};

fn compute_f_ji_product(f: &[Scalar], x: Scalar, i: usize, initial_mask: usize) -> Scalar {
    let mut result = Scalar::ONE;

    let mut mask = initial_mask;
    for f_j in f {
        result *= if (i & mask) != 0 { *f_j } else { x - f_j };
        mask >>= 1;
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

fn verify_loop(ck: ProjectivePoint, parameters: &Parameters, transcript: &Transcript) -> bool {
    let commitments = &transcript.commitments;
    let x = transcript.challenge;
    let response = &transcript.response;

    let c_l = &commitments.c_l;
    let c_a = &commitments.c_a;
    let c_b = &commitments.c_b;

    let f = &response.f;
    let z_a = &response.z_a;
    let z_b = &response.z_b;

    let n = parameters.n;
    for j in 0..n {
        let c_l_j = c_l[j];

        let lhs = (c_l_j * x) + c_a[j];
        let rhs = commit(ck, f[j], z_a[j]);
        if lhs.ne(&rhs) {
            return false;
        }

        let lhs = (c_l_j * (x - f[j])) + c_b[j];
        let rhs = commit(ck, Scalar::ZERO, z_b[j]);
        if lhs.ne(&rhs) {
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
) {
    let n = params.n;
    let cap = params.cap;

    let c_d = &transcript.commitments.c_d;
    let x = transcript.challenge;
    let f = &transcript.response.f;
    let z_d = transcript.response.z_d;

    if !verify_loop(ck, params, transcript) {
        panic!("Proof loop checks failed")
    }

    let (prod_c_d, _) = compute_c_d_product(c_d, x);
    let mut prod_c_i = ProjectivePoint::IDENTITY;

    let mask_start = 1 << (n - 1);
    for i in 0..cap {
        let prod_f_j = compute_f_ji_product(f, x, i, mask_start);
        prod_c_i += commitments[i] * prod_f_j;
    }

    let lhs = prod_c_i + prod_c_d;
    let rhs = commit(ck, Scalar::ZERO, z_d);

    if lhs.ne(&rhs) {
        panic!("Proof final check failed")
    }
}

pub fn verify_membership(
    ck: ProjectivePoint,
    values: &[Scalar],
    commitment: ProjectivePoint,
    params: &Parameters,
    transcript: &Transcript,
) {
    let n = params.n;
    let cap = params.cap;

    let c_d = &transcript.commitments.c_d;
    let x = transcript.challenge;
    let f = &transcript.response.f;
    let z_d = transcript.response.z_d;

    if !verify_loop(ck, params, transcript) {
        panic!("Proof loop checks failed")
    }

    let (prod_c_d, x_exp_n) = compute_c_d_product(c_d, x);

    let lambda = values;
    let mut sum_lambda_p = Scalar::ZERO;

    let mask_start = 1 << (n - 1);
    for i in 0..cap {
        let prod_f_j = compute_f_ji_product(f, x, i, mask_start);
        sum_lambda_p += lambda[i] * prod_f_j;
    }

    let prod_c_i = (commitment * x_exp_n) + commit(ck, -sum_lambda_p, Scalar::ZERO);

    let lhs = prod_c_i + prod_c_d;
    let rhs = commit(ck, Scalar::ZERO, z_d);

    if lhs.ne(&rhs) {
        panic!("Proof final check failed")
    }
}
