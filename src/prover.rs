use crypto_bigint::rand_core::RngCore;
use p384::elliptic_curve::Field;
use p384::{ProjectivePoint, Scalar};

use crate::fiatshamir::compute_challenge;
use crate::proof::{ProofCommitment, ProofResponse, Transcript, Witness};
use crate::{commit, Parameters};

fn scale_polynomial(coefficients: &mut [Scalar], factor: Scalar, degree: usize) {
    for i in 0..=degree {
        coefficients[i] *= factor;
    }
}

fn scale_and_raise_polynomial(coefficients: &mut [Scalar], factor: Scalar, degree: usize) {
    let mut carry = Scalar::ZERO;
    for i in 0..=degree {
        let new_carry = coefficients[i];
        coefficients[i] *= factor;
        coefficients[i] += carry;
        carry = new_carry;
    }
    coefficients[degree + 1] = carry;
}

struct ProverMemory {
    r: Vec<Scalar>,
    a: Vec<Scalar>,
    s: Vec<Scalar>,
    t: Vec<Scalar>,
    rho: Vec<Scalar>,
    l: Vec<Scalar>,
}

fn compute_full_commitments<R: RngCore>(
    rng: &mut R,
    ck: ProjectivePoint,
    commitments: &[ProjectivePoint],
    params: &Parameters,
    witness: &Witness,
) -> (ProofCommitment, ProverMemory) {
    let n = params.n;
    let cap = params.cap;

    let mut r = Vec::with_capacity(n);
    let mut a = Vec::with_capacity(n);
    let mut s = Vec::with_capacity(n);
    let mut t = Vec::with_capacity(n);
    let mut rho = Vec::with_capacity(n);

    for _ in 0..n {
        r.push(Scalar::random(&mut *rng));
        a.push(Scalar::random(&mut *rng));
        s.push(Scalar::random(&mut *rng));
        t.push(Scalar::random(&mut *rng));
        rho.push(Scalar::random(&mut *rng));
    }

    let mut l = Vec::with_capacity(n);
    let mut p_coefficients = Vec::with_capacity(cap);

    let mask_start = 1 << (n - 1);
    for i in 0..cap {
        let mut mask = mask_start;

        let mut coefficients = vec![Scalar::ZERO; n + 1];
        coefficients[0] = Scalar::ONE;

        // j represents the index of the currently considered bit of i and l.
        // E.g. i = 4 has the binary representation 100, and so i_j for j = 0,...,2 represents:
        // i_0 = 1, i_1 = 0, i_2 = 0.
        // In the paper, bits are 1-indexed, rather than 0-indexed.
        for j in 0..n {
            let i_j = (i & mask) != 0;
            let l_j = (witness.l & mask) != 0;

            l.push(if l_j { Scalar::ONE } else { Scalar::ZERO });

            mask >>= 1;

            let a_j = if i_j { a[j] } else { -a[j] };

            if i_j == l_j {
                scale_and_raise_polynomial(&mut coefficients, a_j, j);
            } else {
                scale_polynomial(&mut coefficients, a_j, j);
            }
        }
        p_coefficients.push(coefficients);
    }

    let mut c_l = Vec::with_capacity(n);
    let mut c_a = Vec::with_capacity(n);
    let mut c_b = Vec::with_capacity(n);
    let mut c_d = Vec::with_capacity(n);

    for j in 0..n {
        let k = j;

        let mut prod = ProjectivePoint::IDENTITY;
        for i in 0..cap {
            prod += commitments[i] * p_coefficients[i][k];
        }

        c_l.push(commit(ck, l[j], r[j]));
        c_a.push(commit(ck, a[j], s[j]));
        c_b.push(commit(ck, l[j] * a[j], t[j]));
        c_d.push(prod + commit(ck, Scalar::ZERO, rho[k]));
    }

    (
        ProofCommitment { c_l, c_a, c_b, c_d },
        ProverMemory { r, a, s, t, rho, l },
    )
}

fn compute_response(
    params: &Parameters,
    memory: ProverMemory,
    witness: Witness,
    challenge: Scalar,
) -> ProofResponse {
    let n = params.n;
    let x = challenge;

    let ProverMemory { r, a, s, t, rho, l } = memory;

    let mut f = Vec::with_capacity(n);
    let mut z_a = Vec::with_capacity(n);
    let mut z_b = Vec::with_capacity(n);

    for j in 0..n {
        let f_j = l[j] * x + a[j];
        let z_a_j = r[j] * x + s[j];
        let z_b_j = r[j] * (x - f_j) + t[j];

        f.push(f_j);
        z_a.push(z_a_j);
        z_b.push(z_b_j);
    }

    let mut rho_x_sum = rho[0];
    let mut x_exp = x;

    for k in 1..n {
        rho_x_sum += rho[k] * x_exp;
        x_exp *= x;
    }

    let z_d = (witness.r * x_exp) - rho_x_sum;

    ProofResponse { f, z_a, z_b, z_d }
}

pub fn ni_prove_commitment_to_0<R: RngCore>(
    rng: &mut R,
    ck: ProjectivePoint,
    commitments: &[ProjectivePoint],
    params: &Parameters,
    witness: Witness,
) -> Transcript {
    let (proof_commitments, memory) =
        compute_full_commitments(rng, ck, &commitments, &params, &witness);
    let challenge = compute_challenge(ck, &commitments, &proof_commitments);
    let response = compute_response(&params, memory, witness, challenge);

    Transcript {
        commitments: proof_commitments,
        challenge,
        response,
    }
}
