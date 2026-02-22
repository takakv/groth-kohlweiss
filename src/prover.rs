use crypto_bigint::rand_core::RngCore;
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use p384::elliptic_curve::Field;
use p384::{ProjectivePoint, Scalar};

use crate::crypto::commit;
use crate::fiatshamir::compute_challenge;
use crate::proof::{Parameters, ProofCommitment, ProofResponse, Transcript, Witness};

struct ProverScalars {
    r: Vec<Scalar>,
    a: Vec<Scalar>,
    s: Vec<Scalar>,
    t: Vec<Scalar>,
    rho: Vec<Scalar>,
}

struct ProverMemory {
    scalars: ProverScalars,
    l: Vec<Scalar>,
}

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

fn vector_from_l_bits(l: usize, n: usize) -> Vec<Scalar> {
    let mut l_bits = Vec::with_capacity(n);

    let mut mask = 1;
    for _ in 0..n {
        l_bits.push(Scalar::conditional_select(
            &Scalar::ONE,
            &Scalar::ZERO,
            (l & mask).ct_eq(&0),
        ));
        mask <<= 1;
    }

    l_bits
}

fn compute_p_i_coefficients(i: usize, a: &[Scalar], l: usize) -> Vec<Scalar> {
    let n = a.len();
    let mut mask = 1;

    let mut coefficients = vec![Scalar::ZERO; n + 1];
    coefficients[0] = Scalar::ONE;

    // j represents the index of the currently considered bit of i and l.
    // E.g. i = 4 has the binary representation 100, and so i_j for j = 0,...,2 represents:
    // i_0 = 1, i_1 = 0, i_2 = 0.
    // In the paper, bits are 1-indexed, rather than 0-indexed.
    for j in 0..n {
        let i_j = (i & mask) != 0;
        let l_j = (l & mask).ct_ne(&0);
        mask <<= 1;

        let a_j = if i_j { a[j] } else { -a[j] };
        let delta = Scalar::conditional_select(
            &Scalar::ZERO,
            &Scalar::ONE,
            l_j.ct_eq(&Choice::from(i_j as u8)),
        );

        let mut carry = Scalar::ZERO;
        for i in 0..=j {
            let new_carry = delta * coefficients[i];
            coefficients[i] *= a_j;
            coefficients[i] += carry;
            carry = new_carry;
        }
        coefficients[j + 1] = carry;
    }

    coefficients
}

// NB! This is not constant time, but might be easier to reason about and slightly faster.
#[allow(dead_code)]
fn compute_p_i_coefficients_vartime(
    i: usize,
    a: &[Scalar],
    l: usize,
) -> Vec<Scalar> {
    let n = a.len();
    let mut mask = 1;

    let mut coefficients = vec![Scalar::ZERO; n + 1];
    coefficients[0] = Scalar::ONE;

    // j represents the index of the currently considered bit of i and l.
    // E.g. i = 4 has the binary representation 100, and so i_j for j = 0,...,2 represents:
    // i_0 = 1, i_1 = 0, i_2 = 0.
    // In the paper, bits are 1-indexed, rather than 0-indexed.
    for j in 0..n {
        let i_j = (i & mask) != 0;
        let l_j = (l & mask) != 0;
        mask <<= 1;

        let a_j = if i_j { a[j] } else { -a[j] };

        if i_j == l_j {
            scale_and_raise_polynomial(&mut coefficients, a_j, j);
        } else {
            scale_polynomial(&mut coefficients, a_j, j);
        }
    }

    coefficients
}

fn get_random_scalars<R: RngCore>(rng: &mut R, count: usize) -> ProverScalars {
    let mut r = Vec::with_capacity(count);
    let mut a = Vec::with_capacity(count);
    let mut s = Vec::with_capacity(count);
    let mut t = Vec::with_capacity(count);
    let mut rho = Vec::with_capacity(count);

    for _ in 0..count {
        r.push(Scalar::random(&mut *rng));
        a.push(Scalar::random(&mut *rng));
        s.push(Scalar::random(&mut *rng));
        t.push(Scalar::random(&mut *rng));
        rho.push(Scalar::random(&mut *rng));
    }

    ProverScalars { r, a, s, t, rho }
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

    let scalars = get_random_scalars(rng, n);
    let ProverScalars { r, a, s, t, rho } = &scalars;

    let mut p_coefficients = Vec::with_capacity(cap);
    for i in 0..cap {
        p_coefficients.push(compute_p_i_coefficients(i, &a, witness.l));
    }

    let mut c_l = Vec::with_capacity(n);
    let mut c_a = Vec::with_capacity(n);
    let mut c_b = Vec::with_capacity(n);
    let mut c_d = Vec::with_capacity(n);

    let l = vector_from_l_bits(witness.l, n);
    for j in 0..n {
        let k = j;

        let mut prod = ProjectivePoint::IDENTITY;
        for i in 0..cap {
            prod += commitments[i] * p_coefficients[i][k];
        }

        let c_l_j = commit(ck, l[j], r[j]);
        let c_a_j = commit(ck, a[j], s[j]);
        let c_b_j = commit(ck, l[j] * a[j], t[j]);
        let c_d_k = prod + commit(ck, Scalar::ZERO, rho[k]);

        c_l.push(c_l_j);
        c_a.push(c_a_j);
        c_b.push(c_b_j);
        c_d.push(c_d_k);
    }

    (
        ProofCommitment { c_l, c_a, c_b, c_d },
        ProverMemory { scalars, l },
    )
}

fn compute_fast_commitments<R: RngCore>(
    rng: &mut R,
    ck: ProjectivePoint,
    messages: &[Scalar],
    params: &Parameters,
    witness: &Witness,
) -> (ProofCommitment, ProverMemory) {
    let n = params.n;
    let cap = params.cap;

    let scalars = get_random_scalars(rng, n);
    let ProverScalars { r, a, s, t, rho } = &scalars;

    let mut d = vec![Scalar::ZERO; n];

    for i in 0..cap {
        // lambda_l = 0, so m_i = lambda_l - lambda_i = 0 - lambda_i = -lambda_i
        let m_i = -messages[i];
        let p_i_coefficients = compute_p_i_coefficients(i, &a, witness.l);

        for k in 0..n {
            d[k] += m_i * p_i_coefficients[k];
        }
    }

    let mut c_l = Vec::with_capacity(n);
    let mut c_a = Vec::with_capacity(n);
    let mut c_b = Vec::with_capacity(n);
    let mut c_d = Vec::with_capacity(n);

    let l = vector_from_l_bits(witness.l, n);
    for j in 0..n {
        let k = j;

        let c_l_j = commit(ck, l[j], r[j]);
        let c_a_j = commit(ck, a[j], s[j]);
        let c_b_j = commit(ck, l[j] * a[j], t[j]);

        // Since all commitments have the same randomness, phi(x) = 0 and so phi_k = 0 for all k.
        // It follows that c_d_k = Com_ck(d_k, rho_k).
        let c_d_k = commit(ck, d[k], rho[k]);

        c_l.push(c_l_j);
        c_a.push(c_a_j);
        c_b.push(c_b_j);
        c_d.push(c_d_k);
    }

    (
        ProofCommitment { c_l, c_a, c_b, c_d },
        ProverMemory { scalars, l },
    )
}

fn compute_response(
    params: &Parameters,
    memory: ProverMemory,
    witness: &Witness,
    challenge: Scalar,
) -> ProofResponse {
    let n = params.n;
    let x = challenge;

    let ProverMemory { scalars, l } = memory;
    let ProverScalars { r, a, s, t, rho } = &scalars;

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
    witness: &Witness,
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

pub fn ni_prove_membership<R: RngCore>(
    rng: &mut R,
    ck: ProjectivePoint,
    commitments: &[ProjectivePoint],
    values: &[Scalar],
    params: &Parameters,
    witness: &Witness,
) -> Transcript {
    let (proof_commitments, memory) = compute_fast_commitments(rng, ck, &values, &params, &witness);
    let challenge = compute_challenge(ck, &commitments, &proof_commitments);
    let response = compute_response(&params, memory, witness, challenge);

    Transcript {
        commitments: proof_commitments,
        challenge,
        response,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crypto_bigint::rand_core::OsRng;

    fn get_scalars(count: usize) -> Vec<Scalar> {
        let mut scalars = Vec::with_capacity(count);
        for _ in 0..count {
            scalars.push(Scalar::random(OsRng))
        }

        scalars
    }

    #[test]
    fn var_const_coefficients_match() {
        let n = 10;
        let cap = 2usize.pow(n as u32);

        let a = get_scalars(n);

        let secret_index = 13;

        for i in 0..cap {
            let const_coefficients = compute_p_i_coefficients(i, &a, secret_index);
            let var_coefficients =
                compute_p_i_coefficients_vartime(i, &a, secret_index);

            for j in 0..n {
                assert_eq!(const_coefficients[j], var_coefficients[j]);
            }
        }
    }

    #[test]
    fn p_coefficients_correctness() {
        let n = 10;
        let cap = 2usize.pow(n as u32);

        let a = get_scalars(n);

        let secret_index = 13;

        let x = Scalar::from_u64(987654321).cube();
        let mut powers_of_x = vec![Scalar::ONE; n + 1];
        for k in 1..=n {
            powers_of_x[k] = powers_of_x[k - 1] * x;
        }

        let l = vector_from_l_bits(secret_index, n);
        for i in 0..cap {
            let coefficients = compute_p_i_coefficients_vartime(i, &a, secret_index);

            let mut sum = Scalar::ZERO;
            for k in 0..=n {
                sum += coefficients[k] * powers_of_x[k];
            }

            let mut prod = Scalar::ONE;
            let mut mask = 1;

            for j in 0..n {
                let f_j = (l[j] * x) + a[j];
                prod *= if (i & mask) != 0 { f_j } else { x - f_j };
                mask <<= 1;
            }

            assert_eq!(sum, prod);
        }
    }
}
