use crypto_bigint::rand_core::{OsRng, RngCore};
use p384::elliptic_curve::Field;
use p384::{ProjectivePoint, Scalar};

fn commit(ck: ProjectivePoint, message: Scalar, r: Scalar) -> ProjectivePoint {
    (ProjectivePoint::GENERATOR * message) + (ck * r)
}

fn message_to_scalar(message: &[u8]) -> Scalar {
    let mut bytes = [0u8; 48];
    bytes[48 - message.len()..].copy_from_slice(message);
    Scalar::from_slice(&bytes).unwrap()
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

struct Witness {
    l: usize,
    r: Scalar,
}

struct Parameters {
    n: usize,
    cap: usize,
}

struct ProofCommitment {
    c_l: Vec<ProjectivePoint>,
    c_a: Vec<ProjectivePoint>,
    c_b: Vec<ProjectivePoint>,
    c_d: Vec<ProjectivePoint>,
}

struct ProofResponse {
    f: Vec<Scalar>,
    z_a: Vec<Scalar>,
    z_b: Vec<Scalar>,
    z_d: Scalar,
}

struct Transcript {
    commitments: ProofCommitment,
    challenge: Scalar,
    response: ProofResponse,
}

fn prove<R: RngCore>(
    rng: &mut R,
    ck: ProjectivePoint,
    commitments: &[ProjectivePoint],
    witness: Witness,
    x: Scalar,
    params: &Parameters,
) -> (ProofCommitment, ProofResponse) {
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

    for j in 1..=n {
        let k = j - 1;

        let r_j = r[j - 1];
        let s_j = s[j - 1];
        let t_j = t[j - 1];
        let rho_k = rho[k];

        let l_j = l[j - 1];
        let a_j = a[j - 1];

        let mut prod = ProjectivePoint::IDENTITY;
        for i in 0..cap {
            prod += commitments[i] * p_coefficients[i][k];
        }

        c_l.push(commit(ck, l_j, r_j));
        c_a.push(commit(ck, a_j, s_j));
        c_b.push(commit(ck, l_j * a_j, t_j));
        c_d.push(prod + commit(ck, Scalar::ZERO, rho_k));
    }

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

    let gk_commitments = ProofCommitment { c_l, c_a, c_b, c_d };
    let gk_response = ProofResponse { f, z_a, z_b, z_d };

    (gk_commitments, gk_response)
}

fn verify(
    ck: ProjectivePoint,
    commitments: &[ProjectivePoint],
    params: &Parameters,
    transcript: &Transcript,
) {
    let n = params.n;
    let cap = params.cap;

    let ProofCommitment { c_l, c_a, c_b, c_d } = &transcript.commitments;
    let x = transcript.challenge;
    let ProofResponse { f, z_a, z_b, z_d } = &transcript.response;

    for j in 0..n {
        let c_l_j = c_l[j];

        let lhs = (c_l_j * x) + c_a[j];
        let rhs = commit(ck, f[j], z_a[j]);
        println!("check 1 eq {:?}", lhs.eq(&rhs));

        let lhs = (c_l_j * (x - f[j])) + c_b[j];
        let rhs = commit(ck, Scalar::ZERO, z_b[j]);
        println!("check 2 eq {:?}", lhs.eq(&rhs));
    }

    let mut prod_c_i = ProjectivePoint::IDENTITY;

    let mask_start = 1 << (n - 1);
    for i in 0..cap {
        let mut prod_f_j = Scalar::ONE;

        let mut mask = mask_start;
        for j in 0..n {
            prod_f_j *= if (i & mask) != 0 { f[j] } else { x - f[j] };
            mask >>= 1;
        }

        prod_c_i += commitments[i] * prod_f_j;
    }

    let mut prod_c_d = -c_d[0];
    let mut x_neg_exp = -x;

    for k in 1..n {
        prod_c_d += c_d[k] * (x_neg_exp);
        x_neg_exp *= x;
    }

    let lhs = prod_c_i + prod_c_d;
    let rhs = commit(ck, Scalar::ZERO, *z_d);

    println!("Check final eq {:?}", lhs.eq(&rhs));
}

fn main() {
    let mut messages = vec![
        message_to_scalar("0000.101".as_bytes()),
        message_to_scalar("0000.102".as_bytes()),
        message_to_scalar("0000.103".as_bytes()),
        message_to_scalar("0000.104".as_bytes()),
        message_to_scalar("0000.105".as_bytes()),
        message_to_scalar("0000.106".as_bytes()),
        message_to_scalar("0000.107".as_bytes()),
        message_to_scalar("0000.108".as_bytes()),
    ];

    let cap = messages.len().next_power_of_two();
    let n = cap.ilog2() as usize;
    let parameters = Parameters { n, cap };

    if cap != messages.len() {
        let pad = vec![messages[0]; cap - messages.len()];
        messages.extend(pad);
    }

    let mut rng = OsRng;

    let secret = Scalar::random(&mut rng);
    let pk = ProjectivePoint::GENERATOR * secret;

    let mut commitments = Vec::with_capacity(messages.len());
    for message in &messages {
        commitments.push(commit(pk, *message, Scalar::random(&mut rng)));
    }

    let l = 3;
    let r = Scalar::random(&mut rng);
    let witness = Witness { l, r };

    messages[l] = Scalar::ZERO;
    commitments[l] = commit(pk, messages[l], r);
    assert_eq!(commitments[l], commit(pk, Scalar::ZERO, r));

    let mut x_bytes = [0u8; 16];
    OsRng.fill_bytes(&mut x_bytes);

    let x = message_to_scalar(&x_bytes);

    let (gk_commitments, gk_response) = prove(&mut rng, pk, &commitments, witness, x, &parameters);

    let transcript = Transcript {
        commitments: gk_commitments,
        challenge: x,
        response: gk_response,
    };

    verify(pk, &commitments, &parameters, &transcript);
}
