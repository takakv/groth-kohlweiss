use crypto_bigint::modular::{BoxedMontyForm, ConstMontyForm, MontyForm, MontyParams};
use crypto_bigint::rand_core::{OsRng, RngCore};
use crypto_bigint::{Limb, NonZero, Odd, U384, Uint, Zero};
use p384::elliptic_curve::Field;
use p384::elliptic_curve::group::GroupEncoding;
use p384::{
    AffinePoint, EncodedPoint, FieldBytes, NistP384, ProjectivePoint, Scalar,
    elliptic_curve::{
        PrimeField,
        sec1::{FromEncodedPoint, ToEncodedPoint},
    },
};
use sha3::Shake128;
use sha3::digest::{ExtendableOutput, Update};
use std::io::Read;
use std::num::NonZeroU128;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Sub};

const PADDING_FILL: u8 = 0xFF;
const PADDING_END: u8 = 0xFE;
const IVXV_SHIFT: usize = 10;

const THREE: Limb = Limb::from_u8(3);
const FOUR: NonZero<Limb> = NonZero::<Limb>::new_unwrap(Limb::from_u8(4));

fn encode_to_point(message: &[u8]) -> ProjectivePoint {
    let field_size = 48;

    let padding_head: [Vec<u8>; 11] = [
        vec![0x00],
        vec![0b00111111],
        vec![0b00011111],
        vec![0b00001111],
        vec![0b00000111],
        vec![0b00000011],
        vec![0b00000001],
        vec![0b00000000, 0b11111111],
        vec![0b00000000, 0b01111111],
        vec![0b00000000, 0b00111111],
        vec![0b00000000, 0b00011111],
    ];

    let mut padded = vec![PADDING_FILL; field_size];
    let (meta, msg) = padded.split_at_mut(field_size - message.len());

    let head = &padding_head[IVXV_SHIFT];
    meta[..head.len()].copy_from_slice(head);
    meta[meta.len() - 1] = PADDING_END;
    msg.copy_from_slice(message);

    let p = U384::from_be_hex(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff",
    );
    let a = U384::from_be_hex(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc",
    );
    let b = U384::from_be_hex(
        "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef",
    );
    let exp = p.sub(U384::ONE).shr(1);
    let sqrt_exp = p.add(U384::ONE).shr(2);

    let monty_params = MontyParams::new(Odd::new(p).unwrap());

    let candidate = Uint::from_be_slice(&padded);
    let mut candidate = MontyForm::new(&candidate, monty_params);

    let a = MontyForm::new(&a, monty_params);
    let b = MontyForm::new(&b, monty_params);
    let one = MontyForm::new(&U384::ONE, monty_params);

    let max_tries = 2 << (IVXV_SHIFT - 1);
    for _ in 0..max_tries {
        // y^2 = x^3 + ax + b
        let mut rhs = candidate.square();
        rhs.add_assign(&a);
        rhs.mul_assign(&candidate);
        rhs.add_assign(&b);

        // Only compute the square root for quadratic residues.
        if rhs.pow(&exp).eq(&one) {
            // Here, we require that p mod 4 = 3, which is true for NIST P curves.
            // Otherwise, the modular square root shortcut does not hold.
            assert_eq!(p.rem_limb(FOUR), THREE);

            let root1 = rhs.pow(&sqrt_exp).retrieve();
            let root2 = root1.neg_mod(&p);

            let x_bytes = candidate.retrieve().to_be_bytes();
            let y_bytes = if root1 < root2 {
                root1.to_be_bytes()
            } else {
                root2.to_be_bytes()
            };

            let mut point_bytes = [0x04u8; 96 + 1];
            point_bytes[1..49].copy_from_slice(&x_bytes);
            point_bytes[49..].copy_from_slice(&y_bytes);

            let encoded_point = EncodedPoint::from_bytes(&point_bytes).unwrap();
            return ProjectivePoint::from_encoded_point(&encoded_point).unwrap();
        }

        candidate.add_assign(&one);
    }

    panic!("could not encode message after {} tries", max_tries);
}

fn commit(ck: ProjectivePoint, message: Scalar, r: Scalar) -> ProjectivePoint {
    (ProjectivePoint::GENERATOR * message) + (ck * r)
}

fn fiat_shamir(seed: &[u8]) -> Scalar {
    let mut hasher = Shake128::default();
    hasher.update(seed);

    let mut reader = hasher.finalize_xof();
    let mut buf = [0u8; 48];

    loop {
        reader.read_exact(&mut buf).unwrap();

        let Ok(scalar) = Scalar::from_slice(&buf) else {
            continue;
        };

        return scalar;
    }
}

struct ProofCommitment {
    ca: ProjectivePoint,
    cb: ProjectivePoint,
}

struct ProofResponse {
    f: Scalar,
    za: Scalar,
    zb: Scalar,
}

struct BinaryTranscript {
    commitment: ProofCommitment,
    challenge: Scalar,
    response: ProofResponse,
}

fn prove_binary(ck: ProjectivePoint, m: Scalar, r: Scalar) -> BinaryTranscript {
    let a = Scalar::random(OsRng);
    let s = Scalar::random(OsRng);
    let t = Scalar::random(OsRng);

    let ca = commit(ck, a, s);
    let cb = commit(ck, a * m, t);

    // TODO: implement strong FS.
    let x = fiat_shamir(ca.to_bytes().as_ref());

    let f = m * x + a;
    let za = r * x + s;
    let zb = r * (x - f) + t;

    BinaryTranscript {
        commitment: ProofCommitment { ca, cb },
        challenge: x,
        response: ProofResponse { f, za, zb },
    }
}

fn verify_binary(ck: ProjectivePoint, c: ProjectivePoint, transcript: &BinaryTranscript) {
    let BinaryTranscript {
        commitment,
        challenge,
        response,
    } = transcript;

    let x = fiat_shamir(commitment.ca.to_bytes().as_ref());
    assert_eq!(x, *challenge);

    let lhs_a = c * x + commitment.ca;
    let lhs_b = c * (x - response.f) + commitment.cb;

    let rhs_a = commit(ck, response.f, response.za);
    let rhs_b = commit(ck, Scalar::ZERO, response.zb);

    assert!(lhs_a.eq(&rhs_a));
    assert!(lhs_b.eq(&rhs_b));
}

fn message_to_scalar(message: &[u8]) -> Scalar {
    let mut bytes = [0u8; 48];
    bytes[48 - message.len()..].copy_from_slice(message);
    Scalar::from_slice(&bytes).unwrap()
}

fn commit_index_bits(
    ck: ProjectivePoint,
    idx: usize,
    n: usize,
) -> (Vec<Scalar>, Vec<ProjectivePoint>) {
    let mut bits = Vec::with_capacity(n);
    let mut commitments = Vec::with_capacity(n);

    let mut tmp = idx;
    for i in 0..n {
        let res = {
            if (tmp & 0x01) == 1 {
                Scalar::ONE
            } else {
                Scalar::ZERO
            }
        };
        bits.push(res);
        commitments.push(commit(ck, res, Scalar::ONE));
        tmp >>= 1;
    }

    println!("bits {:?}", bits);
    println!("coms {:?}", commitments);
    (bits, commitments)
}

fn compute_linear_convolution(polys: &[[i32; 2]]) -> Vec<i32> {
    let mut degree = 1;

    let mut poly_left = vec![0; polys.len() + 1];
    poly_left[0] = polys[0][0];
    poly_left[1] = polys[0][1];

    let mut convolution_coefficients = vec![0; polys.len() + 1];

    for h in 1..polys.len() {
        // The degree increases by one since we multiply with linear expressions.
        degree += 1;

        let poly_right = polys[h];
        for k in 0..=degree {
            let mut coefficient = 0;
            for i in 0..=k {
                // The first polynomial must have fewer coefficients than the resulting degree.
                if i >= degree {
                    break;
                }

                let j = k - i;
                // A linear polynomial has exactly two coefficients.
                if j >= 2 {
                    continue;
                }
                coefficient += poly_left[i] * poly_right[j];
            }
            convolution_coefficients[k] = coefficient;
        }
        poly_left.copy_from_slice(&convolution_coefficients);
    }

    convolution_coefficients
}

fn main() {
    println!("Hello, world!");

    let messages = [
        message_to_scalar("0000.101".as_bytes()),
        message_to_scalar("0000.102".as_bytes()),
        Scalar::ZERO,
        message_to_scalar("0000.104".as_bytes()),
        message_to_scalar("0000.105".as_bytes()),
        message_to_scalar("0000.106".as_bytes()),
        message_to_scalar("0000.107".as_bytes()),
        message_to_scalar("0000.108".as_bytes()),
    ];

    // let secret = Scalar::random(OsRng);
    let secret = U384::from_be_hex(
        "788C773608952E9757DCF9E5C9BC9C48CB8F1C650AD6AA87C3BFF0E9E631AD1C435365412903FD7183934B8C21D0AB97",
    );
    let secret = Scalar::from_slice(&secret.to_be_bytes()).unwrap();
    let pk = ProjectivePoint::GENERATOR * secret;

    let l = 3;
    let message = messages[l - 1];
    let commitment = commit(pk, message, secret);

    let binary_transcript = prove_binary(pk, message, secret);
    verify_binary(pk, commitment, &binary_transcript);

    let coeffs = [[1, 2], [3, 4], [2, 5], [7, 14]];
    let conv_coeffs = compute_linear_convolution(&coeffs);
    println!("coeffs {:?}", conv_coeffs.iter().rev().collect::<Vec<_>>());

    let mut commitments = Vec::with_capacity(messages.len());

    for message in messages {
        commitments.push(commitment + commit(pk, message.neg(), Scalar::ZERO));
    }

    let n = 3;
    let cap = 2 << (n - 1);
    println!("n = {}", n);
    println!("N = {}", cap);

    let (bits, index_commitments) = commit_index_bits(pk, l, n);

    // COMMITMENT PHASE
    let mut r = Vec::with_capacity(n);
    let mut a = Vec::with_capacity(n);
    let mut s = Vec::with_capacity(n);
    let mut t = Vec::with_capacity(n);
    let mut rho = Vec::with_capacity(n);

    let mut c_l = Vec::with_capacity(n);
    let mut c_a = Vec::with_capacity(n);
    let mut c_b = Vec::with_capacity(n);

    for _ in 0..n {
        r.push(Scalar::random(OsRng));
        a.push(Scalar::random(OsRng));
        s.push(Scalar::random(OsRng));
        t.push(Scalar::random(OsRng));
        rho.push(Scalar::random(OsRng));
    }

    println!();
    println!("l = {}", l);
    print!("l_bits = ");
    for b in &bits {
        print!("{},", b.to_canonical().to_limbs()[0])
    }
    println!();

    let fake_a = [1, 2, 3];

    let mask_start = 1 << (n - 1);
    for i in 0..cap {
        println!("Loop: i = {}", i);
        let mut mask = mask_start;
        // j represents the index of the currently considered bit of i.
        // E.g. i = 4 has the binary representation 100, and so i_j for j = 0,...,2 represents:
        // i_0 = 1, i_1 = 0, i_2 = 0.
        let mut i_bits_str = String::new();
        let mut l_bits_str = String::new();
        let mut deltas = String::new();
        let mut poly = String::new();

        let mut polynomial_coefficients = vec![0; n + 1];
        polynomial_coefficients[0] = 1;

        for j in 0..n {
            if (i & mask) != 0 {
                // f_{j,1} = l_j * x + a_j
                if (l & mask) == 0 {
                    for idx in 0..polynomial_coefficients.len() {
                        polynomial_coefficients[idx] *= fake_a[j];
                    }
                } else {
                    let mut preceding_coefficient = 0;
                    for idx in 0..polynomial_coefficients.len() {
                        let current_coefficient = polynomial_coefficients[idx];
                        if current_coefficient == 0 {
                            polynomial_coefficients[idx] = preceding_coefficient;
                            // Skip over higher order coefficients, which are all zero.
                            break;
                        }

                        polynomial_coefficients[idx] *= fake_a[j];
                        polynomial_coefficients[idx] += preceding_coefficient;
                        preceding_coefficient = current_coefficient;
                    }
                }
            } else {
                // f_{j,0} = (1 - l_j)x - a_j
                if (l & mask) != 0 {
                    for idx in 0..polynomial_coefficients.len() {
                        polynomial_coefficients[idx] *= -fake_a[j];
                    }
                } else {
                    let mut preceding_coefficient = 0;
                    for idx in 0..polynomial_coefficients.len() {
                        let current_coefficient = polynomial_coefficients[idx];
                        if current_coefficient == 0 {
                            polynomial_coefficients[idx] = preceding_coefficient;
                            // Skip over higher order coefficients, which are all zero.
                            break;
                        }

                        polynomial_coefficients[idx] *= -fake_a[j];
                        polynomial_coefficients[idx] += preceding_coefficient;
                        preceding_coefficient = current_coefficient;
                    }
                }
            }

            let i_j = { if (i & mask) != 0 { 1 } else { 0 } };
            let l_j = { if (l & mask) != 0 { 1 } else { 0 } };

            i_bits_str.push_str(&format!("{}", i_j));
            l_bits_str.push_str(&format!("{}", l_j));
            mask >>= 1;

            let a_j = {
                if i_j == 1 {
                    format!("a_{}", j + 1)
                } else {
                    format!("-a_{}", j + 1)
                }
            };
            let delta = { if i_j == l_j { 1 } else { 0 } };
            deltas.push_str(&format!("{}", delta));

            // let coefficients = [a_j, &format!("{}", delta)];
            poly.push_str(&format!("({} + {}x)", a_j, delta));
        }
        println!("  polycoeff: {:?}", polynomial_coefficients);
        println!("  i_bits = {}", i_bits_str);
        println!("  l_bits = {}", l_bits_str);
        println!("  deltas = {}", deltas);
        println!("  product = {}", poly);
    }

    return;

    //let mut p_i_coefficients = Vec::with_capacity(cap);
    let mask_start = 1 << (n - 1);
    for i in 0..cap {
        println!("Loop: i = {}", i);
        let mut mask = mask_start;
        // j represents the index of the currently considered bit of i.
        // E.g. i = 4 has the binary representation 100, and so i_j for j = 0,...,2 represents:
        // i_0 = 1, i_1 = 0, i_2 = 0.
        let mut i_bits_str = String::new();
        let mut l_bits_str = String::new();
        let mut deltas = String::new();
        let mut poly = String::new();

        let mut polynomial_coefficients = vec![Scalar::ZERO; n + 1];
        polynomial_coefficients[0] = Scalar::ONE;

        for j in 0..n {
            if (i & mask) != 0 {
                // f_{j,1} = l_j * x + a_j
                if (l & mask) == 0 {
                    for idx in 0..polynomial_coefficients.len() {
                        polynomial_coefficients[idx] *= a[j];
                    }
                } else {
                    let mut preceding_coefficient = Scalar::ZERO;
                    for idx in 0..polynomial_coefficients.len() {
                        let current_coefficient = polynomial_coefficients[idx];
                        if current_coefficient == Scalar::ZERO {
                            // Skip over higher order coefficients, which are all zero.
                            break;
                        }

                        polynomial_coefficients[idx] *= a[j];
                        polynomial_coefficients[idx] += preceding_coefficient;
                        preceding_coefficient = current_coefficient;
                    }
                }
            } else {
                // f_{j,0} = (1 - l_j)x - a_j
                if (l & mask) != 0 {
                    for idx in 0..polynomial_coefficients.len() {
                        polynomial_coefficients[idx] *= a[j];
                    }
                } else {
                    let mut preceding_coefficient = Scalar::ZERO;
                    for idx in 0..polynomial_coefficients.len() {
                        let current_coefficient = polynomial_coefficients[idx];
                        if current_coefficient == Scalar::ZERO {
                            // Skip over higher order coefficients, which are all zero.
                            break;
                        }

                        polynomial_coefficients[idx] *= -a[j];
                        polynomial_coefficients[idx] += preceding_coefficient;
                        preceding_coefficient = current_coefficient;
                    }
                }
            }

            let i_j = { if (i & mask) != 0 { 1 } else { 0 } };
            let l_j = { if (l & mask) != 0 { 1 } else { 0 } };

            i_bits_str.push_str(&format!("{}", i_j));
            l_bits_str.push_str(&format!("{}", l_j));
            mask >>= 1;

            let a_j = {
                if i_j == 1 {
                    format!("a_{}", j + 1)
                } else {
                    format!("-a_{}", j + 1)
                }
            };
            let delta = { if i_j == l_j { 1 } else { 0 } };
            deltas.push_str(&format!("{}", delta));

            // let coefficients = [a_j, &format!("{}", delta)];
            poly.push_str(&format!("({} + {}x)", a_j, delta));
        }
        println!("  i_bits = {}", i_bits_str);
        println!("  l_bits = {}", l_bits_str);
        println!("  deltas = {}", deltas);
        println!("  product = {}", poly);
    }

    println!();

    for j in 1..=n {
        let k = j - 1;

        let r_j = r[j - 1];
        let s_j = s[j - 1];
        let t_j = t[j - 1];
        let rho_k = rho[k];

        let l_j = bits[j - 1];
        let a_j = a[j - 1];

        c_l.push(commit(pk, l_j, r_j));
        c_a.push(commit(pk, a_j, s_j));
        c_b.push(commit(pk, l_j * a_j, t_j));
        // let cdk = commit()
    }

    // CHALLENGE PHASE
    let mut x_bytes = [0u8; 16];
    OsRng.fill_bytes(&mut x_bytes);

    let x = message_to_scalar(&x_bytes);

    // RESPONSE PHASE
    let mut f_values = Vec::with_capacity(n);
    let mut za_values = Vec::with_capacity(n);
    let mut zb_values = Vec::with_capacity(n);
    // let mut zd_values = Vec::with_capacity(n);

    for j in 0..n {
        let f_j = bits[j] * x + a[j];
        let za_j = r[j] * x + s[j];
        let zb_j = r[j] * (x - f_j) + t[j];

        f_values.push(f_j);
        za_values.push(za_j);
        zb_values.push(zb_j);
    }

    let mut rho_x_sum = rho[0] * x.pow([0u64]);
    let mut x_exp = x;

    for k in 1..n {
        rho_x_sum.add_assign(rho[k] * x_exp);
        x_exp.mul_assign(&x);
    }

    let zd = (secret * x.pow([n as u64])) - rho_x_sum;

    // VERIFICATION PHASE
    for j in 0..n {
        let c_l_j = c_l[j];

        let lhs = (c_l_j * x) + c_a[j];
        let rhs = commit(pk, f_values[j], za_values[j]);
        println!("check 1 eq {:?}", lhs.eq(&rhs));

        let lhs = (c_l_j * (x - f_values[j])) + c_b[j];
        let rhs = commit(pk, Scalar::ZERO, zb_values[j]);
        println!("check 2 eq {:?}", lhs.eq(&rhs));
    }
}
