use crypto_bigint::modular::{MontyForm, MontyParams};
use crypto_bigint::rand_core::{OsRng, RngCore};
use crypto_bigint::{Limb, NonZero, Odd, Uint, U384};
use p384::elliptic_curve::group::GroupEncoding;
use p384::elliptic_curve::Field;
use p384::{elliptic_curve::sec1::FromEncodedPoint, EncodedPoint, ProjectivePoint, Scalar};
use sha3::digest::{ExtendableOutput, Update};
use sha3::Shake128;
use std::io::Read;
use std::ops::{Add, AddAssign, MulAssign, Sub};

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

    let mut mask = 1 << (n - 1);
    for _ in 0..n {
        let res = {
            if (idx & mask) != 0 {
                Scalar::ONE
            } else {
                Scalar::ZERO
            }
        };
        bits.push(res);
        commitments.push(commit(ck, res, Scalar::ONE));
        mask >>= 1;
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
    bits: Vec<Scalar>,
    r: Scalar,
}

struct Parameters {
    n: usize,
    cap: usize,
}

struct GKCommitments {
    c_l: Vec<ProjectivePoint>,
    c_a: Vec<ProjectivePoint>,
    c_b: Vec<ProjectivePoint>,
    c_d: Vec<ProjectivePoint>,
}

struct GKResponse {
    f: Vec<Scalar>,
    z_a: Vec<Scalar>,
    z_b: Vec<Scalar>,
    z_d: Scalar,
}

fn prove(
    ck: ProjectivePoint,
    commitments: &Vec<ProjectivePoint>,
    witness: Witness,
    x: Scalar,
    params: Parameters,
) -> (GKCommitments, GKResponse) {
    let Witness { l, bits, r } = witness;
    let Parameters { n, cap } = params;

    let mut r = Vec::with_capacity(n);
    let mut a = Vec::with_capacity(n);
    let mut s = Vec::with_capacity(n);
    let mut t = Vec::with_capacity(n);
    let mut rho = Vec::with_capacity(n);

    let mut c_l = Vec::with_capacity(n);
    let mut c_a = Vec::with_capacity(n);
    let mut c_b = Vec::with_capacity(n);
    let mut c_d = Vec::with_capacity(n);

    for _ in 0..n {
        r.push(Scalar::ONE);
        a.push(Scalar::ONE);
        s.push(Scalar::ONE);
        t.push(Scalar::ONE);
        rho.push(Scalar::ONE);
    }

    let mut p_coefficients = Vec::with_capacity(cap);

    let mask_start = 1 << (n - 1);
    for i in 0..cap {
        println!("Loop: i = {}", i);
        let mut mask = mask_start;

        let mut coefficients = vec![Scalar::ZERO; n + 1];
        coefficients[0] = Scalar::ONE;

        // j represents the index of the currently considered bit of i and l.
        // E.g. i = 4 has the binary representation 100, and so i_j for j = 0,...,2 represents:
        // i_0 = 1, i_1 = 0, i_2 = 0.
        // In the paper, bits are 1-indexed, rather than 0-indexed.
        for j in 0..n {
            let i_j = (i & mask) != 0;
            let l_j = (l & mask) != 0;

            mask >>= 1;

            let a_j = if i_j { a[j] } else { -a[j] };

            if i_j == l_j {
                scale_and_raise_polynomial(&mut coefficients, a_j, j);
            } else {
                scale_polynomial(&mut coefficients, a_j, j);
            }
        }
        println!("  coefficients = {:?}", coefficients);
        p_coefficients.push(coefficients);
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

        let mut prod = ProjectivePoint::IDENTITY;
        for i in 0..cap {
            prod += commitments[i] * p_coefficients[i][k];
        }

        c_l.push(commit(ck, l_j, r_j));
        c_a.push(commit(ck, a_j, s_j));
        c_b.push(commit(ck, l_j * a_j, t_j));
        c_d.push(prod + commit(ck, Scalar::ZERO, rho_k));
    }

    let mut f_values = Vec::with_capacity(n);
    let mut za_values = Vec::with_capacity(n);
    let mut zb_values = Vec::with_capacity(n);

    for j in 0..n {
        let f_j = bits[j] * x + a[j];
        let za_j = r[j] * x + s[j];
        let zb_j = r[j] * (x - f_j) + t[j];

        f_values.push(f_j);
        za_values.push(za_j);
        zb_values.push(zb_j);
    }

    // BEGIN DEBUG

    // Compute the powers of x.
    let mut powers_of_x = vec![Scalar::ONE; n + 1];
    for k in 1..=n {
        powers_of_x[k] = powers_of_x[k - 1] * x;
    }
    println!("  powers_of_x = {:?}", powers_of_x);

    let mut evaluations_precomputed = Vec::with_capacity(cap);
    let mut evaluations_recomputed = Vec::with_capacity(cap);
    let mut evaluations_response_based = Vec::with_capacity(cap);

    // Evaluate the polynomials using the precomputed coefficients.
    for i in 0..cap {
        // println!("i = {}", i);
        let mut result = Scalar::ZERO;
        let pi_coefficients = &p_coefficients[i];

        for k in 0..pi_coefficients.len() {
            // println!("  Coefficient = {:?}", pi_coefficients[k].to_canonical());
            result += pi_coefficients[k] * powers_of_x[k];
        }
        evaluations_precomputed.push(result);
        // println!("  Result = {:?}", result.to_canonical());
        // println!();
    }

    // println!("---\n");

    // Evaluate the polynomials using the f_{j,i_j} values.
    for i in 0..cap {
        // println!("i = {}", i);
        let mut result = Scalar::ONE;

        let mut mask = 1 << (n - 1);
        for j in 0..n {
            let term = {
                if (i & mask) != 0 {
                    (bits[j] * x) + a[j]
                } else {
                    (Scalar::ONE - bits[j]) * x - a[j]
                }
            };
            mask >>= 1;

            result *= term;
        }
        evaluations_recomputed.push(result);
        // println!("  Result = {:?}", result.to_canonical());
        // println!();
    }

    // println!("---\n");

    // Evaluate the polynomials using the response f_j values.
    for i in 0..cap {
        // println!("i = {}", i);
        let mut result = Scalar::ONE;

        let mut mask = 1 << (n - 1);
        for j in 0..n {
            let term = {
                if (i & mask) != 0 {
                    f_values[j]
                } else {
                    x - f_values[j]
                }
            };
            mask >>= 1;

            result *= term;
        }
        evaluations_response_based.push(result);
        // println!("  Result = {:?}", result.to_canonical());
        // println!();
    }

    for i in 0..cap {
        assert_eq!(evaluations_precomputed[i], evaluations_recomputed[i]);
        assert_eq!(evaluations_precomputed[i], evaluations_response_based[i]);
    }

    // END DEBUG

    let mut rho_x_sum = rho[0];
    let mut x_exp = x;

    for k in 1..n {
        assert_eq!(powers_of_x[k], x_exp);
        rho_x_sum.add_assign(rho[k] * x_exp);
        x_exp.mul_assign(&x);
    }

    assert_eq!(powers_of_x[0], Scalar::ONE);
    assert_eq!(powers_of_x[n], x_exp);

    assert_eq!(rho[0] * x.pow([0u64]), rho[0]);
    assert_eq!(x.pow([n as u64]), x_exp);

    let zd = (witness.r * x_exp) - rho_x_sum;

    let gk_commitments = GKCommitments { c_l, c_a, c_b, c_d };
    let gk_response = GKResponse {
        f: f_values,
        z_a: za_values,
        z_b: zb_values,
        z_d: zd,
    };

    (gk_commitments, gk_response)
}

fn main() {
    println!("Hello, world!");

    let messages = [
        message_to_scalar("0000.101".as_bytes()),
        message_to_scalar("0000.102".as_bytes()),
        message_to_scalar("0000.103".as_bytes()),
        Scalar::ZERO,
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
    let message = messages[l];
    let commitment = commit(pk, message, secret);

    // let binary_transcript = prove_binary(pk, message, secret);
    // verify_binary(pk, commitment, &binary_transcript);

    // let coeffs = [[1, 2], [3, 4], [2, 5], [7, 14]];
    // let conv_coeffs = compute_linear_convolution(&coeffs);
    // println!("coeffs {:?}", conv_coeffs.iter().rev().collect::<Vec<_>>());

    let mut commitments = Vec::with_capacity(messages.len());

    // for message in messages {
    //     commitments.push(commitment + commit(pk, message.neg(), Scalar::ZERO));
    // }

    for message in messages {
        commitments.push(commit(pk, message, Scalar::ZERO));
    }
    commitments[l] = commitment;

    println!("commitments {:?}", commitments);

    let n = 2;
    let cap = 2 << (n - 1);
    println!("n = {}", n);
    println!("N = {}", cap);

    assert!(l < cap);
    assert_eq!(commitments[l], commit(pk, messages[l], secret));
    assert_eq!(commitments[l], commit(pk, Scalar::ZERO, secret));

    let (bits, index_commitments) = commit_index_bits(pk, l, n);

    println!();
    println!("l = {}", l);
    print!("l_bits = ");
    for b in &bits {
        print!("{},", b.to_canonical().to_limbs()[0])
    }
    println!();

    // let a_nums = [2, 3, 4, 5];
    //
    // let mask_start = 1 << (n - 1);
    // for i in 0..cap {
    //     println!("Loop: i = {}", i);
    //     let mut mask = mask_start;
    //     // j represents the index of the currently considered bit of i.
    //     // E.g. i = 4 has the binary representation 100, and so i_j for j = 0,...,2 represents:
    //     // i_0 = 1, i_1 = 0, i_2 = 0.
    //     let mut i_bits_str = String::new();
    //     let mut l_bits_str = String::new();
    //     let mut deltas = String::new();
    //     let mut poly = String::new();
    //
    //     let mut polynomial_coefficients = vec![0; n + 1];
    //     polynomial_coefficients[0] = 1;
    //
    //     for j in 0..n {
    //         let i_j = (i & mask) != 0;
    //         let l_j = (l & mask) != 0;
    //
    //         let a_j = if i_j { a_nums[j] } else { -a_nums[j] };
    //
    //         if i_j == l_j {
    //             scale_and_raise_polynomial(&mut polynomial_coefficients, a_j, j);
    //         } else {
    //             scale_polynomial(&mut polynomial_coefficients, a_j, j);
    //         }
    //
    //         i_bits_str.push_str(&format!("{}", i32::from(i_j)));
    //         l_bits_str.push_str(&format!("{}", i32::from(l_j)));
    //         mask >>= 1;
    //
    //         let a_j = {
    //             if i_j {
    //                 format!("a_{}", j + 1)
    //             } else {
    //                 format!("-a_{}", j + 1)
    //             }
    //         };
    //         let delta = { if i_j == l_j { 1 } else { 0 } };
    //         deltas.push_str(&format!("{}", delta));
    //
    //         // let coefficients = [a_j, &format!("{}", delta)];
    //         poly.push_str(&format!("({} + {}x)", a_j, delta));
    //     }
    //     println!("  polycoeff: {:?}", polynomial_coefficients);
    //     println!("  i_bits = {}", i_bits_str);
    //     println!("  l_bits = {}", l_bits_str);
    //     println!("  deltas = {}", deltas);
    //     println!("  product = {}", poly);
    // }
    //
    // return;

    // CHALLENGE PHASE
    let mut x_bytes = [0u8; 16];
    OsRng.fill_bytes(&mut x_bytes);

    let x = message_to_scalar(&x_bytes);

    let (gk_commitments, gk_response) = prove(
        pk,
        &commitments,
        Witness { l, bits, r: secret },
        x,
        Parameters { n, cap },
    );

    let GKCommitments { c_l, c_a, c_b, c_d } = gk_commitments;
    let GKResponse { f, z_a, z_b, z_d } = gk_response;

    // VERIFICATION PHASE
    for j in 0..n {
        let c_l_j = c_l[j];

        let lhs = (c_l_j * x) + c_a[j];
        let rhs = commit(pk, f[j], z_a[j]);
        println!("check 1 eq {:?}", lhs.eq(&rhs));

        let lhs = (c_l_j * (x - f[j])) + c_b[j];
        let rhs = commit(pk, Scalar::ZERO, z_b[j]);
        println!("check 2 eq {:?}", lhs.eq(&rhs));
    }

    let mut prod_c_i = ProjectivePoint::IDENTITY;
    let mask_start = 1 << (n - 1);

    for i in 0..cap {
        let mut prod_f_j = Scalar::ONE;

        let mut mask = mask_start;
        for j in 0..n {
            if (i & mask) != 0 {
                prod_f_j *= f[j]
            } else {
                prod_f_j *= x - f[j]
            }
            mask >>= 1;
        }

        let tmp = commitments[i] * prod_f_j;
        prod_c_i += tmp;
    }

    let mut prod_c_d = c_d[0] * -Scalar::ONE;
    let mut x_exp = x;

    for k in 1..n {
        let temp = c_d[k] * (-x_exp);
        x_exp *= x;
        prod_c_d += temp;
    }

    let lhs = prod_c_i + prod_c_d;
    let rhs = commit(pk, Scalar::ZERO, z_d);

    println!("final {:?}", lhs.eq(&rhs));

    // let mut prod_c_d = c_d[0] * (-x.pow([0u64]));
    // let mut x_exp = x;
    //
    // for k in 1..n {
    //     prod_c_d.add_assign(c_d[k] * -x_exp);
    //     x_exp.mul_assign(&x);
    // }
    //
    // let mask_start = 1 << (n - 1);
    //
    // let mut prod_c = ProjectivePoint::identity();
    // for i in 0..cap {
    //     let mut mask = mask_start;
    //     let mut exp = Scalar::ONE;
    //
    //     for j in 0..n {
    //         let tmp = {
    //             if (i & mask) != 0 {
    //                 f_values[j]
    //             } else {
    //                 x - f_values[j]
    //             }
    //         };
    //         mask >>= 1;
    //         exp *= tmp;
    //     }
    //
    //     prod_c.add_assign(commitments[i] * exp);
    // }
    //
    // let lhs = prod_c + prod_c_d;
    // let rhs = commit(pk, Scalar::ZERO, zd);
    //
    // println!("final {:?}", lhs.eq(&rhs));
}
