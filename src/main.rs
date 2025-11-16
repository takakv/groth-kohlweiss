use crypto_bigint::modular::{BoxedMontyForm, ConstMontyForm, MontyForm, MontyParams};
use crypto_bigint::rand_core::OsRng;
use crypto_bigint::{Limb, NonZero, Odd, U384, Uint};
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

fn main() {
    println!("Hello, world!");

    let messages = [
        Scalar::ONE,
        message_to_scalar("0000.102".as_bytes()),
        message_to_scalar("0000.103".as_bytes()),
    ];

    // let secret = Scalar::random(OsRng);
    let secret = U384::from_be_hex(
        "788C773608952E9757DCF9E5C9BC9C48CB8F1C650AD6AA87C3BFF0E9E631AD1C435365412903FD7183934B8C21D0AB97",
    );
    let secret = Scalar::from_slice(&secret.to_be_bytes()).unwrap();
    let pk = ProjectivePoint::GENERATOR * secret;

    let message = messages[0];
    let commitment = commit(pk, message, secret);

    let binary_transcript = prove_binary(pk, message, secret);
    verify_binary(pk, commitment, &binary_transcript);

    let commitments = [
        commitment + commit(pk, messages[0].neg(), Scalar::ZERO),
        commitment + commit(pk, messages[1].neg(), Scalar::ZERO),
        commitment + commit(pk, messages[2].neg(), Scalar::ZERO),
    ];
}
