use crypto_bigint::modular::{BoxedMontyForm, ConstMontyForm, MontyForm, MontyParams};
use crypto_bigint::{Limb, NonZero, Odd, U384, Uint};
use p384::{
    AffinePoint, EncodedPoint, NistP384, ProjectivePoint, Scalar,
    elliptic_curve::{
        Curve, PrimeField,
        sec1::{FromEncodedPoint, ToEncodedPoint},
    },
};
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

fn main() {
    println!("Hello, world!");

    let message = "0000.101";
    let message_bytes = message.as_bytes();
    encode_to_point(message_bytes);
}
