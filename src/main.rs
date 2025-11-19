use crypto_bigint::rand_core::OsRng;
use p384::elliptic_curve::Field;
use p384::{ProjectivePoint, Scalar};

mod fiatshamir;
mod proof;
mod prover;
mod verifier;

use crate::proof::Witness;
use crate::prover::ni_prove_commitment_to_0;
use crate::verifier::verify;

fn commit(ck: ProjectivePoint, message: Scalar, r: Scalar) -> ProjectivePoint {
    (ProjectivePoint::GENERATOR * message) + (ck * r)
}

fn message_to_scalar(message: &[u8]) -> Scalar {
    let mut bytes = [0u8; 48];
    bytes[48 - message.len()..].copy_from_slice(message);
    Scalar::from_slice(&bytes).unwrap()
}

struct Parameters {
    n: usize,
    cap: usize,
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

    let transcript = ni_prove_commitment_to_0(&mut rng, pk, &commitments, &parameters, witness);
    verify(pk, &commitments, &parameters, &transcript);
}
