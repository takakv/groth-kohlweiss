use crypto_bigint::rand_core::OsRng;
use p384::elliptic_curve::Field;
use p384::{ProjectivePoint, Scalar};

use groth_kohlweiss::crypto::{commit, message_to_scalar};
use groth_kohlweiss::proof::{Parameters, Witness};
use groth_kohlweiss::prover::{ni_prove_commitment_to_0, ni_prove_membership};
use groth_kohlweiss::verifier::{verify_commitment_to_0, verify_membership};

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

    let membership_proof = true;

    let l = 3;
    let r = Scalar::random(&mut rng);
    let witness = Witness { l, r };

    if !membership_proof {
        messages[l] = Scalar::ZERO; // NB! variable time
    }
    let commitment = commit(pk, messages[l], r); // NB! variable time

    let mut commitments = Vec::with_capacity(messages.len());
    for message in &messages {
        let c_i = if membership_proof {
            commitment + commit(pk, -(*message), Scalar::ZERO)
        } else {
            commit(pk, *message, Scalar::random(&mut rng))
        };

        commitments.push(c_i);
    }

    commitments[l] = commitment; // NB! variable time

    let transcript = if membership_proof {
        ni_prove_membership(&mut rng, pk, &commitments, &messages, &parameters, &witness)
    } else {
        ni_prove_commitment_to_0(&mut rng, pk, &commitments, &parameters, &witness)
    };

    if membership_proof {
        verify_membership(pk, &messages, commitment, &parameters, &transcript)
            .expect("Verification failed");
    } else {
        verify_commitment_to_0(pk, &commitments, &parameters, &transcript)
            .expect("Verification failed");
    }
}
