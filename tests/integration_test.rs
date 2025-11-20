use crypto_bigint::rand_core::OsRng;
use groth_kohlweiss::crypto::{commit, message_to_scalar};
use groth_kohlweiss::proof::{Parameters, Witness};
use groth_kohlweiss::prover::{ni_prove_commitment_to_0, ni_prove_membership};
use groth_kohlweiss::verifier::{verify_commitment_to_0, verify_membership};
use p384::elliptic_curve::Field;
use p384::{ProjectivePoint, Scalar};

fn prepare_commitments(
    membership_proof: bool,
) -> (
    ProjectivePoint,
    Vec<ProjectivePoint>,
    Vec<Scalar>,
    Parameters,
    Witness,
) {
    let mut messages = Vec::with_capacity(1000);

    for i in 0..3 {
        let message = format!("0000.{:03}", i);
        messages.push(message_to_scalar(&message.as_bytes()));
    }

    let cap = messages.len().next_power_of_two();
    let n = cap.ilog2() as usize;
    let parameters = Parameters { n, cap };

    if cap != messages.len() {
        let pad = vec![messages[0]; cap - messages.len()];
        messages.extend(pad);
    }

    let l = 3;
    let r = Scalar::from_u64(1234567890).cube();
    let witness = Witness { l, r };

    let secret = Scalar::from_u64(9876543210).cube();
    let pk = ProjectivePoint::GENERATOR * secret;

    if !membership_proof {
        messages[l] = Scalar::ZERO;
    }
    let commitment = commit(pk, messages[l], r);

    let mut commitments = Vec::with_capacity(messages.len());
    for message in &messages {
        let c_i = if membership_proof {
            commitment + commit(pk, -(*message), Scalar::ZERO)
        } else {
            // The squared message is just a random value 'placeholder'.
            commit(pk, *message, message.square())
        };

        commitments.push(c_i);
    }
    commitments[l] = commitment;

    (pk, commitments, messages, parameters, witness)
}

#[test]
fn commitment_to_0_verifies() {
    let (pk, commitments, _, parameters, witness) = prepare_commitments(false);

    let transcript = ni_prove_commitment_to_0(&mut OsRng, pk, &commitments, &parameters, &witness);
    verify_commitment_to_0(pk, &commitments, &parameters, &transcript);
}

#[test]
#[should_panic]
fn commitment_to_0_fails() {
    let (pk, commitments, _, parameters, witness) = prepare_commitments(false);

    let transcript = ni_prove_commitment_to_0(&mut OsRng, pk, &commitments, &parameters, &witness);

    let mut reversed = commitments;
    reversed.reverse();

    verify_commitment_to_0(pk, &reversed, &parameters, &transcript);
}

#[test]
fn membership_proof_verifies() {
    let (pk, commitments, messages, parameters, witness) = prepare_commitments(false);
    let commitment = commitments[witness.l];

    let transcript = ni_prove_membership(
        &mut OsRng,
        pk,
        &commitments,
        &messages,
        &parameters,
        &witness,
    );
    verify_membership(pk, &messages, commitment, &parameters, &transcript);
}

#[test]
#[should_panic]
fn membership_proof_fails() {
    let (pk, commitments, messages, parameters, witness) = prepare_commitments(false);
    let commitment = commitments[witness.l - 1];

    let transcript = ni_prove_membership(
        &mut OsRng,
        pk,
        &commitments,
        &messages,
        &parameters,
        &witness,
    );
    verify_membership(pk, &messages, commitment, &parameters, &transcript);
}

// #[test]
// fn membership_proof_verifies_raw() {
//     let (pk, commitments, messages, parameters, witness) = prepare_commitments(false);
//     let commitment = commitments[witness.l];
//
//     let transcript = ni_prove_membership(
//         &mut OsRng,
//         pk,
//         &commitments,
//         &messages,
//         &parameters,
//         &witness,
//     );
//     verify_commitment_to_0(pk, &commitments, &parameters, &transcript);
// }
