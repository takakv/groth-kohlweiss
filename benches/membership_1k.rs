use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use crypto_bigint::rand_core::{OsRng, RngCore};
use p384::elliptic_curve::Field;
use p384::{ProjectivePoint, Scalar};

use groth_kohlweiss::crypto::{commit, message_to_scalar};
use groth_kohlweiss::proof::{Parameters, Witness};
use groth_kohlweiss::prover::ni_prove_membership;
use groth_kohlweiss::verifier::verify_membership;

fn prepare_commitments<R: RngCore>(
    rng: &mut R,
) -> (
    ProjectivePoint,
    Vec<ProjectivePoint>,
    Vec<Scalar>,
    Parameters,
    Witness,
) {
    let mut messages = Vec::with_capacity(1000);

    for i in 0..1000 {
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
    let r = Scalar::random(&mut *rng);
    let witness = Witness { l, r };

    let secret = Scalar::random(&mut *rng);
    let pk = ProjectivePoint::GENERATOR * secret;

    let commitment = commit(pk, messages[l], r);
    let mut commitments = Vec::with_capacity(messages.len());
    for message in &messages {
        let c_i = commitment + commit(pk, -(*message), Scalar::ZERO);
        commitments.push(c_i);
    }
    commitments[l] = commitment;

    (pk, commitments, messages, parameters, witness)
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = OsRng;

    let (pk, commitments, messages, parameters, witness) = prepare_commitments(&mut rng);
    let commitment = commitments[witness.l];

    let mut last_result = None;

    c.bench_function("generate [set size 1k]", |b| {
        b.iter(|| {
            let res = black_box(ni_prove_membership(
                &mut rng,
                pk,
                &commitments,
                &messages,
                &parameters,
                &witness,
            ));

            last_result = Some(res);
        })
    });

    if let Some(transcript) = last_result {
        c.bench_function("verify [set size 1k]", |b| {
            b.iter(|| {
                black_box(verify_membership(
                    pk,
                    &messages,
                    commitment,
                    &parameters,
                    &transcript,
                ))
            })
        });
    }

    // if let Some(transcript) = last_result {
    //     c.bench_function("verify_to_0 [set size 1k]", |b| {
    //         b.iter(|| {
    //             black_box(verify_commitment_to_0(
    //                 pk,
    //                 &commitments,
    //                 &parameters,
    //                 &transcript,
    //             ))
    //         })
    //     });
    // }
}

fn criterion_config() -> Criterion {
    Criterion::default().measurement_time(std::time::Duration::from_secs(12))
}

criterion_group! {
    name = benches;
    config = criterion_config();
    targets = criterion_benchmark
}
criterion_main!(benches);
