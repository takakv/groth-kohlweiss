use crate::proof::{ProofCommitment, ProofResponse, Transcript};
use crate::{commit, Parameters};
use p384::{ProjectivePoint, Scalar};

pub fn verify(
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
