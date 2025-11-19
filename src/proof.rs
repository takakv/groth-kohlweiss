use p384::{ProjectivePoint, Scalar};

pub(crate) struct Witness {
    pub(crate) l: usize,
    pub(crate) r: Scalar,
}

pub struct ProofCommitment {
    pub c_l: Vec<ProjectivePoint>,
    pub c_a: Vec<ProjectivePoint>,
    pub c_b: Vec<ProjectivePoint>,
    pub c_d: Vec<ProjectivePoint>,
}

pub struct ProofResponse {
    pub f: Vec<Scalar>,
    pub z_a: Vec<Scalar>,
    pub z_b: Vec<Scalar>,
    pub z_d: Scalar,
}

pub struct Transcript {
    pub commitments: ProofCommitment,
    pub challenge: Scalar,
    pub response: ProofResponse,
}
