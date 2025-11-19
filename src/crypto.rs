use p384::{ProjectivePoint, Scalar};

pub fn commit(ck: ProjectivePoint, message: Scalar, r: Scalar) -> ProjectivePoint {
    (ProjectivePoint::GENERATOR * message) + (ck * r)
}

pub fn message_to_scalar(message: &[u8]) -> Scalar {
    let mut bytes = [0u8; 48];
    bytes[48 - message.len()..].copy_from_slice(message);
    Scalar::from_slice(&bytes).unwrap()
}
