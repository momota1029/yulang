//! Backend-neutral core boundary for Yulang3.

#[cfg(feature = "shadow")]
pub mod shadow;

#[cfg(feature = "shadow")]
pub mod shadow_derivation;

#[cfg(feature = "shadow")]
pub mod shadow_directional_protection;
