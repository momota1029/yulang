//! Backend-neutral core boundary for Yulang3.

#[cfg(feature = "shadow")]
pub mod shadow;

#[cfg(feature = "shadow")]
pub mod shadow_atom_orbits;

#[cfg(feature = "shadow")]
pub mod shadow_derivation;

#[cfg(feature = "shadow")]
pub mod shadow_directional_protection;

#[cfg(feature = "shadow")]
pub mod shadow_interface_alpha;

#[cfg(feature = "shadow")]
pub mod shadow_typed_evidence;

#[cfg(feature = "shadow")]
pub mod shadow_call_formation;
