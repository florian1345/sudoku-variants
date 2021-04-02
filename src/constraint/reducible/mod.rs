//! This module contains submodules for all reducible constraints. All of them
//! are re-exported in the [constraint](crate::constraint) module, so you
//! should not have to `use` anything from this module directly.

pub mod killer;

pub use killer::{KillerCage, KillerConstraint, KillerError};
