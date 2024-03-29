//! This module contains submodules for all reducible constraints. All of them
//! are re-exported in the [constraint](crate::constraint) module, so you
//! should not have to `use` anything from this module directly.

pub mod killer;
pub mod sandwich;
pub mod thermo;

pub use killer::{KillerCage, KillerConstraint, KillerError};
pub use sandwich::{SandwichConstraint, SandwichError, SandwichResult};
pub use thermo::{ThermoConstraint, ThermoError, Thermometer};
