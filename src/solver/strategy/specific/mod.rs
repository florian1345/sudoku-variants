//! This module contains [Strategy](crate::solver::strategy::Strategy)
//! implementations specific to individual
//! [Constraint](crate::constraint::Constraint)s. All implementations are
//! re-exported in this module.

pub mod killer;
pub mod thermo;

pub use killer::KillerCagePossibilitiesStrategy;
pub use thermo::{
    BackwardThermometerFollowingStrategy,
    ForwardThermometerFollowingStrategy,
    ThermometerFollowingStrategy
};
