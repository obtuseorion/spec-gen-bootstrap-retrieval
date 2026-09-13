//! Phase 2 glue: small functions whose only purpose is their call structure
//! across the Phase 1 modules. See REPORT.md ("Phase 2 — shapes") for the
//! mapping from each required shape to the functions below.
pub mod chain;
pub mod chain_mid;
pub mod chain_end;
pub mod chain_tail;
pub mod diamond;
pub mod fanout;
pub mod mutual;
pub mod looped;
pub mod dispatch;
pub mod shadow;
pub mod dead;
