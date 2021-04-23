#![ allow( dead_code, unused_imports, non_upper_case_globals ) ]

extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;

pub mod scalar_utils;
pub mod r1cs_utils;
pub mod factors;
pub mod gadget_not_equals;
pub mod gadget_bound_check;
pub mod gadget_range_proof;
pub mod gadget_set_membership;
pub mod gadget_set_membership_1;
pub mod gadget_set_non_membership;
pub mod gadget_zero_nonzero;
pub mod gadget_mimc;
pub mod gadget_vsmt_2;
pub mod gadget_vsmt_4;
pub mod gadget_osmt;    /// This is incomplete
mod poseidon_constants;
pub mod gadget_poseidon;
pub mod gadget_unique_elements;
