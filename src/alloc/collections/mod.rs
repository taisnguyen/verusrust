use vstd::prelude::*;

// Below are imports from the Rust standard library.
// Either there already exists a Verus specification for a function,
// or we will provide an external specification for it. If we attempt to
// use a function that does not have a specification, then Verus will yell at us.
use std_alloc::collections::TryReserveErrorKind;

verus! {

// TODO: Check difference between external_type_specification and external_body.
#[verifier::external_type_specification]
pub struct ExCapacityOverflow(TryReserveErrorKind);

} // verus!
