use vstd::prelude::*;

// Below are imports from the Rust standard library.
// Either there already exists a Verus specification for a function,
// or we will provide an external specification for it. If we attempt to
// use a function that does not have a specification, then Verus will yell at us.
use core::cmp::max;

verus! {

pub open spec fn spec_max_usize(a: usize, b: usize) -> usize {
    if a >= b {
        a
    } else {
        b
    }
}

pub fn max_usize(a: usize, b: usize) -> (result: usize)
    ensures
        result == vstd::math::max(a as int, b as int),
{
    if a >= b {
        a
    } else {
        b
    }
}

} // verus!
