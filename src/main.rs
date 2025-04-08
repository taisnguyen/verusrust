#![feature(try_reserve_kind)]
#![feature(alloc_layout_extra)]
#![feature(allocator_api)]
extern crate alloc as std_alloc;

use vstd::prelude::*;

// We must include all modules that we want to verify in this
// main file, although they are not directly used at all.
mod alloc;
// mod allocator;
mod core;
mod std_specs;

verus! {

#[verifier::external_body]
fn main() {
}

} // verus!
