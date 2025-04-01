use vstd::prelude::*;
// We must include all modules that we want to verify in this
// main file, although they are not directly used at all.
mod alloc;

verus! {
    #[verifier::external_body]
    fn main() {}
} // verus!
