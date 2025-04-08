use vstd::prelude::*;

// Below are imports from the Rust standard library.
// Either there already exists a Verus specification for a function,
// or we will provide an external specification for it. If we attempt to
// use a function that does not have a specification, then Verus will yell at us.
use std_alloc::alloc::Layout;

// [Assumptions]
// (A1): We assume that rustc returns a valid layout for the type T.

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLayout(Layout);

//% (A1): We assume that rustc returns a valid layout for the type T.
pub assume_specification<T>[ Layout::new::<T> ]() -> (layout: Layout)
    ensures
        vstd::layout::valid_layout(size_of::<T>(), align_of::<T>()),
;

pub assume_specification[ Layout::size ](layout: &Layout) -> (size: usize)
;

} // verus!
