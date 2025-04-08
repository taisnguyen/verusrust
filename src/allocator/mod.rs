use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::simple_pptr::PPtr;

// Below are imports from the Rust Standard Library.
// We will not be verifying these functions. Instead, we will
// provide an external specification for them.
// use std::alloc::{Allocator, Global, Layout};
use core::ptr::{self, NonNull};
use std_alloc::alloc::{AllocError, Layout};

verus! {

/// Grow with the global allocator.
/// Precondition should be consistent with the [documented safety conditions on `alloc`](https://doc.rust-lang.org/alloc/alloc/trait.Allocator.html#method.grow).
#[verifier::external_body]
pub fn grow(
    ptr: PPtr<u8>,
    // TODO: make struct for Layout and specification
    old_layout: Layout,
    new_layout: Layout,
    old_pt: Tracked<PointsToRaw>,
    old_dealloc: Tracked<Dealloc>,
) -> Result<(*mut u8, Tracked<PointsToRaw>, Tracked<Dealloc>), AllocError> {
    //%   debug_assert!(
    //%     new_layout.size() >= old_layout.size(),
    //%     "`new_layout.size()` must be greater than or equal to `old_layout.size()`"
    //% );
    //% let new_ptr = self.allocate(new_layout)?;
    let new_size = new_layout.size();
    let new_align = new_layout.align();
    let (new_ptr, Tracked(new_pt), Tracked(new_dealloc)) = allocate(new_size, new_align);

    // // SAFETY: because `new_layout.size()` must be greater than or equal to
    // // `old_layout.size()`, both the old and new memory allocation are valid for reads and
    // // writes for `old_layout.size()` bytes. Also, because the old allocation wasn't yet
    // // deallocated, it cannot overlap `new_ptr`. Thus, the call to `copy_nonoverlapping` is
    // // safe. The safety contract for `dealloc` must be upheld by the caller.
    unsafe {
        ptr::copy_nonoverlapping(ptr, new_ptr, old_layout.size());
    }

    let old_size = old_layout.size();
    let old_align = old_layout.align();
    deallocate(ptr, old_size, old_align, old_pt, old_dealloc);

    Ok((new_ptr, Tracked(new_pt), Tracked(new_dealloc)))
}

} // verus!
