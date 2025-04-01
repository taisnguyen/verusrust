use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::simple_pptr::PPtr;
// use vstd::std_
// use vstd::layout::*;

// Below are imports from the Rust Standard Library.
// We will not be verifying these functions. Instead, we will
// provide an external specification for them.
// use std::alloc::{Allocator, Global, Layout};
// use core::cmp;
use core::mem::align_of;
// use core::ptr::{self, NonNull, Unique};
use std::marker::PhantomData;
use std_alloc::alloc::Allocator;
// use std_alloc::collections::TryReserveError;
// use std_alloc::collections::TryReserveErrorKind::*;

// use std::collections::TryReserveError;
// use std::mem::size_of;
// use std::ptr;

// [Assumptions]
// (A1): We assume that `align_of` is a power of 2.

// Lines that are commented out like //@ are original library code.
// Sometimes we need to use Verus's API to reason about such code.

// Comments that are commented like //% are comments about specification/proof-specific
// comments, and will usually be numbered, corresponding to items in the specification/proof.

verus! {

struct Cap(usize);

#[verifier::inline]
pub open spec fn UsizeNoHighBit(x: usize) -> bool {
    x <= isize::MAX
}

impl Cap {
    pub const fn new_verified(x: usize) -> Self
        requires
            UsizeNoHighBit(x),
    {
        Self(x)
    }

    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        UsizeNoHighBit(self.0)
    }

    pub fn as_inner(&self) -> usize {
        self.0
    }
}

fn new_cap<T>(cap: usize) -> Cap
    requires
        UsizeNoHighBit(cap),
{
    if size_of::<T>() == 0 {
        ZERO_CAP
    } else {
        Cap::new_verified(cap)
    }
}

const fn min_non_zero_cap(size: usize) -> usize {
    if size == 1 {
        8
    } else if size <= 1024 {
        4
    } else {
        1
    }
}

//% 1. Verus does not currently support the following:
//%    const ZERO_CAP: Cap = Cap::new_verified(usize::MAX);
//@ const ZERO_CAP: Cap = unsafe { Cap::new_unchecked(0) };
const ZERO_CAP: Cap = Cap(0);

#[verifier::external_body]
pub const fn dangling_aligned(align: usize) -> (pt: (
    PPtr<u8>,
    Tracked<PointsToRaw>,
    Tracked<Dealloc>,
))
    requires
//% 1. Rust requires that the alignment is a power of 2.

        vstd::layout::is_power_2(align as int),
    ensures
//% 1. Ensures the pointer represents a memory allocation of size 0.
//% 2. The tracked Dealloc object correponds to the pointer.
//% 3. The pointer is aligned to the specified alignment.

        pt.1@.is_range(pt.0.addr() as int, 0 as int),
        pt.2@@ == (DeallocData {
            addr: pt.0.addr(),
            size: 0 as nat,
            align: align as nat,
            provenance: pt.1@.provenance(),
        }),
        pt.0.addr() as int == align as int,
    opens_invariants none
{
    let pptr = PPtr(align, PhantomData);
    (pptr, Tracked::assume_new(), Tracked::assume_new())
}

// Currently, Verus only supports the `Global` allocator. Moreover, Verus does not
// support default parameters, i.e., Allocator = Global.
pub(crate) struct RawVec<T, A: Allocator> {
    inner: RawVecInner<A>,
    _marker: PhantomData<T>,
}

// impl<T> RawVec<T, Global> {``
//     #[must_use]
//     pub const fn new() -> Self {
//         Self::new_in(Global)
//     }
// }
impl<T, A: Allocator> RawVec<T, A> {
    #[inline]
    pub const fn new_in(alloc: A) -> Self {
        // (A1): We assume that `align_of` is a power of 2.
        assume(vstd::layout::is_power_2(align_of::<T>() as int));
        Self { inner: RawVecInner::new_in(alloc, align_of::<T>()), _marker: PhantomData }
    }
    // #[inline(never)]
    // #[track_caller]
    // pub fn grow_one(&mut self) {
    //     self.inner.grow_one(Layout::new::<T>());
    // }

}

struct RawVecInner<A: Allocator> {
    //@ ptr: Unique<u8>,
    //@ cap: Cap,
    //@ alloc: A,
    ptr: PPtr<u8>,
    pt: Tracked<PointsToRaw>,
    dealloc: Tracked<Dealloc>,
    cap: Cap,
    alloc: A,
}

impl<A: Allocator> RawVecInner<A> {
    #[inline]
    const fn new_in(alloc: A, align: usize) -> (rvi: RawVecInner<A>)
        requires
            vstd::layout::is_power_2(align as int),
    {
        //@ let ptr = unsafe { core::mem::transmute(align) };
        //@ `cap: 0` means "unallocated". zero-sized types are ignored.
        //@ Self { ptr, cap: ZERO_CAP, alloc }
        let (ptr, pt, dealloc) = dangling_aligned(align);
        Self { ptr, pt, dealloc, cap: ZERO_CAP, alloc }
    }
    // #[inline]
    // #[track_caller]
    // fn grow_one(&mut self, elem_layout: Layout) {
    //     use vstd::pervasive::runtime_assert;
    //     let current_cap = self.cap.as_inner();
    //     if let Err(_err) = self.grow_amortized(current_cap, 1, elem_layout) {
    //         //% handle_error(err);
    //         runtime_assert(false);
    //     }
    // }
    // fn grow_amortized(&mut self, len: usize, additional: usize, elem_layout: Layout) -> Result<
    //     (),
    //     TryReserveError,
    // > {
    //     debug_assert!(additional > 0);
    //     if elem_layout.size() == 0 {
    //         return Err(CapacityOverflow.into());
    //     }
    //     let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
    //     let cap = cmp::max(self.cap.as_inner() * 2, required_cap);
    //     let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap);
    //     let new_layout = layout_array(cap, elem_layout)?;
    //     let ptr = finish_grow(new_layout, self.current_memory(elem_layout), &mut self.alloc)?;
    //     // SAFETY: finish_grow would have resulted in a capacity overflow if we tried to allocate more than `isize::MAX` items
    //     unsafe { self.set_ptr_and_cap(ptr, cap) };
    //     Ok(())
    // }
    // #[inline]
    // unsafe fn set_ptr_and_cap(
    //     &mut self,
    //     ptr: PPtr<u8>,
    //     pt: Tracked<PointsToRaw>,
    //     dealloc: Tracked<Dealloc>,
    //     cap: usize,
    // )
    //     requires
    //         UsizeNoHighBit(cap),
    // {
    //     //% self.ptr = Unique::from(ptr.cast());
    //     //% self.cap = unsafe { Cap::new_unchecked(cap) };
    //     self.ptr = ptr;
    //     self.pt = pt;
    //     self.dealloc = dealloc;
    //     self.cap = Cap::new_verified(cap);
    // }
    // TODO:
    // #[inline]
    // fn current_memory(&self, elem_layout: Layout) -> Option<(NonNull<u8>, Layout)> {
    //     if elem_layout.size() == 0 || self.cap.as_inner() == 0 {
    //         None
    //     } else {
    //         // Verus can check for overflow here
    //         let alloc_size = elem_layout.size() * self.cap.as_inner();
    //         // We could use Layout::array here which ensures the absence of isize and usize overflows
    //         // and could hypothetically handle differences between stride and size, but this memory
    //         // has already been allocated so we know it can't overflow and currently Rust does not
    //         // support such types. So we can do better by skipping some checks and avoid an unwrap.
    //         unsafe {
    //             let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
    //             Some((self.ptr.into(), layout))
    //         }
    //     }
    // }

}

// #[cold]
// fn finish_grow<A>(
//     new_layout: Layout,
//     current_memory: Option<(NonNull<u8>, Layout)>,
//     alloc: &mut A,
// ) -> Result<NonNull<[u8]>, TryReserveError> where A: Allocator {
//     // alloc_guard(new_layout.size())?;
//     let memory = if let Some((ptr, old_layout)) = current_memory {
//         debug_assert_eq!(old_layout.align(), new_layout.align());
//         unsafe {
//             // hint::assert_unchecked(old_layout.align() == new_layout.align());
//             alloc.grow(ptr, old_layout, new_layout)
//         }
//     } else {
//         alloc.allocate(new_layout)
//     };
//     memory.map_err(|_| AllocError { layout: new_layout, non_exhaustive: () }.into())
// }
// #[inline]
// fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError> {
//     elem_layout.repeat(cap).map(|(layout, _pad)| layout).map_err(|_| CapacityOverflow.into())
// }
} // verus!
