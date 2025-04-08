use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::simple_pptr::PPtr;
// use vstd::std_
// use vstd::layout::*;
use crate::core::cmp as cmp_v;
// Below are imports from the Rust standard library.
// Either there already exists a Verus specification for a function,
// or we will provide an external specification for it. If we attempt to
// use a function that does not have a specification, then Verus will yell at us.

use core::cmp;
use core::mem::{align_of, size_of};
use core::ptr::{self, NonNull};
use std::collections::TryReserveError;
use std::convert::*;
use std::marker::PhantomData;
use std_alloc::alloc::{Allocator, Global, Layout};
use std_alloc::collections::TryReserveErrorKind::*;

// [Assumptions]
// (A1): We assume that `align_of` is a power of 2, as guaranteed by rustc.
// (A2): Layout::new::<T>(): We assume that if the type is instantiated,
//       rustc already ensures that its layout is valid.

// Lines that are commented out like //@ are original library code.
// Sometimes we need to use Verus's API to reason about such code.

// Comments that are commented like //% are comments about specification/proof-specific
// comments, and will usually be numbered, corresponding to items in the specification/proof.

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTryReserveError(TryReserveError);

// pub assume_specification[ TryReserveErrorKind::CapacityOverflow::into ]() -> (err: TryReserveError)
//     ensures
//         err.kind == TryReserveErrorKind::CapacityOverflow,
// ;
struct Cap(usize);

impl View for Cap {
    type V = usize;

    closed spec fn view(&self) -> Self::V {
        self.0
    }
}

#[allow(non_snake_case)]
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

    pub fn as_inner(&self) -> (result: usize)
        ensures
            result == self.view(),
    {
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

impl<T, A: Allocator> View for RawVec<T, A> {
    type V = RawVec<T, A>;

    closed spec fn view(&self) -> Self::V {
        RawVec { inner: self.inner@, _marker: PhantomData }
    }
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
        //% (A1): We assume that `align_of` is a power of 2, as guaranteed by rustc.
        assume(vstd::layout::is_power_2(align_of::<T>() as int));
        Self { inner: RawVecInner::new_in(alloc, align_of::<T>()), _marker: PhantomData }
    }

    #[inline(never)]
    #[track_caller]
    pub fn grow_one(&mut self)
        requires
            old(self)@ == old(self)@,
    {
        // TODO: Do not assume this.
        assume(self.inner.cap@ <= isize::MAX);
        self.inner.grow_one(Layout::new::<T>());
    }
}

pub struct RawVecInner<A: Allocator> {
    //@ ptr: Unique<u8>,
    //@ cap: Cap,
    //@ alloc: A,
    pub ptr: PPtr<u8>,
    pub pt: Tracked<PointsToRaw>,
    pub dealloc: Tracked<Dealloc>,
    pub cap: Cap,
    pub alloc: A,
}

impl<A: Allocator> View for RawVecInner<A> {
    type V = RawVecInner<A>;

    open spec fn view(&self) -> Self::V {
        RawVecInner {
            ptr: self.ptr,
            pt: self.pt,
            dealloc: self.dealloc,
            cap: self.cap,
            alloc: self.alloc,
        }
    }
}

impl<A: Allocator> RawVecInner<A> {
    #[inline]
    const fn new_in(alloc: A, align: usize) -> (rvi: RawVecInner<A>)
        requires
            vstd::layout::is_power_2(
                align as int,
            ),
    //% 1. This aligns with a specification in the original code. This ensures no overflow occurs.

        ensures
            rvi.cap@ <= isize::MAX,
    {
        //@ let ptr = unsafe { core::mem::transmute(align) };
        //@ `cap: 0` means "unallocated". zero-sized types are ignored.
        //@ Self { ptr, cap: ZERO_CAP, alloc }
        let (ptr, pt, dealloc) = dangling_aligned(align);
        Self { ptr, pt, dealloc, cap: ZERO_CAP, alloc }
    }

    #[inline]
    #[track_caller]
    fn grow_one(
        &mut self,
        elem_layout: Layout,
    )
    //% 1. Ensure self.cap.as_inner() * 2 does not overflow. This is a SAFETY comment in the original code.

        requires
            old(self).cap@ <= isize::MAX,
    {
        //% Instead of the below original code, we modified grow_amortized to
        //% to throw a failed assertion if the allocation fails. So we can
        //% just call self.grow_amortized directly.
        //@ if let Err(_err) = self.grow_amortized(current_cap, 1, elem_layout) {
        //@ handle_error(err);
        //@ }
        self.grow_amortized(self.cap.as_inner(), 1, elem_layout);
    }

    fn grow_amortized(&mut self, len: usize, additional: usize, elem_layout: Layout) -> Result<
        (),
        TryReserveError,
    >
    //% 1. The original code has debug_assert!(additional > 0). We are ensuring that this checks.
    //% 2. Ensure self.cap.as_inner() * 2 does not overflow. This is a SAFETY comment in the original code.

        requires
            additional > 0,
            old(self).cap@ <= isize::MAX,
    {
        //# debug_assert!(additional > 0);
        assert(additional > 0);
        // TODO: Write external specification for CapacityOveflow.into().
        // if elem_layout.size() == 0 {
        //     return Err(CapacityOverflow.into());
        // }

        let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
        //@ let cap = cmp::max(self.cap.as_inner() * 2, required_cap);
        //@ let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap);
        let cap = cmp_v::max_usize(self.cap.as_inner() * 2, required_cap);
        let cap = cmp_v::max_usize(min_non_zero_cap(elem_layout.size()), cap);

        let new_layout = layout_array(cap, elem_layout)?;

        // let ptr = finish_grow(new_layout, self.current_memory(elem_layout), &mut self.alloc)?;

        Ok(())  //

    }

    #[verifier::external_body]
    #[inline]
    fn current_memory(&self, elem_layout: Layout) -> Option<(PPtr<u8>, Layout)> {
        if elem_layout.size() == 0 || self.cap.as_inner() == 0 {
            None
        } else {
            // We could use Layout::array here which ensures the absence of isize and usize overflows
            // and could hypothetically handle differences between stride and size, but this memory
            // has already been allocated so we know it can't overflow and currently Rust does not
            // support such types. So we can do better by skipping some checks and avoid an unwrap.
            unsafe {
                let alloc_size = elem_layout.size().unchecked_mul(self.cap.as_inner());
                let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
                Some((self.ptr.into(), layout))
            }
        }
    }
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

}

// #[verifier::external_body]
// #[cold]
// fn finish_grow<A>(
//     new_layout: Layout,
//     current_memory: Option<(PPtr<u8>, Layout)>,
//     alloc: &mut A,
// ) -> Result<NonNull<[u8]>, TryReserveError> where A: Allocator {
//     alloc_guard(new_layout.size())?;
//     // let memory = if let Some((ptr, old_layout)) = current_memory {
//     //     debug_assert_eq!(old_layout.align(), new_layout.align());
//     //     unsafe {
//     //         // The allocator checks for alignment equality
//     //         // hint::assert_unchecked(old_layout.align() == new_layout.align());
//     //         // alloc.grow(ptr, old_layout, new_layout)
//     //     }
//     // } else {
//     //     // alloc.allocate(new_layout)
//     // };
//     // memory.map_err(|_| AllocError { layout: new_layout, non_exhaustive: () }.into())
// }
#[verifier::external_body]
#[inline]
fn alloc_guard(alloc_size: usize) -> Result<(), TryReserveError> {
    if usize::BITS < 64 && alloc_size > isize::MAX as usize {
        Err(CapacityOverflow.into())
    } else {
        Ok(())
    }
}

// TODO: Write a specification for this.
#[verifier::external_body]
#[inline]
fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError> {
    elem_layout.repeat(cap).map(|(layout, _pad)| layout).map_err(|_| CapacityOverflow.into())
}

} // verus!
