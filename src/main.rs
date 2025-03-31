use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn main() {
    println!("Hello, world!");
}

} // verus!
