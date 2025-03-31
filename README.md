<!-- ABOUT THE PROJECT -->
## VerusRust: A Verus-Verified Rust 

A verified port of a (currently very small) subset of the Rust standard library using <a href="https://github.com/verus-lang/verus" target="_blank">Verus</a>, an SMT-based tool for formally verifying Rust programs. VerusRust verifies v1.86.0 of the Rust standard library.


<!-- GETTING STARTED -->
## Setup

VerusRust uses `rustc` v1.76.0, which you can install with `rustup`:
```sh
$ rustup install 1.76.0
$ rustup override set 1.76.0
```

To begin, clone the repository:
```sh
$ git clone https://github.com/taisnguyen/verusrust.git
```
### Prerequisites

To run verification, you must have `Verus` installed. Please see <a href="https://github.com/verus-lang/verus/blob/main/INSTALL.md" target="_blank">here</a> for installation instructions. VerusRust uses `Verus` v0.2025.03.20.71dfb82.

### Usage
To run verification, you can run from the root directory:
```sh
$ verus --crate-type=lib src/lib.rs
```
   
## Trusted Computing Base

A trusted computing base (TCB) is a set of operations that we assume to be safe or trusted. These tend
to be operations that we cannot verify, such as hardware-level operations. Within VerusRust, this is indicated by macros such as `#[verifier::external_body]`, `assume_specifications`, etc. Please see the <a href="https://verus-lang.github.io/verus/guide/" target="_blank">Verus Tutorial</a> for more information.