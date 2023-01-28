# TeMoS

Repository for TeMoS, **Te**mporal Stream Logic **Mo**dulo Theories **S**ynthesis.

## News
`TeMoS` has been rewritten, integrating it directly with [`tsltools`](https://github.com/Barnard-PL-Labs/tsltools).

Documentation is available [here](https://github.com/Barnard-PL-Labs/tsltools/blob/master/docs/tool-docs/tslmt2tsl.md).

## Installation

### Preliminaries
1. Make directory `bin`.
2. Download [CVC4](https://cvc4.github.io/downloads.html) and move the binary into `bin`.
Please name the binary `cvc4`.
3. Install `rustc`, probably preferably through [`rustup`](https://doc.rust-lang.org/book/ch01-01-installation.html#installation)

### Building the source
Simple as
```sh
cargo build
```
