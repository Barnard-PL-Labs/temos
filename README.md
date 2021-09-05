# TeMoS

Repository for TeMoS, **Te**mporal Stream Logic **Mo**dulo Theories **S**ynthesis.

## WARNING!
This repository is going through major refactoring.
To use the tool at its latest release, please download the source from [the alpha release](https://github.com/Barnard-PL-Labs/temos/releases/tag/v0.1.0a).

## Local Installation

Installation is currently only supported for Linux systems.

### Dependencies
* [`Haskell` Stack](https://docs.haskellstack.org/en/stable/README/)
* [`rustc` and `cargo`](https://doc.rust-lang.org/book/ch01-01-installation.html#installation)
* [`wget`](https://www.gnu.org/software/wget/)

### Compilation
To compile the executable, run `make all`.

MacOS users may be able to run the tool by installing the appropriate CVC4 homebrew tap, and Windows users may be able to run the tool by editing the Makefile.

### Running the tool
```
./temos <TSLMT FILE>
```
For instance:
```
./temos examples/cfs.tslmt
```
prints a TSL specification, which can then be converted into executable code with [tsltools](https://github.com/reactive-systems/tsltools).
