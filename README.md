# TeMoS

Repository for TeMoS, **Te**mporal Stream Logic **Mo**dulo Theories **S**ynthesis.

## Local Installation

Installation is currently only supported for Linux systems.

### Dependencies
* [`Haskell` Stack](https://docs.haskellstack.org/en/stable/README/)
* [`Java` 8 or newer](https://www.java.com/en/download/)
* [`maven`](https://maven.apache.org/download.cgi)
* [`rustc` and `cargo`](https://doc.rust-lang.org/book/ch01-01-installation.html#installation)
* [`wget`](https://www.gnu.org/software/wget/)

### Compilation
To compile the executable, run `make all`.

MacOS users may be able to run the tool by installing the appropriate CVC4 homebrew tap, and Windows users may be able to run the tool with manual edits of the Makefile, but these are untested.

### Running the tool
```
./temos.sh <TSLMT FILE>
```
For instance:
```
./temos.sh examples/cfs.tslmt
```
prints a TSL specification, which can then be converted into executable code with [tsltools](https://github.com/reactive-systems/tsltools).
