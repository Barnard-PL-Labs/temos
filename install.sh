#/usr/bin/env bash
mkdir bin
cd bin
git clone https://github.com/reactive-systems/tsltools.git
cd tsltools
make
cd ..
cp tsltools/tslsym .
cd ..
cargo build --release
