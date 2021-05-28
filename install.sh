#/usr/bin/env bash
cd decomp/src
wget https://storage.googleapis.com/google-code-archive-downloads/v2/code.google.com/json-simple/json-simple-1.1.1.jar
javac Decomp.java
mkdir bin
cd bin
git clone https://github.com/reactive-systems/tsltools.git
cd tsltools
make
cd ..
cp tsltools/tslsym .
cd ..
cargo build --release
