#/usr/bin/env bash
cd decomp
mvn clean && mvn package
mkdir bin
cd bin
git clone https://github.com/reactive-systems/tsltools.git
cd tsltools
make
cd ..
cp tsltools/tslsym .
cd ..
cargo build --release
