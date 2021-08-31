default:
	cargo build --release
	cd decomp && mvn package
	chmod +x temos.sh

clean:
	cargo clean
	cd decomp && mvn clean

nuke: clean
	rm -rf bin

all: tsltools cvc4 default

tsltools:
	mkdir bin
	git clone https://github.com/reactive-systems/tsltools.git bin/tsltools
	cd bin/tsltools/ && make tslsym && cp tslsym ../

cvc4:
	wget http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/cvc4-2021-03-23-x86_64-linux-opt -O bin/cvc4
	chmod +x bin/cvc4
