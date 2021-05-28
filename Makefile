default:
	cargo build --release
	cd decomp && mvn package

clean:
	rm -rf bin
	cargo clean
	cd decomp && mvn clean

all: tsltools cvc4 default

tsltools:
	mkdir bin
	git clone https://github.com/reactive-systems/tsltools.git bin/tsltools
	cd bin/tsltools/ && make && cp tslsym ../

cvc4:
	cd bin
	wget http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/cvc4-2021-03-23-x86_64-linux-opt cvc4
