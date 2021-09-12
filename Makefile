default:
	cargo build --release

clean:
	cargo clean

nuke: clean
	rm -rf bin

all: tsltools cvc4 default

tsltools:
	mkdir bin
	cd bin
	git clone https://github.com/reactive-systems/tsltools.git tsltools
	cd tsltools && make

cvc4:
	wget https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt -O bin/cvc4 
	chmod +x bin/cvc4
