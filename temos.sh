#!/usr/bin/env bash

if [ "$#" -ne 1 ]; then
    echo "USAGE: ./temos.sh <tslmt file>"&2
	exit 1
fi

tslmt=$1

java -jar decomp/target/decomp-1.0-SNAPSHOT-jar-with-dependencies.jar $tslmt > tmp.json
target/release/temos tmp.json $tslmt
rm tmp.json
