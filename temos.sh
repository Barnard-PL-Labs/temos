#!/usr/bin/env bash

if [ "$#" -ne 2 ]; then
    echo "USAGE: ./temos.sh <tslmt file> <output name>" >&2
	exit 1
fi

tslmt=$1
output=$2

java -jar decomp/target/decomp-1.0-SNAPSHOT-jar-with-dependencies.jar $tslmt > tmp.json
target/release/temos tmp.json $tslmt $output
rm tmp.json
