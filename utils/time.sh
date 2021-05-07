#! /usr/bin/env bash

if [ "$#" -ne 2 ]; then
    echo "USAGE: ./time.sh <path_header> <bin_mode>"
	exit 1
fi

path_header=$1
bin_mode=$2
json="benchmarks/$path_header.json"
tsl="benchmarks/$path_header.tsl"

target/$bin_mode/streamos "--time" $json $tsl