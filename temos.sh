#!/usr/bin/env bash

if [ "$#" -ne 2 ]; then
    echo "USAGE: temos.sh <TSLMT file> <TARGET>" >&2
	echo "Example: ./temos.sh benchmarks/music/vibrato/vibrato.tslmt --webaudio"
	exit 1
fi

file_name=$1
file_header=${file_name:0:-6}
tsl="$file_header.tsl"
json="$file_header.json"
tlsf="$file_header.tlsf"
aag="$file_header.aag"
BIN_PATH="bin"
target=$2

target/release/temos --synth $json $file_name > $tsl
tail -n +2 "$tsl" > "$tsl.tmp" && mv "$tsl.tmp" "$tsl"
cat $tsl
exit 0

# Build TLSF
$BIN_PATH/tsl2tlsf $tsl | cat > $tlsf

# Build AAG from docker
# sudo docker run --rm -v $(pwd):/files wonhyukchoi/tsl-strix-docker /Strix/scripts/strix_tlsf.sh files/$tlsf > $aag
/Strix/scripts/strix_tlsf.sh $tlsf > $aag

# Change to unix format
dos2unix $aag 2> /dev/null

# Check for realizability
is_realizable=$(head -n1 $aag)

if [ "$is_realizable" = "UNREALIZABLE" ]; then
	echo $is_realizable >&2
	exit 1
fi

# Remove first line 
# https://stackoverflow.com/a/339941/11801882
tail -n +2 "$aag" > "$aag.tmp" && mv "$aag.tmp" "$aag"

# Synthesize the resulting code
$BIN_PATH/cfm2code $aag $target

rm -rf $tsl $tlsf $aag
