#!/usr/bin/env bash
dir=$1
file=$2
path="$1/$2"
out="$dir/oracle.tsl"
tsltools/tslminrealizable $path -r tsltools/stdin_run.sh > $out
