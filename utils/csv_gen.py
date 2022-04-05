#!/usr/bin/env python3

"""
I.e. utils/csv_gen.py benchmarks/pong/single/
"""

import pandas as pd
import subprocess
import os
import sys

def format_duration(s):
    return f"{float(s) / 1000:.3f}"

def run_spec(path):
    if path[-1] != '/':
        path = path + '/'
    dentries = path.replace('/', ' ').strip().split()
    dir_name = dentries[-1]
    tslmt = path + dir_name + ".tslmt"
    json = path + dir_name + ".json"
    result = subprocess.run(["target/release/temos",
        "--time", json, tslmt], stdout=subprocess.PIPE)

    result = result.stdout.decode("utf-8") .strip().split('\n')

    if "REALIZABLE" not in result:
        raise Exception

    result = [int(r) for r in result[-2:]]

    assumptions = subprocess.run(["target/release/temos",
        "--lia", json, tslmt], stdout=subprocess.PIPE).stdout.decode("utf-8") .strip().split('\n')

    guarantee_idx = assumptions.index("always assume{")
    NUM_TAIL = 3

    return {
        "TYPE": dentries[-2],
        "NAME": dir_name,
        "NUM ASSUMPTIONS": len([a for a in assumptions if ";" in a and "->" in a]),
        "SyGuS(s)": format_duration(result[0]),
        "REACTIVE SYNTH(s)": format_duration(result[1]),
        "SUM(s)": format_duration(result[0] + result[1])
    }

def gen_csv(path):
    data = run_spec(path)
    columns = list(data.keys())
    df = pd.DataFrame(columns=columns, data=run_spec(path), index=[0])
    return df

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("USAGE: ./csv_gen.py <PATH TO TSLMT FILE>")
        sys.exit(1)
    if sys.argv[1] == "--all":
        raise NotImplementedError
    else:
        result = gen_csv(sys.argv[1])
        result.reset_index(drop=True, inplace=True)
        print(result)
