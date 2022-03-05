#!/usr/bin/env python3

"""
I.e. utils/csv_gen.py benchmarks/pong/single/
"""

import pandas as pd
import subprocess
import os
import sys

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
    result = [int(r) for r in result[-2:]]

    assumptions = subprocess.run(["target/release/temos",
        "--lia", json, tslmt], stdout=subprocess.PIPE).stdout.decode("utf-8") .strip().split('\n')
    NUM_SURROUNDERS = 5

    return dict(type=dentries[-2],
            name=dentries[-1],
            num_assumptions=len(assumptions)-NUM_SURROUNDERS,
            lia=result[0],
            tsl=result[1],
            sum=result[0]+result[1])

def gen_csv(path):
    columns = ["type", "name", "num_assumptions", "lia", "tsl", "sum"]
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
        print(result)
