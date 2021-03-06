#!/usr/bin/env python3

import os
import subprocess
import time
import pandas as pd
from colorama import Fore, Style
from csv_gen import gen_csv

ITERS = 0x2f

BENCHMARKS = ["escalator", "pong", "music", "scheduler"]
BENCHMARK_DIR = "benchmarks"
ORDER = {name: order for order,name in zip(range(16),
    [
        "vibrato",
        "modulation",
        "intertwined",
        "multieffect",
        "single",
        "two_player",
        "bouncing",
        "automatic",
        "simple",
        "counting",
        "bidirectional",
        "smart",
        "rr",
        "load_balancer",
        "preemptive",
        "cfs"
    ]
)}

if __name__ == "__main__":
    eval_df = pd.DataFrame()
    oracle_times = []
    for benchmark in BENCHMARKS:
        benchmark_dir = BENCHMARK_DIR + '/' + benchmark
        if not os.path.isdir(benchmark_dir):
            continue
        for benchmark_type in os.listdir(benchmark_dir):
            path = benchmark_dir + '/' + benchmark_type
            if not os.path.isdir(path):
                continue

            for _ in range(ITERS):
                try:
                    eval_df = eval_df.append(gen_csv(path))
                    break
                except Exception as e:
                    print(e)
                    print(f"{Fore.GREEN}Refinement loop, trying again...{Style.RESET_ALL}")
                    pass

            oracle = path + '/oracle.tsl'
            oracle_before = time.time()
            subprocess.run(["bin/tsl2js.sh", oracle])
            oracle_after = time.time() - oracle_before
            oracle_times.append(int(oracle_after * 1000))

    eval_df["oracle"] = oracle_times
    eval_df["order"] = [ORDER[name] for name in eval_df["NAME"]]
    eval_df.sort_values(by="order", inplace=True)
    eval_df.drop(columns=['order'], inplace=True)
    print(eval_df)
