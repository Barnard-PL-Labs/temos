#!/usr/bin/env python3

from csv_gen import gen_csv
import os
import pandas as pd

BENCHMARKS = ["escalator", "pong", "music", "scheduler"]
BENCHMARK_DIR = "benchmarks"

if __name__ == "__main__":
    eval_df = pd.DataFrame()
    for benchmark in BENCHMARKS:
        benchmark_dir = BENCHMARK_DIR + '/' + benchmark
        if not os.path.isdir(benchmark_dir):
            continue
        for benchmark_type in os.listdir(benchmark_dir):
            path = benchmark_dir + '/' + benchmark_type
            if not os.path.isdir(path):
                continue
            print(path)
            eval_df = eval_df.append(gen_csv(path))
    print(eval_df)
