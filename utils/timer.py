#!/usr/bin/env python3
import time
import os
import sys
import pandas as pd

def obtain_files(directory: str):
    raise NotImplementedError

def tsllia_synthesis(file_name) -> float:
    start = time.time()
    end = time.time()
    return end - start

def tsl_synthesis(lia, tsl) -> float:
    start = time.time()
    end = time.time()
    return end - start

def timer(directory):
    csv_name = os.path.join(directory, "timer.csv")
    df = pd.DataFrame()
    df.to_csv(csv_name)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("USAGE: <benchmark directory>")
        sys.exit(1)
    print(0x2f)

