import matplotlib.pyplot as plt

NUM_ITERS = 1000
X1_BEGIN = 0.2
X2_BEGIN = 0.2

assert 0.2 <= X1_BEGIN < 0.7
assert 0.2 <= X2_BEGIN < 0.7

def next_step(x1, x2):
    next_x1, next_x2 = -1, -1
    if x1 < 0.2 and x2 < 0.2:
        next_x1  = x1 + 0.09740259
        next_x2 = 0.09740259 * x2
    else:
        next_x1 = 0.8281 * x1 + 0.1719 * x2 + 0.09740259
        if 0.7 < next_x1:
            next_x1 -= 0.0974
        next_x2 = 0.7916 * x2 + 0.1719 * x1

    assert 0.1 <= next_x1 < 0.7, f"x1 is {x1}"
    assert 0.1 <= next_x2 < 0.7, f"x2 is {x2}"

    return next_x1, next_x2

def generate_data(x1_begin=X1_BEGIN, x2_begin=X2_BEGIN, num_iters=NUM_ITERS):
    x1_data, x2_data = [], []
    x1, x2 = x1_begin, x2_begin
    for _ in range(num_iters):
        x1_data.append(x1)
        x2_data.append(x2)
        x1, x2 = next_step(x1, x2)
    return x1_data, x2_data
