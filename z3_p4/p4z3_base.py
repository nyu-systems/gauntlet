from z3 import *


def step(func_chain, inouts, expr=True):
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        # emulate pass-by-value behavior
        inouts = copy.deepcopy(inouts)
        expr = next_fun(func_chain, inouts)
    return expr
