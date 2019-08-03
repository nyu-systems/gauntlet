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


def slice_assign(lval, rval, range):
    lval_max = lval.size() - 1
    slice_l = range[0]
    slice_r = range[1]
    if slice_l == lval_max and slice_r == 0:
        return rval
    assemble = []
    if (slice_l < lval_max):
        assemble.append(Extract(lval_max, slice_l + 1, lval))
    assemble.append(rval)
    if (slice_r > 0):
        assemble.append(Extract(slice_r - 1, 0, lval))
    return Concat(*assemble)
