"""Experimental real-valued threshold MLMC with independent cost calibration.

Only the observation source knows the latent outer variable. The classifier
receives real observations, not the conditional mean, target, or sign.
The sample-variance boundary is a heuristic for this unbounded model, not a
confidence sequence. Final clipping, performed by the runner, introduces bias.
"""
from __future__ import annotations

import math
import numpy as np
from numba import njit
from reference import real_x


@njit(cache=True)
def decision(total, sumsq, n, cap, threshold, minimum):
    if n >= cap:
        return int(total > 0)
    if n < minimum:
        return -1
    mean = total / n
    variance = max(0.0, (sumsq - total * total / n) / (n - 1))
    boundary = threshold * math.sqrt(variance * (1 + math.log(cap / n)) / n)
    if abs(mean) > boundary:
        return int(mean > 0)
    return -1


@njit(cache=True)
def real_pair(j, start, ratio, threshold, minimum=16):
    cap = start * ratio**j
    coarse = 0 if j == 0 else cap // ratio
    z, zc = -1, (0 if j == 0 else -1)
    total, sumsq = 0.0, 0.0
    previous, n = 0, 1
    y = np.random.normal()
    while True:
        for _ in range(previous, n):
            x = real_x(y)
            total += x
            sumsq += x*x
        if z < 0:
            z = decision(total, sumsq, n, cap, threshold, minimum)
        if zc < 0:
            zc = decision(total, sumsq, n, coarse, threshold, minimum)
        if z >= 0 and zc >= 0:
            return float(z-zc), n
        previous, n = n, 2*n


@njit(cache=True)
def tape_pair(tape, j, start, ratio, threshold, minimum=16):
    """Same stopping state machine on a prescribed finite tape, for verification."""
    cap = start * ratio**j
    coarse = 0 if j == 0 else cap // ratio
    z, zc = -1, (0 if j == 0 else -1)
    total, sumsq = 0.0, 0.0
    previous, n = 0, 1
    while True:
        for k in range(previous, n):
            total += tape[k]
            sumsq += tape[k]**2
        if z < 0:
            z = decision(total, sumsq, n, cap, threshold, minimum)
        if zc < 0:
            zc = decision(total, sumsq, n, coarse, threshold, minimum)
        if z >= 0 and zc >= 0:
            return float(z-zc), n
        previous, n = n, 2*n


@njit(cache=True)
def antithetic_pair(j, start, ratio, threshold, minimum=16):
    if j==0:
        return real_pair(j,start,ratio,threshold,minimum)
    cap=start*ratio**j
    coarse=cap//ratio
    total,sumsq=0.,0.
    ct,cs=np.zeros(ratio),np.zeros(ratio)
    cz=np.full(ratio,-1)
    z,previous,n=-1,0,1
    y=np.random.normal()
    while True:
        for k in range(previous,n):
            x=real_x(y)
            total+=x;sumsq+=x*x
            block=k%ratio;local_n=k//ratio+1
            ct[block]+=x;cs[block]+=x*x
            if cz[block]<0 and (local_n & (local_n-1))==0:
                cz[block]=decision(ct[block],cs[block],local_n,coarse,threshold,minimum)
        if z<0:z=decision(total,sumsq,n,cap,threshold,minimum)
        if z>=0 and np.all(cz>=0):return z-float(cz.sum())/ratio,n
        previous,n=n,2*n


@njit(cache=True)
def antithetic_tape(tape,j,start,ratio,threshold,minimum=16):
    if j==0:return tape_pair(tape,j,start,ratio,threshold,minimum)
    cap=start*ratio**j;coarse=cap//ratio
    total,sumsq=0.,0.
    ct,cs=np.zeros(ratio),np.zeros(ratio);cz=np.full(ratio,-1)
    z,previous,n=-1,0,1
    while True:
        for k in range(previous,n):
            x=tape[k];total+=x;sumsq+=x*x
            block=k%ratio;local_n=k//ratio+1
            ct[block]+=x;cs[block]+=x*x
            if cz[block]<0 and (local_n & (local_n-1))==0:
                cz[block]=decision(ct[block],cs[block],local_n,coarse,threshold,minimum)
        if z<0:z=decision(total,sumsq,n,cap,threshold,minimum)
        if z>=0 and np.all(cz>=0):return z-float(cz.sum())/ratio,n
        previous,n=n,2*n


@njit(cache=True)
def train_level(j, start, ratio, threshold, reps, antithetic=False):
    values, costs = np.empty(reps), np.empty(reps)
    for i in range(reps):
        if antithetic:values[i], costs[i] = antithetic_pair(j,start,ratio,threshold)
        else:values[i], costs[i] = real_pair(j, start, ratio, threshold)
    return values, costs


@njit(cache=True)
def sum_tape(tape,j,start,ratio,threshold,probabilities):
    caps=np.empty(j+1,dtype=np.int64)
    for k in range(j+1):caps[k]=start*ratio**k
    zs=np.full(j+1,-1);total,sumsq=0.,0.;previous,n=0,1
    while True:
        for k in range(previous,n):
            x=tape[k];total+=x;sumsq+=x*x
        for k in range(j+1):
            if zs[k]<0:zs[k]=decision(total,sumsq,n,caps[k],threshold,16)
        if np.all(zs>=0):
            value=float(zs[0])
            for k in range(1,j+1):value+=(zs[k]-zs[k-1])/probabilities[k:].sum()
            return value,n
        previous,n=n,2*n


@njit(cache=True)
def sum_term(start,ratio,threshold,probabilities):
    u,cumulative,j=np.random.random(),0.,len(probabilities)-1
    for k in range(len(probabilities)):
        cumulative+=probabilities[k]
        if u<cumulative:j=k;break
    caps=np.empty(j+1,dtype=np.int64)
    for k in range(j+1):caps[k]=start*ratio**k
    zs=np.full(j+1,-1)
    total,sumsq=0.,0.;previous,n=0,1;y=np.random.normal()
    while True:
        for _ in range(previous,n):
            x=real_x(y);total+=x;sumsq+=x*x
        for k in range(j+1):
            if zs[k]<0:zs[k]=decision(total,sumsq,n,caps[k],threshold,16)
        if np.all(zs>=0):
            value=float(zs[0])
            for k in range(1,j+1):
                value+=(zs[k]-zs[k-1])/probabilities[k:].sum()
            return value,n
        previous,n=n,2*n


@njit(cache=True)
def real_term(start, ratio, threshold, probabilities, antithetic=False, sum_mode=False):
    if sum_mode:return sum_term(start,ratio,threshold,probabilities)
    u, cumulative, j = np.random.random(), 0.0, len(probabilities)-1
    for k in range(len(probabilities)):
        cumulative += probabilities[k]
        if u < cumulative:
            j = k
            break
    if antithetic:value,cost=antithetic_pair(j,start,ratio,threshold)
    else:value, cost = real_pair(j, start, ratio, threshold)
    return value/probabilities[j], cost


@njit(cache=True)
def real_estimate(start, ratio, threshold, probabilities, antithetic=False, sum_mode=False):
    cap = start * ratio**(len(probabilities)-1)
    attempts, successes, work = 0, 0, 0
    while successes < 2:
        _, cost = real_term(start, ratio, threshold, probabilities,antithetic,sum_mode)
        attempts += 1
        work += cost
        if np.random.random() < cost/cap:
            successes += 1
    total = 0.0
    # Fresh draws, independent of the calibration data and its stopping time.
    for _ in range(attempts-1):
        value, cost = real_term(start, ratio, threshold, probabilities,antithetic,sum_mode)
        total += value
        work += cost
    return total/(attempts-1), work


@njit(cache=True)
def real_replicates(start, ratio, threshold, probabilities, reps, antithetic=False, sum_mode=False, repeats=1):
    values, costs = np.empty(reps), np.empty(reps)
    for i in range(reps):
        value,cost=0.,0.
        for _ in range(repeats):
            v,c=real_estimate(start, ratio, threshold, probabilities,antithetic,sum_mode)
            value+=v;cost+=c
        values[i],costs[i]=value/repeats,cost
    return values, costs


def level_count(budget, start, ratio):
    level = 0
    while start * ratio**(level+1) <= budget/4:
        level += 1
    return level+1
