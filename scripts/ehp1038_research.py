#!/usr/bin/env python3
import math, json, os, sys, time, argparse
import numpy as np
from scipy.optimize import linprog
from concurrent.futures import ProcessPoolExecutor, as_completed

BASE=1.708
K=560

def s_for_M(M, eps=1e-7):
    return [eps, 0.7404600000000001, 0.8606154749999999, 0.8606154749999999+(M-BASE)+eps]

def V_y(y, ds, weights):
    return -math.log(abs(y)) - sum(w*math.log(abs(y-d)) for w,d in zip(weights,ds))

def deriv_num_coeffs(ds, weights):
    poly=np.array([1.0])
    for d in ds:
        poly=np.convolve(poly, np.array([-d,1.0]))
    N=-poly.copy()
    for j,(w,dj) in enumerate(zip(weights,ds)):
        prod=np.array([1.0])
        for l,dl in enumerate(ds):
            if l!=j:
                prod=np.convolve(prod,np.array([-dl,1.0]))
        term=np.convolve(prod,np.array([0.0,1.0]))
        if len(term)<len(N):
            term=np.pad(term,(0,len(N)-len(term)))
        N -= w*term
    return N

def block_intervals(M, i, K=K, base=BASE):
    h=(M-base)/K
    A=M-i*h
    C=A-h
    T0,T1=(C,A) if C<A else (A,C)
    return [(T0-1,T1-1),(T0,T1+1)]

def block_ds(M, i, s, pis, K=K, base=BASE):
    h=(M-base)/K
    A=M-i*h
    return [A+s[j]+pis[j][i]*h for j in range(4)]

def exact_margin(ds, weights, intervals):
    candidates=[]
    for lo,hi in intervals:
        candidates.append(lo); candidates.append(hi)
    coeff=deriv_num_coeffs(ds,weights)
    roots=np.roots(coeff[::-1])
    for r in roots:
        if abs(r.imag)<1e-7:
            y=float(r.real)
            if y<=0: continue
            if any(abs(y-d)<1e-8 for d in ds): continue
            for lo,hi in intervals:
                if lo-1e-8 <= y <= hi+1e-8:
                    candidates.append(y); break
    cand=[]
    for y in candidates:
        if y>0 and all(abs(y-d)>1e-10 for d in ds):
            if not any(abs(y-z)<1e-8 for z in cand):
                cand.append(float(y))
    vals=[(V_y(y,ds,weights), y) for y in cand]
    return min(vals)

def solve_block(ds, intervals, init_grid=10, max_iter=45, tol=1e-9, weight_bound=None):
    points=[]
    for lo,hi in intervals:
        for y in (lo,hi):
            if y>0 and all(abs(y-d)>1e-10 for d in ds):
                points.append(float(y))
        if init_grid>1:
            for y in np.linspace(lo,hi,init_grid):
                if y>0 and all(abs(y-d)>1e-7 for d in ds):
                    points.append(float(y))
    # unique but preserve-ish
    points=sorted(set([round(float(y),15) for y in points]))
    bounds=[(0, weight_bound)]*4+[(None,None)]
    c=np.array([0,0,0,0,-1.0])
    last=None
    for it in range(max_iter):
        A=[]; b=[]
        for y in points:
            A.append([math.log(abs(y-d)) for d in ds] + [1.0])
            b.append(-math.log(abs(y)))
        res=linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method='highs-ds', options={'time_limit': 5.0})
        if not res.success:
            raise RuntimeError(res.message)
        w=res.x[:4]; t=res.x[4]
        m,y=exact_margin(ds,w,intervals)
        last=(w,t,m,y,it+1,len(points))
        if t-m <= tol:
            return {"weights":w.tolist(),"margin":float(m),"y":float(y),"lp_t":float(t),"iterations":it+1,"points":len(points)}
        if all(abs(y-p)>1e-9 for p in points):
            points.append(float(y)); points.sort()
        else:
            # stalled: accept
            return {"weights":w.tolist(),"margin":float(m),"y":float(y),"lp_t":float(t),"iterations":it+1,"points":len(points),"stalled":True}
    w,t,m,y,it,pts=last
    return {"weights":w.tolist(),"margin":float(m),"y":float(y),"lp_t":float(t),"iterations":it,"points":pts,"not_converged":True}

def solve_one(args):
    M,s,pis,i,init_grid=args
    ds=block_ds(M,i,s,pis)
    intervals=block_intervals(M,i)
    sol=solve_block(ds,intervals,init_grid=init_grid)
    sol['i']=i
    return sol

def solve_cert(M, pis, init_grid=10, workers=1):
    s=s_for_M(M)
    t0=time.time()
    sols=[None]*K
    if workers<=1:
        for i in range(K): sols[i]=solve_one((M,s,pis,i,init_grid))
    else:
        with ProcessPoolExecutor(max_workers=workers) as ex:
            futs=[ex.submit(solve_one,(M,s,pis,i,init_grid)) for i in range(K)]
            for fut in as_completed(futs):
                sol=fut.result(); sols[sol['i']]=sol
    margins=[sol['margin'] for sol in sols]
    worst_i=int(np.argmin(margins))
    return {"M":M,"base":BASE,"K":K,"h":(M-BASE)/K,"lane_starts_s":s,"permutations":pis,
            "weights":[sol['weights'] for sol in sols],"margins":margins,"y_min":[sol['y'] for sol in sols],
            "worst_margin":float(margins[worst_i]),"worst_block":worst_i,"worst_y":sols[worst_i]['y'],
            "iterations":[sol['iterations'] for sol in sols],"time_sec":time.time()-t0}


def make_final8162_pis():
    ids=list(range(K))
    # Lane 3: reversed interval assignment, then a local swap among the bad blocks.
    pi3=make_revswap_pi3(95,321,333)
    for t in range(26):
        pi3[95+t], pi3[200+t] = pi3[200+t], pi3[95+t]
    # Lane 4: ordinary interval swap to rescue the donor cluster.
    pi4=ids.copy()
    for t in range(376-344+1):
        pi4[344+t], pi4[279+t] = pi4[279+t], pi4[344+t]
    return [ids.copy(), ids.copy(), pi3, pi4]

def make_identity_pis():
    ids=list(range(K))
    return [ids.copy(),ids.copy(),ids.copy(),ids.copy()]

def make_swap_pi3(a,b,c):
    pi=list(range(K)); L=b-a+1; d=c+L-1
    if not (0<=a<=b<K and 0<=c<=d<K and (d<a or c>b)):
        raise ValueError((a,b,c,d))
    for t in range(L):
        pi[a+t]=c+t; pi[c+t]=a+t
    return pi


def make_revswap_pi3(a,b,c):
    pi=list(range(K)); L=b-a+1; d=c+L-1
    if not (0<=a<=b<K and 0<=c<=d<K and (d<a or c>b)):
        raise ValueError((a,b,c,d))
    for t in range(L):
        pi[a+t]=c+t
        pi[c+t]=b-t
    return pi

def pis_from_pi3(pi3):
    ids=list(range(K)); return [ids.copy(), ids.copy(), list(pi3), ids.copy()]

def make_multiswap_pi3(swaps):
    pi=list(range(K))
    for a,b,c in swaps:
        L=b-a+1; d=c+L-1
        for t in range(L):
            x=a+t; y=c+t
            pi[x],pi[y]=pi[y],pi[x]
    return pi

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--M',type=float,default=1.815)
    ap.add_argument('--workers',type=int,default=4)
    ap.add_argument('--init-grid',type=int,default=10)
    ap.add_argument('--variant',type=str,default='current')
    ap.add_argument('--out',type=str,default='')
    args=ap.parse_args()
    if args.variant=='final8162':
        cert=solve_cert(args.M, make_final8162_pis(), init_grid=args.init_grid, workers=args.workers)
        mins=sorted((v,i) for i,v in enumerate(cert['margins']))[:10]
        print(json.dumps({"M":cert['M'],"variant":args.variant,"worst_margin":cert['worst_margin'],"worst_block":cert['worst_block'],"time_sec":cert['time_sec'],"mins":mins,"mean_iter":float(np.mean(cert['iterations'])),"max_iter":int(max(cert['iterations']))},indent=2))
        if args.out:
            cert['problem']='EHP #1038 experimental finite-atom piecewise-shift certificate'
            cert['status']='floating point only; not a formal/interval proof'
            cert['variant']='final8162: lane3 revswap(95,321,333) plus lane3 local swap [95,120]<->[200,225]; lane4 swap [344,376]<->[279,311]'
            cert['lane_description']='d_{j,i}=A_i+s_j+pi_j(i)h, A_i=M-i h, h=(M-1.708)/560; pi1,pi2 identity; pi3 and pi4 as stored.'
            with open(args.out,'w') as f: json.dump(cert,f,indent=2)
        return
    if args.variant=='identity': pi3=list(range(K))
    elif args.variant=='current': pi3=make_swap_pi3(140,280,400)
    elif args.variant.startswith('swap:'):
        a,b,c=map(int,args.variant.split(':')[1].split(',')); pi3=make_swap_pi3(a,b,c)
    elif args.variant.startswith('revswap:'):
        a,b,c=map(int,args.variant.split(':')[1].split(',')); pi3=make_revswap_pi3(a,b,c)
    elif args.variant.startswith('mswap:'):
        swaps=[]
        for part in args.variant.split(':',1)[1].split(';'):
            a,b,c=map(int,part.split(',')); swaps.append((a,b,c))
        pi3=make_multiswap_pi3(swaps)
    else:
        raise ValueError(args.variant)
    cert=solve_cert(args.M,pis_from_pi3(pi3),init_grid=args.init_grid,workers=args.workers)
    mins=sorted((v,i) for i,v in enumerate(cert['margins']))[:10]
    print(json.dumps({"M":cert['M'],"variant":args.variant,"worst_margin":cert['worst_margin'],"worst_block":cert['worst_block'],"time_sec":cert['time_sec'],"mins":mins,"mean_iter":float(np.mean(cert['iterations'])),"max_iter":int(max(cert['iterations']))},indent=2))
    if args.out:
        cert['problem']='EHP #1038 experimental piecewise-shift certificate'
        cert['status']='floating point; not a proof'
        cert['variant']=args.variant
        with open(args.out,'w') as f: json.dump(cert,f,indent=2)

if __name__=='__main__': main()
