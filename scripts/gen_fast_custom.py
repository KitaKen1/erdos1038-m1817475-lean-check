#!/usr/bin/env python3
import sys,json,time,argparse,os
from concurrent.futures import ProcessPoolExecutor, as_completed
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
BASE=1.708; K=560
np = None
r = None

def require_generation_deps():
    global np, r
    if np is None:
        try:
            import numpy as _np
        except ModuleNotFoundError as exc:
            raise SystemExit(
                "Missing optional dependency 'numpy'. Install optional "
                "generation dependencies with: python3 -m pip install -r "
                "requirements.txt"
            ) from exc
        np = _np
    if r is None:
        try:
            import ehp1038_research as _r
        except ModuleNotFoundError as exc:
            if exc.name in {"numpy", "scipy"}:
                raise SystemExit(
                    f"Missing optional dependency '{exc.name}'. Install "
                    "optional generation dependencies with: python3 -m pip "
                    "install -r requirements.txt"
                ) from exc
            raise SystemExit(
                "Could not import ehp1038_research.py from scripts/."
            ) from exc
        r = _r

def parse_triples(s):
    if not s or s=='none': return []
    return [tuple(map(int,part.split(','))) for part in s.split(';') if part]

def make_pis(a,b,c,locs,lswaps):
    require_generation_deps()
    ids=list(range(K)); pi3=r.make_revswap_pi3(a,b,c)
    for x,y,L in locs:
        for t in range(L):
            pi3[x+t],pi3[y+t]=pi3[y+t],pi3[x+t]
    pi4=ids.copy()
    for u,v,p in lswaps:
        for t in range(v-u+1):
            pi4[u+t],pi4[p+t]=pi4[p+t],pi4[u+t]
    assert sorted(pi3)==ids, 'pi3 not perm'
    assert sorted(pi4)==ids, 'pi4 not perm'
    return [ids.copy(),ids.copy(),pi3,pi4]

def solve_task(arg):
    require_generation_deps()
    M,s,pis,i,init_grid,max_iter=arg
    sol=r.solve_block(r.block_ds(M,i,s,pis,K,BASE),r.block_intervals(M,i,K,BASE),init_grid=init_grid,max_iter=max_iter,tol=1e-9)
    sol['i']=i
    return sol

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--M',type=float,required=True); ap.add_argument('--ds3',type=float,default=0.0)
    ap.add_argument('--a',type=int,default=94); ap.add_argument('--b',type=int,default=324); ap.add_argument('--c',type=int,default=329)
    ap.add_argument('--locs',default='94,198,31'); ap.add_argument('--lswaps',required=True)
    ap.add_argument('--workers',type=int,default=24); ap.add_argument('--init-grid',type=int,default=3); ap.add_argument('--max-iter',type=int,default=45)
    ap.add_argument('--out',required=True)
    args=ap.parse_args()
    require_generation_deps()
    M=args.M; s=[1e-7,0.74046,0.860615475+args.ds3,0.860615475+args.ds3+(M-BASE)+1e-7]
    pis=make_pis(args.a,args.b,args.c,parse_triples(args.locs),parse_triples(args.lswaps))
    tasks=[(M,s,pis,i,args.init_grid,args.max_iter) for i in range(K)]
    t0=time.time(); sols=[None]*K; done=0
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs=[ex.submit(solve_task,t) for t in tasks]
        for fut in as_completed(futs):
            sol=fut.result(); sols[sol['i']]=sol; done+=1
            if done%50==0:
                vals=[x['margin'] for x in sols if x]
                print('done',done,'min',min(vals),'elapsed',time.time()-t0,flush=True)
    margins=[sol['margin'] for sol in sols]
    worst_i=int(np.argmin(margins))
    cert={"problem":"EHP #1038 experimental finite-atom piecewise-shift certificate", "status":"floating point only; not a formal/interval proof", "M":M,"base":BASE,"K":K,"h":(M-BASE)/K,"lane_starts_s":s,"permutations":pis,"weights":[sol['weights'] for sol in sols],"margins":margins,"y_min":[sol['y'] for sol in sols],"worst_margin":float(margins[worst_i]),"worst_block":worst_i,"worst_y":sols[worst_i]['y'],"iterations":[sol['iterations'] for sol in sols],"time_sec":time.time()-t0,"variant":f"custom fast: M={M}; ds3={args.ds3}; pi3 revswap({args.a},{args.b},{args.c}) locs={args.locs}; pi4 swaps={args.lswaps}","lane_description":"d_{j,i}=A_i+s_j+pi_j(i)h, A_i=M-ih, h=(M-1.708)/560; pi1,pi2 identity; pi3/pi4 stored."}
    with open(args.out,'w') as f: json.dump(cert,f,indent=2)
    print(json.dumps({"M":M,"worst_margin":cert['worst_margin'],"worst_block":worst_i,"worst_y":cert['worst_y'],"time_sec":cert['time_sec'],"mins":sorted((v,i) for i,v in enumerate(margins))[:30],"mean_iter":float(np.mean(cert['iterations'])),"max_iter":int(max(cert['iterations']))},indent=2))
if __name__=='__main__': main()
