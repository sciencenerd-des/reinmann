"""Finite ball-certified deficit/recurrence laboratory; no extrapolation in rank."""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from flint import arb, arb_mat, ctx
from coefficients import endpoints as exact_endpoints


def endpoints(value):
    # Compact reports by outward rounding; coefficient inputs retain full precision.
    with ctx.workprec(192):
        return exact_endpoints(value + arb(0))


def interval(record):
    lo, hi = Fraction(record['lo']), Fraction(record['hi'])
    if lo > hi:
        raise ValueError('reversed rational enclosure')
    return arb(str(lo)).union(arb(str(hi)))


def load_coefficients(path):
    data = json.loads(path.read_text())
    if data.get('schema_version') != 1 or data.get('status') != 'rigorous_ball_enclosures_not_Lean_certificates':
        raise ValueError('unsupported coefficient provenance')
    rows = data['coefficients']
    if len(rows) != data['max_n'] + 1 or [v['n'] for v in rows] != list(range(len(rows))):
        raise ValueError('noncontiguous coefficient indices')
    mu = [interval(v) for v in rows]
    if not all(v > 0 for v in mu):
        raise ValueError('coefficient positivity unresolved')
    theta = data['theta_check']['records']
    if [v['n'] for v in theta] != list(range(len(theta))):
        raise ValueError('noncontiguous theta indices')
    independent = [interval(v['enclosure']) for v in theta]
    if len(independent) > len(mu) or any(not a.overlaps(b) for a,b in zip(mu, independent)):
        raise ValueError('independent formula disagreement')
    return mu, independent


def sign(value):
    return 'positive' if value > 0 else 'negative' if value < 0 else 'unresolved'


def minor(mu, rank, shift):
    if rank < 0 or shift < 0 or shift + rank > len(mu):
        raise ValueError('minor outside available coefficients')
    if rank == 0:
        return arb(1)
    # Positive normalization removes small overall magnitude, not uncertainty.
    a0 = mu[0]
    return arb_mat([[mu[shift+i-j]/a0 if shift+i-j >= 0 else arb(0)
                     for j in range(rank)] for i in range(rank)]).det()


def deficits(mu):
    q = [mu[n]*mu[n+2]/mu[n+1]**2 for n in range(len(mu)-2)]
    delta = [1-x for x in q]
    records = []
    for n in range(len(delta)-2):
        left = delta[n+1]**2
        right = q[n+1]**2 * delta[n] * delta[n+2]
        margin = left-right
        row = {'n':n, 'normalized_D3':endpoints(margin), 'status':sign(margin)}
        if all(x > 0 for x in (delta[n],delta[n+1],delta[n+2],q[n+1])):
            curvature = delta[n].log()-2*delta[n+1].log()+delta[n+2].log()
            budget = -2*q[n+1].log()
            row.update(log_curvature=endpoints(curvature), log_budget=endpoints(budget),
                       log_slack=endpoints(budget-curvature),
                       relative_safety=endpoints(margin/left))
        records.append(row)
    return records


def complete_symmetric(e):
    # H(z) E(-z)=1. Only algebra, no positivity assumption.
    h = [arb(1)]
    for k in range(1,len(e)):
        h.append(sum(((-1)**(j-1)*e[j]*h[k-j] for j in range(1,k+1)),arb(0)))
    return h


def run(path, max_rank=12):
    ctx.prec = 2048
    mu, theta = load_coefficients(path)
    if not 1 <= max_rank <= min(64,len(mu)-1):
        raise ValueError('invalid rank budget')
    determinants = {}
    rank_records = []
    for r in range(max_rank+1):
        for m in range(len(mu)-r+1):
            determinants[r,m] = minor(mu,r,m)
        if r:
            counts = {s:0 for s in ('positive','negative','unresolved')}
            for m in range(len(mu)-r+1):
                counts[sign(determinants[r,m])] += 1
            rank_records.append({'rank':r,'shift_min':0,'shift_max':len(mu)-r,**counts})
    # Every residual must CONTAIN zero, never interpreted as an identity proof.
    recurrences = []
    for r in range(1,max_rank):
        for m in range(1,len(mu)-r):
            lhs = determinants[r+1,m]*determinants[r-1,m]
            rhs = determinants[r,m]**2-determinants[r,m-1]*determinants[r,m+1]
            if not (lhs-rhs).contains(0):
                raise ArithmeticError('Desnanot-Jacobi cross-check disagrees')
            if determinants[r,m] > 0:
                budget = 1-determinants[r,m-1]*determinants[r,m+1]/determinants[r,m]**2
                candidate_slack = budget - arb(r)/(m+r)
                recurrences.append({'rank':r,'shift':m,'relative_margin':endpoints(budget),
                                    'status':sign(budget),
                                    'candidate_slack':endpoints(candidate_slack),
                                    'candidate_status':sign(candidate_slack)})
    e = [x/mu[0] for x in mu]
    h = complete_symmetric(e[:25])
    dual = []
    for r in range(1,min(max_rank,12)+1):
        for m in range(1,7):
            if r+m > len(h):
                continue
            value = arb_mat([[h[r+i-j] if r+i-j>=0 else arb(0)
                              for j in range(m)] for i in range(m)]).det()
            if not (value-determinants[r,m]).contains(0):
                raise ArithmeticError('rank-shift duality cross-check disagrees')
            dual.append({'rank':r,'shift':m,'dual_status':sign(value)})
    # Off-real-zero positive cosine-kernel control: A=3 fails rank 6 at shift 2.
    control = [arb(3+4**n)/math.factorial(2*n) for n in range(32)]
    control_minor = minor(control,6,2)
    if not control_minor < 0:
        raise ArithmeticError('adversarial control was not rejected')
    return {'schema_version':1,'status':'finite_ball_results_not_unbounded_order_proof',
            'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'laboratory_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'working_bits':ctx.prec,'ranks':rank_records,
            'taylor_deficits':deficits(mu),'independent_theta_deficits':deficits(theta),
            'recurrence_windows':recurrences,'rank_shift_duality_checks':dual,
            'negative_control':{'function':'3 cos(t)+cos(2t)', 'rank':6,'shift':2,
                                'normalized_determinant':endpoints(control_minor),'status':sign(control_minor)},
            'candidate_bound':'eta_r(m) >= r/(m+r), conjectural outside tested windows',
            'remaining_obligation':'Prove positive recurrence margins uniformly in both rank and shift, or supply a nonnegative factorization from the theta/arithmetic data. Finite margins do not imply this.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients',type=Path,required=True)
    parser.add_argument('--max-rank',type=int,default=12)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.coefficients,args.max_rank)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'ranks':result['ranks'],'theta_windows':len(result['independent_theta_deficits']),
                      'recurrence_windows':len(result['recurrence_windows'])},indent=2))

if __name__=='__main__':
    main()
