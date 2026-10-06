"""Finite certification of the scaled-deficit mechanism for the rank-two bound."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
from flint import arb, ctx
from laboratory import load_coefficients, endpoints, sign, minor


def analyze(mu):
    if len(mu) < 5 or not all(v > 0 for v in mu):
        raise ValueError('at least five strictly positive coefficient balls required')
    q = {m:mu[m-1]*mu[m+1]/mu[m]**2 for m in range(1,len(mu)-1)}
    epsilon = {m:(m+1)*(1-q[m]) for m in q}
    rows=[]
    for m in range(2,len(mu)-2):
        eps_slack=epsilon[m]**2-epsilon[m-1]*epsilon[m+1]
        gamma=[math.factorial(j)*mu[j]/mu[0] for j in (m-1,m,m+1)]
        # A_2(m) = D_2(m)/P_2(m) = gamma_m^2 epsilon_m.
        normalized=[]
        for j in (m-1,m,m+1):
            p=arb(1)/(math.factorial(j)*math.factorial(j+1))
            normalized.append(minor(mu,2,j)/p)
        factors=[gamma[j]**2*epsilon[m+j-1] for j in range(3)]
        if any(not (a-b).contains(0) for a,b in zip(normalized,factors)):
            raise ArithmeticError('rank-two factorization mismatch')
        q_now=q[m]
        c=arb(2*m*(2*m-1))/((2*m+2)*(2*m+1))
        cv2=q_now/c-1
        row={'center_m':m, 'epsilon':endpoints(epsilon[m]),
             'epsilon_logconcavity_slack':endpoints(eps_slack),
             'epsilon_logconcavity_status':sign(eps_slack),
             'gamma_logconcavity_slack':endpoints(gamma[1]**2-gamma[0]*gamma[2]),
             'normalized_rank2_slack':endpoints(normalized[1]**2-normalized[0]*normalized[2]),
             'tilted_squared_variable_cv2':endpoints(cv2),
             'rank1_cv_budget_slack':endpoints(arb(2)/(2*m-1)-cv2)}
        if all(1-q[j]>0 for j in (m-1,m,m+1)):
            curvature=(1-q[m-1]).log()-2*(1-q_now).log()+(1-q[m+1]).log()
            budget=-2*q_now.log()+(arb(m)/(m+2)).log()
            row['rank2_log_budget_slack']=endpoints(budget-curvature)
        rows.append(row)
    return rows


def boundary(mu):
    if len(mu)<4 or not all(v>0 for v in mu[:4]):
        raise ValueError('four positive coefficient balls required at the boundary')
    a=[v/mu[0] for v in mu[:4]]
    slack=(2*(a[1]**2-a[2]))**2-12*(a[2]**2-a[1]*a[3])
    direct=(2*minor(mu,2,1))**2-12*minor(mu,2,0)*minor(mu,2,2)
    if not (slack-direct).contains(0):
        raise ArithmeticError('boundary normalization mismatch')
    return {'center_m':1,'A2_logconcavity_slack':endpoints(slack),'status':sign(slack)}


def run(path):
    ctx.prec=1024
    mu,theta=load_coefficients(path)
    control=[arb(1)]+[arb(2)/math.factorial(n) for n in range(1,8)]
    c=analyze(control)[0]
    if c['epsilon_logconcavity_status']!='negative':
        raise ArithmeticError('shifted exponential control was not rejected')
    return {'schema_version':1,'status':'finite_scaled_deficit_evidence_not_tail_proof',
            'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'working_bits':ctx.prec,
            'taylor':analyze(mu),'independent_theta':analyze(theta),
            'boundary':{'taylor':boundary(mu),'independent_theta':boundary(theta)},
            'control':{'function':'2 exp(z)-1','rank1_gamma':'1,2,2,2,...; globally log-concave',
                       'rank2_shift2_eta':'1/4 < 1/2', 'record':c},
            'mechanism':'A2(m)=gamma_m^2 epsilon_m, epsilon_m=(m+1)(1-mu_(m-1)mu_(m+1)/mu_m^2)',
            'open_obligation':'Prove epsilon_m positive and log-concave at every m from the theta kernel. This is sufficient for the rank-two bound when gamma is nonnegative and log-concave, not a proof at all ranks.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    try:
        result=run(args.coefficients)
    except (ValueError,ArithmeticError,OSError,KeyError) as exc:
        parser.error(str(exc))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print({key:{'windows':len(result[key]),'positive':sum(v['epsilon_logconcavity_status']=='positive' for v in result[key])} for key in ('taylor','independent_theta')})

if __name__=='__main__':
    main()
