"""Interval finite Weil forms and finite simplicity/parity/normalization gates.

No Xi coefficients or zeta zeros are inputs. No infinite-mode convergence claim.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import arb, acb, ctx
from weil_matrix import prime_powers


def endpoints(x):
    return {'lo': str(x.lower().fmpq()), 'hi': str(x.upper().fmpq())}


def correlation_ball(m, n, z, length):
    if m == n:
        return 2*(1-z/length)*(2*arb.pi()*n*z/length).cos()
    return -2*z/length*(arb.pi()*(m+n)*z/length).cos()*(arb.pi()*(m-n)*z/length).sinc()


def arch_regularized(m, n, z, length):
    sinhc = (acb(0,1)*z).sinc()
    if m != n:
        q_over_z = -2/length*(arb.pi()*(m+n)*z/length).cos()*(arb.pi()*(m-n)*z/length).sinc()
        return (z/2).exp()*q_over_z/(2*sinhc)
    omega = 2*arb.pi()*n/length
    q = correlation_ball(m,n,z,length)
    divided_expm1 = (z/4).exp()*(acb(0,1)*z/4).sinc()/2
    q_difference_over_z = -2*(omega*z).cos()/length-omega**2*z*(omega*z/2).sinc()**2
    return (divided_expm1*q+q_difference_over_z)/(2*sinhc)


def entry(m, n, length, powers, cutoff):
    tolerance = arb(2)**-240
    pole = acb.integral(lambda z, _: 2*(z/2).cosh()*correlation_ball(m,n,z,length),
                        0, length, rel_tol=tolerance, abs_tol=tolerance, eval_limit=200000)
    arch = acb.integral(lambda z, _: arch_regularized(m,n,z,length),
                        0, length, rel_tol=tolerance, abs_tol=tolerance, eval_limit=200000)
    q0 = 2 if m == n else 0
    arch += ((4*arb.pi()).log()+arb.const_euler())*q0/2
    arch += q0/2*(length/2).tanh().log()
    primes = acb(0)
    for power, prime in powers:
        if power == cutoff:
            continue  # Correlation vanishes exactly at the support endpoint.
        primes += arb(prime).log()/arb(power).sqrt()*correlation_ball(m,n,acb(arb(power).log()),length)
    value = pole-arch-primes
    if not value.is_finite() or not value.imag.contains(0):
        raise ArithmeticError('certified integral unresolved')
    return value.real


def certified_matrix(cutoff, modes):
    if type(cutoff) is not int or not 2<=cutoff<=100000 or type(modes) is not int or not 1<=modes<=16:
        raise ValueError('integer cutoff 2..100000 and modes 1..16 required')
    length = arb(cutoff).log()
    powers = prime_powers(cutoff)
    cache = {}
    def cell(m,n):
        # Symmetry and simultaneous sign reversal follow from the formulas.
        key = min((m,n),(n,m),(-m,-n),(-n,-m))
        if key not in cache:
            cache[key] = entry(*key,length,powers,cutoff)
        return cache[key]
    matrix = [[cell(m,n) for n in range(-modes,modes+1)] for m in range(-modes,modes+1)]
    even = [[arb(0) for _ in range(modes+1)] for _ in range(modes+1)]
    odd = [[cell(m,n)-cell(m,-n) for n in range(1,modes+1)] for m in range(1,modes+1)]
    even[0][0] = cell(0,0)
    for m in range(1,modes+1):
        even[0][m] = even[m][0] = arb(2).sqrt()*cell(0,m)
        for n in range(1,modes+1):
            even[m][n] = cell(m,n)+cell(m,-n)
    return matrix, even, odd


def inertia(matrix, shift=0):
    """Interval LDL without pivoting; fails closed if any pivot sign is unclear."""
    n = len(matrix)
    if not n or any(len(row)!=n for row in matrix):
        raise ValueError('nonempty square matrix required')
    L = [[arb(0) for _ in range(n)] for _ in range(n)]
    pivots = []
    for i in range(n):
        pivot = matrix[i][i]-arb(shift)-sum((L[i][k]**2*pivots[k] for k in range(i)),arb(0))
        if not pivot.is_finite() or pivot.contains(0):
            raise ArithmeticError('LDL pivot sign unresolved')
        pivots.append(pivot)
        L[i][i] = arb(1)
        for j in range(i+1,n):
            L[j][i] = (matrix[j][i]-sum((L[j][k]*L[i][k]*pivots[k] for k in range(i)),arb(0)))/pivot
    return sum(p<0 for p in pivots), pivots


def eigen_interval(matrix, index, iterations=160):
    if type(index) is not int or not 0<=index<len(matrix) or type(iterations) is not int or iterations<1:
        raise ValueError('valid eigenvalue index and positive iteration count required')
    bound = max(sum((abs(x) for x in row),arb(0)).upper() for row in matrix)
    width = int(bound.ceil().fmpq())+1
    lo, hi = Fraction(-width), Fraction(width)
    for _ in range(iterations):
        mid = (lo+hi)/2
        count, _ = inertia(matrix, arb(str(mid)))
        if count<=index:
            lo=mid
        else:
            hi=mid
    return arb(str(lo)).union(arb(str(hi)))


def run(cutoff=13, modes=4):
    with ctx.workprec(512):
        matrix, even, odd = certified_matrix(cutoff,modes)
        count, positive_pivots = inertia(matrix)
        first = eigen_interval(even,0)
        second = eigen_interval(even,1)
        odd_first = eigen_interval(odd,0)
        gap = second.min(odd_first)-first
        # Boundary evaluation on the even block is proportional to (1,sqrt2,...).
        # V_j=e_j-sqrt2 e_0 spans its kernel. Test V^T(A-upper I)V > 0.
        upper = first.upper()
        shifted = [[even[i][j]-(upper if i==j else 0) for j in range(modes+1)] for i in range(modes+1)]
        restricted = [[shifted[i][j]-arb(2).sqrt()*(shifted[i][0]+shifted[0][j])+2*shifted[0][0]
                       for j in range(1,modes+1)] for i in range(1,modes+1)]
        boundary_count, boundary_pivots = inertia(restricted)
        passed = count==0 and first>0 and gap>0 and boundary_count==0
        return {'schema_version':1, 'status':'certified_finite_weil_gates' if passed else 'unresolved',
                'cutoff':cutoff,'modes':modes,'dimension':2*modes+1,
                'prime_powers':prime_powers(cutoff),'working_bits':512,
                'matrix':[[endpoints(x) for x in row] for row in matrix],
                'smallest_even_eigenvalue':endpoints(first),'second_even_eigenvalue':endpoints(second),
                'smallest_odd_eigenvalue':endpoints(odd_first),'spectral_gap':endpoints(gap),
                'positive_LDL_pivots':[endpoints(p) for p in positive_pivots],
                'boundary_kernel_LDL_pivots':[endpoints(p) for p in boundary_pivots],
                'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                 for name in ('certified_weil.py','weil_matrix.py')},
                'scope':'Only this finite Weil form: positivity, simple even lowest eigenvector, and nonzero boundary evaluation.',
                'remaining':'Perturbed operator construction and uniform mode/support convergence to Xi. Weil-form eigenvalues are not zeta ordinates.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff',type=int,default=13)
    parser.add_argument('--modes',type=int,default=4)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.cutoff,args.modes)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],result['smallest_even_eigenvalue'])


if __name__=='__main__':
    main()
