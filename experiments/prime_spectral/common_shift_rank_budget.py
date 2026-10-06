"""Two telescoping Galerkin energies at one common finite Weil shift.

The joint Cauchy bound is tested, not assumed to improve paired rank bounds.
All matrices in the chain are restrictions of the same saved large matrix.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import acb, arb, arb_mat, ctx
from certified_mode_comparison import box
from certified_weil import endpoints
from eigenvalue_response import _fourier_functional
from rank_schur_recurrence import _even_matrix
from weil_eigenfamily import center_basis


def conditional_ground_tail_upper(length, height, eigen_drop, coupling_norm, gap):
    """Ground Cauchy bound, conditional on a gap throughout the spectral window.

    The caller must prove that every relevant constrained block C_n-lambda I
    is >= gap*I and its origin coupling has norm <= coupling_norm. A finite
    positive input is not itself evidence for an all-rank gap.
    """
    if not all(x.is_finite() for x in (length, height, eigen_drop, coupling_norm, gap)):
        raise ValueError('finite conditional bound inputs required')
    if not length > 0 or not height >= 0 or not eigen_drop >= 0 or not coupling_norm >= 0 or not gap > 0:
        raise ValueError('positive support/gap and nonnegative height, drop, coupling required')
    kappa, drop, bound = gap.lower(), eigen_drop.upper(), coupling_norm.upper()
    argument = height.upper()*length.upper()
    weight = arb(1) if argument == 0 else (argument.sinh()/argument).sqrt()
    return (weight*((drop*(1+bound*bound/(kappa*kappa))/kappa).sqrt()
                    +drop*bound/(kappa*kappa))).upper()


def nonnegative(value):
    """Intersect an analytically nonnegative energy enclosure with [0,infinity)."""
    if not value.is_finite() or value.upper() < 0:
        raise ArithmeticError('nonnegative finite Galerkin energy contradicted')
    return value.lower().max(arb(0)).union(value.upper())


def spectral_gram(operator, sources):
    size = operator.nrows()
    if operator.ncols() != size or not size or not sources or any(len(s) != size for s in sources):
        raise ValueError('nonempty square operator and matching sources required')
    if any(not x.is_finite() for s in sources for x in s):
        raise ValueError('finite sources required')
    if any(endpoints(operator[i, j]) != endpoints(operator[j, i]) for i in range(size) for j in range(i)):
        raise ValueError('symmetric matrix enclosure required')
    values, basis = center_basis(operator)
    if not all(x > 0 for x in values):
        raise ArithmeticError('strictly positive constrained spectrum required')
    projections = [[sum((basis[i, k]*s[i] for i in range(size)), arb(0))
                    for k in range(size)] for s in sources]
    gram = arb_mat([[sum((a*b/mu for a, b, mu in zip(left, right, values)), arb(0))
                     for right in projections] for left in projections])
    return gram, values


def chain_budget(operator, sources, ranks):
    size = operator.nrows()
    if (operator.ncols() != size or len(ranks) < 2 or any(type(n) is not int for n in ranks)
            or not 0 < ranks[0] or ranks[-1] != size
            or any(a >= b for a, b in zip(ranks, ranks[1:]))):
        raise ValueError('strictly increasing positive ranks ending at full size required')
    if not sources or any(len(s) != size for s in sources):
        raise ValueError('full-size common sources required')
    grams, spectra = [], []
    for n in ranks:
        block = arb_mat([[operator[i, j] for j in range(n)] for i in range(n)])
        gram, values = spectral_gram(block, [s[:n] for s in sources])
        grams.append(gram)
        spectra.append(values)
    increments = [right-left for left, right in zip(grams, grams[1:])]
    total = grams[-1]-grams[0]
    count = len(sources)
    for inc in increments+[total]:
        for i in range(count):
            inc[i, i] = nonnegative(inc[i, i])
    summed = increments[0]
    for inc in increments[1:]:
        summed = summed+inc
    if any(not (summed[i, j]-total[i, j]).contains(0) for i in range(count) for j in range(count)):
        raise ArithmeticError('Gram-energy telescoping identity disagrees')
    profiles = []
    for k in range(1, count):
        paired = sum(((inc[0, 0]*inc[k, k]).sqrt() for inc in increments), arb(0))
        joint = (total[0, 0]*total[k, k]).sqrt()
        signed = sum((-inc[0, k] for inc in increments), arb(0))
        for inc in increments:
            # Analytically each Gram increment is positive semidefinite.
            # This check rejects intervals contradicting its 2x2 consequence.
            if (inc[0, 0]*inc[k, k]-inc[0, k]*inc[0, k]).upper() < 0:
                raise ArithmeticError('incremental Gram positivity contradicted')
        if not (-total[0, k]).overlaps(signed) or not joint.upper() >= abs(signed).lower():
            raise ArithmeticError('signed cumulative transfer contradicts energy bound')
        profiles.append({
            'signed_increment_intervals': [endpoints(-inc[0, k]) for inc in increments],
            'signed_cumulative_profile_change': endpoints(signed),
            'dual_energy_increment_intervals': [endpoints(inc[k, k]) for inc in increments],
            'paired_increment_cauchy_sum_upper': str(paired.upper().fmpq()),
            'joint_telescoped_cauchy_upper': str(joint.upper().fmpq()),
            'joint_to_paired_ratio_lower': (str((joint.lower()/paired.upper()).lower().fmpq())
                                            if paired.upper() > 0 else None),
        })
    return {
        'ranks': ranks,
        'positive_common_shift_spectra': [[endpoints(x) for x in values] for values in spectra],
        'source_gram_matrices': [[[endpoints(g[i, j]) for j in range(count)] for i in range(count)] for g in grams],
        'primal_energy_increment_intervals': [endpoints(inc[0, 0]) for inc in increments],
        'total_primal_energy_increment_interval': endpoints(total[0, 0]),
        'profile_transfers': profiles,
    }


def run(paths):
    if len(paths) < 2:
        raise ValueError('at least two nested finite Weil certificates required')
    raw = [path.read_bytes() for path in paths]
    certificates = [json.loads(data) for data in raw]
    source_dir = Path(__file__).parent
    for c in certificates:
        if c.get('status') != 'certified_finite_weil_gates':
            raise ValueError('certified finite Weil inputs required')
        if c['cutoff'] != certificates[0]['cutoff']:
            raise ValueError('one fixed support required')
        for name, digest in c['source_hashes'].items():
            if hashlib.sha256((source_dir/name).read_bytes()).hexdigest() != digest:
                raise ValueError('stale finite Weil source: '+name)
    ranks = [c['modes'] for c in certificates]
    if any(a >= b for a, b in zip(ranks, ranks[1:])):
        raise ValueError('strictly increasing input ranks required')
    with ctx.workprec(1024):
        full = _even_matrix(certificates[-1])
        for c in certificates[:-1]:
            smaller = _even_matrix(c)
            if any(not (full[i][j]-smaller[i][j]).contains(0)
                   for i in range(c['modes']+1) for j in range(c['modes']+1)):
                raise ArithmeticError('nested principal Weil matrices disagree')
        nu = box(certificates[-1]['smallest_even_eigenvalue'])
        size = ranks[-1]
        operator = arb_mat([[full[i][j]-(nu if i == j else 0)
                             for j in range(1, size+1)] for i in range(1, size+1)])
        length = arb(certificates[0]['cutoff']).log()
        sources = [[full[i][0] for i in range(1, size+1)]]
        labels = []
        for label, z in (('real_4', acb(4)), ('real_8', acb(8)), ('imag_1', acb(0, 1))):
            labels.append(label)
            sources.append(_fourier_functional(size, length, z)[1:])
        result = chain_budget(operator, sources, ranks)
        result['profile_transfers'] = dict(zip(labels, result['profile_transfers']))
        result['common_shift_interval'] = endpoints(nu)
    result.update({
        'status': 'certified_finite_common_shift_joint_energy_audit_not_ground_rank_budget',
        'cutoff': certificates[0]['cutoff'], 'working_bits': 1024,
        'input_sha256': [hashlib.sha256(data).hexdigest() for data in raw],
        'source_hashes': {name: hashlib.sha256((source_dir/name).read_bytes()).hexdigest()
                          for name in ('common_shift_rank_budget.py', 'weil_eigenfamily.py',
                                       'certified_mode_comparison.py', 'certified_weil.py',
                                       'rank_schur_recurrence.py', 'eigenvalue_response.py')},
        'scope': 'One finite fixed-support nested chain at the same spectral parameter; older profiles here are shifted Schur profiles rather than their own ground profiles.',
        'remaining': 'Uniform integrated dual energy, common-shift ground drift, low spectrum and origin control, support and boundary path budget, Xi identification and RH.',
    })
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates', nargs='+', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificates)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    for label, item in result['profile_transfers'].items():
        print(label, float(Fraction(item['joint_telescoped_cauchy_upper'])))


if __name__ == '__main__':
    main()
