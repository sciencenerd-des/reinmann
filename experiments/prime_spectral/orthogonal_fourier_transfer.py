"""Orthogonality-aware full-ground Fourier transfer, with whole-strip coverage.

Uses the previously validated full-operator energy bounds. The analytic
Hilbert-space argument is written, not formalized here; Arb certifies its
scalar inputs and the universal cosine-kernel variance cover.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import endpoints
from full_ground_fourier import OUTPUT, energy_distance, sha256
from threshold_ground_gap import box


def protected_mean(mass_upper, trial_mean_lower):
    """Sharp mean lower bound from angle and unit-vector geometry."""
    r, m = arb(mass_upper), arb(trial_mean_lower)
    if not all(x.is_finite() for x in (r, m)):
        raise ValueError('finite mass and mean required')
    r, m = arb(r.upper()), arb(m.lower())
    if not 0 <= r < 1 or not 0 < m <= 1:
        raise ValueError('mass in [0,1), mean in (0,1] required')
    lower = m*(1-r).sqrt() - (r*(1-m*m)).sqrt()
    if not lower > 0:
        raise ArithmeticError('orthogonal angle does not protect the origin')
    return lower


def kernel_variance(a, b):
    """Squared norm of the mean-zero cosine kernel, a=L Re(z), b=L Im(z).

    V = (sinh(b)/b + sinc(a))/2 - |sinc((a+ib)/2)|^2.
    Entire sinc evaluation also covers rectangles containing the origin.
    """
    a, b = arb(a), arb(b)
    if not a.is_finite() or not b.is_finite():
        raise ValueError('finite scaled frequency rectangle required')
    s = acb(a/2, b/2).sinc()
    return (acb(0, b).sinc().real+a.sinc())/2 - s.real**2-s.imag**2


def variance_cover(length, height, extent=16, real_cells=512, imag_cells=16):
    """Cover all real frequencies, not a sampled-frequency assertion.

    V is even in a,b. Interval rectangles cover [0,A] x [0,L*height].
    For a>=A, V <= (sinh(B)/B + 1/A)/2. The discarded term is nonnegative.
    """
    length, height, A = arb(length), arb(height), arb(extent)
    if (not all(x.is_finite() for x in (length, height, A))
            or not length > 0 or not height >= 0 or not A > 0
            or type(real_cells) is not int or real_cells < 1
            or type(imag_cells) is not int or imag_cells < 1):
        raise ValueError('positive length, extent, cell counts and nonnegative height required')
    B = arb((length*height).upper())
    W2 = acb(0, B).sinc().real
    tail = (W2+1/A)/2
    # At height zero the imaginary partition collapses to a line.
    ny = 1 if B.is_zero() else imag_cells
    best, location = arb(0), None
    for i in range(real_cells):
        a = (A*i/real_cells).union(A*(i+1)/real_cells)
        for j in range(ny):
            b = (B*j/ny).union(B*(j+1)/ny)
            upper = arb(kernel_variance(a,b).upper())
            if upper > best:
                best, location = upper, [i,j]
    bound = arb(max(best.upper(), tail.upper()))
    if not bound > 0:
        raise ArithmeticError('positive universal kernel bound unresolved')
    return {'upper': bound, 'compact_upper': best, 'tail_upper': tail,
            'scaled_imaginary_upper': B, 'extent': str(extent),
            'real_cells': real_cells, 'imag_cells': ny,
            'max_cell': location, 'rectangles_checked': real_cells*ny}


def profile_error(mass_upper, trial_mean_lower, variance_upper):
    """Origin-normalized profile error using u=c*g+w with w perpendicular g."""
    r, m, V = map(arb, (mass_upper, trial_mean_lower, variance_upper))
    if not V.is_finite() or not V >= 0:
        raise ValueError('finite nonnegative kernel variance upper bound required')
    r, m, V = arb(r.upper()), arb(m.lower()), arb(V.upper())
    mean = protected_mean(r,m)
    return (r*V).sqrt()/(m*mean)


def validated_base(path):
    """Bind the numerical dependency to the completed prior validation record."""
    path = Path(path)
    manifest = json.loads((path.parent/'manifest.json').read_text())
    if manifest['numerical_artifact_sha256'].get(path.name) != sha256(path):
        raise ValueError('base numerical certificate hash mismatch')
    data = json.loads(path.read_text())
    if data.get('status') != 'fixed_support_full_ground_fourier_enclosures':
        raise ValueError('full-operator ground certificate required')
    for name, digest in data['source_hashes'].items():
        if sha256(name) != digest:
            raise ValueError('base source hash mismatch: '+name)
    if sha256('research/prime_spectral/verification_2026_10_07_assembled_trial/assembled_trials.json') != data['trial_input_sha256']:
        raise ValueError('base trial provenance mismatch')
    return data


def generate(base_path, real_cells=512, imag_cells=16):
    base = validated_base(base_path)
    rows = []
    with ctx.workprec(256):
        for row in base['results']:
            # Recompute from the outward full spectral and Rayleigh inputs;
            # no retained-block gap is substituted for the full one.
            r, _ = energy_distance(box(row['trial_rayleigh_enclosure']),
                                   box(row['full_ground_lower']), box(row['full_second_lower']))
            coeff = [arb(x) for x in row['exact_cosine_coefficients']]
            m = coeff[0]/sum((x*x for x in coeff),arb(0)).sqrt()
            L = arb(row['threshold_prime']).log()
            mean = protected_mean(r,m)
            strips = []
            for old in row['strips']:
                Y = arb(old['height'])
                cover = variance_cover(L,Y,real_cells=real_cells,imag_cells=imag_cells)
                bound = profile_error(r,m,cover['upper'])
                elementary_variance = (1+acb(0,L*Y).sinc().real)/2
                elementary = profile_error(r,m,elementary_variance)
                if not bound < box(old['origin_normalized_profile_error_upper']):
                    raise ArithmeticError('new observable bound did not improve the saved bound')
                strips.append({'height': old['height'],
                               'origin_normalized_profile_error_upper': endpoints(bound),
                               'elementary_orthogonal_error_upper': endpoints(elementary),
                               'previous_profile_error_upper': old['origin_normalized_profile_error_upper'],
                               'variance_cover': {k:endpoints(v) if isinstance(v,arb) else v
                                                  for k,v in cover.items()}})
            rows.append({'cutoff':row['threshold_prime'], 'orthogonal_mass_upper':endpoints(r),
                         'trial_mean':endpoints(m),'ground_mean_lower':endpoints(mean),
                         'previous_ground_mean_lower':row['ground_mean_lower'], 'strips':strips})
            print('orthogonal whole-strip transfer at cutoff',row['threshold_prime'],flush=True)
    return {'status':'orthogonal_full_ground_fourier_transfer', 'bits':256, 'results':rows,
            'base_sha256':sha256(base_path),
            'source_sha256':sha256(__file__),
            'scope':'Written Hilbert-space/operator dependencies plus Arb scalar and complete rectangle/tail arithmetic; no growing-support Xi convergence or RH proof.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=OUTPUT/'full_ground_fourier.json')
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--real-cells',type=int,default=512)
    parser.add_argument('--imag-cells',type=int,default=16)
    args=parser.parse_args()
    result=generate(args.base,args.real_cells,args.imag_cells)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
