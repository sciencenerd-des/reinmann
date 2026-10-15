"""Unprojected canonical prolate Fourier profiles and actual Weil adjoints.

Every decimal prolate vector is replayed against the infinite Jacobi tail.
Taylor moments describe the complete arithmetic sum, including its odd part.
The actual Weil residual includes all omitted modes and eigenvalue uncertainty.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from flint import acb, arb, ctx

from adjoint_fourier_certificate import (OUT as MATRIX_DIR, endpoint_zero_coefficients,
    fourier_coordinate, full_tail, l2_norm_bounds, matrix_inputs, select_correction)
from certified_prolate_projection import _ball, _normalized_trial, _polynomials
from certified_prolate_vectors import certify_trials
from certified_weil import endpoints
from full_ground_fourier import OUTPUT, energy_distance, sha256
from orthogonal_fourier_transfer import protected_mean, validated_base
from threshold_ground_gap import box

OUT = Path('research/prime_spectral/verification_2026_10_11_prolate_adjoint')


def widen(value, radius):
    """Enclose a complex disk by an outward complex rectangle."""
    value = acb(value)
    radius = arb(arb(radius).upper())
    if not value.is_finite() or not radius.is_finite() or not radius >= 0:
        raise ValueError('finite value and nonnegative radius required')
    return acb((value.real-radius).union(value.real+radius),
               (value.imag-radius).union(value.imag+radius))


def complex_box(value):
    return {'real': endpoints(value.real), 'imag': endpoints(value.imag)}


class CanonicalProfile:
    """K_C(t)=exp(t/2) sum H(n exp(t)/sqrt(C)), with no Fourier projection."""
    def __init__(self, jacobi_path, vectors_path, order=20):
        if type(order) is not int or order < 4:
            raise ValueError('Taylor order at least four required')
        jacobi_path, vectors_path = map(Path, (jacobi_path, vectors_path))
        jacobi, vectors = [json.loads(p.read_text()) for p in (jacobi_path, vectors_path)]
        if jacobi.get('generator_sha256') != sha256(Path(__file__).with_name('certified_prolate_jacobi.py')):
            raise ValueError('Jacobi generator provenance mismatch')
        if (vectors.get('generator_sha256') != sha256(Path(__file__).with_name('certified_prolate_vectors.py'))
                or vectors.get('jacobi_certificate_sha256') != sha256(jacobi_path)
                or vectors.get('cutoff') != jacobi.get('cutoff')
                or vectors.get('even_legendre_terms') != jacobi.get('even_legendre_terms')):
            raise ValueError('prolate vector provenance mismatch')
        trials = {key: {name: row[name] for name in ('trial_eigenvalue', 'trial_vector')}
                  for key, row in vectors['modes'].items()}
        replay = certify_trials(jacobi, trials)
        if replay['modes'] != vectors['modes'] or vectors.get('status') != replay['status']:
            raise ValueError('prolate vector certificate differs from replay')
        self.cutoff, self.order = jacobi['cutoff'], order
        self.length = arb(self.cutoff).log()
        zero, four = [_normalized_trial(trials[key]['trial_vector']) for key in ('0', '2')]
        e0, e4 = [arb(vectors['modes'][key]['oriented_unit_eigenvector_l2_error_upper'])
                  for key in ('0', '2')]
        z0 = arb(zero[0].lower()); f0 = arb(abs(four[0]).upper())
        denominator = z0-e0
        if not denominator > 0:
            raise ArithmeticError('zero-integral ratio denominator unresolved')
        ratio_upper = (f0+e4)/denominator
        ratio_error = e4/denominator+f0*e0/(denominator*z0)
        self.input_error = arb((e4+ratio_upper*e0+ratio_error).upper())
        ratio = four[0]/zero[0]
        amplitudes = [four[k]-ratio*zero[k] for k in range(len(zero))]
        self.map_norm = arb(self.cutoff).sqrt().sqrt()*sum(
            (1/arb(n).sqrt() for n in range(1, self.cutoff)), arb(0))
        self.output_error = arb((self.map_norm*self.input_error).upper())
        self.trial_norm_upper = arb((self.map_norm*l2_norm_bounds(amplitudes)).upper())
        polynomials = _polynomials(2*len(zero)-2)
        self.coefficients = [arb(0) for _ in zero]
        for k, amplitude in enumerate(amplitudes):
            for power in range(k+1):
                self.coefficients[power] += amplitude*(arb(4*k+1)/2).sqrt()*_ball(polynomials[2*k][2*power])
        self.moments = self._moments()
        # Only the real error matters at zero; the exact candidate is real.
        origin = self.raw_direct(acb(0)).real
        error0 = self.length.sqrt()*self.output_error
        self.origin = (origin-error0).union(origin+error0)
        if not self.origin > 0:
            raise ArithmeticError('exact canonical Fourier origin may vanish')
        self.provenance = {str(p): sha256(p) for p in (jacobi_path, vectors_path)}

    def raw_direct(self, z):
        """Closed Mellin antiderivative; valid on |Im z|<1/2."""
        z = acb(z)
        if not z.is_finite() or not abs(z.imag) < arb('1/2'):
            raise ValueError('finite frequency in the open half strip required')
        total = acb(0)
        C = self.cutoff
        for n in range(1, C):
            D = (arb(C)/n).log()
            phase = (-acb(0,1)*z*D).exp()*(arb(C)/n).sqrt()
            power_n = arb(1)
            for k, coefficient in enumerate(self.coefficients):
                total += coefficient*(phase-power_n)/(arb(2*k)+arb('1/2')-acb(0,1)*z)
                power_n *= (arb(n)/C)**2
        return total*(acb(0,1)*z*self.length/2).exp()/arb(C).sqrt().sqrt()

    def _moments(self):
        """Real integral moments int t^j K_trial(t) dt on every support piece."""
        result = [arb(0) for _ in range(self.order)]
        C = self.cutoff
        left = -self.length/2
        for n in range(1, C):
            D = (arb(C)/n).log(); right = D+left
            power_n = arb(1)
            for k, coefficient in enumerate(self.coefficients):
                beta = arb(2*k)+arb('1/2'); exponential = (beta*D).exp()
                integral = (beta*D).expm1()/beta
                for j in range(self.order):
                    if j:
                        integral = (exponential*right**j-left**j-j*integral)/beta
                    result[j] += coefficient*power_n*integral
                power_n *= (arb(n)/C)**2
        return [value/arb(C).sqrt().sqrt() for value in result]

    def raw_taylor(self, z):
        z = acb(z)
        if not z.is_finite():
            raise ValueError('finite complex frequency required')
        value = acb(0)
        for j in range(self.order-1, -1, -1):
            value = value*(-acb(0,1)*z)+self.moments[j]/math.factorial(j)
        R = abs(z)*self.length/2
        remainder = self.length.sqrt()*self.trial_norm_upper*R.exp()*R**self.order/math.factorial(self.order)
        return widen(value, remainder)

    def profile(self, z):
        z = acb(z)
        if z.is_zero():
            return acb(1)
        # ||exp(-izt)||_2 <= sqrt(L) exp(|Im z| L/2).
        error = self.length.sqrt()*(abs(z.imag)*self.length/2).exp()*self.output_error
        return widen(self.raw_taylor(z), error)/self.origin

    def target_constant(self, z):
        """Cancel the shared constant and low moments before interval evaluation."""
        z = acb(z)
        if z.is_zero():
            return acb(0)
        mean = self.moments[0]
        error0 = self.length.sqrt()*self.output_error
        if not mean-error0 > 0:
            raise ArithmeticError('trial mean protection unresolved')
        value = acb(0)
        for j in range(self.order-1, 0, -1):
            uniform_moment = (self.length/2)**j/(j+1) if j%2 == 0 else arb(0)
            coefficient = uniform_moment-self.moments[j]/mean
            value = value*(-acb(0,1)*z)+coefficient/math.factorial(j)
        value *= -acb(0,1)*z
        R = abs(z)*self.length/2
        remainder = R.exp()*R**self.order/math.factorial(self.order)
        remainder *= 1+self.length.sqrt()*self.trial_norm_upper/arb(mean.lower())
        trial_profile = self.raw_taylor(z)/mean
        error_z = error0*(abs(z.imag)*self.length/2).exp()
        exact_profile_error = (error_z+abs(trial_profile)*error0)/(mean-error0)
        return widen(value, remainder+exact_profile_error)

    def summary(self):
        return {'cutoff': self.cutoff, 'taylor_order': self.order,
                'input_combination_L2_error_upper': endpoints(self.input_error),
                'arithmetic_map_L2_norm_upper': endpoints(self.map_norm),
                'unprojected_candidate_L2_error_upper': endpoints(self.output_error),
                'trial_arithmetic_candidate_L2_norm_upper': endpoints(self.trial_norm_upper),
                'exact_candidate_fourier_origin': endpoints(self.origin),
                'trial_moments': [endpoints(v) for v in self.moments],
                'input_sha256': self.provenance}


def external_target(z, length, profile, prefix):
    p = profile.profile(z)
    return p, [profile.target_constant(z),
               *[fourier_coordinate(z,length,n) for n in range(1,prefix+1)]]


def certify_external(cutoff, positive, matrix, b, z, profile, nu, delta, mean):
    h = endpoint_zero_coefficients(positive); N = len(positive); M = len(matrix)-1
    if (not delta >= 0 or not mean > 0 or not all(v.is_finite() for v in (nu,delta,mean))
            or cutoff != profile.cutoff or len(matrix[0]) != N+1 or any(len(row) != N+1 for row in matrix)):
        raise ValueError('valid rectangular matrix, uncertainty and protected mean required')
    p,k = external_target(z,arb(cutoff).log(),profile,M)
    residual = [sum((row[n]*h[n] for n in range(N+1)),acb(0))-k[m]
                -(nu*h[m] if m<=N else 0) for m,row in enumerate(matrix)]
    prefix = l2_norm_bounds(residual); tail, details = full_tail(cutoff,positive,b,z,M)
    full = (arb(prefix.upper())**2+arb(tail.upper())**2).sqrt()
    norm = l2_norm_bounds(h); uncertainty = delta*norm
    return {'exact_positive_coefficients': positive, 'target_profile': complex_box(p),
            'residual_prefix_norm': endpoints(prefix), 'entire_residual_tail': details,
            'full_residual_norm_upper': endpoints(full), 'correction_norm': endpoints(norm),
            'eigenvalue_uncertainty_times_norm': endpoints(uncertainty),
            'normalized_profile_error_upper': endpoints((full+uncertainty)/mean)}


def generate(directory=OUT, cover_cells=None, modes=8, prefix=64):
    directory=Path(directory)
    base_path=OUTPUT/'full_ground_fourier.json'; base=validated_base(base_path)
    results=[]; dependencies={str(base_path):sha256(base_path)}
    with ctx.workprec(1024):
        for row in base['results']:
            C=row['threshold_prime']
            profile=CanonicalProfile(directory/f'jacobi_C{C}_T40.json',directory/f'vectors_C{C}_T40.json')
            ell=arb(box(row['full_ground_lower']).lower()); upper=arb(box(row['trial_rayleigh_enclosure']).upper())
            nu=(ell+upper)/2; delta=(upper-ell)/2
            r,_=energy_distance(box(row['trial_rayleigh_enclosure']),ell,box(row['full_second_lower']))
            c=list(map(arb,row['exact_cosine_coefficients'])); m=c[0]/sum((x*x for x in c),arb(0)).sqrt()
            mean=arb(protected_mean(r,m).lower())
            with ctx.workprec(384):
                matrix,b,path=matrix_inputs(C,modes,prefix,MATRIX_DIR if (modes,prefix)==(8,64) else directory)
            dependencies[str(path)]=sha256(path); dependencies.update(profile.provenance)
            probes=[]
            for re,im in [('0','2/5'),('1','0'),('1','2/5'),('-1','2/5')]:
                z=acb(arb(re),arb(im)); _,k=external_target(z,profile.length,profile,prefix)
                positive=select_correction(matrix,k,nu,delta)
                checked=certify_external(C,positive,matrix,b,z,profile,nu,delta,mean)
                checked['z']={'real':re,'imag':im}
                # Retain odd part: no even-profile assumption is used.
                checked['canonical_odd_profile']=complex_box((profile.profile(z)-profile.profile(-z))/2)
                probes.append(checked)
            result={'cutoff':C,'canonical_profile':profile.summary(),'spectral_shift':endpoints(nu),
                    'eigenvalue_uncertainty':endpoints(delta),'ground_mean_lower':endpoints(mean),'probes':probes}
            if cover_cells:
                nx,ny=cover_cells
                if type(nx) is not int or type(ny) is not int or min(nx,ny)<1:
                    raise ValueError('positive rectangle subdivisions required')
                records=[]; maximum=arb(0)
                # Positive real half and both signs of Im z: real K gives
                # p(-conj z)=conj p(z), without assuming evenness.
                for i in range(nx):
                    for j in range(2*ny):
                        x0=arb(i)/nx; x1=arb(i+1)/nx
                        y0=arb(2)*(j-ny)/(5*ny); y1=arb(2)*(j+1-ny)/(5*ny)
                        center=acb((x0+x1)/2,(y0+y1)/2)
                        z=acb(x0.union(x1),y0.union(y1))
                        _,k=external_target(center,profile.length,profile,prefix)
                        positive=select_correction(matrix,k,nu,delta)
                        checked=certify_external(C,positive,matrix,b,z,profile,nu,delta,mean)
                        checked['cell']=[i,j]; records.append(checked)
                        maximum=arb(max(maximum.upper(),arb(checked['normalized_profile_error_upper']['hi']).upper()))
                result['rectangle_cover']={'region':'|Re z|<=1, |Im z|<=2/5',
                    'real_half_subdivisions':nx,'imag_half_subdivisions':ny,
                    'symmetry':'Real candidate and even real ground: E(-conj z)=conj E(z); no candidate evenness assumed',
                    'normalized_profile_error_upper':endpoints(maximum),'cells':records}
            results.append(result)
            print('canonical unprojected prolate adjoints checked:',C,flush=True)
    source_names=('canonical_prolate_adjoint.py','adjoint_fourier_certificate.py','certified_prolate_jacobi.py',
        'certified_prolate_vectors.py','certified_prolate_projection.py','certified_weil.py','weil_matrix.py',
        'full_ground_fourier.py','orthogonal_fourier_transfer.py','threshold_ground_gap.py')
    return {'status':'canonical_unprojected_prolate_full_weil_adjoint_certificate','bits':1024,
            'correction_modes':modes,'residual_prefix':prefix,'results':results,'dependency_sha256':dependencies,
            'source_sha256':{str(Path(__file__).with_name(n)):sha256(Path(__file__).with_name(n)) for n in source_names},
            'scope':'Fixed cutoffs 2 and 3. Written prolate/Jacobi realization, full Weil operator, domain and tail arguments plus Arb arithmetic. No growing-support theorem, global strip comparison, novelty or RH claim.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,default=OUT)
    parser.add_argument('--cover-cells',nargs=2,type=int)
    parser.add_argument('--modes',type=int,default=8)
    parser.add_argument('--prefix',type=int,default=64)
    args=parser.parse_args()
    result=generate(args.directory,args.cover_cells,args.modes,args.prefix)
    suffix='' if args.cover_cells is None else f'_cover{args.cover_cells[0]}x{args.cover_cells[1]}'
    if (args.modes,args.prefix)!=(8,64):
        suffix=f'_N{args.modes}_M{args.prefix}'+suffix
    (args.directory/f'canonical_adjoint{suffix}.json').write_text(json.dumps(result,indent=2)+'\n')
