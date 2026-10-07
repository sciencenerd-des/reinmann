"""Actual operator-domain trials: norm, Rayleigh and FULL residual enclosures.

The trials replace the endpoint jumps of the saved cosine Rayleigh trials
by localized normalized renewal Green profiles. A mode outside the saved
trial space supplies a LOWER bound on the full residual, not a projected
residual advertised as the full one. Both trace-transfer gates fail.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_weil import certified_matrix, endpoints
from residual_endpoint_certificate import bounds_for_interval, residual_constants
from threshold_ground_gap import box, minmax_second_bound

ROOT = Path('research/prime_spectral/verification_2026_10_07_assembled_trial')
BASIS = Path('research/prime_spectral/verification_2026_10_07_boundary_basis/renewal_basis.json')
GAPS = Path('research/prime_spectral/verification_2026_10_07_trace_stability/threshold_ground_gaps.json')
OLD_MASS = Path('research/prime_spectral/renewal_trace_enclosures_2026_10_07.json')


def cutoff_graph_bounds(log_inverse_radius, J, V1, E0):
    """Fixed trace J with a proved vanishing full L2 graph-norm upper bound."""
    R,J,V1,E0=map(arb,(log_inverse_radius,J,V1,E0))
    if (not all(v.is_finite() for v in (R,J,V1,E0)) or not R >= 4
            or not J > 0 or not V1 > 0 or not E0 >= 0):
        raise ValueError('finite R>=4, J,V1>0, E0>=0 required')
    r=(-R).exp()
    H=3*J*V1
    norm=H*(2*r).sqrt()
    image=(2*r).sqrt()+H*r.sqrt()*(2*arb(2).sqrt()+2*R+2/arb(1).exp())+E0*norm
    return {'log_inverse_radius':R,'norm_upper':norm,'image_upper':image,
            'graph_upper':norm+image,'exact_trace':J}


def assembled_bounds(length, coefficients, matrix, eta, J, V1, Vlocal, prime_norm, ground_upper):
    """Enclose the trial described in ASSEMBLED_TRIAL_FULL_RESIDUAL_2026_10_07.md.

    All functions live on [0,L]. Coefficients denote exact rationals in
    the normalized even cosine basis. eta is the exact Green coefficient.
    The support cutoff is fixed at r=exp(-64); Vlocal bounds V(exp(-32)).
    """
    L, eta, J, V1, Vlocal, m, U = map(arb, (length,eta,J,V1,Vlocal,prime_norm,ground_upper))
    c = list(map(arb,coefficients))
    if (not all(x.is_finite() for x in (L,eta,J,V1,Vlocal,m,U,*c))
            or not L > arb(1)/2 or not eta > 0 or not J > 0 or not V1 > 0
            or not Vlocal > 0 or not m >= 0 or len(c) != 9 or len(matrix) != 10
            or any(len(row) != 10 for row in matrix)):
        raise ValueError('positive finite inputs and matching nine-mode/ten-mode data required')
    norm_c = sum((x*x for x in c),arb(0)).sqrt()
    if not norm_c > 0:
        raise ValueError('nonzero cosine trial required')
    c = [x/norm_c for x in c]
    edge = (c[0]+arb(2).sqrt()*sum(c[1:],arb(0)))/L.sqrt()
    P = (abs(c[0])+arb(2).sqrt()*sum((abs(x) for x in c[1:]),arb(0)))/L.sqrt()
    D = arb(2).sqrt()/L.sqrt()*sum((abs(c[j])*2*arb.pi()*j/L for j in range(1,len(c))),arb(0))
    qg = sum((c[i]*matrix[i][j]*c[j] for i in range(9) for j in range(9)),arb(0))
    coupling = sum((matrix[9][j]*c[j] for j in range(9)),arb(0))
    if not qg > 0:
        raise ArithmeticError('positive cosine Rayleigh value unresolved')

    r = (-arb(64)).exp()
    if not 4*r < L or not 2*r < (-arb(32)).exp():
        raise ArithmeticError('disjoint cutoff supports or renewal majorant unresolved')
    Hlocal = J*Vlocal
    Hglobal = 3*J*V1  # a=1/2: J V(1)(1+1/a).
    E0 = (2*arb.pi()).log()+L*(arb(5)/4+2*(L/2).cosh())+m
    tail = arb(64)+1/arb(1).exp()  # E1(r) <= log(1/r)+e^-1.
    commutator = 1+tail
    Bphi_inf = 1+Hglobal*commutator
    Bchi_two = r.sqrt()*(2*arb(2).sqrt()+2*tail)
    Bphi_two = (2*r).sqrt()+Hglobal*Bchi_two
    e_two = (4*r).sqrt()*(abs(edge)+eta*Hlocal)
    if not e_two < 1:
        raise ArithmeticError('normalization enclosure excludes no zero trial')
    Nlo,Nhi = (1-e_two).lower(),(1+e_two).upper()

    # Positive comparison form plus bounded perturbation controls the
    # ACTUAL form error of e, including all modes and endpoint jumps.
    QBchi = r*(1+2*tail)
    QBphi = 2*r*Hlocal*Bphi_inf
    QBe = (2*eta*QBphi.sqrt()+2*abs(edge)*QBchi.sqrt())**2
    QAe = QBe+E0*e_two**2
    form_error = 2*(qg*QAe).sqrt()+QAe
    mu_numerator = qg+arb(0,form_error.upper())
    mu = mu_numerator/arb(Nlo*Nlo).union(arb(Nhi*Nhi))
    if not mu > 0 or not mu < U:
        raise ArithmeticError('assembled Rayleigh bound failed the supplied ground upper bound')
    mu_abs = abs(mu).upper()

    # Full L2 upper bound by the actual operator decomposition. The
    # half-line Bphi bound includes its nonlocal tail outside cutoff support.
    Ae_two = 2*eta*Bphi_two+2*abs(edge)*Bchi_two+E0*e_two
    Bg_two = L.sqrt()*D+P*(2*arb(2).log()).sqrt()
    residual_two_upper = ((Bg_two+E0+Ae_two)/Nlo+mu_abs).upper()
    residual_two_lower = ((abs(coupling)-Ae_two-mu_abs*e_two)/Nhi).lower()
    if not residual_two_lower > 0:
        raise ArithmeticError('full-residual omitted-mode obstruction unresolved')

    # p=g-edge*(chi_left+chi_right) is globally Lipschitz after zero
    # extension. Integrate min(M1 |z|,2 Pp) against the full Levy measure.
    Pp = P+abs(edge)
    M1 = D+abs(edge)/r
    split = 2*Pp/M1
    if not 0 < split < 1:
        raise ArithmeticError('Lipschitz-modulus split outside proved range')
    Bp_inf = 2*Pp*(1+(1/split).log()+1/arb(1).exp())
    f_inf = P+abs(edge)+eta*Hlocal
    residual_inf_upper = ((Bp_inf+2*eta*Bphi_inf+(E0+mu_abs)*f_inf)/Nlo).upper()
    residual_inf_lower = (residual_two_lower/L.sqrt()).lower()
    trace_lo,trace_hi = (eta*J/Nhi).lower(),(eta*J/Nlo).upper()

    return {'edge':edge,'cosine_rayleigh':qg,'omitted_mode_coupling':coupling,
            'cutoff_radius':r,'L2_change_upper':e_two,'positive_form_change_upper':QAe,
            'Nlo':Nlo,'Nhi':Nhi,'rayleigh':mu,'R2lo':residual_two_lower,
            'R2hi':residual_two_upper,'Rinflo':residual_inf_lower,
            'Rinfhi':residual_inf_upper,'trace_lo':trace_lo,'trace_hi':trace_hi,
            'Bphi_L2_upper':Bphi_two,'Ae_L2_upper':Ae_two}


def generate():
    basis, gaps, masses = [json.loads(p.read_text()) for p in (BASIS,GAPS,OLD_MASS)]
    comparisons = [(2,Path('research/prime_spectral/verification_2026_10_07_trace_stability/threshold_two_lower_operator.json'),'57/1000','56999/1000000','1/5'),
                   (3,ROOT/'closer_prime_three_lower.json','103/25000000','4119/1000000000','1/400')]
    sources = [BASIS,GAPS,OLD_MASS,Path(__file__),*[p for _,p,_,_,_ in comparisons]]
    sources += [Path(__file__).with_name(name) for name in ('certified_weil.py','weil_matrix.py','compact_window_certificate.py','threshold_ground_gap.py','residual_endpoint_certificate.py')]
    for path,digest in basis['source_hashes'].items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest()!=digest:
            raise ArithmeticError('boundary profile source hash mismatch')
    output=[]
    with ctx.workprec(384):
        J=box(basis['exact_basis_trace'])
        V1=box(next(row for row in basis['rows'] if row['distance_label']=='1')['renewal'])
        Vlocal=box(next(row for row in masses['rows'] if row['distance_label']=='exp(-32)')['renewal_mass'])
        for prime,path,shift,second_weakened,eta in comparisons:
            lower=json.loads(path.read_text())
            if lower['half_width'] != ('7/20' if prime==2 else '11/20') or not box(lower['full_lower_bound']) > 0:
                raise ArithmeticError('positive full comparison at intended support required')
            for name,digest in lower['source_hashes'].items():
                if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()!=digest:
                    raise ArithmeticError('full comparison source hash mismatch')
            second,sectors=minmax_second_bound(lower,shift)
            if not second > arb(second_weakened):
                raise ArithmeticError('full complementary lower bound insufficient')
            witness=next(row for row in gaps['results'] if row['threshold_prime']==prime)
            L=arb(prime).log()
            m=arb(0) if prime==2 else 2*arb(2).log()/arb(2).sqrt()
            U=arb('142/100000' if prime==2 else '103/1000000000')
            _,matrix,_=certified_matrix(prime,9)
            bounds=assembled_bounds(L,witness['trial_even_cosine_coefficients'],matrix,eta,J,V1,Vlocal,m,U)
            state=bounds_for_interval(L,m,U,V1)
            gap=arb(second_weakened)-U
            A,B=residual_constants(state,gap)
            # Even the smallest possible residual allowed by the proved
            # lower bound defeats this interface's nonzero-trace condition.
            obstruction=A*bounds['R2lo']-bounds['trace_hi']
            if not obstruction > 0:
                raise ArithmeticError('trace-transfer obstruction not certified')
            record={'threshold_prime':prime,'status':'assembled_full_residual_enclosed_trace_gate_fails',
                    'exact_green_coefficient':eta,'cosine_coefficients':witness['trial_even_cosine_coefficients'],
                    'norm_enclosure':{'lo':str(bounds['Nlo'].fmpq()),'hi':str(bounds['Nhi'].fmpq())},
                    'actual_rayleigh_enclosure':endpoints(bounds['rayleigh']),
                    'actual_full_L2_residual_enclosure':{'lo':str(bounds['R2lo'].fmpq()),'hi':str(bounds['R2hi'].fmpq())},
                    'actual_full_Linfty_residual_enclosure':{'lo':str(bounds['Rinflo'].fmpq()),'hi':str(bounds['Rinfhi'].fmpq())},
                    'both_exact_trial_trace_enclosures':{'lo':str(bounds['trace_lo'].fmpq()),'hi':str(bounds['trace_hi'].fmpq())},
                    'full_second_eigenvalue_lower':endpoints(second),
                    'weakened_full_complementary_clearance':endpoints(gap),
                    'L2_trace_coefficient':endpoints(A),'Linfty_trace_coefficient':endpoints(B),
                    'split_L2_budget_for_trace_error_1e-3':endpoints(arb('5e-4')/A),
                    'split_Linfty_budget_for_trace_error_1e-3':endpoints(arb('5e-4')/B),
                    'trace_gate_obstruction_lower':endpoints(obstruction),
                    'normalization_details':{key:endpoints(bounds[key]) for key in ('edge','L2_change_upper','positive_form_change_upper','Ae_L2_upper','omitted_mode_coupling')},
                    'fixed_trace_small_graph_examples':[
                        {key:endpoints(value) for key,value in
                         cutoff_graph_bounds(R,J,V1,state['E0']).items()}
                        for R in (32,64,128)],
                    'lower_operator_input':str(path),'lower_operator_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                    'shift':shift,'inertia_sectors':sectors}
            output.append(record)
            print('actual assembled full residual enclosed; trace gate fails at prime',prime,flush=True)
    return {'status':'actual_trials_certified_but_nonzero_actual_trace_transfer_failed','bits':384,
            'results':output,'source_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
            'scope':'Actual unit operator-domain trials, not actual minimizing states. Written operator/renewal/form inputs plus Arb. Nonzero trial traces do not imply nonzero minimizing-state traces. No larger window or novelty claim.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    data=generate()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
