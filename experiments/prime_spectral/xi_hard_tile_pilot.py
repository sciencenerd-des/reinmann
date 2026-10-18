"""External Arb hard-tile pilot, not a Lean centre/jet certificate."""
import argparse, hashlib, json, time
from pathlib import Path
from fractions import Fraction
from flint import arb, acb, acb_series, ctx


def xi(s):
    z = 1+(s-1)*s.zeta(deflate=True) if isinstance(s, acb_series) else (s-1)*s.zeta()
    return s*(s/2).gamma()*(-s*arb.pi().log()/2).exp()*z/2


def run(output):
    ctx.prec = 192
    ctx.cap = 17
    start = time.monotonic()
    centre = acb(arb("1/2"), 14)
    jet = xi(acb_series([centre,1]))
    # Cover the entire unit circle by interval angles, not point samples.
    best = None
    circle_rows = []
    for count in [64,256,1024]:
        begin = time.monotonic()
        maximum = arb(0)
        for k in range(count):
            lo = 2*arb.pi()*k/count
            hi = 2*arb.pi()*(k+1)/count
            angle = arb((lo+hi)/2, (hi-lo)/2)
            s = centre + acb(angle.cos(),angle.sin())
            bound = abs(xi(s))
            if not bound.is_finite():
                raise RuntimeError("Nonfinite circle enclosure")
            maximum = arb(max(maximum.upper(),bound.upper()))
        circle_rows.append({"arcs":count,"majorant_upper":str(maximum.upper()),
                            "seconds":time.monotonic()-begin})
        best = maximum
    radius = arb("1/16")
    K = sum((n*abs(jet[n])*radius**(n-1) for n in range(1,17)),arb(0))
    K += best*radius**16*(17-16*radius)/(1-radius)**2
    # First-order panel count estimate from a proved/coarse Lipschitz rule
    # is deliberately kept separate from the high-order integrator requirement.
    result = {"status":"external_arb_hard_tile_only", "centre":["1/2","14"],
              "radius":"1/16", "bits":ctx.prec,"degree":16,
              "jet":[str(jet[n]) for n in range(17)],
              "xi_modulus_lower":str(abs(jet[0]).lower()),
              "derivative_upper":str(K.upper()),
              "centre_error_budget":"1/1000000",
              "margin_lower":str((abs(jet[0])-K*radius-arb("1/1000000")).lower()),
              "unit_circle":circle_rows,"seconds":time.monotonic()-start,
              "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "Lean_centre_and_jet_certified":False,
              "scope":"Arb enclosure and proposed local tile. No Lean panel time, tile time or 35-tile extrapolation is asserted."}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!='jet'},indent=2))


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    run(p.parse_args().output)
