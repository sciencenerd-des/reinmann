"""Propose rational scalar-exp certificates. Lean checks all their inequalities."""
from dataclasses import dataclass
from fractions import Fraction as Q
import math
from pathlib import Path


def literal(x):
    x=Q(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'


def pair(a): return f'({literal(a[0])}, {literal(a[1])})'
def cadd(a,b): return (a[0]+b[0],a[1]+b[1])
def cmul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def size(a): return abs(a[0])+abs(a[1])


@dataclass(frozen=True)
class Disk:
    c: tuple
    r: Q=Q(0)

    def add(self,b): return Disk(cadd(self.c,b.c),self.r+b.r)
    def mul(self,b): return Disk(cmul(self.c,b.c), self.r*size(b.c)+size(self.c)*b.r+self.r*b.r)
    def lean(self): return f'⟨{pair(self.c)}, {literal(self.r)}, by norm_num⟩'


def exact(re,im=0): return Disk((Q(re),Q(im)))
def exponent(x):
    x=abs(x)
    e=x.numerator.bit_length()-x.denominator.bit_length()
    if x < Q(2)**e: e-=1
    return e


def outward(a,bits=50):
    m=max(size(a.c),a.r)
    if not m: return a
    step=Q(2)**(exponent(m)-bits)
    c=tuple(round(x/step)*step for x in a.c)
    r=a.r+size((a.c[0]-c[0],a.c[1]-c[1]))
    r=-(-r//step)*step
    return Disk(c,r)


PI=Disk((Q('3.14159265358979323846'),Q(0)),Q(1,10**20))


def certificate(a):
    turns=round(float(a.c[1])/(2*math.pi))
    small=exact(Q(1,64)).mul(a.add(exact(0,-2*turns).mul(PI)))
    assert size(small.c)+small.r <= 1
    poly={20:exact(0)}
    for k in reversed(range(20)):
        poly[k]=outward(exact(Q(1,math.factorial(k))).add(small.mul(poly[k+1])))
    squares={0:Disk(poly[0].c,poly[0].r+Q(1,10**18))}
    for k in range(6): squares[k+1]=outward(squares[k].mul(squares[k]))
    return turns,poly,squares


def lean_certificate(name,a):
    turns,poly,squares=certificate(a)
    out=f'def {name}Poly : ℕ → Disk\n'
    for k,b in poly.items(): out+=f'  | {k} => {b.lean()}\n'
    out+='  | _ => zero\n\n'
    out+=f'def {name}Squares : ℕ → Disk\n'
    for k,b in squares.items(): out+=f'  | {k} => {b.lean()}\n'
    out+='  | _ => zero\n\n'
    out+=f'def {name} : CertifiedScalarExp.Data :=\n  ⟨{a.lean()}, {turns}, {name}Poly, {name}Squares⟩\n\n'
    out+=f'''set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem {name}_checks : CertifiedScalarExp.Checks {name} := by
  constructor
  · norm_num [{name}, CertifiedScalarExp.reduced, {name}Poly, {name}Squares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [{name}, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        {name}Poly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [{name}, CertifiedScalarExp.roundingCheck, {name}Squares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

'''
    # square_zero is not definitionally equal because it contains a rational sum.
    out=out.replace('  · rfl\n  · intro k hk\n    interval_cases k <;>\n      norm_num ['+name+', CertifiedScalarExp.roundingCheck, '+name+'Squares,',
                    '  · apply CertifiedScalarExp.disk_ext <;> norm_num ['+name+', '+name+'Squares, '+name+'Poly, inflate]\n  · intro k hk\n    interval_cases k <;>\n      norm_num ['+name+', CertifiedScalarExp.roundingCheck, '+name+'Squares,')
    return out,squares[6]


HEADER='''/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CertifiedScalarExp
import Reinmann.HardTileLogInputs
import Mathlib.Tactic.IntervalCases

noncomputable section
namespace Reinmann.HardTilePowerInputs
open CertifiedTaylorModel CertifiedScalarExp
set_option maxRecDepth 10000

'''


def render(ns):
    out=HEADER
    for n in ns:
        a=Q(round(math.log(n)*10**15),10**15)
        e=Q(1 if n==2 else 6,10**15)
        input_disk=exact(Q(-1,2),-14).mul(Disk((a,Q(0)),e))
        source,result=lean_certificate('power'+str(n),input_disk)
        out+=source
        out+=f'''theorem power{n}_value : Contains (power{n}.squares 6)
    (Complex.exp (-((1/2 : ℂ)+14*Complex.I)*(Real.log ({n}:ℝ) : ℂ))) := by
  apply CertifiedScalarExp.sound power{n} power{n}_checks
  have hl : Contains (⟨({literal(a)},0),{literal(e)},by norm_num⟩ : Disk)
      (Real.log ({n}:ℝ) : ℂ) := by
    apply contains_real
    convert HardTileLogInputs.log_{n} using 1 <;> norm_num
  have h := contains_mul (contains_exact ((-1/2 : ℚ),-14)) hl
  have hv : value ((-1/2 : ℚ),-14) = -((1/2 : ℂ)+14*Complex.I) := by
    norm_num [value]
    ring
  rw [hv] at h
  have hd : power{n}.input = mul (exact ((-1/2 : ℚ),-14))
      (⟨({literal(a)},0),{literal(e)},by norm_num⟩ : Disk) := by
    apply CertifiedScalarExp.disk_ext <;>
      norm_num [power{n}, CertifiedTaylorModel.mul, exact, qmul, size]
  rw [hd]
  exact h

'''
    return out+'end Reinmann.HardTilePowerInputs\n'


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--all',action='store_true')
    p.add_argument('--check',action='store_true')
    args=p.parse_args()
    target=Path(__file__).resolve().parents[2]/'Reinmann/HardTilePowerInputs.lean'
    source=render(range(2,22) if args.all else [2])
    if args.check:
        assert target.read_text()==source, 'Generated scalar certificates differ'
    else:
        target.write_text(source)
    print(target)
