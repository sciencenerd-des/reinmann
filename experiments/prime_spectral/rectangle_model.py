"""Shared pole-free Xi expression graph and exact rational Taylor proposals.

All floating point choices are proposals. The emitted Lean checks establish
every enclosure and rounding step independently.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import math

from degree8_scalar_certificates import Disk, exact, certificate, outward, size, cmul

ROUND_BITS = 50
ZERO = exact(0)
GAMMA_ERROR = Q(4, 10**14)
ZETA_ERROR = Q(6, 10**8)
BERNOULLI_CORRECTIONS = (Q(1, 12), Q(-1, 720), Q(1, 30240),
                         Q(-1, 1209600), Q(1, 47900160), Q(-691, 1307674368000))


def rounded(a):
    # Retain small exact rationals, including non-dyadic grid coordinates.
    # Long rational inverse powers are rounded outward as before.
    if not a.r and max(max(abs(x.numerator).bit_length(), x.denominator.bit_length())
                       for x in a.c) <= 64:
        return a
    return outward(a,bits=ROUND_BITS)


def add(a, b):
    return [rounded(x.add(y)) for x, y in zip(a, b)]


def scale(q, a):
    return [rounded(exact(*q).mul(x)) for x in a]


def sum_disks(values):
    result = ZERO
    for value in values:
        result = result.add(value)
    return result


def mul(a, b):
    return [rounded(sum_disks(a[i].mul(b[n-i]) for i in range(n+1)))
            for n in range(len(a))]


def inverse(a):
    assert a[0].r == 0
    x, y = a[0].c
    denominator = x*x + y*y
    result = [exact(x/denominator, -y/denominator)]
    for n in range(len(a)-1):
        result.append(rounded(exact(-1).mul(result[0].mul(
            sum_disks(a[i+1].mul(result[n-i]) for i in range(n+1))))))
    return result


def exponential(a, constant):
    result = [constant]
    for n in range(len(a)-1):
        result.append(rounded(exact(Q(1, n+1)).mul(sum_disks(
            exact(i+1).mul(a[i+1].mul(result[n-i])) for i in range(n+1)))))
    return result


def log_constant(n):
    value = Q(round(math.log(math.pi if n == 'pi' else n)*10**15), 10**15)
    return Disk((value, Q(0)), Q(1 if n == 2 else (8 if n != 'pi' and n > 21 else 6), 10**15))


def logarithm(a, inv):
    assert not a[0].r
    w = a[0].c
    z = (w[0]/16-1, w[1]/16)
    assert z[0]**2 + z[1]**2 <= Q(1, 4)
    table = {48: ZERO}
    for k in reversed(range(48)):
        coef = Q((-1)**(k+1), k) if k else Q(0)
        table[k] = rounded(exact(coef).add(exact(*z).mul(table[k+1])))
    raw = exact(4).mul(log_constant(2)).add(Disk(table[0].c, table[0].r+Q(1, 10**15)))
    constant = rounded(raw)
    result = [constant]
    for n in range(len(a)-1):
        result.append(rounded(exact(Q(1, n+1)).mul(sum_disks(
            exact(i+1).mul(a[i+1].mul(inv[n-i])) for i in range(n+1)))))
    return result, {'input': z, 'table': table, 'raw': raw, 'constant': constant}


@dataclass
class Node:
    name: str
    op: str
    inputs: tuple = ()
    q: tuple = (Q(0), Q(0))
    n: object = None


class Graph:
    def __init__(self):
        self.nodes = []
        self.by_name = {}
        self.constants = {}
        self.logs = {}

    def node(self, name, op, *inputs, q=(Q(0), Q(0)), n=None):
        assert name not in self.by_name, name
        node = Node(name, op, tuple(x.name for x in inputs), q, n)
        self.nodes.append(node)
        self.by_name[name] = node
        return node

    def const(self, re, im=0):
        q = (Q(re), Q(im))
        if q not in self.constants:
            self.constants[q] = self.node('q'+str(len(self.constants)), 'const', q=q)
        return self.constants[q]

    def log(self, n):
        if n not in self.logs:
            self.logs[n] = self.node('log'+str(n), 'logconst', n=n)
        return self.logs[n]

    def plus(self, name, a, b):
        return self.node(name, 'add', a, b)

    def times(self, name, a, b):
        return self.node(name, 'mul', a, b)

    def scaled(self, name, q, a):
        return self.node(name, 'scale', a, q=(Q(q), Q(0)))

    def reachable(self, name, stop=()):
        seen = []
        def visit(n):
            if n in stop or n in seen:
                return
            seen.append(n)
            for child in self.by_name[n].inputs:
                visit(child)
        visit(name)
        return seen


def build_graph():
    g = Graph()
    v = g.node('variable', 'var')
    half = g.scaled('halfVariable', Q(1, 2), v)
    base = g.plus('base', g.const(1), half)
    w = g.plus('shift', base, g.const(12))
    iw = g.node('shiftInv', 'inv', w)
    lw = g.node('shiftLog', 'log', w, iw)
    lead = g.times('mainLead', g.plus('shiftMinusHalf', w, g.const(Q(-1, 2))), lw)
    lead = g.plus('mainMinusShift', lead, g.scaled('negativeShift', -1, w))
    logs = g.plus('logTwoPi', g.log(2), g.log('pi'))
    lead = g.plus('mainConstant', lead, g.scaled('halfLogTwoPi', Q(1, 2), logs))
    power = iw
    powers = {1: power}
    for k in range(2, 12):
        power = g.times('invPower'+str(k), power, iw)
        powers[k] = power
    corrections = (Q(1, 12), Q(-1, 360), Q(1, 1260), Q(-1, 1680), Q(1, 1188), Q(-691, 360360))
    for j, q in enumerate(corrections, 1):
        lead = g.plus('mainCorr'+str(j), lead,
                      g.scaled('mainTerm'+str(j), q, powers[2*j-1]))
    g.gamma_main = lead
    expmain = g.node('gammaExp', 'exp', lead)
    denominator = None
    for j in range(12):
        factor = base if j == 0 else g.plus('gammaFactor'+str(j), base, g.const(j))
        inv = g.node('gammaInverse'+str(j), 'inv', factor)
        denominator = inv if denominator is None else g.times('gammaProduct'+str(j), denominator, inv)
    g.gamma_denominator = denominator
    g.gamma_finite = g.times('gammaFinite', expmain, denominator)
    g.gamma_actual = g.node('gammaActual', 'gamma_actual', g.gamma_finite)

    terms = {1: g.const(1)}
    for n in range(2, 28):
        argument = g.times('arg'+str(n), g.scaled('negLog'+str(n), -1, g.log(n)), v)
        terms[n] = g.node('term'+str(n), 'exp', argument)
    g.zeta_terms = terms
    initial = terms[1]
    for n in range(2, 27):
        initial = g.plus('initial'+str(n), initial, terms[n])
    part = g.plus('initialHalf', initial, g.scaled('endpointHalf', Q(1, 2), terms[27]))
    rising = {1: v}
    for n in range(2, 12):
        rising[n] = g.times('rising'+str(n), rising[n-1],
                            g.plus('risingFactor'+str(n-1), v, g.const(n-1)))
    g.zeta_rising = rising
    for k, q in enumerate(BERNOULLI_CORRECTIONS, 1):
        correction = g.scaled('zetaCorr'+str(k), q/27**(2*k-1),
                              g.times('zetaCorrProduct'+str(k), rising[2*k-1], terms[27]))
        part = g.plus('zetaPart'+str(k), part, correction)
    minusone = g.plus('sminusone', v, g.const(-1))
    g.zeta_finite = g.plus('zetaFinite', g.times('zetaRegularPart', minusone, part),
                           g.scaled('zetaIntegral', 27, terms[27]))
    g.zeta_actual = g.node('zetaActual', 'zeta_actual', g.zeta_finite)
    parg = g.times('piArg', g.scaled('negativeHalfLogPi', Q(-1, 2), g.log('pi')), v)
    g.pi = g.node('piPower', 'exp', parg)
    g.xi = g.times('xiProduct', g.times('piGamma', g.pi, g.gamma_actual), g.zeta_actual)
    return g


def evaluate(g, centre, degree, bits=50):
    global ROUND_BITS
    ROUND_BITS=bits
    data, extras = {}, {}
    for node in g.nodes:
        args = [data[n] for n in node.inputs]
        if node.op == 'const':
            jet = [exact(*node.q)] + [ZERO]*degree
        elif node.op == 'var':
            jet = [exact(*centre), exact(1)] + [ZERO]*(degree-1)
        elif node.op == 'logconst':
            jet = [log_constant(node.n)] + [ZERO]*degree
        elif node.op == 'add':
            jet = add(*args)
        elif node.op == 'scale':
            jet = scale(node.q, args[0])
        elif node.op == 'mul':
            jet = mul(*args)
        elif node.op == 'inv':
            jet = inverse(args[0])
        elif node.op == 'exp':
            turns, poly, squares = certificate(args[0][0])
            extras[node.name] = {'turns': turns, 'poly': poly, 'squares': squares}
            jet = exponential(args[0], squares[6])
        elif node.op == 'log':
            jet, extras[node.name] = logarithm(*args)
        elif node.op in ('gamma_actual', 'zeta_actual'):
            error = GAMMA_ERROR if node.op == 'gamma_actual' else ZETA_ERROR
            jet = [rounded(Disk(a.c, a.r+error)) for a in args[0]]
        else:
            raise ValueError(node.op)
        data[node.name] = jet
    return data, extras
