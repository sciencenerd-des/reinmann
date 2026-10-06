"use strict";

declare function require(name: string): any;
declare const __dirname: string;
declare const process: { argv: string[]; version: string };

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");

type Interval = Readonly<{ lo: bigint; hi: bigint }>;
type Counts = { positive: number; negative: number; zero: number; inconclusive: number };

const root = path.resolve(__dirname, "../..");
const coefficientPath = path.join(root, "research/figures/coeffs_M120.txt");

type TokenParts = Readonly<{ sign: string; digits: string; unitExponent: number }>;

function tokenParts(token: string): TokenParts {
  const match = token.trim().match(/^([+-]?)(\d+)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/);
  if (!match) throw new Error(`invalid decimal token: ${token}`);
  const [, sign, whole, fraction = "", exponent = "0"] = match;
  return { sign, digits: `${whole}${fraction}`, unitExponent: Number(exponent) - fraction.length };
}

function parseScaled(token: string, places: number): bigint {
  const parts = tokenParts(token);
  const shift = parts.unitExponent + places;
  if (shift < 0) throw new Error("common scale is too small");
  const sign = parts.sign === "-" ? -1n : 1n;
  return sign * BigInt(parts.digits || "0") * 10n ** BigInt(shift);
}

function loadIntervals(raw: string): { values: Interval[]; places: number } {
  const tokens = raw.trim().split(/\r?\n/).slice(1);
  const places = Math.max(...tokens.map((token) => -tokenParts(token).unitExponent));
  const values = tokens.map((token): Interval => {
    const parts = tokenParts(token);
    const midpoint = parseScaled(token, places);
    const halfUlpNumerator = 10n ** BigInt(places + parts.unitExponent);
    return { lo: 2n * midpoint - halfUlpNumerator, hi: 2n * midpoint + halfUlpNumerator };
  });
  return { values, places };
}

function validateScientificParser(): void {
  if (parseScaled("1.230e-4", 7) !== 1230n) {
    throw new Error("scientific-notation parser self-test failed");
  }
}

function point(value: bigint): Interval {
  return { lo: value, hi: value };
}

function add(left: Interval, right: Interval): Interval {
  return { lo: left.lo + right.lo, hi: left.hi + right.hi };
}

function negate(value: Interval): Interval {
  return { lo: -value.hi, hi: -value.lo };
}

function multiply(left: Interval, right: Interval): Interval {
  const products = [
    left.lo * right.lo,
    left.lo * right.hi,
    left.hi * right.lo,
    left.hi * right.hi,
  ];
  return {
    lo: products.reduce((best, value) => (value < best ? value : best)),
    hi: products.reduce((best, value) => (value > best ? value : best)),
  };
}

function signedMoment(values: Interval[], index: number): Interval {
  return index % 2 === 0 ? values[index] : negate(values[index]);
}

function entry(values: Interval[], row: number, column: number): Interval {
  return column > row ? point(0n) : signedMoment(values, row - column);
}

function permutations(size: number): number[][] {
  const result: number[][] = [];
  const visit = (prefix: number[], remaining: number[]): void => {
    if (remaining.length === 0) {
      result.push(prefix);
      return;
    }
    remaining.forEach((value, index) => {
      visit([...prefix, value], [...remaining.slice(0, index), ...remaining.slice(index + 1)]);
    });
  };
  visit([], Array.from({ length: size }, (_, index) => index));
  return result;
}

function permutationSign(permutation: number[]): number {
  let inversions = 0;
  for (let left = 0; left < permutation.length; left += 1) {
    for (let right = left + 1; right < permutation.length; right += 1) {
      if (permutation[left] > permutation[right]) inversions += 1;
    }
  }
  return inversions % 2 === 0 ? 1 : -1;
}

function determinant(values: Interval[], rows: number[]): Interval {
  let result = point(0n);
  for (const permutation of permutations(rows.length)) {
    let term = point(1n);
    permutation.forEach((column, rowIndex) => {
      term = multiply(term, entry(values, rows[rowIndex], column));
    });
    result = add(result, permutationSign(permutation) > 0 ? term : negate(term));
  }
  return result;
}

function* combinations(
  maxInclusive: number,
  size: number,
  prefix: number[] = [],
  start = 0,
): Generator<number[]> {
  if (prefix.length === size) {
    yield prefix;
    return;
  }
  const remaining = size - prefix.length;
  for (let value = start; value <= maxInclusive - remaining + 1; value += 1) {
    yield* combinations(maxInclusive, size, [...prefix, value], value + 1);
  }
}

function signCode(interval: Interval): "+" | "-" | "0" | "?" {
  if (interval.lo > 0n) return "+";
  if (interval.hi < 0n) return "-";
  if (interval.lo === 0n && interval.hi === 0n) return "0";
  return "?";
}

function scan(values: Interval[], order: number, maxRow: number): object {
  const counts: Counts = { positive: 0, negative: 0, zero: 0, inconclusive: 0 };
  const names = { "+": "positive", "-": "negative", "0": "zero", "?": "inconclusive" } as const;
  const digest = crypto.createHash("sha256");
  for (const rows of combinations(maxRow, order)) {
    const code = signCode(determinant(values, rows));
    counts[names[code]] += 1;
    digest.update(`${rows.join(",")}:${code}\n`);
  }
  return {
    order,
    total: counts.positive + counts.negative + counts.zero + counts.inconclusive,
    counts,
    sign_stream_sha256: digest.digest("hex"),
  };
}

function controlSign(values: number[]): number {
  const intervals = values.map((value) => point(BigInt(value)));
  const code = signCode(determinant(intervals, [2, 3, 4]));
  return code === "+" ? 1 : code === "-" ? -1 : 0;
}

function main(): void {
  validateScientificParser();
  const maxRow = Number(process.argv[2] || "30");
  const output = process.argv[3];
  if (!output) throw new Error("usage: node typescript_interval.ts MAX_ROW OUTPUT");
  const rawBuffer = fs.readFileSync(coefficientPath);
  const { values, places } = loadIntervals(rawBuffer.toString("utf8"));
  if (maxRow >= values.length) throw new Error("max row exceeds coefficient cache");
  const payload = {
    implementation: "typescript-bigint-interval-leibniz",
    runtime: process.version,
    input: path.relative(root, coefficientPath),
    input_sha256: crypto.createHash("sha256").update(rawBuffer).digest("hex"),
    max_row: maxRow,
    common_denominator: `2*10^${places}`,
    uncertainty: "half-unit in each token's last displayed decimal place",
    controls: {
      positive: controlSign([1, 2, 5, 13, 33]),
      zero: controlSign([1, 2, 4, 8, 16]),
      negative: controlSign([1, 1, 2, 6, 24]),
    },
    orders: [scan(values, 3, maxRow), scan(values, 4, maxRow)],
  };
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, `${JSON.stringify(payload, null, 2)}\n`);
  console.log(JSON.stringify(payload, null, 2));
}

main();
