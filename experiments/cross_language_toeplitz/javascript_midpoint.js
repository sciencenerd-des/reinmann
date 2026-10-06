"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");

const root = path.resolve(__dirname, "../..");
const coefficientPath = path.join(root, "research/figures/coeffs_M120.txt");

function tokenParts(token) {
  const match = token.trim().match(/^([+-]?)(\d+)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/);
  if (!match) throw new Error(`invalid decimal token: ${token}`);
  const [, sign, whole, fraction = "", exponent = "0"] = match;
  return { sign, digits: `${whole}${fraction}`, unitExponent: Number(exponent) - fraction.length };
}

function parseScaled(token, places) {
  const parts = tokenParts(token);
  const shift = parts.unitExponent + places;
  if (shift < 0) throw new Error("common scale is too small");
  const sign = parts.sign === "-" ? -1n : 1n;
  return sign * BigInt(parts.digits || "0") * 10n ** BigInt(shift);
}

function loadMidpoints(raw) {
  const tokens = raw.trim().split(/\r?\n/).slice(1);
  const places = Math.max(...tokens.map((token) => -tokenParts(token).unitExponent));
  return {
    values: tokens.map((token) => parseScaled(token, places)),
    places,
  };
}

function validateScientificParser() {
  if (parseScaled("1.230e-4", 7) !== 1230n) {
    throw new Error("scientific-notation parser self-test failed");
  }
}

function signedMoment(values, index) {
  return index % 2 === 0 ? values[index] : -values[index];
}

function matrixForRows(values, rows) {
  return rows.map((row) =>
    rows.map((_, column) => (column > row ? 0n : signedMoment(values, row - column))),
  );
}

function bareissDeterminant(input) {
  const matrix = input.map((row) => row.slice());
  const size = matrix.length;
  if (size === 0) return 1n;
  let sign = 1n;
  let previousPivot = 1n;
  for (let pivotIndex = 0; pivotIndex < size - 1; pivotIndex += 1) {
    if (matrix[pivotIndex][pivotIndex] === 0n) {
      const swapIndex = matrix.findIndex(
        (row, index) => index > pivotIndex && row[pivotIndex] !== 0n,
      );
      if (swapIndex < 0) return 0n;
      [matrix[pivotIndex], matrix[swapIndex]] = [matrix[swapIndex], matrix[pivotIndex]];
      sign = -sign;
    }
    const pivot = matrix[pivotIndex][pivotIndex];
    for (let row = pivotIndex + 1; row < size; row += 1) {
      for (let column = pivotIndex + 1; column < size; column += 1) {
        const numerator =
          matrix[row][column] * pivot - matrix[row][pivotIndex] * matrix[pivotIndex][column];
        if (numerator % previousPivot !== 0n) {
          throw new Error("Bareiss division was not exact");
        }
        matrix[row][column] = numerator / previousPivot;
      }
    }
    previousPivot = pivot;
  }
  return sign * matrix[size - 1][size - 1];
}

function* combinations(maxInclusive, size, prefix = [], start = 0) {
  if (prefix.length === size) {
    yield prefix;
    return;
  }
  const remaining = size - prefix.length;
  for (let value = start; value <= maxInclusive - remaining + 1; value += 1) {
    yield* combinations(maxInclusive, size, [...prefix, value], value + 1);
  }
}

function signCode(value) {
  return value > 0n ? "+" : value < 0n ? "-" : "0";
}

function scan(values, order, maxRow) {
  const counts = { positive: 0, negative: 0, zero: 0 };
  const digest = crypto.createHash("sha256");
  const names = { "+": "positive", "-": "negative", "0": "zero" };
  for (const rows of combinations(maxRow, order)) {
    const code = signCode(bareissDeterminant(matrixForRows(values, rows)));
    counts[names[code]] += 1;
    digest.update(`${rows.join(",")}:${code}\n`);
  }
  return {
    order,
    total: counts.positive + counts.negative + counts.zero,
    counts,
    sign_stream_sha256: digest.digest("hex"),
  };
}

function controlSign(values) {
  const code = signCode(bareissDeterminant(matrixForRows(values.map(BigInt), [2, 3, 4])));
  return code === "+" ? 1 : code === "-" ? -1 : 0;
}

function main() {
  validateScientificParser();
  const maxRow = Number(process.argv[2] || "30");
  const output = process.argv[3];
  if (!output) throw new Error("usage: node javascript_midpoint.js MAX_ROW OUTPUT");
  const rawBuffer = fs.readFileSync(coefficientPath);
  const { values, places } = loadMidpoints(rawBuffer.toString("utf8"));
  if (maxRow >= values.length) throw new Error("max row exceeds coefficient cache");
  const payload = {
    implementation: "javascript-bigint-midpoint-bareiss",
    runtime: process.version,
    input: path.relative(root, coefficientPath),
    input_sha256: crypto.createHash("sha256").update(rawBuffer).digest("hex"),
    max_row: maxRow,
    common_decimal_places: places,
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
