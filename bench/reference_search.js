// Exhaustive Schur search in Node.js (fast enough for r=4, N<=45).
// Colors are used in first-occurrence order (symmetry breaking).
// Usage: node schur_search.js r Nmax [timeLimitSeconds]

const r = parseInt(process.argv[2] || '4', 10);
const Nmax = parseInt(process.argv[3] || '45', 10);
const timeLimit = parseFloat(process.argv[4] || '600') * 1000;
const t0 = Date.now();

function searchN(r, N) {
  const color = new Int8Array(N + 2);
  let nodes = 0;
  let count = 0;
  let firstSolution = null;

  function feasible(k, col) {
    if ((k & 1) === 0 && color[k >> 1] === col) return false;
    const half = k >> 1;
    for (let a = 1; a <= half; a++) {
      const b = k - a;
      if (b <= a) break;
      if (color[a] === col && color[b] === col) return false;
    }
    return true;
  }

  function dfs(k, used) {
    nodes++;
    if (k > N) {
      count++;
      if (firstSolution === null) firstSolution = Array.from(color.slice(1, N + 1));
      return;
    }
    const top = Math.min(used + 1, r - 1);
    for (let col = 0; col <= top; col++) {
      if (feasible(k, col)) {
        color[k] = col;
        dfs(k + 1, used > col ? used : col);
      }
    }
    color[k] = 0;
  }

  color[1] = 0;
  dfs(2, 0);
  return { nodes, count, firstSolution };
}

for (let N = 1; N <= Nmax; N++) {
  const t = Date.now();
  const { nodes, count, firstSolution } = searchN(r, N);
  const el = ((Date.now() - t) / 1000).toFixed(2);
  console.log(`r=${r} N=${N}: nodes=${nodes} validColorings=${count} time=${el}s`);
  if (count === 0) {
    console.log(`=> S(${r}) = ${N - 1}  (no valid ${r}-coloring of [1,${N}])`);
    if (firstSolution) console.log('   example of the extremal coloring:', firstSolution.join(' '));
    process.exit(0);
  }
  if (N === Nmax) {
    console.log(`example coloring of [1,${N}]:`, firstSolution.join(' '));
  }
  if (Date.now() - t0 > timeLimit) {
    console.log('time limit reached');
    process.exit(0);
  }
}
