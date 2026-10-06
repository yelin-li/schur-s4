// Collects the search-tree statistics quoted in the documentation.
//
//   node  "initial state" convention identical to the Lean function:
//   a state is counted when the search is entered, children that fail the
//   incremental feasibility check are not entered.
//
//   mode 'none' : no symmetry breaking
//   mode 'c1'   : c(1) = 0                         (4-fold)
//   mode 'A'    : c(1) = 0, c(2) = 1               (12-fold)
//   mode 'AB'   : 'A' plus rule B: colour 3 only after colour 2   (24-fold)
//
// Usage: node measure.js <mode> [N] [--profile] [--branches]
const mode = process.argv[2] || 'AB';
const N = parseInt(process.argv[3] || '45', 10);
const wantProfile = process.argv.includes('--profile');
const wantBranches = process.argv.includes('--branches');

function run(mode, N) {
  const color = new Int8Array(N + 2);
  const perDepth = new Array(N + 2).fill(0);
  let nodes = 0;

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

  function seen2(k) {
    for (let i = 1; i < k; i++) if (color[i] === 2) return true;
    return false;
  }

  function firstAllowed(k) { return mode === 'none' ? 0 : 0; }

  function dfs(k) {
    nodes++;
    perDepth[k]++;
    if (k > N) return;
    for (let col = 0; col < 4; col++) {
      if (mode !== 'none') {
        if (k === 1 && col !== 0) continue;                 // c(1) = 0
        if ((mode === 'A' || mode === 'AB') && k === 2 && col !== 1) continue;  // c(2) = 1
      }
      if (mode === 'AB' && col === 3 && !seen2(k)) continue; // rule B
      if (!feasible(k, col)) continue;
      color[k] = col;
      dfs(k + 1);
      color[k] = 0;
    }
  }
  dfs(1);
  return { nodes, perDepth };
}

const t0 = Date.now();
const { nodes, perDepth } = run(mode, N);
const seconds = (Date.now() - t0) / 1000;

const out = { mode, N, nodes, seconds: Number(seconds.toFixed(2)) };
if (wantProfile) out.perDepth = perDepth.slice(1, N + 1);
const json = JSON.stringify(out);
const outFile = process.argv.find((a) => a.startsWith('--out='));
if (outFile) {
  require('fs').writeFileSync(outFile.slice('--out='.length), json + '\n');
}
console.log(json);
