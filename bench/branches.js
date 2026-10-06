// Node counts of the three verified branches of the Lean proof: the subtrees of
//   searchB 42 ([0,1] ++ [c])   for c = 0, 1, 2
// where the state [0,1] is coloured 0,1 and rule B is in force.
// Usage: node branches.js [N]
const N = parseInt(process.argv[2] || '45', 10);

function subtree(prefix) {
  const color = new Int8Array(N + 2);
  for (let i = 0; i < prefix.length; i++) color[i + 1] = prefix[i];
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
  function dfs(k) {
    nodes++;
    if (k > N) return;
    for (let col = 0; col < 4; col++) {
      if (col === 3 && !seen2(k)) continue;
      if (!feasible(k, col)) continue;
      color[k] = col;
      dfs(k + 1);
      color[k] = 0;
    }
  }
  dfs(prefix.length + 1);
  return nodes;
}

const out = {};
let total = 0;
for (const c of [0, 1, 2]) {
  const t = Date.now();
  const n = subtree([0, 1, c]);
  out['branch' + c] = n;
  out['seconds' + c] = Number(((Date.now() - t) / 1000).toFixed(2));
  total += n;
}
out.totalBranches = total;
out.rootState = 1;
console.log(JSON.stringify(out, null, 1));
