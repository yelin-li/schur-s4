// Experiment documented in docs/OPTIMIZATION.md:
// the rule "every 14 consecutive integers must use all 4 colours" is NOT a
// valid consequence of S(3) = 13.  This script searches for good 4-colourings
// that violate it, i.e. that contain 14 consecutive positions using <= 3
// colours.  If one is found, the rule is unsound and cannot be used to prune.
//
// Usage: node window_check.js [N] [window]
const N = parseInt(process.argv[2] || '44', 10);
const W = parseInt(process.argv[3] || '14', 10);

let found = 0;
const color = new Int8Array(N + 2);

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

function badWindow() {
  // window [k-W+1, k], needs k >= W; also the window must be inside [1, N]
  for (let k = W; k <= N; k++) {
    let m = 0;
    for (let i = k - W + 1; i <= k; i++) m |= 1 << color[i];
    const bits = m.toString(2).split('').filter((c) => c === '1').length;
    if (bits < 4) return [k - W + 1, k, bits];
  }
  return null;
}

function dfs(k, used) {
  if (k > N) {
    if (k - 1 >= W) {
      const bad = badWindow();
      if (bad) {
        found++;
        if (found <= 3) {
          console.log(`good 4-colouring of [1,${N}] violating the window rule: ` +
            `window [${bad[0]},${bad[1]}] uses only ${bad[2]} colours`);
          console.log('   colouring: ' + Array.from(color.slice(1, N + 1)).join(' '));
        }
      }
    }
    return;
  }
  const top = Math.min(used + 1, 3); // first-occurrence canonical labelling
  for (let col = 0; col <= top; col++) {
    if (!feasible(k, col)) continue;
    color[k] = col;
    dfs(k + 1, used > col ? used : col);
    color[k] = 0;
  }
}

dfs(1, 0);
console.log(`\n${found} of the good 4-colourings of [1,${N}] violate the window rule ` +
  `(searched with first-occurrence canonical labelling)`);
