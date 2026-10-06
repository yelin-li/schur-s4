#!/usr/bin/env node
'use strict';
/*
 * CDCL SAT solver written from scratch, emitting RUP certificates.
 *
 * A JavaScript port of `cdcl45.py`: same propagation, same 1UIP analysis, same
 * hint generation (conflict-analysis chain, validated by a local copy of the
 * checker semantics), same certificate format, so `verify_rup.py`,
 * `trim_proof.py`, `expand_resolution.py` and `gen_lean_cert.py` consume its
 * output unchanged.
 *
 * It exists because the Python version cannot refute the `S(4)` instance in the
 * available time.  Clauses live in flat typed arrays (a few bytes per literal
 * plus two ints per clause) so that multi-million-conflict runs fit in memory;
 * the occurrence lists used by the slow hint fallback are built lazily.
 *
 * Usage:
 *   node cdcl45.js --problem s4 --sym --order positional --out proof45.rup \
 *        --budget 200000000 --stats
 */

const fs = require('fs');

const N = 45;
const COLORS = 4;

function dedupe(clauses) {
  const out = [];
  for (const cl of clauses) {
    const seen = new Set();
    const nw = [];
    for (const l of cl) if (!seen.has(l)) { seen.add(l); nw.push(l); }
    out.push(nw);
  }
  return out;
}

/** CNF for "a k-colouring of {1..n} with no monochromatic a + b = c".
 *  Clause order mirrors `build_cnf` in cdcl45.py exactly (all ALO, then all
 *  AMO, then the triples, then the symmetry units): the certificate indices
 *  must refer to the same database in both implementations. */
function buildCnf(n, k, symmetryBreak) {
  const v = (i, c) => (i - 1) * k + c + 1;
  const clauses = [];
  for (let i = 1; i <= n; i++) {
    const alo = [];
    for (let c = 0; c < k; c++) alo.push(v(i, c));
    clauses.push(alo);
  }
  for (let i = 1; i <= n; i++) {
    for (let c = 0; c < k; c++) {
      for (let d = c + 1; d < k; d++) clauses.push([-v(i, c), -v(i, d)]);
    }
  }
  for (let a = 1; a < n; a++) {
    for (let b = a; b <= n - a; b++) {
      const s = a + b;
      for (let c = 0; c < k; c++) clauses.push([-v(a, c), -v(b, c), -v(s, c)]);
    }
  }
  if (symmetryBreak) {
    // x(1,0) and x(2,1): sound by `Schur.exists_good_first_two`
    clauses.push([v(1, 0)]);
    clauses.push([v(2, 1)]);
  }
  return dedupe(clauses);
}

/** CNF for the S(3) instance: 3-colouring of {1, ..., 14} (S(3) = 13). */
function buildCnfS3() {
  const n = 14, k = 3;
  const v = (i, c) => (i - 1) * k + c + 1;
  const clauses = [];
  for (let i = 1; i <= n; i++) {
    const alo = [];
    for (let c = 0; c < k; c++) alo.push(v(i, c));
    clauses.push(alo);
    for (let c = 0; c < k; c++) {
      for (let d = c + 1; d < k; d++) clauses.push([-v(i, c), -v(i, d)]);
    }
  }
  for (let a = 1; a < n; a++) {
    for (let b = a; b <= n - a; b++) {
      const s = a + b;
      for (let c = 0; c < k; c++) clauses.push([-v(a, c), -v(b, c), -v(s, c)]);
    }
  }
  return dedupe(clauses);
}

class Solver {
  constructor(clauses, nvars, opts) {
    opts = opts || {};
    this.nvars = nvars;
    this.colors = opts.colors || 4;
    this.npos = Math.ceil(this.nvars / this.colors);
    this.order = opts.order || 'positional';
    this.diag = opts.diag || false;

    // ---- flat clause store ------------------------------------------------
    let nLit = 0;
    for (const cl of clauses) nLit += cl.length;
    this.cdata = new Int32Array(Math.max(1024, nLit * 2));
    this.coff = new Int32Array(Math.max(1024, clauses.length * 2));
    this.clen = new Int32Array(Math.max(1024, clauses.length * 2));
    this.nclauses = 0;
    this.dataTop = 0;

    this.value = new Int32Array(nvars + 1);
    this.level = new Int32Array(nvars + 1);
    this.reason = new Int32Array(nvars + 1).fill(-1);
    this.phase = new Int32Array(nvars + 1).fill(1);
    this.activity = new Float64Array(nvars + 1);
    this.varInc = 1.0;

    this.trail = new Int32Array(nvars + 1);
    this.trailSize = 0;
    this.trailLim = new Int32Array(nvars + 2);
    this.limSize = 0;
    this.qhead = 0;

    this.watches = new Array(2 * nvars + 2);
    for (let i = 0; i < this.watches.length; i++) this.watches[i] = [];

    this.deleted = new Uint8Array(4096);
    this.units = [];                    // indices of unit clauses
    this.occ = null;                    // built lazily, only for the fallback

    this.stats = {
      conflicts: 0, decisions: 0, propagations: 0, restarts: 0,
      learned: 0, deleted: 0, fastHints: 0, fallbackHints: 0, dropped: 0,
    };
    // coarse timing of the three phases, printed with the progress line
    this.tProp = 0; this.tAnalyze = 0; this.tHints = 0;

    this.rval = new Int32Array(nvars + 1);
    this.rtouched = new Int32Array(nvars + 1);
    this.seenStamp = new Int32Array(nvars + 1);
    this.stamp = 0;
    this.conflict = -1;
    this.out = null;

    for (const cl of clauses) this.addClause(cl, true);
    this.baseLen = this.nclauses;
    for (let ci = 0; ci < this.baseLen; ci++) {
      if (this.clen[ci] === 1) this.units.push(ci);
    }
  }

  // ---- clause store -------------------------------------------------------
  addClause(lits, install) {
    const ci = this.nclauses;
    if (ci >= this.coff.length) {
      const bigger = new Int32Array(this.coff.length * 2);
      bigger.set(this.coff); this.coff = bigger;
      const bigger2 = new Int32Array(this.clen.length * 2);
      bigger2.set(this.clen); this.clen = bigger2;
      const del = new Uint8Array(this.deleted.length * 2);
      del.set(this.deleted); this.deleted = del;
    }
    if (this.dataTop + lits.length > this.cdata.length) {
      let cap = this.cdata.length;
      while (cap < this.dataTop + lits.length) cap *= 2;
      const bigger = new Int32Array(cap);
      bigger.set(this.cdata.subarray(0, this.dataTop));
      this.cdata = bigger;
    }
    this.coff[ci] = this.dataTop;
    this.clen[ci] = lits.length;
    for (let j = 0; j < lits.length; j++) this.cdata[this.dataTop++] = lits[j];
    this.nclauses++;
    if (install === true) {
      if (lits.length === 1) this.enqueue(lits[0], ci);
      else {
        this.watches[this.widx(lits[0])].push(ci);
        this.watches[this.widx(lits[1])].push(ci);
      }
    }
    return ci;
  }

  cLit(ci, j) { return this.cdata[this.coff[ci] + j]; }
  cLen(ci) { return this.clen[ci]; }
  setLit(ci, j, v) { this.cdata[this.coff[ci] + j] = v; }

  widx(lit) { return 2 * Math.abs(lit) + (lit > 0 ? 0 : 1); }

  enqueue(lit, reason) {
    const v = lit > 0 ? lit : -lit;
    this.value[v] = lit > 0 ? 1 : -1;
    this.level[v] = this.limSize;
    this.reason[v] = reason;
    this.trail[this.trailSize++] = lit;
  }

  litValue(lit) {
    const v = this.value[lit > 0 ? lit : -lit];
    if (v === 0) return 0;
    return lit > 0 ? v : -v;
  }

  propagate() {
    const cdata = this.cdata;
    while (this.qhead < this.trailSize) {
      const p = this.trail[this.qhead++];
      this.stats.propagations++;
      const ws = this.watches[this.widx(-p)];
      let i = 0;
      while (i < ws.length) {
        const ci = ws[i];
        if (this.deleted[ci]) { ws[i] = ws[ws.length - 1]; ws.pop(); continue; }
        const off = this.coff[ci];
        if (cdata[off] === -p) { cdata[off] = cdata[off + 1]; cdata[off + 1] = -p; }
        if (cdata[off + 1] !== -p) { i++; continue; }
        const first = cdata[off];
        if (this.litValue(first) === 1) { i++; continue; }
        let replaced = false;
        const len = this.clen[ci];
        for (let k = 2; k < len; k++) {
          if (this.litValue(cdata[off + k]) !== -1) {
            const t = cdata[off + 1]; cdata[off + 1] = cdata[off + k]; cdata[off + k] = t;
            ws[i] = ws[ws.length - 1]; ws.pop();
            this.watches[this.widx(cdata[off + 1])].push(ci);
            replaced = true;
            break;
          }
        }
        if (replaced) continue;
        if (this.litValue(first) === -1) {
          this.qhead = this.trailSize;
          return ci;
        }
        this.enqueue(first, ci);
        i++;
      }
    }
    return -1;
  }

  bump(v) {
    this.activity[v] += this.varInc;
    if (this.activity[v] > 1e100) {
      for (let i = 1; i <= this.nvars; i++) this.activity[i] *= 1e-100;
      this.varInc *= 1e-100;
    }
  }

  analyze(conflict) {
    const curLevel = this.limSize;
    this.stamp++;
    const learned = [0];
    let counter = 0;
    let cur = conflict;
    let p = 0;
    let idx = this.trailSize - 1;
    const chain = [];
    for (;;) {
      const off = this.coff[cur], len = this.clen[cur];
      for (let j = 0; j < len; j++) {
        const q = this.cdata[off + j];
        if (q === p) continue;
        const v = q > 0 ? q : -q;
        if (this.seenStamp[v] !== this.stamp && this.level[v] > 0) {
          this.seenStamp[v] = this.stamp;
          this.bump(v);
          if (this.level[v] === curLevel) counter++;
          else learned.push(q);
        }
      }
      while (idx >= 0 &&
             !(this.seenStamp[Math.abs(this.trail[idx])] === this.stamp &&
               this.level[Math.abs(this.trail[idx])] === curLevel)) idx--;
      if (idx < 0) throw new Error('conflict analysis ran off the trail');
      p = this.trail[idx--];
      this.seenStamp[p > 0 ? p : -p] = 0;
      counter--;
      if (counter === 0) break;
      cur = this.reason[p > 0 ? p : -p];
      if (cur < 0) throw new Error('pivot literal has no reason');
      chain.push(cur);
    }
    learned[0] = -p;
    const out = [learned[0]];
    for (let j = 1; j < learned.length; j++) {
      const l = learned[j];
      let dup = false;
      for (let t = 0; t < out.length; t++) {
        if (Math.abs(out[t]) === Math.abs(l)) { dup = true; break; }
      }
      if (!dup) out.push(l);
    }
    let back = 0;
    for (let j = 1; j < out.length; j++) {
      const lv = this.level[Math.abs(out[j])];
      if (lv > back) back = lv;
    }
    return { learned: Int32Array.from(out), back, chain };
  }

  /** Local copy of the checker semantics: unit clauses seed, then hints. */
  replay(clause, hints) {
    const val = this.rval, touched = this.rtouched;
    let nt = 0;
    const reset = () => { for (let i = 0; i < nt; i++) val[touched[i]] = 0; };
    for (let k = 0; k < this.units.length; k++) {
      const l = this.cdata[this.coff[this.units[k]]];
      const v = l > 0 ? l : -l, w = l > 0 ? 1 : -1;
      if (val[v] !== 0) { if (val[v] !== w) { reset(); return true; } continue; }
      val[v] = w; touched[nt++] = v;
    }
    for (let j = 0; j < clause.length; j++) {
      const l = clause[j];
      const v = l > 0 ? l : -l, w = l > 0 ? -1 : 1;
      if (val[v] !== 0) { if (val[v] !== w) { reset(); return true; } continue; }
      val[v] = w; touched[nt++] = v;
    }
    for (let h = 0; h < hints.length; h++) {
      const off = this.coff[hints[h]], len = this.clen[hints[h]];
      let un = 0, unit = 0, sat = false;
      for (let j = 0; j < len; j++) {
        const l = this.cdata[off + j];
        const a = val[l > 0 ? l : -l];
        if (a === 0) {
          un++; unit = l;
          if (un > 1) break;
        } else if (a === (l > 0 ? 1 : -1)) { sat = true; break; }
      }
      if (sat || un > 1) { reset(); return false; }
      if (un === 0) { reset(); return true; }
      const uv = unit > 0 ? unit : -unit;
      val[uv] = unit > 0 ? 1 : -1;
      touched[nt++] = uv;
    }
    reset();
    return false;
  }

  /** Hints from the conflict-analysis chain (validated by `replay`). */
  chainHints(chain, clause, conflict) {
    if (chain === null) return null;
    const covered = new Map();
    for (let j = 0; j < clause.length; j++) {
      const l = clause[j];
      const v = l > 0 ? l : -l, val = l < 0;
      const prev = covered.get(v);
      if (prev !== undefined && prev !== val) return null;
      covered.set(v, val);
    }
    const n0 = this.limSize > 0 ? this.trailLim[0] : this.trailSize;
    const level0 = [];
    for (let j = 0; j < n0; j++) {
      const v = Math.abs(this.trail[j]);
      if (covered.has(v)) continue;
      const r = this.reason[v];
      if (r >= 0 && this.clen[r] !== 1 && level0.indexOf(r) < 0) level0.push(r);
    }
    const hints = level0;
    for (let j = chain.length - 1; j >= 0; j--) hints.push(chain[j]);
    hints.push(conflict);
    return hints;
  }

  buildOcc() {
    const occ = new Map();
    for (let ci = 0; ci < this.nclauses; ci++) {
      const off = this.coff[ci], len = this.clen[ci];
      for (let j = 0; j < len; j++) {
        const l = this.cdata[off + j];
        let lst = occ.get(l);
        if (lst === undefined) { lst = []; occ.set(l, lst); }
        lst.push(ci);
      }
    }
    this.occ = occ;
  }

  /** Fallback: hints by a fresh unit propagation over the whole database. */
  rupHints(clause) {
    if (this.occ === null) this.buildOcc();
    const val = new Int32Array(this.nvars + 1);
    const touch = [];
    const set = (v, w) => { val[v] = w; touch.push(v); };
    for (let j = 0; j < clause.length; j++) {
      const l = clause[j];
      const v = l > 0 ? l : -l, w = l > 0 ? -1 : 1;
      if (val[v] !== 0 && val[v] !== w) return null;
      if (val[v] === 0) set(v, w);
    }
    for (let k = 0; k < this.units.length; k++) {
      const l = this.cdata[this.coff[this.units[k]]];
      const v = l > 0 ? l : -l, w = l > 0 ? 1 : -1;
      if (val[v] !== 0) { if (val[v] !== w) return null; continue; }
      set(v, w);
    }
    const hints = [];
    let head = 0;
    while (head < touch.length) {
      const v0 = touch[head++];
      const falseLit = val[v0] > 0 ? -v0 : v0;
      const lst = this.occ.get(falseLit);
      if (lst === undefined) continue;
      for (let t = 0; t < lst.length; t++) {
        const ci = lst[t];
        // deleted clauses are *not* skipped: the certificate checker sees the
        // database without deletions, so its propagation is at least as strong
        const off = this.coff[ci], len = this.clen[ci];
        let un = 0, unit = 0, sat = false;
        for (let j = 0; j < len; j++) {
          const l = this.cdata[off + j];
          const a = val[l > 0 ? l : -l];
          if (a === 0) {
            un++; unit = l;
            if (un > 1) break;
          } else if (a === (l > 0 ? 1 : -1)) { sat = true; break; }
        }
        if (sat || un > 1) continue;
        if (un === 0) { hints.push(ci); return hints; }
        const uv = unit > 0 ? unit : -unit;
        set(uv, unit > 0 ? 1 : -1);
        hints.push(ci);
      }
    }
    return null;
  }

  backtrack(level) {
    while (this.limSize > level) {
      const lim = this.trailLim[--this.limSize];
      for (let j = this.trailSize - 1; j >= lim; j--) {
        const lit = this.trail[j];
        const v = lit > 0 ? lit : -lit;
        this.phase[v] = this.value[v];
        this.value[v] = 0;
        this.reason[v] = -1;
      }
      this.trailSize = lim;
    }
    this.qhead = this.trailSize;
  }

  pickBranch() {
    if (this.order === 'positional') {
      for (let i = 1; i <= this.npos; i++) {
        for (let c = 0; c < this.colors; c++) {
          const v = (i - 1) * this.colors + c + 1;
          if (v <= this.nvars && this.value[v] === 0) return v;
        }
      }
      for (let v = 1; v <= this.nvars; v++) if (this.value[v] === 0) return v;
      return 0;
    }
    let best = 0, bestAct = -1;
    for (let v = 1; v <= this.nvars; v++) {
      if (this.value[v] === 0 && this.activity[v] > bestAct) { best = v; bestAct = this.activity[v]; }
    }
    return best;
  }

  reduceDb() {
    if (this.nclauses < 30000) return;
    let kept = 0;
    for (let ci = this.baseLen; ci < this.nclauses; ci++) {
      if (this.deleted[ci] || this.clen[ci] <= 4) continue;
      kept++;
      if (kept % 2 === 0) { this.deleted[ci] = 1; this.stats.deleted++; }
    }
  }

  emit(clause, hints) {
    if (!this.out) return;
    let s = '';
    for (let j = 0; j < clause.length; j++) s += clause[j] + ' ';
    s += '0 ' + hints.length;
    for (let j = 0; j < hints.length; j++) s += ' ' + hints[j];
    this.out.write(s + '\n');
  }

  /** Print everything about the first clause whose hints cannot be certified. */
  dumpDiagnostics(learned, chain, conflict) {
    const w = (s) => process.stderr.write(s + '\n');
    w(`DIAG: conflict ${this.stats.conflicts}, conflict clause ${conflict}`);
    w(`  learned = [${Array.from(learned)}]`);
    w(`  levels  = [${Array.from(learned).map(l => this.level[Math.abs(l)])}]`);
    w(`  curLevel = ${this.limSize}, trailSize = ${this.trailSize}`);
    w(`  trail = [${Array.from(this.trail.subarray(0, this.trailSize))}]`);
    w(`  conf-clause lits = [${Array.from({length: this.clen[conflict]},
        (_, j) => this.cLit(conflict, j))}]`);
    w(`  chain = [${chain}]`);
    const hints = this.chainHints(chain, learned, conflict);
    const n0 = this.limSize > 0 ? this.trailLim[0] : this.trailSize;
    w(`  n0 (level-0 prefix length) = ${n0}, limSize = ${this.limSize}`);
    const lvl0 = [];
    for (let j = 0; j < n0; j++) {
      const lit = this.trail[j];
      lvl0.push(`${lit}(L${this.level[Math.abs(lit)]},r${this.reason[Math.abs(lit)]})`);
    }
    w(`  trail[0..n0) = ${lvl0.join(' ')}`);
    w(`  chainHints = ${hints === null ? 'null' : '[' + hints + ']'}`);
    if (hints !== null) {
      // replay step by step to find where it breaks (unit clauses seed first)
      const val = new Int32Array(this.nvars + 1);
      for (let k = 0; k < this.units.length; k++) {
        const l = this.cdata[this.coff[this.units[k]]];
        val[l > 0 ? l : -l] = l > 0 ? 1 : -1;
      }
      for (let j = 0; j < learned.length; j++) {
        const l = learned[j];
        val[Math.abs(l)] = l > 0 ? -1 : 1;
      }
      for (let h = 0; h < hints.length; h++) {
        const ci = hints[h];
        const off = this.coff[ci], len = this.clen[ci];
        let un = 0, unit = 0, sat = false;
        for (let j = 0; j < len; j++) {
          const l = this.cdata[off + j];
          const a = val[Math.abs(l)];
          if (a === 0) { un++; unit = l; if (un > 1) break; }
          else if (a === (l > 0 ? 1 : -1)) { sat = true; break; }
        }
        const cl = Array.from({length: len}, (_, j) => this.cdata[off + j]);
        w(`   hint ${h}: clause ${ci} = [${cl}] len(clause)=${this.clen[ci]} ` +
          `unassigned=${un} unit=${unit} sat=${sat}`);
        if (sat || un > 1 || un === 0) {
          for (const l of cl) {
            const v = Math.abs(l);
            w(`      lit ${l}: var ${v} solverLevel=${this.level[v]} ` +
              `solverValue=${this.value[v]} reason=${this.reason[v]} ` +
              `replayValue=${val[v]}`);
          }
          break;
        }
        val[Math.abs(unit)] = unit > 0 ? 1 : -1;
      }
    }
  }

  solve(budget) {
    const luby = [1, 1, 2, 1, 1, 2, 4];
    let restartAt = 100;
    let sinceRestart = 0;
    const t0 = Date.now();
    for (;;) {
      const tp0 = performance.now();
      const conflict = this.propagate();
      this.tProp += performance.now() - tp0;
      if (conflict >= 0) {
        this.stats.conflicts++;
        sinceRestart++;
        if (this.limSize === 0) {
          this.conflict = -1;
          const final = this.rupHints(new Int32Array(0));
          if (final === null) {
            throw new Error('could not derive the empty clause at conflict ' +
                            this.stats.conflicts);
          }
          this.emit(new Int32Array(0), final);
          return false;
        }
        const ta0 = performance.now();
        const res = this.analyze(conflict);
        this.tAnalyze += performance.now() - ta0;
        const learned = res.learned;
        this.conflict = conflict;
        const th0 = performance.now();
        let hints = this.chainHints(res.chain, learned, conflict);
        if (hints !== null && this.replay(learned, hints)) this.stats.fastHints++;
        else {
          const alt = this.rupHints(learned);
          if (alt === null) {
            // Neither the trail-based hints nor a fresh propagation can certify
            // this clause.  `replay` passing is what justifies adding a clause,
            // so the clause is dropped and the search restarts: never add an
            // unjustified clause.
            if (this.diag) {
              this.dumpDiagnostics(learned, res.chain, conflict);
              process.exit(3);
            }
            this.tHints += performance.now() - th0;
            this.stats.dropped++;
            this.backtrack(0);
            if (this.stats.conflicts >= budget) {
              throw new Error('conflict budget exhausted (after dropping a clause)');
            }
            continue;
          }
          hints = alt;
          this.stats.fallbackHints++;
        }
        this.tHints += performance.now() - th0;
        const ci = this.addClause(learned, false);
        if (learned.length === 1) {
          // a learned unit clause is part of unit propagation in the checker, so
          // it must be registered: it seeds the trail of every later replay
          this.units.push(ci);
          this.backtrack(0);
          this.enqueue(learned[0], ci);
        } else {
          this.watches[this.widx(learned[0])].push(ci);
          this.watches[this.widx(learned[1])].push(ci);
          this.backtrack(res.back);
          this.enqueue(learned[0], ci);
        }
        this.emit(learned, hints);
        this.stats.learned++;
        this.varInc /= 0.95;
        if (sinceRestart >= restartAt) {
          this.backtrack(0);
          sinceRestart = 0;
          this.stats.restarts++;
          restartAt = 100 * luby[this.stats.restarts % luby.length];
        }
        if (this.stats.conflicts % 200000 === 0) {
          const mb = process.memoryUsage().heapUsed / (1 << 20);
          process.stderr.write(`  [cdcl] conflicts=${this.stats.conflicts} ` +
            `decisions=${this.stats.decisions} props=${this.stats.propagations} ` +
            `db=${this.nclauses} units=${this.units.length} heap=${mb.toFixed(0)}MB ` +
            `t=${((Date.now() - t0) / 1000).toFixed(0)}s ` +
            `[prop=${(this.tProp / 1000).toFixed(0)}s ana=${(this.tAnalyze / 1000).toFixed(0)}s ` +
            `hints=${(this.tHints / 1000).toFixed(0)}s]\n`);
        }
        if (this.stats.conflicts >= budget) throw new Error('conflict budget exhausted');
        // deleting clauses is O(database), so it must not run per conflict
        if (this.stats.conflicts % 10000 === 0) this.reduceDb();
      } else {
        const v = this.pickBranch();
        if (v === 0) return true;
        this.stats.decisions++;
        this.trailLim[this.limSize++] = this.trailSize;
        this.enqueue(this.phase[v] > 0 ? v : -v, -1);
      }
    }
  }
}

function main() {
  const args = process.argv.slice(2);
  const opt = { out: null, problem: 's4', sym: false, budget: 200000000,
                stats: false, order: 'positional' };
  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a === '--out') opt.out = args[++i];
    else if (a === '--problem') opt.problem = args[++i];
    else if (a === '--sym') opt.sym = true;
    else if (a === '--budget') opt.budget = parseInt(args[++i], 10);
    else if (a === '--stats') opt.stats = true;
    else if (a === '--order') opt.order = args[++i];
    else if (a === '--diag') opt.diag = true;
  }
  let base, nvars, colors;
  if (opt.problem === 's3') { base = buildCnfS3(); nvars = 14 * 3; colors = 3; }
  else { base = buildCnf(N, COLORS, opt.sym); nvars = N * COLORS; colors = COLORS; }
  process.stderr.write(`CNF: ${nvars} vars, ${base.length} clauses, ` +
    `problem=${opt.problem}, symmetry units: ${opt.problem === 's4' ? opt.sym : false}\n`);
  const s = new Solver(base, nvars, { colors, order: opt.order, diag: opt.diag });
  if (opt.out) s.out = fs.createWriteStream(opt.out, { flags: 'w', highWaterMark: 1 << 22 });
  const t0 = Date.now();
  let sat = false;
  try {
    sat = s.solve(opt.budget);
  } catch (e) {
    process.stderr.write('error: ' + e.message + '\n');
    if (s.out) s.out.destroy();
    process.exit(1);
  }
  if (s.out) s.out.end();
  const dt = (Date.now() - t0) / 1000;
  process.stderr.write(`result: ${sat ? 'SAT' : 'UNSAT'} in ${dt.toFixed(1)}s\n`);
  if (opt.stats) process.stderr.write('stats: ' + JSON.stringify(s.stats) + '\n');
}

if (require.main === module) main();
