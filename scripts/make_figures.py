#!/usr/bin/env python3
"""
Generates the SVG figures of docs/figures/ from measured data.

All numbers are measurements, not estimates; provenance:

  search-tree sizes (nodes of the backtracking search for [1,45], 4 colours)
      5 300 623 637   no symmetry breaking          bench/measure.js none 45
      1 325 155 910   colour of 1 fixed to 0        bench/measure.js c1 45
        441 718 638   first two colours fixed 0,1   bench/measure.js A 45
        220 859 322   + transposition (2 3) rule    bench/measure.js AB 45
  per-depth profile of the verified search          bench/measure.js AB 45 --profile
  the three verified branches                       bench/branches.js 45
        47 033 043 (third integer coloured 0)
        95 553 318 (third integer coloured 1)
        78 272 958 (third integer coloured 2)

No third-party plotting library is used: the SVG is written directly.
"""

import os
import json
import math

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "docs", "figures")
BENCH = os.path.join(HERE, "..", "bench")

INK = "#1f2933"
MUTED = "#7b8794"
BLUE = "#2b6cb0"
LIGHTBLUE = "#90cdf4"
ORANGE = "#c05621"
LIGHTORANGE = "#fbd38d"
GREEN = "#276749"
LIGHTGREEN = "#9ae6b4"
GREY = "#e4e7eb"
BG = "#ffffff"

FONT = "font-family='-apple-system,Segoe UI,Helvetica,Arial,sans-serif'"


def svg_start(w, h, title):
    return (f"<svg xmlns='http://www.w3.org/2000/svg' width='{w}' height='{h}' "
            f"viewBox='0 0 {w} {h}' role='img' aria-label='{title}'>\n"
            f"<rect width='{w}' height='{h}' fill='{BG}'/>\n")


def text(x, y, s, size=12, fill=INK, anchor="start", weight="normal", style=""):
    return (f"<text x='{x}' y='{y}' {FONT} font-size='{size}' fill='{fill}' "
            f"text-anchor='{anchor}' font-weight='{weight}' {style}>{s}</text>\n")


def rect(x, y, w, h, fill, stroke="none", rx=3, sw=1):
    return (f"<rect x='{x}' y='{y}' width='{w}' height='{h}' fill='{fill}' "
            f"stroke='{stroke}' stroke-width='{sw}' rx='{rx}'/>\n")


def line(x1, y1, x2, y2, stroke=MUTED, sw=1, dash=""):
    d = f" stroke-dasharray='{dash}'" if dash else ""
    return (f"<line x1='{x1}' y1='{y1}' x2='{x2}' y2='{y2}' stroke='{stroke}' "
            f"stroke-width='{sw}'{d}/>\n")


def polyline(points, stroke=BLUE, sw=2, fill="none"):
    pts = " ".join(f"{x},{y}" for x, y in points)
    return f"<polyline points='{pts}' fill='{fill}' stroke='{stroke}' stroke-width='{sw}'/>\n"


def polygon(points, fill, opacity=1.0):
    pts = " ".join(f"{x},{y}" for x, y in points)
    return f"<polygon points='{pts}' fill='{fill}' opacity='{opacity}'/>\n"


def arrow_defs():
    return ("<defs><marker id='arrow' viewBox='0 0 10 10' refX='9' refY='5' "
            "markerWidth='7' markerHeight='7' orient='auto-start-reverse'>"
            f"<path d='M 0 0 L 10 5 L 0 10 z' fill='{MUTED}'/></marker></defs>\n")


def arrow(x1, y1, x2, y2, stroke=MUTED, sw=1.4):
    return (f"<line x1='{x1}' y1='{y1}' x2='{x2}' y2='{y2}' stroke='{stroke}' "
            f"stroke-width='{sw}' marker-end='url(#arrow)'/>\n")


def load_profile():
    """Per-depth state counts of the verified search, from bench/out_AB.json."""
    path = os.path.join(BENCH, "out_AB.json")
    if os.path.exists(path):
        with open(path) as f:
            data = json.load(f)
        prof = data["perDepth"]                      # depths 1 … 45
        return [1] + prof + [0]                      # depth 0 = the root state
    return None


PROFILE = load_profile()


def fig_tree_profile():
    prof = PROFILE
    if prof is None:
        return None
    w, h = 900, 430
    ml, mr, mt, mb = 70, 30, 50, 55
    pw, ph = w - ml - mr, h - mt - mb
    n = len(prof)
    lmax = math.log10(max(prof) * 1.6)

    s = svg_start(w, h, "nodes visited per search depth")
    s += text(ml, 28, f"Verified search: states visited per depth "
                      f"(sum = {sum(prof):,})",
              size=15, weight="600")
    s += text(ml, 44, "4 colours, colours of 1 and 2 fixed to 0,1, transposition (2 3) applied",
              size=11, fill=MUTED)

    # y axis (log scale)
    e = 0
    while 10 ** e <= max(prof) * 1.6:
        v = 10 ** e
        y = mt + ph - (math.log10(v) / lmax) * ph
        s += line(ml, y, ml + pw, y, stroke=GREY)
        s += text(ml - 8, y + 4, f"{v:,}", size=10, fill=MUTED, anchor="end")
        e += 1
    s += line(ml, mt, ml, mt + ph, stroke=MUTED)
    s += line(ml, mt + ph, ml + pw, mt + ph, stroke=MUTED)
    s += text(ml - 8, mt - 10, "nodes", size=11, fill=MUTED, anchor="end")

    for k in range(0, n + 1, 5):
        x = ml + (k / n) * pw
        s += line(x, mt + ph, x, mt + ph + 4, stroke=MUTED)
        s += text(x, mt + ph + 18, str(k), size=10, fill=MUTED, anchor="middle")
    s += text(ml + pw / 2, mt + ph + 38, "depth  (integers coloured)", size=11,
              fill=MUTED, anchor="middle")

    pts = []
    for k, c in enumerate(prof):
        x = ml + (k / n) * pw
        y = mt + ph if c == 0 else mt + ph - (math.log10(max(c, 1)) / lmax) * ph
        pts.append((x, y))
    s += polygon([(ml, mt + ph)] + pts + [(ml + pw, mt + ph)], LIGHTBLUE, 0.55)
    s += polyline(pts, BLUE, 2)

    pk = max(range(n), key=lambda i: prof[i])
    xpk = ml + (pk / n) * pw
    ypk = mt + ph - (math.log10(prof[pk]) / lmax) * ph
    s += f"<circle cx='{xpk:.1f}' cy='{ypk:.1f}' r='3.5' fill='{ORANGE}'/>\n"
    s += text(xpk, ypk - 10, f"peak: {prof[pk]:,} states at depth {pk}",
              size=10, fill=ORANGE, anchor="middle")
    last = max(i for i, c in enumerate(prof) if c > 0)
    xl = ml + (last / n) * pw
    yl = mt + ph - (math.log10(prof[last]) / lmax) * ph
    s += f"<circle cx='{xl:.1f}' cy='{yl:.1f}' r='3.5' fill='{ORANGE}'/>\n"
    s += text(xl - 6, yl - 10,
              f"{prof[last]} states at depth {last} = the valid 4-colourings of [1,44]",
              size=10, fill=ORANGE, anchor="end")
    s += text(ml + pw, mt + ph + 32, "depth 45 = no full colouring", size=10,
              fill=ORANGE, anchor="end")
    s += "</svg>\n"
    return "tree_profile.svg", s


# --------------------------------------------------------------------------
# Figure 2: effect of the symmetry reductions
# --------------------------------------------------------------------------

REDUCTIONS = [
    ("no symmetry breaking", 5300623637, GREY, "measure.js none"),
    ("colour of 1 fixed to 0", 1325155910, LIGHTBLUE, "measure.js c1"),
    ("first two colours fixed to 0,1", 441718638, BLUE, "measure.js A"),
    ("+ transposition (2 3)  (verified)", 220859322, GREEN, "measure.js AB"),
]


def fig_reductions():
    w, h = 900, 360
    ml, mr, mt = 290, 190, 60
    bh, gap = 40, 22
    s = svg_start(w, h, "effect of the symmetry reductions on the search tree")
    s += text(ml - 240, 30, "Search tree below [1,45] with 4 colours (nodes visited)",
              size=15, weight="600")
    s += text(ml - 240, 46, "smaller is better; the last bar is the part actually verified in Lean",
              size=11, fill=MUTED)

    maxv = REDUCTIONS[0][1]
    scale = lambda v: (v / maxv) ** 0.5  # square-root scale keeps the small bars visible
    avail = w - ml - mr
    for i, (label, v, colour, src) in enumerate(REDUCTIONS):
        y = mt + i * (bh + gap)
        s += rect(ml, y, avail * scale(v), bh, colour)
        s += text(ml - 12, y + bh / 2 + 4, label, size=12, anchor="end")
        s += text(ml + avail * scale(v) + 8, y + bh / 2 + 4, f"{v:,}", size=12,
                  weight="600")
        s += text(ml + 6, y + bh - 8, src, size=9, fill="#ffffff" if v > maxv / 4 else MUTED)

    # factor annotations
    y0 = mt + bh / 2 + 4
    s += text(ml + avail + 8, y0 + 4 * (bh + gap) - 6,
              "24× smaller than no symmetry", size=11, fill=GREEN, weight="600")
    s += "</svg>\n"
    return "reductions.svg", s


# --------------------------------------------------------------------------
# Figure 3: the three verified branches
# --------------------------------------------------------------------------

BRANCHES = [
    ("third integer = 0", 47033043, None),
    ("third integer = 1", 95553318, None),
    ("third integer = 2", 78272958, None),
]


def fig_branches(timings=None):
    w, h = 900, 320
    ml, mr, mt = 210, 250, 70
    bh, gap = 34, 20
    s = svg_start(w, h, "the three verified branches")
    s += text(ml - 180, 30, "The exhaustive search is split into three disjoint branches",
              size=15, weight="600")
    s += text(ml - 180, 46, "each branch is a separate Lean file verified by native_decide; "
                            "the verdicts are combined by a proved lemma",
              size=11, fill=MUTED)
    maxv = max(v for _, v, _ in BRANCHES)
    avail = w - ml - mr
    for i, (label, v, _) in enumerate(BRANCHES):
        y = mt + i * (bh + gap)
        frac = v / maxv
        s += rect(ml, y, max(2, avail * frac), bh, BLUE)
        s += text(ml - 12, y + bh / 2 + 4, label, size=12, anchor="end")
        extra = f"{v:,} nodes"
        if timings and i < len(timings):
            extra += f"   ({timings[i]})"
        s += text(ml + avail * frac + 8, y + bh / 2 + 4, extra, size=12, weight="600")
    y = mt + 3 * (bh + gap) + 4
    s += text(ml - 12, y + 4, "total", size=12, anchor="end", weight="600")
    s += text(ml + 8, y + 4, f"{sum(v for _, v, _ in BRANCHES):,} nodes  =  "
                             f"220 859 322 states (minus the 3 prefix states)",
              size=12, weight="600", fill=GREEN)
    s += "</svg>\n"
    return "branches.svg", s


# --------------------------------------------------------------------------
# Figure 4: what is kernel-checked and what is trusted
# --------------------------------------------------------------------------

def fig_trust_base():
    w, h = 900, 380
    s = svg_start(w, h, "trust base of the formalisation")
    s += text(40, 32, "What Lean actually checks", size=15, weight="600")
    s += text(40, 50, "blue = proved inside the kernel (no extra trust) · "
                      "orange = closed evaluation by native_decide (Lean compiler trusted)",
              size=11, fill=MUTED)

    boxes = [
        (40, 80, 250, 78, "Good / checkGood", "definition of “no monochromatic\n"
                                              "a + b = c”, plus soundness and\n"
                                              "completeness of the test", BLUE, LIGHTBLUE),
        (320, 80, 250, 78, "search / searchB", "the backtracking search is\n"
                                               "specified by a theorem:\n"
                                               "searchB_spec (proved)", BLUE, LIGHTBLUE),
        (600, 80, 260, 78, "symmetry reductions", "exists_good_first_two and\n"
                                                  "exists_good_first_two_ok23\n"
                                                  "(proved, kernel only)", BLUE, LIGHTBLUE),
        (40, 200, 250, 96, "branchB0 / branchB1 / branchB2",
         "three closed evaluations of\nsearchB on disjoint subtrees\n"
         "47M / 96M / 78M states", ORANGE, LIGHTORANGE),
        (320, 200, 250, 96, "lookup_ok, c4_44 checks",
         "finite checks — done by the\nkernel (decide), not by\nnative_decide", GREEN, LIGHTGREEN),
        (600, 200, 260, 96, "combination lemmas",
         "searchB_false_of_three turns the\nthree branch verdicts into one;\nproved, kernel only",
         BLUE, LIGHTBLUE),
    ]
    for x, y, bw, bh, head, body, stroke, fill in boxes:
        s += rect(x, y, bw, bh, fill, stroke, rx=8, sw=1.6)
        s += text(x + 14, y + 24, head, size=13, weight="600")
        for j, ln in enumerate(body.split("\n")):
            s += text(x + 14, y + 44 + j * 15, ln, size=11, fill=INK)

    s += text(40, 330, "Result:", size=13, weight="600")
    s += text(100, 330, "four_colors_exact :  (∃ t, t.length = 44 ∧ Good t) ∧ Forcing 4 45", size=13)
    s += text(40, 352, "#print axioms shows: propext, Classical.choice, Quot.sound + "
                       "the three native_decide axioms.", size=11, fill=MUTED)
    s += "</svg>\n"
    return "trust_base.svg", s


# --------------------------------------------------------------------------
# Figure 5: proof pipeline (files and theorems)
# --------------------------------------------------------------------------

def fig_pipeline():
    w, h = 940, 420
    s = svg_start(w, h, "proof pipeline")
    s += text(40, 30, "Proof pipeline: from definitions to S(4) = 44", size=15, weight="600")
    s += arrow_defs()

    def box(x, y, bw, bh, head, body, stroke=BLUE, fill=LIGHTBLUE):
        out = rect(x, y, bw, bh, fill, stroke, rx=8, sw=1.5)
        out += text(x + 12, y + 22, head, size=12, weight="600")
        for j, ln in enumerate(body.split("\n")):
            out += text(x + 12, y + 40 + j * 14, ln, size=10, fill=INK)
        return out

    s += box(40, 60, 200, 76, "Schur.lean",
             "Good, checkGood, extendOk\nsearch, search_spec\nS(1), S(2), S(3)")
    s += box(290, 60, 200, 76, "Symmetry.lean",
             "12 permutations, lookup_ok\nexists_good_first_two\n(12-fold reduction)")
    s += box(540, 60, 200, 76, "RuleB.lean",
             "swap23, Ok23, searchB\nsearchB_spec, ok23_disj\nexists_good_first_two_ok23")
    s += box(790, 60, 120, 76, "SchurData.lean",
             "explicit\ncolourings\n(generated)")
    s += box(40, 210, 200, 76, "BranchB0/1/2.lean",
             "three native_decide runs\n47M / 96M / 78M states", ORANGE, LIGHTORANGE)
    s += box(290, 210, 200, 76, "searchB_false_of_three",
             "kernel-checked\ncombination of the\nthree branch verdicts")
    s += box(540, 210, 200, 76, "RuleB.searchB_prefix_43",
             "no good colouring of\nlength 45 starts with 0,1\nafter relabelling")
    s += box(790, 210, 120, 76, "S4.lean",
             "no_good_four_45\nfour_colors_exact\nS(4) = 44", GREEN, LIGHTGREEN)

    s += arrow(140, 136, 140, 210)
    s += arrow(340, 136, 330, 210)
    s += arrow(240, 248, 290, 248)
    s += arrow(490, 248, 540, 248)
    s += arrow(740, 248, 790, 248)
    s += arrow(640, 136, 620, 210)
    s += arrow(850, 136, 850, 210)

    s += text(40, 330, "The only non-kernel steps are the three orange boxes: closed "
                       "evaluations of a search function whose specification is proved.",
              size=11, fill=MUTED)
    s += text(40, 350, "Independent cross-checks: bench/reference_search.js "
                       "(JavaScript) and bench/verify_coloring.py (Python).",
              size=11, fill=MUTED)
    s += text(40, 370, "Inputs the search is applied to (colourings of [1,44], [1,536], …) "
                       "are verified twice: by brute force and inside Lean.",
              size=11, fill=MUTED)
    s += "</svg>\n"
    return "pipeline.svg", s


def main():
    os.makedirs(OUT, exist_ok=True)
    timings = None
    tfile = os.path.join(HERE, "..", "bench", "branch_timings.txt")
    if os.path.exists(tfile):
        with open(tfile) as f:
            timings = [ln.strip() for ln in f if ln.strip()]
    figures = [f for f in (fig_tree_profile(), fig_reductions(), fig_branches(timings),
                           fig_trust_base(), fig_pipeline()) if f]
    for name, content in figures:
        path = os.path.join(OUT, name)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
        print("wrote", os.path.relpath(path))


if __name__ == "__main__":
    main()
