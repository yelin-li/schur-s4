"""
Independent verifier for a Schur (sum-free) coloring.

Input: a whitespace-separated list of colors (0-based) for the integers
1, 2, 3, ..., N.  We check, from scratch and with a brute-force O(N^2) scan
over all pairs, that no color class contains a, b, a+b.

Nothing is trusted: the file content is not assumed to be anything.
"""
import sys


def load(path):
    with open(path) as f:
        toks = f.read().split()
    return [int(t) for t in toks]


def check(c, N, ncolors, verbose=True):
    """c is 0-indexed: c[i] = color of integer i+1.  Only first N entries used."""
    assert len(c) >= N, f"need {N} colors, have {len(c)}"
    c = c[:N]
    if verbose:
        print(f"checking {N} integers, {ncolors} colors, "
              f"max color value = {max(c)}")
    if max(c) >= ncolors:
        return False, f"color value {max(c)} exceeds {ncolors - 1}"
    classes = [[] for _ in range(ncolors)]
    for i, col in enumerate(c):
        classes[col].append(i + 1)
    if verbose:
        print("class sizes:", [len(x) for x in classes])
    pairs = 0
    for col, cls in enumerate(classes):
        members = set(cls)
        for a in cls:
            for b in cls:
                pairs += 1
                if a + b in members:
                    return False, f"monochromatic triple {a}+{b}={a+b} in color {col}"
    if verbose:
        print(f"OK: no monochromatic (a,b,a+b) among all {pairs} ordered pairs")
    return True, "valid"


def check_symmetry(c, N):
    """Check c(i) == c(N+1-i) for all i (0-indexed: c[i] == c[N-1-i])."""
    bad = [i + 1 for i in range(N) if c[i] != c[N - 1 - i]]
    return bad


if __name__ == "__main__":
    path = sys.argv[1]
    data = load(path)
    print(f"{path}: {len(data)} tokens")
    # how many leading entries avoid color 6?
    first6 = next((i for i, v in enumerate(data) if v >= 6), None)
    print("first index (0-based) with color >= 6:", first6)

    print("\n--- base [1,536] as a 6-coloring ---")
    ok, msg = check(data, 536, 6)
    print("verdict:", ok, msg)

    if ok:
        out = " ".join(str(v) for v in data[:536])
        with open(path.replace(".txt", "_base536.txt"), "w") as f:
            f.write(out + "\n")
        print("wrote base coloring to", path.replace(".txt", "_base536.txt"))
        print("\nsymmetry check of the [1,536] block against the mirror block:")
        N = len(data)
        if N >= 1696:
            bad = check_symmetry(data[:1696], 1696)
            print(f"asymmetric positions in full 1696: {len(bad)} {bad[:10]}")
        else:
            print(f"file has only {N} tokens, cannot test mirror symmetry at 1697")
