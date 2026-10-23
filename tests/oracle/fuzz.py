#!/usr/bin/env python3
#
# Differential fuzzing of Kater's prover against kater-oracle.
#
# Generates random .kat files, each with one assertion and possibly a few
# assumptions, runs `kater` on them, and for every assertion Kater proves,
# asks `kater-oracle` for a counterexample. A counterexample to a proved
# assertion is a soundness bug: the file is kept under the findings
# directory, with the oracle's report next to it.
#
# The right-hand side of an assertion is a random weakening of its
# left-hand side, mixing sound steps (rfe -> rf, adding alternatives,
# closures, dropping guards) with unsound ones (po -> po-loc, rf -> rfe,
# ATOM -> ACQ), so that Kater sees many plausible claims, some false.
#
# Usage: fuzz.py [--kater K] [--oracle O] [--cases N] [--jobs J] [--seed S]
#                [--events E] [--findings DIR] [--profile P]

import argparse
import os
import random
import subprocess
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor, as_completed

# Builtin vocabulary (hidden relations such as po-imm cannot be named)
RELATIONS = ["po", "po-loc", "rf", "rfe", "rfi", "mo", "moe", "moi",
             "fr", "fre", "fri", "rmw", "detour"]
DEPENDENCIES = ["ctrl", "addr", "data"]
PREDICATES = ["R", "W", "F", "ACQ", "REL", "SC", "NA", "RLX", "ATOM",
              "EXCL", "NEXCL", "UR", "UW", "MEM", "DEP"]

# Sound weakenings of a relation, in GenMC's graphs
SOUND_REL = {
    "rfe": ["rf"], "rfi": ["rf", "po", "po-loc"],
    "moe": ["mo"], "moi": ["mo", "po", "po-loc"],
    "fre": ["fr"], "fri": ["fr", "po", "po-loc"],
    "po-loc": ["po"], "rmw": ["po", "po-loc"],
    "detour": ["po", "po-loc"],
    "ctrl": ["po"], "addr": ["po"], "data": ["po"],
}
# Plausible but unsound weakenings
UNSOUND_REL = {
    "po": ["po-loc", "rf", "mo"], "rf": ["rfe", "rfi", "po"],
    "mo": ["moe", "moi", "po"], "fr": ["fre", "fri", "po"],
    "po-loc": ["rf", "mo"], "rmw": ["rf"], "detour": ["rf", "mo"],
}
SOUND_PRED = {
    "ACQ": ["ATOM"], "REL": ["ATOM"], "RLX": ["ATOM"], "SC": ["ACQ", "REL", "ATOM"],
    "R": ["MEM", "DEP"], "W": ["MEM"], "UR": ["R", "EXCL"], "UW": ["W", "EXCL"],
}
UNSOUND_PRED = {
    "ATOM": ["ACQ", "REL", "SC"], "MEM": ["R", "W"], "R": ["W"], "W": ["R"],
    "ACQ": ["SC"], "REL": ["SC"], "NA": ["RLX"], "DEP": ["R"],
}


class Gen:
    def __init__(self, rng, profile):
        self.rng = rng
        self.profile = profile
        self.relations = list(RELATIONS)
        if "deps" in profile:
            self.relations += DEPENDENCIES
        self.user_rels = []
        self.user_preds = []

    def pick(self, xs):
        return self.rng.choice(xs)

    def chance(self, p):
        return self.rng.random() < p

    def pred(self):
        pool = PREDICATES + self.user_preds
        p = self.pick(pool)
        if self.chance(0.15):
            p = p + ";" + self.pick(pool)
        return "[" + p + "]"

    def leaf(self):
        """A leaf, and whether it relates events through predicates only"""
        r = self.rng.random()
        if r < 0.65:
            pool = self.relations + self.user_rels * 3
            rel = self.pick(pool)
            if self.chance(0.1):
                rel = rel + "^-1"
            return rel, False
        if r < 0.95:
            return self.pred(), True
        return "id", True

    def node(self, depth):
        """An expression, and whether it accepts a word of predicates only"""
        if depth <= 0 or self.chance(0.25):
            return self.leaf()
        op = self.rng.random()
        a, pa = self.node(depth - 1)
        if op < 0.40:
            b, pb = self.node(depth - 1)
            return "(" + a + " ; " + b + ")", pa and pb
        if op < 0.60:
            b, pb = self.node(depth - 1)
            return "(" + a + " | " + b + ")", pa or pb
        if op < 0.70:
            return "(" + a + ")+", pa
        if op < 0.78:
            return "(" + a + ")*", True
        if op < 0.86:
            return "(" + a + ")?", True
        return self.pred() + " ; " + "(" + a + ") ; " + self.pred(), pa

    def expr(self, depth):
        return self.node(depth)[0]

    def weaken_token(self, tok):
        """Weakens one token, soundly or not"""
        base = tok[:-3] if tok.endswith("^-1") else tok
        inv = tok[len(base):]
        if base in SOUND_REL and self.chance(0.6):
            return self.pick(SOUND_REL[base]) + inv
        if base in UNSOUND_REL and self.chance(0.5):
            return self.pick(UNSOUND_REL[base]) + inv
        if base.startswith("[") and base.endswith("]"):
            parts = base[1:-1].split(";")
            i = self.rng.randrange(len(parts))
            p = parts[i]
            if self.chance(0.3):
                parts.pop(i)
            elif p in SOUND_PRED and self.chance(0.6):
                parts[i] = self.pick(SOUND_PRED[p])
            elif p in UNSOUND_PRED:
                parts[i] = self.pick(UNSOUND_PRED[p])
            return "[" + ";".join(parts) + "]" if parts else "id"
        return tok

    def weaken(self, e):
        """A random weakening of expression E (as text)"""
        tokens = tokenize(e)
        steps = self.rng.randint(1, 3)
        for _ in range(steps):
            r = self.rng.random()
            if r < 0.5:
                idx = [i for i, t in enumerate(tokens) if is_atom(t)]
                if idx:
                    i = self.pick(idx)
                    tokens[i] = self.weaken_token(tokens[i])
            elif r < 0.65:
                tokens = ["("] + tokens + [")", "|"] + tokenize(self.expr(2))
                tokens = ["("] + tokens + [")"]
            elif r < 0.75:
                tokens = ["("] + tokens + [")", "+"]
            elif r < 0.85:
                tokens = ["("] + tokens + [")", "*"]
            else:
                tokens = ["("] + tokens + [")", "?"]
        return " ".join(tokens)

    def declarations(self):
        """User symbols, with assumptions exercising the saturation rules"""
        lines = []
        nrels = self.rng.choice([0, 0, 1, 1, 2])
        for i in range(nrels):
            name = "u%d" % i
            lines.append("relation " + name)
            self.user_rels.append(name)
        if self.chance(0.2):
            lines.append("predicate P0")
            self.user_preds.append("P0")
            if self.chance(0.5):
                lines.append("predicate P1")
                lines.append("disjoint P0 # P1")
                self.user_preds.append("P1")
        for _ in range(self.rng.choice([0, 0, 1, 1, 2])):
            lines.append("assume " + self.assumption())
        return lines

    def assumption(self):
        u = self.pick(self.user_rels) if self.user_rels else None
        kinds = ["empty", "id", "builtin", "equal", "domain", "incompat"]
        if u:
            kinds += ["trans", "trans", "plus", "below"]
        if "comp" in self.profile:
            kinds.append("comp")
        if "total" in self.profile and u:
            kinds.append("total")
        if "shapes" in self.profile:
            kinds += ["trans-any", "plus-any", "total-any", "below-pred", "cycles"]
        k = self.pick(kinds)
        if k == "empty":
            return self.expr(2) + " <= 0"
        if k == "id":
            return self.expr(2) + " <= id"
        if k == "builtin":
            target = u if u and self.chance(0.6) else self.pick(self.relations)
            return self.expr(2) + " <= " + target
        if k == "equal":
            return self.expr(1) + " = " + self.expr(1)
        if k == "domain":
            v = u or self.pick(self.relations)
            return v + " <= " + self.pred() + " ; " + v + " ; " + self.pred()
        if k == "incompat":
            return "[" + self.pick(PREDICATES + self.user_preds) + ";" + \
                self.pick(PREDICATES + self.user_preds) + "] = 0"
        if k == "trans":
            return u + " ; " + u + " <= " + u
        if k == "plus":
            return u + "+ <= " + u
        if k == "below":
            return u + " <= " + self.expr(2)
        if k == "comp":
            a, b, c = self.pred(), self.pred(), self.pred()
            return a + " ; po ; " + b + " <= " + a + " ; po ; " + c + " ; po ; " + b
        if k == "total":
            return "total " + u
        if k == "trans-any":
            x = self.leaf()[0]
            return x + " ; " + x + " <= " + x
        if k == "plus-any":
            x = self.leaf()[0]
            return x + "+ <= " + x
        if k == "total-any":
            return "total " + self.expr(1)
        if k == "below-pred":
            return self.expr(2) + " <= " + self.pred()
        if k == "cycles":
            return self.expr(2) + " & id <= " + self.expr(2)
        raise AssertionError(k)

    def case(self):
        lines = self.declarations()
        lhs, pred_word = self.node(self.rng.choice([1, 2, 2, 3]))
        rhs = self.weaken(lhs) if self.chance(0.8) else self.expr(2)
        form = self.rng.random()
        if pred_word and "nopredlhs" in self.profile:
            form = form * 0.7  # the & id forms drop words of predicates only
            lines.append("assert " + lhs + " <= " + rhs)
        elif form < 0.7:
            lines.append("assert " + lhs + " = " + rhs)
        elif form < 0.9:
            lines.append("assert " + lhs + " & id <= " + rhs)
        else:
            lines.append("assert " + lhs + " & id <= rot " + rhs)
        return "\n".join(lines) + "\n"


def tokenize(e):
    out, cur = [], ""
    for ch in e:
        if ch in "()|;+*? ":
            if cur:
                out.append(cur)
                cur = ""
            if ch != " ":
                out.append(ch)
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def is_atom(t):
    return t not in "()|;+*?" and t != "id"


def run_case(args, seed):
    rng = random.Random(seed)
    text = Gen(rng, args.profile).case()
    with tempfile.TemporaryDirectory(prefix="kfuzz") as d:
        path = os.path.join(d, "case.kat")
        with open(path, "w") as f:
            f.write(text)
        try:
            k = subprocess.run([args.kater, path], capture_output=True, timeout=30)
        except subprocess.TimeoutExpired:
            return seed, "kater-timeout", text, ""
        if k.returncode != 0:
            return seed, "kater-fails" if k.returncode == 6 else "kater-error", text, \
                k.stderr.decode(errors="replace")
        try:
            o = subprocess.run([args.oracle, "check", "-n", str(args.events), "-t", "60",
                                path], capture_output=True, timeout=600)
        except subprocess.TimeoutExpired:
            return seed, "oracle-timeout", text, ""
        out = o.stdout.decode(errors="replace")
        if "UNSOUND" in out:
            return seed, "UNSOUND", text, out
        if "unsupported" in out:
            return seed, "unsupported", text, out
        if "unknown at" in out:
            return seed, "oracle-unknown", text, out
        return seed, "agree", text, out


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.normpath(os.path.join(here, "..", ".."))
    ap = argparse.ArgumentParser()
    ap.add_argument("--kater", default=os.path.join(root, "Release", "kater"))
    ap.add_argument("--oracle", default=os.path.join(root, "Release", "kater-oracle"))
    ap.add_argument("--cases", type=int, default=200)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--events", type=int, default=4)
    ap.add_argument("--findings", default="fuzz-findings")
    ap.add_argument("--profile", default="",
                    help="comma-separated extras: deps, comp, total, shapes (odd "
                    "assumption shapes); nopredlhs "
                    "avoids & id over left-hand sides with words of predicates only")
    args = ap.parse_args()
    os.makedirs(args.findings, exist_ok=True)

    counts = {}
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        futs = [ex.submit(run_case, args, args.seed * 1000003 + i) for i in range(args.cases)]
        for fut in as_completed(futs):
            seed, verdict, text, report = fut.result()
            counts[verdict] = counts.get(verdict, 0) + 1
            if verdict in ("UNSOUND", "kater-error", "kater-timeout", "unsupported"):
                base = os.path.join(args.findings, "%s-%d" % (verdict.lower(), seed))
                with open(base + ".kat", "w") as f:
                    f.write(text)
                with open(base + ".txt", "w") as f:
                    f.write(report)
                if verdict in ("UNSOUND", "kater-error"):
                    print("%s seed=%d\n%s%s" % (verdict, seed, text, report), flush=True)
    print("summary:", ", ".join("%s=%d" % kv for kv in sorted(counts.items())), flush=True)
    return 1 if counts.get("UNSOUND") else 0


if __name__ == "__main__":
    sys.exit(main())
