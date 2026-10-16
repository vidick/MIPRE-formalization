#!/usr/bin/env python3
"""Shared pieces of the per-tree `make_config.py` scripts (the stage trees of increment 3 onwards).

    blueprint_names(extract_dir)       the `\\lean{}` names of the blueprint found in the extracted closure
    auto_renames(plan_log, decl_names) ASCII renames for the node names the planner reported

The platform requires ASCII theorem names.  plan.py prints the offending node names
("node names needing renames: [...]"); the config script turns them into renames by transliteration
(Greek letters to their names, subscripts to digits, primes to `_prime`) and the next plan run applies
them.  gen.py also replaces the last component of a renamed name as a token in every generated file,
so a last component shared with another declaration is reported: the local build then decides."""
import ast, glob, json, os, re, unicodedata

GREEK = {"α": "alpha", "β": "beta", "γ": "gamma", "δ": "delta", "ε": "eps", "ζ": "zeta", "η": "eta", "θ": "theta",
         "ι": "iota", "κ": "kappa", "λ": "lam", "μ": "mu", "ν": "nu", "ξ": "xi", "π": "pi", "ρ": "rho", "σ": "sigma",
         "τ": "tau", "υ": "upsilon", "φ": "phi", "χ": "chi", "ψ": "psi", "ω": "omega", "ϕ": "phi", "ϵ": "eps",
         "Γ": "Gamma", "Δ": "Delta", "Θ": "Theta", "Λ": "Lambda", "Ξ": "Xi", "Π": "Pi", "Σ": "Sigma", "Φ": "Phi",
         "Ψ": "Psi", "Ω": "Omega", "ℓ": "ell", "∞": "inf", "′": "_prime", "'": "_prime", "⁻¹": "_inv", "ᵀ": "_T",
         "∗": "_star", "ᶜ": "_compl", "ᵒᵖ": "_op", "√": "sqrt_"}
SUBS = {c: str(i) for i, c in enumerate("₀₁₂₃₄₅₆₇₈₉")}
SUPS = {c: str(i) for i, c in enumerate("⁰¹²³⁴⁵⁶⁷⁸⁹")}

def ascii_name(name):
    out = []
    for ch in name:
        if ch.isascii() and (ch.isalnum() or ch in "_."):
            out.append(ch)
        elif ch in GREEK:
            out.append(GREEK[ch])
        elif ch in SUBS:
            out.append(SUBS[ch])
        elif ch in SUPS:
            out.append(SUPS[ch])
        else:
            dec = unicodedata.normalize("NFKD", ch)
            dec = "".join(c for c in dec if c.isascii() and c.isalnum())
            out.append(dec if dec else f"_u{ord(ch):x}")
    s = "".join(out)
    s = re.sub(r"\.(\d)", r"._\1", s)          # a component may not start with a digit
    return s

def blueprint_names(extract_dir, repo):
    names = set()
    for f in glob.glob(f"{repo}/blueprint/src/content/*.tex"):
        t = open(f, encoding="utf-8").read()
        for m in re.finditer(r"\\lean\{([^}]*)\}", t, re.S):
            for n in re.sub(r"\s+", "", m.group(1)).split(","):
                if n:
                    names.add(n)
    decls = decl_names(extract_dir)
    return sorted(names & decls), decls

def decl_names(extract_dir):
    return {json.loads(l)["name"] for l in open(f"{extract_dir}/decl_graph.jsonl", encoding="utf-8") if l.strip()}

def auto_renames(plan_log, decls, fixed=None):
    """Renames for the node names the last plan run reported, plus `fixed` (hand-written ones)."""
    ren = dict(fixed or {})
    if not (plan_log and os.path.exists(plan_log)):
        return ren, []
    bad = []
    for line in open(plan_log, encoding="utf-8"):
        if line.startswith("node names needing renames:"):
            bad = ast.literal_eval(line.split(":", 1)[1].strip())
    last = {}
    for d in decls:
        last.setdefault(d.split(".")[-1], []).append(d)
    taken = set(decls) | set(ren.values())
    warnings = []
    for name in bad:
        if name in ren:
            continue
        new = ascii_name(name)
        while new in taken:
            new += "_r"
        taken.add(new)
        ren[name] = new
        others = [d for d in last.get(name.split(".")[-1], []) if d != name]
        if others:
            warnings.append(f"{name}: last component shared with {others[:3]}")
    return ren, warnings
