#!/usr/bin/env python3
"""Templated platform metadata for a tree's theorem items and bundles, from the writer packets.

    P2M_CONFIG=prove2me/<tree>/config.json python3 prove2me/tools/auto_meta.py --packets <dir> --out <tree dir>

For every item the record carries the facts the packet has: the module and its docstring, the
declaration's docstring, the Lean statement (in a code block, after the prose), the source link
with blueprint labels, tags from the module path, and an explanation built from the proof's size,
pasted helpers and imported theorems.  Each record is marked ``"auto": true`` so the merge script
applies the looser display-math rule; writer records (``meta_out_<k>.json``) override these for
the items they cover, so the blueprint-named results can still be written by hand.
"""
import argparse, glob, json, os, re

ap = argparse.ArgumentParser()
ap.add_argument("--packets", required=True)
ap.add_argument("--out", required=True)
ap.add_argument("--commit", default="70cbf1c")
args = ap.parse_args()

TAG_RULES = [  # (module path fragment, tags)
    ("TenProofs", ["parallel-repetition", "entangled-strategies", "nonlocal-games"]),
    ("CommutingRepetition", ["parallel-repetition", "operator-algebras", "nonlocal-games"]),
    ("Repetition", ["parallel-repetition", "nonlocal-games"]), ("Repeat", ["parallel-repetition", "verifiers"]),
    ("Orthonormalization", ["linear-algebra", "operator-algebras"]), ("Orthogonalization", ["linear-algebra"]),
    ("QLD", ["pauli-basis-test", "quantum-information", "nonlocal-games"]), ("LIDT", ["low-degree-test", "polynomial-time"]),
    ("Introspection", ["introspection", "verifiers"]), ("AnswerReduction", ["answer-reduction", "pcp"]),
    ("CookLevin", ["cook-levin", "turing-machines"]), ("CL", ["cook-levin", "linear-algebra"]),
    ("TM", ["turing-machines", "computability"]), ("Cost", ["cost-model", "polynomial-time"]),
    ("Halting", ["halting-problem", "computability"]), ("Verifier", ["verifiers", "nonlocal-games"]),
    ("Game", ["nonlocal-games", "game-value"]), ("ValueApprox", ["game-value", "quantum-information"]),
    ("Pipeline", ["gap-compression", "verifiers"]), ("Compress", ["gap-compression", "recursive-compression"]),
    ("LCS", ["linear-algebra"]), ("Cslib", ["computability"]), ("Dilation", ["quantum-information", "linear-algebra"]),
    ("TensorFamily", ["entangled-strategies", "quantum-information"]),
    ("ClassMIPStarTab", ["interactive-proofs", "tabulation"]), ("ClassMIPStar", ["interactive-proofs", "complexity-theory"]),
    ("Class", ["interactive-proofs", "complexity-theory"]), ("Tabulate", ["tabulation", "verifiers"]),
    ("Semidecide", ["semidecidability", "computability"]), ("Encoding", ["bit-strings", "cost-model"]),
    ("Binary", ["binary-arithmetic", "cost-model"]), ("Lists", ["list-programs", "cost-model"]),
    ("Foundations", ["verifiers"]),
]

def tags_for(module):
    out = ["mip-re"]
    for frag, tags in TAG_RULES:
        if re.search(r"(^|\.)" + re.escape(frag) + r"(\.|$)", module or ""):
            for t in tags:
                if t not in out and len(out) < 5:
                    out.append(t)
    if len(out) < 2:
        out.append("quantum-information")
    return out

def clean_doc(s):
    s = (s or "").strip()
    s = re.sub(r"^/-[-!]?\s*", "", s); s = re.sub(r"\s*-/$", "", s)
    return s.strip()

def first_sentence(s, limit=180):
    s = re.sub(r"\s+", " ", clean_doc(s))
    s = re.sub(r"^#+\s*", "", s)
    m = re.match(r"(.+?[.!?])(\s|$)", s)
    out = (m.group(1) if m else s).strip()
    if len(out) > limit:
        out = out[:limit].rsplit(" ", 1)[0] + "…"
    return out

def title_of(name, doc, kind_word):
    d = first_sentence(doc)
    d = re.sub(r"\*\*(.+?)\*\*", r"\1", d).replace("`", "")
    d = d.rstrip(".:")
    short = name.split(".")[-1]
    if len(d) >= 10 and not d.lower().startswith(("the uploaded", "statement", "formal")):
        t = d
    else:
        t = f"{kind_word} {short} of the MIP* = RE formalization"
    return t[:200] if len(t) >= 10 else (t + " (" + short + ")")[:200]

def module_sentence(module, module_doc):
    md = clean_doc(module_doc)
    md = re.sub(r"^#+\s*(.+?)\n", r"\1. ", md, count=1)   # a title line becomes the lead
    md = re.sub(r"\s+", " ", md)
    para = md.split(" ## ")[0]
    if len(para) > 600:
        para = para[:600].rsplit(" ", 1)[0] + "…"
    return para

VENDORED = [  # (module prefix, provenance sentence): third-party code the repository vendors read-only
    ("MIPRE.Background.Repetition.TenProofs.",
     "The module is one of the eight parts into which the repository splits `QuantumParallelRepetition.lean` of "
     "[openai/ten-proofs](https://github.com/openai/ten-proofs) (commit `94bc0feb`, 2026-08-01, Apache 2.0), the Lean proof of "
     "*exponential parallel repetition for all two-player entangled games* (Chapter 6 of OpenAI's *Ten Advances in Mathematics "
     "and Theoretical Computer Science*, 2026); it is vendored read-only by `scripts/vendor-repetition.py`, which also records its "
     "toolchain compile fixes, and the uploaded copy replaces upstream's wholesale `import Mathlib` by the Mathlib modules the "
     "proofs use. The declarations, statements and proofs are upstream's, not this repository's."),
    ("MIPRE.Background.Repetition.CommutingRepetition.",
     "The module is vendored read-only from [vidick/commuting-repetition](https://github.com/vidick/commuting-repetition) "
     "(Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-repetition.py`."),
    ("MIPRE.Background.Orthonormalization.Orthogonalization.",
     "The module is vendored read-only from the `orthogonalization` development of "
     "[vidick/commuting-repetition](https://github.com/vidick/commuting-repetition) (Apache 2.0; commit and upstream path in the "
     "file header) by `scripts/vendor-repetition.py`."),
    ("MIPRE.Background.LIDT.MIPStarRE.",
     "The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) "
     "(Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`."),
]

OWN_HOLDERS = {"MIPRE contributors", "Thomas Vidick"}   # this repository's own copyright lines
_HEADERS = {}

def source_header(module):
    """The leading comment of the module's source at the commit (its copyright header)."""
    if module not in _HEADERS:
        import subprocess
        repo = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        r = subprocess.run(["git", "show", f"{args.commit}:{module.replace('.', '/')}.lean"], cwd=repo,
                           capture_output=True, text=True)
        text, blocks = r.stdout if r.returncode == 0 else "", []
        while True:   # every leading comment block: CSLib's copies add a second one, on the vendoring
            m = re.match(r"\s*(/-(?![!-]).*?-/)", text, re.S)
            if not m:
                break
            blocks.append(m.group(1)); text = text[m.end():]
        _HEADERS[module] = "\n".join(blocks)
    return _HEADERS[module]

def provenance(module):
    """The sentence crediting code this repository did not write: the vendored trees by path, and any
    other module whose copyright header names someone else, from the header itself (CSLib's files
    name their authors; the LCS development is Sean Perazzolo's)."""
    for prefix, sentence in VENDORED:
        if (module or "").startswith(prefix):
            return sentence
    if not module:
        return ""
    h = source_header(module)
    m = re.search(r"Copyright \(c\) (\d+) (.+?)\. All rights reserved", h)
    if not m or m.group(2) in OWN_HOLDERS:
        return ""
    holder = m.group(2)
    authors = re.search(r"Authors?: (.+)", h)
    authors = authors.group(1).strip() if authors else holder
    if "Vendored from CSLib" in h:
        up = re.search(r"upstream file\s+(\S+)", h)
        return (f"The module is vendored from [CSLib](https://github.com/leanprover/cslib) (commit `3aa9d441`, 2026-08-03; "
                f"Apache 2.0): upstream file `{up.group(1) if up else '?'}`, by {authors}; the file header lists the adaptations. "
                "The declarations, statements and proofs are upstream's, not this repository's.")
    if holder == "Sean Perazzolo":
        return ("The module belongs to the linear constraint system games development contributed by Sean Perazzolo, "
                "vendored with permission from [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted "
                "to this repository (Apache 2.0; the author is named in the file header).")
    print(f"warning: {module} has the copyright holder {holder!r} and no provenance sentence")
    return f"The module's copyright holder is {holder} (Apache 2.0; see the file header of the source)."

def lean_block(formal, opens):
    stmt = re.sub(r"\s*:=\s*by\s+sorry\s*$", "", formal.strip())
    ctx = "\n".join(l for l in opens if l.strip()) if opens else ""
    return "```lean\n" + ((ctx + "\n\n") if ctx else "") + stmt + "\n```"

def source_of(it):
    s = it["source"]
    labels = sorted({b["label"] for b in it.get("blueprint", [])})
    if labels:
        s += "; blueprint " + ", ".join(labels)
    return s

def theorem_record(it):
    name = it["theorem_name"]; kind = it.get("kind", "theorem")
    module = it.get("module") or ""
    doc = clean_doc(it.get("docstring", ""))
    lines = it.get("lines") or [None, None]
    where = f"`{it['source_path']}`" + (f", lines {lines[0]}–{lines[1]}" if lines and lines[0] else "")
    parts = []
    if module:
        parts.append(f"A statement of the module `{module}` of the MIP\\* = RE formalization (commit `{args.commit}` of "
                     f"vidick/MIPRE-formalization). " + module_sentence(module, it.get("module_doc", "")))
        if provenance(module):
            parts.append(provenance(module))
    else:
        parts.append(f"A statement of the MIP\\* = RE formalization (commit `{args.commit}` of vidick/MIPRE-formalization), "
                     f"declared in {where}.")
    if doc:
        parts.append(doc)
    if kind == "glue-leaf":
        parts.append("The statement asserts that the stage contract named in it is inhabited; it is uploaded as an **Open leaf**: "
                     "its witness exists in the repository, in code the platform cannot host yet.")
    parts.append("**Formal statement.** In Lean, with the scope shown:\n\n" + lean_block(it["formal_statement"], it.get("preamble_opens", [])))
    note = (f"**Formalization Note** `{name}` is declared in {where}. The binders, hypotheses and conclusion are exactly those of the "
            f"Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository")
    if it.get("source_name") and it["source_name"] != name:
        note += f" (there named `{it['source_name']}`; renamed for the platform, which requires ASCII identifiers)"
    note += ". The definitions it mentions are those of the published definition bundles of the module's import closure."
    parts.append(note)
    stmt = "\n\n".join(parts)
    if kind == "glue-leaf":
        expl = (f"The statement is uploaded without a proof: its witness `{it.get('witness')}` exists in the repository at commit "
                f"`{args.commit}`, in `{it['source_path']}`, which the platform cannot host yet; the Lean development proves it, the platform does not.")
    elif kind in ("leaf-closure", "glue-leaf-closure"):
        # tested before the generic glue case: a glue item's kind is "glue-" + its kind, and the leaf
        # closure of the repetition tree went out with the sketch text below (2026-10-16)
        expl = (f"The proof is the witness `{it.get('witness')}` of the repository, built from the published definition bundles; it closes the "
                "leaf, so every sketch resting on it is proved.")
    elif kind.startswith("glue-"):
        expl = ("The proof is the source's one-line application of the own-code theorem to the stage witnesses taken from the "
                f"`Nonempty` leaves ({', '.join('`' + c + '`' for c in it.get('imported_nodes', []))}), so the theorem is an accepted "
                "sketch whose open frontier is those leaves; the repository proves them in full.")
    else:
        pl = it.get("prooflines"); ph = it.get("pasted_helpers", 0); imp = it.get("imported_nodes", [])
        expl = f"The uploaded proof is the source proof" + (f" ({pl} lines)" if pl else "") + "."
        if ph:
            expl += f" It pastes {ph} helper lemma{'s' if ph != 1 else ''} verbatim from the source modules, each used only by proofs."
        if imp:
            expl += " It reduces to the uploaded theorem" + ("s" if len(imp) > 1 else "") + " " + ", ".join(f"`{c}`" for c in imp[:12]) + (" and others" if len(imp) > 12 else "") + ", imported as statement stubs."
        else:
            expl += " It imports no theorem of the development: the upload is the statement and its proof alone."
        expl += " It compiles against the published definition bundles of the module's import closure."
    return {"theorem_name": name, "theorem_title": title_of(name, doc, "Lemma" if kind == "theorem" else "Statement"),
            "natural_language_statement": stmt, "source": source_of(it), "tags": tags_for(module or name), "explanation": expl, "auto": True}

def bundle_record(b):
    name = b["definition_name"]; module = b["module"]
    md = module_sentence(module, b.get("module_doc", ""))
    defs = b.get("defmat", []); emb = b.get("embedded", [])
    docs = b.get("defmat_docstrings") or {}
    parts = [f"The definitions of the module `{module}` of the MIP\\* = RE formalization (commit `{args.commit}` of vidick/MIPRE-formalization). " + md]
    if provenance(module):
        parts.append(provenance(module))
    if b.get("published_bundle"):
        parts.append(f"This bundle **adds** the declarations below to the already published bundle `{b['published_bundle']}` of the same module, "
                     "which the new statements of this upload need and the earlier bundle left out.")
    if defs:
        items = []
        for d in defs:
            ds = docs.get(d)
            s = first_sentence(" ".join(ds), 140) if isinstance(ds, list) and ds else ""
            items.append(f"`{d}`" + (f" ({s})" if s else ""))
        text = "; ".join(items)
        if len(text) > 1500:
            cut = text[:1500].rsplit(";", 1)[0]
            text = cut + f"; and {len(defs) - cut.count('`') // 2} more"
        parts.append(f"**Definitions** ({len(defs)}): " + text + ".")
    if emb:
        parts.append(f"**Embedded lemmas** ({len(emb)}): the small results the bodies of these definitions need (proof fields, `simp` rules, "
                     "decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement"
                     + (": " + ", ".join(f"`{e.split('.')[-1]}`" for e in emb[:10]) + (", …" if len(emb) > 10 else "") if emb else "") + ".")
    if not defs:
        parts.append("The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.")
    parts.append(f"**Formalization Note** The bundle is the module `{module}` (`{b['source_path']}`) with every declaration not listed removed, "
                 "imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies"
                 + (f"; the source module is split over {len(b.get('imports', []))} imported bundle(s)" if b.get("imports") else "") + ".")
    short = module.split(".")[-1]
    lead = first_sentence(b.get("module_doc", ""), 120).rstrip(".")
    title = (f"Definitions of {short}" + (" (addendum)" if b.get("published_bundle") else "")
             + (f": {lead}" if lead else f" ({len(defs)} definitions" + (f", {len(emb)} embedded lemmas" if emb else "") + ")"))
    return {"definition_name": name, "definition_title": title[:200],
            "natural_language_statement": "\n\n".join(parts), "source": (b["source"] + ("; blueprint " + ", ".join(b["blueprint"]) if b.get("blueprint") else "")),
            "tags": tags_for(module), "auto": True}

theorems, bundles = [], []
for f in sorted(glob.glob(os.path.join(args.packets, "batch_*.json"))):
    theorems += [theorem_record(it) for it in json.load(open(f, encoding="utf-8"))]
for f in sorted(glob.glob(os.path.join(args.packets, "bundles_*.json"))):
    bundles += [bundle_record(b) for b in json.load(open(f, encoding="utf-8"))]
os.makedirs(args.out, exist_ok=True)
json.dump(theorems, open(os.path.join(args.out, "meta_out_auto.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
json.dump(bundles, open(os.path.join(args.out, "meta_out_bundles_auto.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
print(f"auto metadata: {len(theorems)} theorem records, {len(bundles)} bundle records -> {args.out}")
