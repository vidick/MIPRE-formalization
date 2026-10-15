#!/usr/bin/env python3
"""Write prove2me/assembly/config.json for plan.py / gen.py: the assembly layer of MIP* = RE.

The targets are the own-code theorems that `MIPRE/Background/Pipeline.lean` applies at `70cbf1c`
(the conditional consequences of a `GapCompression` and a universal machine); the definition
targets are the data those applications pass (`GapCompression.ofPipeline`, `Cost.selfUniversal`,
`Cost.selfClockedUniversal`).  The blueprint names are the `\\lean{}` names of the blueprint that
Stage 1 finds in the closure, so the list is exact rather than guessed.
"""
import json, os, re, glob, sys

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
A = f"{S}/assembly"

TARGETS = [
    "MIPRE.Halting.halting_reduces_to_gameValue_of",
    "MIPRE.Halting.halting_reduction_quantum_of",
    "MIPRE.Halting.gameValue_uncomputable_of",
    "MIPRE.Halting.quantumValue_uncomputable_of",
    "MIPRE.Halting.re_subset_mipstarComputable_of",
    "MIPRE.Halting.mipstarComputable_eq_re_of",
    "MIPRE.Halting.re_subset_mipstar_of",
    "MIPRE.Halting.mipstar_eq_re_of",
]
DEFMAT_TARGETS = [
    "MIPRE.GapCompression.ofPipeline",
    "MIPRE.Cost.selfUniversal",
    "MIPRE.Cost.selfClockedUniversal",
    # the stage contracts, which the Nonempty leaves and the glue sketches state
    "MIPRE.Introspection", "MIPRE.AnswerReduction", "MIPRE.Repetition",
]

names = set()
for f in glob.glob(f"{REPO}/blueprint/src/content/*.tex"):
    t = open(f, encoding="utf-8").read()
    for m in re.finditer(r"\\lean\{([^}]*)\}", t, re.S):
        for n in re.sub(r"\s+", "", m.group(1)).split(","):
            if n:
                names.add(n)
decls = {json.loads(l)["name"] for l in open(f"{A}/extract/decl_graph.jsonl", encoding="utf-8") if l.strip()}
blueprint = sorted(names & decls)
missing = [t for t in TARGETS + DEFMAT_TARGETS if t not in decls]
if missing:
    sys.exit(f"targets absent from the extracted closure: {missing}")

cfg = {
    "extract_dir": f"{A}/extract",
    "out": f"{A}/plan.json",
    "tree_out": f"{A}/tree.json",
    "manifest": f"{A}/generated.json",
    "wipe": False,
    "targets": TARGETS,
    "defmat_targets": DEFMAT_TARGETS,
    "blueprint_names": blueprint,
    "published_tree": f"{REPO}/prove2me/tree.json",
    "published_bundles": [
        {"module": "MIPRE.HaltingGameValue", "definition_name": "MIPRE_HaltingGameValue", "kept": "all"}
    ],
    "blueprint_seeds": False,
    "force_blueprint_nodes": False,
    "renames": {"MIPRE.Halting.classV_game_μ": "MIPRE.Halting.classV_game_mu"},
}
json.dump(cfg, open(f"{REPO}/prove2me/assembly/config.json", "w", encoding="utf-8"), indent=1)
print(f"blueprint-named declarations in the closure: {len(blueprint)}; wrote prove2me/assembly/config.json")
