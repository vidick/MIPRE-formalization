#!/usr/bin/env python3
"""Write prove2me/answerreduction/config.json for plan.py / gen.py: the answer reduction stage of MIP* = RE.

The increment closes the leaf `MIPRE.AnswerReduction.nonempty_five` (Open on the platform): its
witness `MIPRE.AnswerReduction.answerReduction` (`MIPRE/Background/AnswerReduction/Instance.lean`) is
the definition target, so the planner reaches the answer-reduction layer, the Cook--Levin and
Turing-machine material (`TM/`), the low individual degree test (`Background/LIDT/`, the vendored
LionSR/MIPStarRE tree at 507e8122 with the in-repo adapter and bridge) and the Foundations they rest
on.  The compression, assembly and repetition trees are the published registry.  Run plan.py once,
then this script again: it turns the node names the planner reported as non-ASCII into renames."""
import json, os, sys
S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(REPO, "prove2me", "tools"))
from config_common import blueprint_names, auto_renames
A = f"{S}/answerreduction"           # this tree's scratch directory (plan, manifest, logs)
E = f"{S}/stage3/extract"           # the extraction shared by the two stage trees of increment 3

TARGETS = []
DEFMAT_TARGETS = ["MIPRE.AnswerReduction.answerReduction"]
blueprint, decls = blueprint_names(E, REPO)
missing = [t for t in TARGETS + DEFMAT_TARGETS if t not in decls]
if missing:
    sys.exit(f"targets absent from the extracted closure: {missing}")
renames, warnings = auto_renames(f"{A}/plan.log", decls)
for w in warnings:
    print("rename warning:", w)

cfg = {
    "extract_dir": E,
    "out": f"{A}/plan.json",
    "tree_out": f"{A}/tree.json",
    "manifest": f"{A}/generated.json",
    "wipe": False,
    "targets": TARGETS,
    "defmat_targets": DEFMAT_TARGETS,
    "blueprint_names": blueprint,
    "published_trees": [f"{REPO}/prove2me/tree.json", f"{REPO}/prove2me/assembly/tree.json",
                        f"{REPO}/prove2me/repetition/tree.json"],
    "published_bundles": [],
    "published_nodes_extra": {},
    "blueprint_seeds": False,
    "force_blueprint_nodes": False,
    "renames": renames,          # the platform wants ASCII identifiers
    "token_renames": {},
    "glue_leaves": [
        {"theorem_name": "MIPRE.AnswerReduction.nonempty_five", "statement": "Nonempty (MIPRE.AnswerReduction 5)",
         "proof": "⟨MIPRE.AnswerReduction.answerReduction⟩",
         "constants": ["MIPRE.AnswerReduction.answerReduction", "MIPRE.AnswerReduction"],
         "source": {"file": "MIPRE/Background/AnswerReduction/Instance.lean", "commit": "70cbf1c"}}
    ],
}
os.makedirs(A, exist_ok=True)
json.dump(cfg, open(os.path.join(REPO, "prove2me", "answerreduction", "config.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
print(f"config written: {len(blueprint)} blueprint names in the closure, defmat targets {DEFMAT_TARGETS}, {len(renames)} renames")
