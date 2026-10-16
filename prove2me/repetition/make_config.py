#!/usr/bin/env python3
"""Write prove2me/repetition/config.json for plan.py / gen.py: the repetition stage of MIP* = RE.

The increment closes the leaf `MIPRE.Repetition.nonempty_seven` (Open on the platform): its witness
`MIPRE.repetition 7` (`MIPRE/Background/Repetition/Verifier.lean`) is the definition target, so the
planner reaches the own-code repetition layer (`Foundations/Repeat/*`, `CL/Repeat`, `TensorFamily`,
`Dilation`) and the vendored parallel repetition proof (openai/ten-proofs, 8 parts) with the
commuting-operator and direct-product modules.  The compression and assembly trees are the published
registry; the blueprint names found in the closure are a promotion signal only.
"""
import json, os, re, glob, sys

S = os.environ.get("P2M_DIR", "/tmp/claude-0/-home-user-MIPRE-formalization/b05e6b3f-df9f-5d1d-be42-41cac66efc40/scratchpad/p2m")
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
A = f"{S}/repetition"

TARGETS = []
DEFMAT_TARGETS = ["MIPRE.repetition"]

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
    "published_trees": [f"{REPO}/prove2me/tree.json", f"{REPO}/prove2me/assembly/tree.json"],
    "published_bundles": [
        {"module": "MIPRE.HaltingGameValue", "definition_name": "MIPRE_HaltingGameValue", "kept": "all"},
        # the platform's own copy of the ten-proofs statement file (openai/ten-proofs,
        # ComparatorChallenges/G_QuantumParallelRepetition.lean, uploaded 2026-08-09, public): the
        # definitions the own-code repetition layer uses, imported from there, not re-uploaded
        {"module": "MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition.Part01", "definition_name": "quantum_parallel_repetition_game", "kept": ["QuantumParallelRepetition.Game", "QuantumParallelRepetition.Game.repeat", "QuantumParallelRepetition.DensityMatrix", "QuantumParallelRepetition.POVM", "QuantumParallelRepetition.Strategy", "QuantumParallelRepetition.Strategy.outcomeProbability", "QuantumParallelRepetition.Strategy.winProbability", "QuantumParallelRepetition.entangledValue", "QuantumParallelRepetition.repeatedEntangledValue"]}
    ],
    # the ten-proofs theorems the own code applies, Proved on the platform since 2026-08 (same statements)
    "published_nodes_extra": {
        "QuantumParallelRepetition.distributionUniformExponential": "QuantumParallelRepetition_distributionUniformExponential",
        "QuantumParallelRepetition.entangledValue_nonneg": "QuantumParallelRepetition_entangledValue_nonneg",
        "QuantumParallelRepetition.winProbabilities_bddAbove": "QuantumParallelRepetition_winProbabilities_bddAbove",
        "QuantumParallelRepetition.Strategy.winProbability_nonneg": "QuantumParallelRepetition_Strategy_winProbability_nonneg",
        "QuantumParallelRepetition.Strategy.winProbability_le_one": "QuantumParallelRepetition_Strategy_winProbability_le_one"
    },
    "blueprint_seeds": False,
    "force_blueprint_nodes": False,
    "renames": {"MIPRE.Cost.Data.length_le_size_list'": "MIPRE.Cost.Data.length_le_size_list_prime"},   # the platform wants ASCII identifiers
    "glue_leaves": [
        {"theorem_name": "MIPRE.Repetition.nonempty_seven", "statement": "Nonempty (MIPRE.Repetition 7)",
         "proof": "⟨MIPRE.repetition 7⟩", "constants": ["MIPRE.repetition", "MIPRE.Repetition"],
         "source": {"file": "MIPRE/Background/Repetition/Verifier.lean", "commit": "70cbf1c"}}
    ],
}
os.makedirs(os.path.join(REPO, "prove2me", "repetition"), exist_ok=True)
json.dump(cfg, open(os.path.join(REPO, "prove2me", "repetition", "config.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
print(f"config written: {len(blueprint)} blueprint names in the closure, defmat targets {DEFMAT_TARGETS}")
