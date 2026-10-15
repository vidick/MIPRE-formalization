# Writing the platform metadata for one packet

You are given a packet file (`batch_<k>.json`, theorem items, or `bundles_<k>.json`, definition
bundles) of the MIP\* = RE assembly layer, and you write one JSON file of metadata records for its
items. Everything you need is in the packet: for a theorem item the Lean statement
(`formal_statement`), the `open`/`variable` lines of its scope (`preamble_opens`), its docstring,
its module's docstring, its source link at the pinned commit, the blueprint labels that name it,
the theorems its proof imports and how many helper lemmas are pasted; for a bundle the module
docstring, the list of kept declarations with their kinds and the docstrings of the definitions.
You may also read the Lean source file named in `source_path` in the repository (`git show
70cbf1c:<path>`) when a statement needs more context than the packet gives. Do not consult the
platform, do not invent facts, and never state what a proof does beyond what the packet says.

## The records

For a theorem item (`kind` = `theorem`, `glue-leaf`, `glue-conditional`, `glue-unconditional`):

```json
{"theorem_name": "...", "theorem_title": "...", "natural_language_statement": "...",
 "source": "...", "tags": ["..."], "explanation": "..."}
```

For a bundle (`kind` = `bundle-new` or `bundle-delta`):

```json
{"definition_name": "...", "definition_title": "...", "natural_language_statement": "...",
 "source": "...", "tags": ["..."]}
```

Write the file as a JSON array of such records, one per packet item, UTF-8, with single
backslashes in the LaTeX (the uploader does the JSON escaping).

## Rules for every field

* `theorem_title` / `definition_title`: at most 200 characters, 10 or more, plain English with
  inline KaTeX where it helps; a name a reader recognizes, not the Lean identifier.
* `natural_language_statement`: 120 to 2,500 characters, written as a lecture note or a paper
  would state the result: introduce every symbol, give the hypotheses, then **one display-math
  block** (`$$ ... $$`) with the main formula or conclusion, then a short paragraph on the
  result's role or reuse value, and finally a paragraph beginning exactly with
  `**Formalization Note**` that carries all Lean-specific information (the representation
  chosen, total functions and their junk values, what a definition unfolds to, the relaxation
  of a paper hypothesis, the name of the proposition stated). The statement must say exactly
  what the Lean says: every binder and hypothesis, the exact strength of each inequality or
  equality, no more. Never "it is easy to see", never a proof idea. For a definition bundle,
  describe each definition kept (what object it is, what its fields or clauses are) and say in
  one sentence what the embedded lemmas are for; group them by concept.
* `source`: the packet's `source` link, followed by the blueprint label(s) when the packet lists
  any (`blueprint <label>`), and the paper reference when the docstring or the module docstring
  names one (for example `[JNVWY20, Theorem 12.2]`, `[MNY, Lemma 5.1]`, `[Lin23]`). Keep the
  link exactly as given.
* `tags`: 2 to 5 from this list only: `computability`, `complexity-theory`, `turing-machines`,
  `polynomial-time`, `undecidability`, `recursive-compression`, `universal-machine`,
  `kleene-recursion`, `smn-theorem`, `cost-model`, `self-interpreter`, `succinct-descriptions`,
  `mip-re`, `nonlocal-games`, `quantum-information`, `interactive-proofs`, `halting-problem`,
  `verifiers`, `gap-compression`, `game-value`, `synchronous-games`, `entangled-strategies`,
  `bit-strings`, `list-programs`, `binary-arithmetic`, `semidecidability`, `tabulation`,
  `pcc-strategies`. Every item gets `mip-re`.
* `explanation` (theorems only): 80 to 1,500 characters on how the uploaded proof is organised,
  from the packet alone: which imported theorems it reduces to (`imported_nodes`), that it
  pastes helper lemmas from the source modules (`pasted_helpers`), the size of the proof
  (`prooflines`). For a `glue-leaf` say that the statement is uploaded without a proof: its
  witness (`witness`) exists in the repository in code the platform cannot host yet, and name
  that file. For `glue-conditional` and `glue-unconditional` say that the proof is the source's
  one-line application with the stage instances replaced by the witnesses of the `Nonempty`
  leaves, so the theorem is an accepted sketch whose open frontier is those leaves.

## Tone

Neutral and exact. No "elegant", "clever", "trick", "beautiful". No first person. The three
`Nonempty` leaves and the glue theorems must be described honestly: the Lean development proves
them, the platform does not yet hold those proofs.

## Where things go

Save the output as `<tree dir>/meta_out_<k>.json` for a theorem packet `batch_<k>.json` and
`<tree dir>/meta_out_bundles_<k>.json` for `bundles_<k>.json`, where `<tree dir>` is given with
the packet. Report, at the end, the number of records written and any item you could not
describe faithfully from the packet, with the reason.
