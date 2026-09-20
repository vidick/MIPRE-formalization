# The blueprint's print build has been red on `main` since #118, with the error invisible

**Status**: open. Not caused by, and not fixable from, any pull request: `blueprint.yml` runs
only on `main`. This report records the diagnosis, what it rules out, and the one change made
to make the next failure legible.

## What fails

`Build blueprint and deploy pages` fails at the `xu-cheng/texlive-action` step that runs
`latexmk -output-directory=../print`. The workflow's later steps (the declaration check, the
API docs, Jekyll, the Pages deploy) are all skipped, so **the published blueprint has not been
updated since 2026-09-19**.

| run | commit | result |
|---|---|---|
| 151 | `8db3f94` (2026-09-19) | success |
| 155, 156 | `43c115f` (#118) | failure |
| 157 | `01b57c8` (#119) | failure |
| 158 | `0647dc8` (#121) | failure |

So the regression entered with `43c115f`, whose only LaTeX changes are
`02_foundations.tex` (+542), `03_background_results.tex` (+863), `06_proof_structure.tex`
(24) and seven lines of `macros/common.tex`.

## Why the log does not say what is wrong

This is exactly the trap `CLAUDE.md` records for `\downsize`, and it is worth restating
because it defeats the obvious way of reading the log. Under `-interaction=nonstopmode`
pdflatex prints an error, **continues to the end of the document**, writes a complete PDF
(122 pages at `0647dc8`), and exits 1 only at the very end. `latexmk` then

* refuses to rerun, because the run errored, so no `.aux` is ever complete;
* reports `Latex failed to resolve 4279 reference(s)` and `183 citation(s)` --- every
  reference in the document, which looks like the failure but is a *consequence* of there
  having been only one pass;
* prints `pdflatex: Command for 'pdflatex' gave return code 1` and exits 12.

The tail of the CI log is therefore hundreds of `LaTeX Warning: Reference ... undefined`
lines and no `!` line at all. The actual error is somewhere in the middle of a 20 MB log that
the log-download URL will not serve to this environment (the egress proxy rejects
`productionresultssa0.blob.core.windows.net`), and `print.log` is not uploaded as an
artifact.

## What has been ruled out

Checked mechanically against `blueprint/src/content/*.tex` at `0647dc8`:

* **No undefined control sequence in the content.** Every command used in the content files
  is defined in `macros/common.tex`, shimmed in `macros/print.tex`, or standard in
  `article` + `amsmath`/`amssymb`/`amsthm`/`mathtools`/`mathrsfs`/`enumitem`/`hyperref`/`cleveref`.
  In particular none of the plastex-side commands (`\graphcolor`, `\home`, `\dochome`) is used
  outside `web.tex`, and all four effort badges and `\qlib` have print overrides.
* **No environment nesting error**, no `\end{x}` closing a `\begin{y}`, no unclosed
  environment, and no odd `$` count.
* **No alignment tab** inside `equation`/`equation*`/`displaymath` outside a nested
  `array`/`aligned`/`cases`/`substack`.
* **No `\item` outside a list.**
* **No blueprint annotation inside a math environment**, and no `\uses{}`/`\lean{}` argument
  spanning a blank line (both would be errors, since `\uses` is an expl3 short-argument
  command and `\lean` a one-argument `\newcommand`).
* **No duplicate `\newcommand`**: `\tnote` is the only repeated name, and its two definitions
  are in `macros/print.tex` and `macros/web.tex`, never loaded together.
* `scripts/lean-coverage.py` and `scripts/ledger-sync.py` are both at `PROBLEMS: 0` on `main`
  once the orphaned guards of #121 are repaired (PR #122), and the Lean build is green. This
  is a LaTeX-only failure.

Every label reported as undefined in the log (`cor:tsirelson`, `lem:cep-implies-equal`,
`thm:separation`, `rem:admitted-nodes`, ...) does exist in the content; they are undefined
only because pass 1's `.aux` was never completed.

## What was changed

`blueprint/src/latexmkrc` now passes `-halt-on-error` alongside `nonstopmode`. pdflatex then
stops at the first error, so the error and its context are the **last** thing in the CI log
rather than being buried under a full document's worth of reference warnings. A build with no
errors behaves exactly as before.

## Next step

Read the next `main` build's log tail; it will name the file and line. If more is needed, have
the workflow upload `blueprint/print/print.log` as an artifact --- there is no pdflatex in a
cloud session, so the log is the only way to see the error from here.
