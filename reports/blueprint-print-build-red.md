# The blueprint's print build was red on `main` from #118, with the error invisible

**Status**: found and fixed. Two Lean identifiers were quoted with backticks instead of
`\texttt{}` in `02_foundations.tex`, so their underscores were in text mode; the fix is those
two lines, and `scripts/lean-coverage.py` now refuses that class of error outright. This report
keeps the diagnosis because the *shape* of the failure is the reusable part: it is the second
time an invisible LaTeX error has kept `main`'s blueprint red for a day or more, and the first
time it has been caught mechanically.

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

## What was changed, and what the change found

`blueprint/src/latexmkrc` now passes `-halt-on-error` alongside `nonstopmode`. pdflatex then
stops at the first error, so the error and its context are the **last** thing in the CI log
rather than being buried under a full document's worth of reference warnings. A build with no
errors behaves exactly as before.

The very next `main` build (run 159, `663fd72`) then ended with

```
! Missing $ inserted.
<inserted text>
                $
l.644 step. `norm_
                  stateVec_comm_le` is~\eqref{eq:anticomm-transfer-bp} with ...
!  ==> Fatal error occurred, no output PDF file produced!
```

`02_foundations.tex` line 644 and line 646 each quoted a Lean identifier with **backticks**
instead of `\texttt{}`, so `norm_stateVec_comm_le` and `snorm_swapVec_aOp_sub_bOp` put their
underscores in text mode. Both were introduced by #118, which is exactly where the run table
puts the regression. The fix is those two lines.

Note what the list of ruled-out causes above got wrong: it checked that every *command* used is
defined and that every environment is balanced, and both were true. The error was not a command
at all --- it was a character, in the wrong mode. That is why the check added here is about
characters.

## The check that makes it not happen again

`scripts/lean-coverage.py` gained `text_mode_specials()`, which walks the content character by
character tracking `$`, `\[`/`\]`, `\(`/`\)` and the math environments, skipping comments,
escapes and the braced arguments of commands whose argument is not typeset (`\label`, `\ref`,
`\uses`, `\lean`, `\cite`, ...), and reports

* any `_` or `^` reached in text mode --- the thing that stops pdflatex;
* any single backtick before a letter --- never what this blueprint means, since code is
  `\texttt{}` and quotation marks are doubled, and it is how the underscores got in;
* unbalanced math mode at end of file.

Reintroducing either of the two original lines makes it report four failures naming line 644.
CI runs it before the Lean build, so this class of error now costs one script run rather than a
day of a red `main` and a log that does not say why.
