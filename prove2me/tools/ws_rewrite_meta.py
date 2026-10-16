#!/usr/bin/env python3
"""Rewrite the workspace copies of the modules whose metaprogramming the platform rejects.

The platform refuses custom syntax and elaborator registration in a submission, and gen.py drops
such commands from the bundles, so no use of them may remain in a generated file.  The closure of
the introspection and answer-reduction stages has five kinds.  They are rewritten here, in the
workspace copies only (the sources at 70cbf1c are untouched), each into the text the elaborator
would have produced or into core tactics running the same search:

* `local notation` (30 commands): every use in the notation's scope (to the `end` of the enclosing
  section or namespace) is replaced by the right-hand side, arguments substituted and parenthesized,
  and the command is removed;
* the tactic macros `solve_line_comm`, `norm_ds at h…` and `norm_ds_goal`: every use is replaced by
  the macro's quotation and the command is removed;
* `quantum_nonneg`, a recursive `macro_rules` tactic (five uses): each use is replaced by the macro
  unfolded to depth 2, which takes the macro's own path wherever its search succeeds within that
  depth (checked by compiling the module);
* `avg_congr`, an elaborator (five uses, none with `using`): replaced by its no-`using` path, the
  named peels with `avgOver_congr`, then `repeat` unnamed peels, then `try` `rfl` or a closing
  `simp` (a use without names must close its goal, as the elaborator requires);
* the `ldt_simp` simp set (three uses): each use is replaced by the set's members, read from the
  built package (13 definitions unfolded, 8 lemmas); the registration and the attribute command go;

and the four vendored tactic modules keep their headers only.

    P2M_DIR=<dir> python3 prove2me/tools/ws_rewrite_meta.py [--check]

Idempotent: a rewritten module has no such command left.  Records what it did in
<P2M_DIR>/meta_rewrites.json.  Recompile the rewritten modules with
`compile_modules.py --parts <modules>` (their dependents keep their oleans: only proofs and
notation change, not a declaration or its type) and extract them again.
"""
import argparse, json, os, re, sys

ap = argparse.ArgumentParser()
ap.add_argument("--check", action="store_true", help="report what would change, write nothing")
args = ap.parse_args()
S = os.environ.get("P2M_DIR") or sys.exit("set P2M_DIR to the p2m scratch directory")
WS = f"{S}/ws"
LDT = "MIPRE/Background/LIDT/MIPStarRE/LDT"
CLOSURE = [l.strip() for l in open(f"{S}/remaining_modules.txt", encoding="utf-8") if l.strip()]

IDCH = re.compile(r"[\w'!?]")
OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄", "⟪": "⟫", "‖": None}
CLOSE = {v: k for k, v in OPEN.items() if v}


def code_mask(text):
    """mask[i] is True where text[i] is code: not inside a comment or a string literal."""
    n, mask, i = len(text), bytearray(b"\x01") * len(text), 0
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i); j = n if j < 0 else j
            mask[i:j] = b"\x00" * (j - i); i = j; continue
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j): depth += 1; j += 2
                elif text.startswith("-/", j): depth -= 1; j += 2
                else: j += 1
            mask[i:j] = b"\x00" * (j - i); i = j; continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            mask[i:j] = b"\x00" * (j - i); i = j; continue
        i += 1
    return mask


def blocks(text, mask):
    """[(start_offset_of_line, depth_after_line)] per line; depth counts open section/namespace/mutual."""
    out, depth, off = [], 0, 0
    for line in text.split("\n"):
        if off < len(mask) and mask[off]:
            s = line.strip()
            if re.match(r"(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?section\b", s) or \
               re.match(r"namespace\s+\S", s) or re.match(r"mutual\b", s):
                depth += 1
            elif re.match(r"end\b", s):
                depth -= 1
        out.append((off, depth))
        off += len(line) + 1
    return out


def parse_notation(cmd):
    """`local notation "A[" i ", " j "]" => rhs` -> (pieces, params, rhs); pieces alternate tokens and params."""
    m = re.match(r'\s*local\s+notation\s+(.*?)\s*=>\s*(.*\S)\s*$', cmd)
    assert m, cmd
    lhs, rhs = m.group(1), m.group(2)
    pieces = []
    for tok in re.findall(r'"([^"]*)"|([^\s"]+)', lhs):
        if tok[0] != "" or tok[1] == "":
            pieces.append(("tok", tok[0].strip() or tok[0]))
        else:
            assert re.fullmatch(r"[\w']+", tok[1]), (cmd, tok)
            pieces.append(("arg", tok[1]))
    assert pieces and pieces[0][0] == "tok", cmd
    return pieces, [p for k, p in pieces if k == "arg"], rhs


def read_arg(text, mask, i, stop):
    """The term starting at i, up to the separator `stop` at bracket depth 0; returns (arg, index of stop)."""
    depth, j = [], i
    while j < len(text):
        if mask[j]:
            if not depth and text.startswith(stop, j):
                return text[i:j], j
            c = text[j]
            if c in OPEN and OPEN[c]:
                depth.append(OPEN[c])
            elif c in CLOSE:
                if not depth:
                    return None, j
                depth.pop()
        j += 1
    return None, j


def is_token_at(text, mask, i, tok):
    if not mask[i] or not text.startswith(tok, i):
        return False
    if i > 0 and (IDCH.match(text[i - 1]) or text[i - 1] == "."):
        return False
    if IDCH.match(tok[-1]):   # a token ending in an identifier character must not run into one
        k = i + len(tok)
        if k < len(text) and IDCH.match(text[k]):
            return False
        if k + 1 < len(text) and text[k] == "." and (text[k + 1].isalpha() or text[k + 1] == "_"):
            return False      # `F.foo` is the identifier `F.foo`, not the notation
    return True


def substitute(rhs, params, args):
    """All parameters at once: `A[j, i]` with parameters `i j` must not substitute into a substitution."""
    amap = {}
    for p, a in zip(params, args):
        a = a.strip()
        amap[p] = a if re.fullmatch(r"[\w'.]+", a) else f"({a})"
    if not amap:
        return f"({rhs})"
    pat = r"(?<![\w'.])(" + "|".join(re.escape(p) for p in sorted(amap, key=len, reverse=True)) + r")(?![\w'])"
    return "(" + re.sub(pat, lambda m: amap[m.group(1)], rhs) + ")"


def expand(text, notations):
    """Replace every use of the notations in `text` (which has no notation commands left)."""
    changed, count = True, 0
    while changed:
        changed = False
        mask = code_mask(text)
        for pieces, params, rhs in notations:
            first = pieces[0][1]
            i = 0
            while True:
                i = text.find(first, i)
                if i < 0:
                    break
                if not is_token_at(text, mask, i, first):
                    i += 1; continue
                j, args, ok = i + len(first), [], True
                for k in range(1, len(pieces)):
                    kind, val = pieces[k]
                    if kind == "tok":
                        while j < len(text) and text[j] in " \t": j += 1
                        if not text.startswith(val, j):
                            ok = False; break
                        j += len(val)
                    else:
                        nxt = pieces[k + 1][1] if k + 1 < len(pieces) else None
                        if nxt is None:   # a trailing argument: one identifier or bracketed term
                            m = re.match(r"\s*([\w'.]+|\([^()]*\))", text[j:])
                            if not m:
                                ok = False; break
                            args.append(m.group(1)); j += m.end(); continue
                        a, stop = read_arg(text, mask, j, nxt)
                        if a is None:
                            ok = False; break
                        args.append(expand(a, notations)[0]); j = stop
                if not ok:
                    i += 1; continue
                rep = substitute(rhs, params, args)
                text = text[:i] + rep + text[j:]
                count += 1; changed = True
                mask = code_mask(text)
                i += len(rep)
    return text, count


def rewrite_notations(text):
    mask = code_mask(text)
    lines = text.split("\n")
    bl = blocks(text, mask)
    cmds = []   # (line index, notation)
    for li, line in enumerate(lines):
        if re.match(r"\s*local\s+notation\b", line) and mask[bl[li][0]]:
            cmds.append((li, parse_notation(line)))
    if not cmds:
        return text, 0, 0
    # scope of each command: the following lines up to the `end` closing its block
    scopes = []
    for li, nt in cmds:
        d = bl[li][1]
        end = len(lines)
        for lj in range(li + 1, len(lines)):
            if bl[lj][1] < d:
                end = lj; break
        scopes.append((li, end, nt))
    total, out = 0, list(lines)
    # the command lines go, each with the docstring right above it (left alone, the docstring would
    # attach to the next command); blank them first (a later command can sit in an earlier one's
    # scope), so that no line index moves while the scopes are expanded (an expansion adds no breaks)
    drop = set()
    for li, _, _ in scopes:
        drop.add(li)
        k = li - 1
        if k >= 0 and lines[k].rstrip().endswith("-/"):
            while k >= 0 and "/--" not in lines[k]:
                k -= 1
            if k >= 0 and lines[k].lstrip().startswith("/--"):
                drop.update(range(k, li))
    for k in drop:
        out[k] = ""
    # expand scope by scope, from the last command up
    for li, end, nt in sorted(scopes, key=lambda s: -s[0]):
        seg = "\n".join(out[li + 1:end])
        active = [nt] + [n2 for l2, e2, n2 in scopes if l2 < li and e2 >= end]   # an enclosing scope's notations too
        seg2, c = expand(seg, active)
        total += c
        new_lines = seg2.split("\n")
        assert len(new_lines) == end - li - 1, "an expansion changed the line count"
        out[li + 1:end] = new_lines
    return "\n".join(l for k, l in enumerate(out) if k not in drop), len(cmds), total


def macro_body(text, start):
    """Text inside `(tactic| … )` starting at the macro command at `start`; returns (body, end offset)."""
    q = text.index("`(tactic|", start) + len("`(tactic|")
    depth, j = 1, q
    mask = code_mask(text)
    while j < len(text) and depth:
        if mask[j]:
            if text[j] == "(": depth += 1
            elif text[j] == ")": depth -= 1
        j += 1
    return text[q:j - 1], j


def cut_command(text, start, end):
    """Remove text[start:end] together with a docstring right before it and the trailing newline."""
    head = text[:start].rstrip()
    if head.endswith("-/"):
        d = head.rfind("/--")
        if d >= 0:
            start = d
    while end < len(text) and text[end] in " \t":
        end += 1
    if end < len(text) and text[end] == "\n":
        end += 1
    return text[:start].rstrip("\n") + "\n\n" + text[end:].lstrip("\n")


def rewrite_tactic_macros(text, rel):
    notes = []
    if rel == "MIPRE/TM/Interp/Step.lean" and 'macro "norm_ds"' in text:
        a = text.index('macro "norm_ds" "at"')
        body_at, e1 = macro_body(text, a)
        b = text.index('macro "norm_ds_goal"')
        body_goal, e2 = macro_body(text, b)
        body_at = re.sub(r"\s+", " ", body_at).strip()
        body_goal = re.sub(r"\s+", " ", body_goal).strip()
        assert body_at.endswith("at $hs*"), body_at[-40:]
        text = cut_command(text, b, e2)
        text = cut_command(text, a, e1)
        mask = code_mask(text)
        n_at = n_goal = 0
        def sub_at(m):
            nonlocal n_at
            if not mask[m.start()]: return m.group(0)
            n_at += 1
            return body_at[:-len("$hs*")] + m.group(1).strip()
        text = re.sub(r"(?<![\w'.])norm_ds at((?:[ \t]+[\w'.]+)+)", sub_at, text)
        mask = code_mask(text)
        def sub_goal(m):
            nonlocal n_goal
            if not mask[m.start()]: return m.group(0)
            n_goal += 1
            return body_goal
        text = re.sub(r"(?<![\w'.])norm_ds_goal(?![\w'])", sub_goal, text)
        notes.append(f"norm_ds at: {n_at} uses, norm_ds_goal: {n_goal} uses")
    if rel == "MIPRE/LCS/MagicSquare/Strategy.lean" and 'macro "solve_line_comm"' in text:
        a = text.index('macro "solve_line_comm"')
        body, e = macro_body(text, a)
        text = cut_command(text, a, e)
        blines = body.strip("\n").split("\n")
        n = 0
        out = []
        for line in text.split("\n"):
            m = re.fullmatch(r"(\s*)solve_line_comm\s*", line)
            if m:
                ind = m.group(1)
                out.append(ind + blines[0].strip())
                out.extend((ind + l) if l.strip() else l for l in blines[1:])
                n += 1
            else:
                out.append(line)
        text = "\n".join(out)
        notes.append(f"solve_line_comm: {n} uses")
    return text, notes


# `quantum_nonneg` (LDT/Tactic/QuantumNonneg.lean) is `first` over these alternatives, `R` marking a
# recursive call; names carry `_root_` as the macro's hygiene resolved them.  Unfolded to depth d (at
# depth 0 the recursive alternatives go) it takes the macro's own path wherever that search succeeds
# within depth d: an alternative that failed in the macro fails here too, cutting deeper recursion
# only removes options, and `first` keeps the order.  Depth 2 covers every use (checked by compiling).
QN_ALTS = [
    "assumption",
    "apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; R",
    "exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _",
    "exact _root_.star_mul_self_nonneg _",
    "apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> R",
    "apply _root_.MIPStarRE.LDT.leftTensor_nonneg; R",
    "apply _root_.MIPStarRE.LDT.rightTensor_nonneg; R",
    # the two bullets of the source, as `focus … done` on the two goals in order
    "apply _root_.IsSelfAdjoint.conjugate_nonneg; focus (R; done); focus ((first | assumption | "
    "exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)",
    "apply _root_.Finset.sum_nonneg; intro _ _; R",
    "apply _root_.smul_nonneg <;> R",
    "exact _root_.zero_le_one",
    "exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _",
    "exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _",
    "positivity",
    "nlinarith",
]

def quantum_nonneg(depth):
    alts = [a for a in QN_ALTS if depth > 0 or not re.search(r"\bR\b", a)]
    inner = quantum_nonneg(depth - 1) if depth > 0 else None
    return "first " + " ".join("| (" + (re.sub(r"\bR\b", lambda _m: "(" + inner + ")", a) if inner else a) + ")"
                               for a in alts)

QN_DEPTH = 2
QN_FILES = {f"{LDT}/Preliminaries/ComparisonCore.lean", f"{LDT}/Preliminaries/Defs.lean"}
PEEL = "refine _root_.MIPStarRE.LDT.avgOver_congr _ _ _ ?_"
LEAF = "first | rfl | (simp; done)"
LDT_SIMP = ["MIPStarRE.LDT.avgOver", "MIPStarRE.LDT.uniformDistribution", "MIPStarRE.LDT.constSubMeasFamily",
            "MIPStarRE.LDT.sddError", "MIPStarRE.LDT.sddErrorOp", "MIPStarRE.LDT.bipartiteConsError",
            "MIPStarRE.LDT.bipartiteSSCError", "MIPStarRE.LDT.IdxMeas.toIdxSubMeas", "MIPStarRE.LDT.IdxSubMeas.liftLeft",
            "MIPStarRE.LDT.IdxSubMeas.liftRight", "MIPStarRE.LDT.SubMeas.liftLeft", "MIPStarRE.LDT.SubMeas.liftRight",
            "MIPStarRE.LDT.ProjSubMeas.liftLeft", "MIPStarRE.LDT.leftTensor_mul_leftTensor",
            "MIPStarRE.LDT.rightTensor_mul_rightTensor", "MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor",
            "MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor", "MIPStarRE.LDT.leftTensor_conjTranspose",
            "MIPStarRE.LDT.rightTensor_conjTranspose", "MIPStarRE.LDT.leftTensor_one", "MIPStarRE.LDT.rightTensor_one"]
TACTIC_FILES = [f"{LDT}/Tactic/AvgCongr.lean", f"{LDT}/Tactic/QuantumNonneg.lean",
                f"{LDT}/Tactic/LdtSimpAttr.lean", f"{LDT}/Tactic/LdtSimp.lean"]


def rewrite_vendored_tactics(text, rel):
    notes = []
    if rel in QN_FILES:
        n = 0
        exp = quantum_nonneg(QN_DEPTH)
        def sub(m):
            nonlocal n
            n += 1
            return m.group(1) + exp
        text = re.sub(r"(?m)^(\s*)quantum_nonneg\s*$", sub, text)
        notes.append(f"quantum_nonneg: {n} uses, unfolded to depth {QN_DEPTH} ({len(exp)} characters each)")
    n = 0
    def sub_avg(m):
        nonlocal n
        n += 1
        ind, names = m.group(1), m.group(2)
        if names:
            lines = []
            for x in [s.strip() for s in names.split(",")]:
                lines += [PEEL, f"intro {x}"]
            lines += [f"repeat ({PEEL}; intro)", f"try ({LEAF})"]
        else:   # without names the elaborator must close the goal unless a peel succeeded
            lines = [f"first | (({PEEL}; intro); repeat ({PEEL}; intro); try ({LEAF})) | ({LEAF})"]
        return "\n".join(ind + l for l in lines)
    if rel not in TACTIC_FILES:
        text = re.sub(r"(?m)^(\s*)avg_congr(?: with ([\w'₀-₉]+(?:,\s*[\w'₀-₉]+)*))?\s*$", sub_avg, text)
        if n:
            notes.append(f"avg_congr: {n} uses")
        mask = code_mask(text)
        k = 0
        def sub_simp(m):
            nonlocal k
            if not mask[m.start()]: return m.group(0)
            k += 1
            return ", ".join(LDT_SIMP)
        text = re.sub(r"(?<![\w'.])ldt_simp(?![\w'])", sub_simp, text)
        if k:
            notes.append(f"ldt_simp: {k} uses")
    return text, notes


def header_only(text):
    """Keep the module's header (comments, imports, set_option lines before the first other command)."""
    out = []
    mask = code_mask(text)
    off = 0
    for line in text.split("\n"):
        s = line.strip()
        is_code = off < len(mask) and mask[off] and s
        if is_code and not re.match(r"(import|set_option|prelude|module)\b", s):
            break
        out.append(line)
        off += len(line) + 1
    text = "\n".join(out).rstrip()
    # a docstring (`/-- … -/`) documents the command after it, which is gone: drop it with that command
    k = text.rfind("/--")
    if k >= 0 and text.endswith("-/") and "-/" not in text[k:-2]:
        text = text[:k].rstrip()
    return text + "\n"


def main():
    record_path = f"{S}/meta_rewrites.json"
    record = json.load(open(record_path)) if os.path.exists(record_path) else {}
    changed = []
    for mod in CLOSURE:
        rel = mod.replace(".", "/") + ".lean"
        path = f"{WS}/{rel}"
        if not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8").read()
        new, notes = text, []
        if rel in TACTIC_FILES:
            if re.search(r"^(syntax|macro_rules|register_simp_attr|attribute \[ldt_simp\]|@\[tactic)", new, re.M):
                new = header_only(new)
                notes.append("tactic module: header only")
        else:
            new, nc, nu = rewrite_notations(new)
            if nc:
                notes.append(f"local notation: {nc} commands, {nu} uses expanded")
            new, n2 = rewrite_tactic_macros(new, rel)
            notes += n2
            new, n3 = rewrite_vendored_tactics(new, rel)
            notes += n3
        if new != text:
            changed.append(mod)
            print(f"{mod}: " + "; ".join(notes))
            if not args.check:
                open(path, "w", encoding="utf-8").write(new)
                record[mod] = notes
    # nothing the platform rejects may remain
    left = []
    for mod in CLOSURE:
        rel = mod.replace(".", "/") + ".lean"
        path = f"{WS}/{rel}"
        if not os.path.exists(path):
            continue
        t = open(path, encoding="utf-8").read()
        mask = code_mask(t)
        for m in re.finditer(r"(?m)^\s*(?:(?:local|scoped)\s+)?(notation3?|macro_rules|macro|syntax|elab_rules|elab|register_simp_attr|infixl?|infixr|prefix|postfix)\b", t):
            if mask[m.start(1)]:
                left.append(f"{mod}:{t[:m.start()].count(chr(10)) + 1} {m.group(1)}")
        for k in ("avg_congr", "quantum_nonneg", "ldt_simp", "norm_ds", "solve_line_comm"):
            for m in re.finditer(r"(?<![\w'.])" + re.escape(k) + r"(?![\w'])", t):
                if mask[m.start()]:
                    left.append(f"{mod}:{t[:m.start()].count(chr(10)) + 1} {k}")
    if not args.check:
        json.dump(record, open(record_path, "w"), indent=1)
    print(f"{len(changed)} module(s) {'would change' if args.check else 'rewritten'}; left: {left if left else 'none'}")
    if not args.check:   # every module ever rewritten (a rerun after a restore lists some again)
        open(f"{S}/meta_rewritten_modules.txt", "w").write("\n".join(sorted(record)) + "\n")


if __name__ == "__main__":
    main()
