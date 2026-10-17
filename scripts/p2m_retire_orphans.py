#!/usr/bin/env python3
"""Retire the orphans of the repetition tree's first upload attempt on Prove2Me.

`prove2me/repetition/orphans.json` lists what a first upload attempt published on 2026-10-16, before
the platform's own copy of the openai/ten-proofs parallel repetition development was found: statements
of vendored lemmas (Open, no solution) and the Part01 definition bundle, none of them used by any tree
of this project.  Each one not yet retired is deprecated (`PATCH /theorems/:id` with
`{"deprecated": true}`), and, as the platform asks of a retired node, its natural-language statement
gets a note saying why and naming the hosted item that replaces it: the hosted theorem of the same name
when there is one, the hosted game bundle `quantum_parallel_repetition_game` for the bundle.  The record
is updated with the time and the replacement.  Deprecation hides an item from discovery and is
reversible (`{"deprecated": false}`); whatever imports an item keeps working.

    python3 scripts/p2m_retire_orphans.py          # dry run: what would be sent
    python3 scripts/p2m_retire_orphans.py --yes    # retire them

Reads PROVE2ME_API_KEY from the environment (never printed) and talks to https://prove2.me only.
"""
import argparse, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import p2m_upload as P   # request(), Auth: the uploader's client

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ORPHANS = os.path.join(ROOT, "prove2me", "repetition", "orphans.json")
# the hosted ten-proofs definition bundle the repetition tree imports (the platform has two of this name)
RECORDS = os.path.join(ROOT, "prove2me", "repetition", "platform-records.json")
GAME_BUNDLE = "quantum_parallel_repetition_game"
TODAY = "2026-10-17"


def note(replacement, day=TODAY):
    by = (f"Replaced by the platform's hosted `{replacement['theorem_name']}` ({replacement['theorem_id']})."
          if replacement else "Superseded by the platform's hosted openai/ten-proofs development "
                              "(tag `openai-ten-proofs`).")
    return (f"\n\n**Retired {day}.** Published by a first upload attempt of the MIP* = RE formalization "
            "(vidick/MIPRE-formalization) before the platform's own copy of the openai/ten-proofs parallel "
            "repetition development (the same upstream commit) was found; nothing in that formalization uses "
            f"it. {by}")


def hosted(name, own_id):
    """The hosted, non-deprecated item of this exact name other than our own copy."""
    code, d = P.request("GET", "/theorems", params={"theorem_name": name, "limit": 50})
    if code != 200:
        raise SystemExit(f"lookup of {name}: HTTP {code} {str(d)[:200]}")
    rows = [r for r in d.get("theorems", []) if r.get("theorem_id") != own_id and not r.get("deprecated_at")]
    return {"theorem_name": rows[0]["theorem_name"], "theorem_id": rows[0]["theorem_id"]} if len(rows) == 1 else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--yes", action="store_true", help="send the changes (default: dry run)")
    args = ap.parse_args()
    P.AUTH = P.Auth()
    rec = json.load(open(ORPHANS, encoding="utf-8"))
    todo = [("statement", n, r) for n, r in rec["statements"].items()] + \
           [("definition", n, r) for n, r in rec["definitions"].items()]
    done = skipped = 0
    for kind, name, r in todo:
        tid = r["theorem_id"]
        code, cur = P.request("GET", f"/theorems/{tid}")
        if code != 200 or cur.get("theorem_name") != name:
            raise SystemExit(f"{name}: GET returned HTTP {code}, name {cur.get('theorem_name') if isinstance(cur, dict) else cur}")
        text = (cur.get("natural_language_statement") or "").rstrip()
        if cur.get("deprecated_at"):
            r["deprecated_at"] = cur["deprecated_at"]
            skipped += 1
            if "**Retired " not in text:
                # retired before this script (the API probe): the note alone, dated as the retirement
                print(f"{'add' if args.yes else '[dry run] would add'} the retirement note to {name}, retired "
                      f"{cur['deprecated_at'][:10]}")
                if args.yes:
                    code, d = P.request("PATCH", f"/theorems/{tid}", body={
                        "natural_language_statement": text + note(hosted(name, tid), cur["deprecated_at"][:10]),
                        "reason": "the retirement note for a statement retired during the API probe"})
                    if code != 200:
                        raise SystemExit(f"{name}: PATCH returned HTTP {code} {str(d)[:300]}")
            continue
        if kind == "definition":
            gid = json.load(open(RECORDS, encoding="utf-8"))[GAME_BUNDLE]["theorem_id"]
            code, g = P.request("GET", f"/theorems/{gid}")
            if code != 200 or g.get("theorem_name") != GAME_BUNDLE or g.get("deprecated_at"):
                raise SystemExit(f"the hosted bundle {GAME_BUNDLE} ({gid}) is not available: HTTP {code}")
            repl = {"theorem_name": GAME_BUNDLE, "theorem_id": gid}
        else:
            repl = hosted(name, tid)
        body = {"deprecated": True,
                "natural_language_statement": text + note(repl),
                "reason": "retired: a duplicate of the hosted openai/ten-proofs content, used by nothing"}
        print(f"{'retire' if args.yes else '[dry run] would retire'} {kind} {name} ({tid}); "
              f"replacement: {repl['theorem_name'] + ' ' + repl['theorem_id'] if repl else 'the hosted development'}")
        if not args.yes:
            continue
        code, d = P.request("PATCH", f"/theorems/{tid}", body=body)
        if code != 200 or not d.get("deprecated_at"):
            raise SystemExit(f"{name}: PATCH returned HTTP {code} {str(d)[:300]}")
        r.update({"deprecated_at": d["deprecated_at"], "replaced_by": repl})
        done += 1
        tmp = ORPHANS + ".tmp"
        json.dump(rec, open(tmp, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
        os.replace(tmp, ORPHANS)
    if args.yes and done:
        rec["note"] = (rec["note"].split(" One statement was deprecated")[0] +
                       f" One statement was deprecated during the API probe (PATCH {{deprecated: true}}); the rest "
                       f"were retired on {TODAY} at the maintainer's request (scripts/p2m_retire_orphans.py), each "
                       "with a note naming the hosted item that replaces it.")
        json.dump(rec, open(ORPHANS + ".tmp", "w", encoding="utf-8"), indent=1, ensure_ascii=False)
        os.replace(ORPHANS + ".tmp", ORPHANS)
    print(f"{done} retired, {skipped} already retired, {len(todo)} in all" + ("" if args.yes else " (dry run)"))


if __name__ == "__main__":
    main()
