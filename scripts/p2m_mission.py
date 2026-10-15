#!/usr/bin/env python3
"""Build the private Prove2Me mission proposal "MIP* = RE", idempotently, from prove2me/mission/.

    python3 scripts/p2m_mission.py              # create or update the proposal, its items and milestone
    python3 scripts/p2m_mission.py --status     # read the proposal back as the platform stores it
    python3 scripts/p2m_mission.py --dry-run    # print what would be sent; needs no key
    python3 scripts/p2m_mission.py --fields quantum-information,complexity-theory
                                                # choose the mission's fields by slug (else: proposal.json's
                                                # preference list against the platform's catalog)

The content is ``prove2me/mission/proposal.json`` and the files it names: the description, the two
draft items (a definition bundle and the goal theorem's stub, both built against the platform's
environment), their natural-language statements and blind read-backs, one reference item (the
recursive compression lemma already published privately) and its milestone text.

The proposal is created with ``visibility: "private"`` and stays a ``Draft``: launching it (Submit
Proposal, which compiles and publishes the draft items as private content) and any release are
human actions on the website. Nothing here publishes anything.

The API key is read from ``PROVE2ME_API_KEY`` through ``scripts/p2m_upload.py`` and is never
printed or stored. State: ``prove2me/mission-state.json``.
"""
import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import p2m_upload as up  # noqa: E402  (Auth, request, log)

ROOT = up.ROOT
MDIR = os.path.join(ROOT, "prove2me", "mission")
STATE_PATH = os.path.join(ROOT, "prove2me", "mission-state.json")
log = up.log


# ----------------------------------------------------------------------------- content
def read(rel):
    with open(os.path.join(MDIR, rel), encoding="utf-8") as f:
        return f.read()


def split_stub(code, theorem_name):
    """A stub file is a comment header, the preamble (imports, opens) and the theorem.
    Return (preamble, formal_statement) as the platform wants them."""
    lines = code.splitlines()
    idx = next(i for i, l in enumerate(lines) if l.startswith("theorem "))
    preamble = "\n".join(l for l in lines[:idx]
                         if l.startswith(("import ", "open ", "variable ", "set_option ")))
    statement = "\n".join(lines[idx:]).strip()
    assert f"theorem {theorem_name} " in statement or f"theorem {theorem_name}\n" in statement, statement
    assert statement.endswith(":= by sorry"), statement
    return preamble, statement


def spec():
    sp = json.load(open(os.path.join(MDIR, "proposal.json"), encoding="utf-8"))
    sp["description"] = read(sp["description_file"]).strip()
    for it in sp["items"]:
        if it["kind"] == "reference":
            continue
        it["natural_language_statement"] = read(it["natural_language_file"]).strip()
        code = read(it["code_file"])
        if it["kind"] == "definition":
            it["definition"] = code
        else:
            it["preamble"], it["formal_statement"] = split_stub(code, it["theorem_name"])
        p = os.path.join(MDIR, it.get("readback_file", ""))
        it["readback"] = open(p, encoding="utf-8").read().strip() if it.get("readback_file") and os.path.exists(p) else None
    for ms in sp["milestones"]:
        ms["milestone_description"] = read(ms["description_file"]).strip()
    names = [it["name"] for it in sp["items"]]
    assert len(set(names)) == len(names)
    assert sp["main_item"] in names and set(sp["item_order"]) == set(names)
    return sp


def item_body(it):
    rb = {"readback": it["readback"], "readback_model": it["readback_model"]} if it.get("readback") else {}
    if it["kind"] == "definition":
        return {"kind": "definition", "definition_name": it["definition_name"], "definition_title": it["title"],
                "definition": it["definition"], "natural_language_statement": it["natural_language_statement"],
                "source": it["source"], "tags": it["tags"], **rb}
    if it["kind"] == "theorem":
        return {"kind": "theorem", "theorem_name": it["theorem_name"], "theorem_title": it["title"],
                "formal_statement": it["formal_statement"], "preamble": it["preamble"],
                "natural_language_statement": it["natural_language_statement"],
                "source": it["source"], "tags": it["tags"], **rb}
    return {"kind": "reference", "theorem_id": it["theorem_id"]}


def item_key(it):
    """The platform-side identity of a draft or reference item."""
    return it.get("theorem_name") or it.get("definition_name") or it.get("theorem_id")


# ----------------------------------------------------------------------------- state
def load_state():
    if os.path.exists(STATE_PATH):
        return json.load(open(STATE_PATH, encoding="utf-8"))
    return {"proposal": {}, "items": {}, "milestones": {}, "fields": {}, "log": []}


def save_state(st):
    tmp = STATE_PATH + ".tmp"
    json.dump(st, open(tmp, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    os.replace(tmp, STATE_PATH)


def note(st, msg):
    log(msg)
    st["log"].append({"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "msg": msg})
    save_state(st)


def first_list(d):
    if isinstance(d, list):
        return d
    for v in d.values():
        if isinstance(v, list):
            return v
    return []


def iid(obj):
    return obj.get("item_id") or obj.get("id")


# ----------------------------------------------------------------------------- platform
def choose_fields(sp, st, override):
    found = {}
    for q in sp["fields"]["queries"]:
        code, d = up.request("GET", "/fields", params={"q": q, "sort": "popular", "limit": 50})
        if code != 200:
            log(f"GET /fields?q={q}: {code} {str(d)[:200]}")
            continue
        for f in first_list(d):
            found[f["slug"]] = {"id": f["id"], "name": f.get("name"), "mission_count": f.get("mission_count")}
    st["fields"]["catalog"] = found
    wanted = [s.strip() for s in override.split(",")] if override else sp["fields"]["prefer"]
    chosen = [s for s in wanted if s in found]
    if override and len(chosen) != len(wanted):
        sys.exit(f"unknown field slug(s) {sorted(set(wanted) - set(chosen))}; known: {sorted(found)}")
    if not override:
        chosen = chosen[:2]
    st["fields"]["chosen"] = chosen
    if chosen:
        note(st, f"fields: {chosen}")
    else:
        note(st, f"no preferred field found in the catalog; candidates: {sorted(found)} (set with --fields)")
    return [found[s]["id"] for s in chosen]


def ensure_proposal(sp, st, field_ids):
    pid = st["proposal"].get("id")
    detail = None
    if pid:
        code, detail = up.request("GET", f"/mission-proposals/{pid}")
        if code != 200:
            note(st, f"proposal {pid} not readable ({code}); looking it up by name")
            pid, detail = None, None
    if not pid:
        code, d = up.request("GET", "/mission-proposals", params={"limit": 100, "offset": 0})
        if code == 200:
            for p in first_list(d):
                if p.get("name") == sp["name"]:
                    pid = p["id"]
                    code, detail = up.request("GET", f"/mission-proposals/{pid}")
                    note(st, f"adopted existing proposal {pid} named {sp['name']!r}")
                    break
    if not pid:
        body = {"name": sp["name"], "description": sp["description"], "mission_type": sp["mission_type"],
                "visibility": sp["visibility"]}
        if field_ids:
            body["field_ids"] = field_ids
        if sp.get("env"):
            body["env"] = sp["env"]
        code, detail = up.request("POST", "/mission-proposals", body=body)
        if code not in (200, 201):
            sys.exit(f"POST /mission-proposals failed: {code} {str(detail)[:600]}")
        pid = detail["id"]
        note(st, f"created proposal {pid} ({sp['visibility']}, {sp['mission_type']})")
    st["proposal"].update({"id": pid, "name": detail.get("name"), "status": detail.get("status"),
                           "visibility": detail.get("visibility")})
    save_state(st)
    if detail.get("status") not in ("Draft", "Changes requested"):
        sys.exit(f"proposal {pid} is {detail.get('status')!r}: not editable, nothing changed")
    # Keep the editable metadata in sync with the files.
    body = {"description": sp["description"], "mission_type": sp["mission_type"], "visibility": sp["visibility"]}
    if field_ids:
        body["field_ids"] = field_ids
    code, d = up.request("PATCH", f"/mission-proposals/{pid}", body=body)
    if code != 200:
        sys.exit(f"PATCH /mission-proposals/{pid} failed: {code} {str(d)[:600]}")
    st["proposal"].update({"status": d.get("status", st["proposal"].get("status")),
                           "visibility": d.get("visibility", sp["visibility"])})
    note(st, "proposal metadata synced (description, type, visibility" + (", fields)" if field_ids else ")"))
    return pid


def ensure_items(sp, st, pid):
    for it in sp["items"]:
        body = item_body(it)
        code, d = up.request("POST", f"/mission-proposals/{pid}/items", body=body)
        if it["kind"] == "reference" and code == 409:
            note(st, f"reference {it['theorem_name']} already in the proposal")
        elif code not in (200, 201):
            sys.exit(f"item {it['name']}: POST failed {code} {str(d)[:800]}")
        else:
            note(st, f"item {it['name']} ({it['kind']}): {'updated' if code == 200 else 'created'}"
                     + (" with read-back" if body.get("readback") else " WITHOUT read-back"))
    # Map every item to its id from the authoritative detail.
    code, detail = up.request("GET", f"/mission-proposals/{pid}")
    if code != 200:
        sys.exit(f"GET /mission-proposals/{pid}: {code}")
    by_key = {}
    for obj in detail.get("items", []):
        for k in ("theorem_name", "definition_name", "theorem_id"):
            if obj.get(k):
                by_key[obj[k]] = iid(obj)
    for it in sp["items"]:
        k = it.get("theorem_name") if it["kind"] == "theorem" else item_key(it)
        cand = [by_key.get(x) for x in (it.get("theorem_name"), it.get("definition_name"), it.get("theorem_id")) if x]
        found = next((c for c in cand if c), None)
        if not found:
            sys.exit(f"item {it['name']} not found in the proposal detail; keys seen: {sorted(by_key)}")
        st["items"][it["name"]] = {"id": found, "kind": it["kind"], "key": k}
    save_state(st)
    return detail


def set_main_and_order(sp, st, pid):
    order = [st["items"][n]["id"] for n in sp["item_order"]]
    body = {"main_item_id": st["items"][sp["main_item"]]["id"], "item_order": order}
    code, d = up.request("PATCH", f"/mission-proposals/{pid}", body=body)
    if code != 200:
        sys.exit(f"PATCH main_item_id/item_order failed: {code} {str(d)[:600]}")
    note(st, f"goal = {sp['main_item']}; order = {sp['item_order']}")


def ensure_milestones(sp, st, pid):
    for ms in sp["milestones"]:
        item_id = st["items"][ms["item"]]["id"]
        body = {"item_id": item_id, "milestone_title": ms["title"],
                "milestone_description": ms["milestone_description"]}
        code, d = up.request("POST", f"/mission-proposals/{pid}/milestones", body=body)
        if code not in (200, 201):
            sys.exit(f"milestone {ms['item']}: {code} {str(d)[:600]}")
        st["milestones"][ms["item"]] = {"item_id": item_id, "sort_order": d.get("sort_order"),
                                        "theorem_id": d.get("theorem_id")}
        note(st, f"milestone {ms['item']!r}: {'updated' if code == 200 else 'created'}")


def status(sp, st):
    pid = st["proposal"].get("id")
    if not pid:
        print("no proposal recorded in", STATE_PATH)
        return
    code, d = up.request("GET", f"/mission-proposals/{pid}")
    if code != 200:
        print(f"GET /mission-proposals/{pid}: {code} {str(d)[:300]}")
        return
    print(f"proposal {pid}")
    print(f"  name        {d.get('name')}")
    print(f"  status      {d.get('status')}    visibility {d.get('visibility')}    type {d.get('mission_type')}")
    print(f"  fields      {[f.get('slug') or f.get('name') for f in d.get('fields', [])]}")
    print(f"  main item   {d.get('main_item_id')}")
    for obj in d.get("items", []):
        key = obj.get("theorem_name") or obj.get("definition_name") or obj.get("theorem_id")
        extra = " read-back" if obj.get("readback") else ""
        print(f"  item        {obj.get('kind', '?'):10} {key}  {iid(obj)}{extra}")
    code, m = up.request("GET", f"/mission-proposals/{pid}/milestones")
    for ms in first_list(m) if code == 200 else []:
        title = ms.get("milestone_title") or ms.get("title")
        print(f"  milestone   {ms.get('sort_order')}: {title}  (item {ms.get('item_id')})")
    st["proposal"]["status"] = d.get("status")
    st["proposal"]["visibility"] = d.get("visibility")
    save_state(st)
    print("review: prove2.me, signed in, homepage -> My missions -> the proposal; confirm each item, then Submit Proposal"
          " (a private proposal launches privately, with no moderator step)")


def dry_run(sp):
    for it in sp["items"]:
        b = item_body(it)
        for k in ("definition", "natural_language_statement", "readback", "formal_statement", "preamble"):
            if k in b and b[k]:
                b[k] = b[k][:160].replace("\n", " ") + f"... ({len(b[k])} chars)"
        print(json.dumps(b, indent=1, ensure_ascii=False))
    print(json.dumps({"name": sp["name"], "mission_type": sp["mission_type"], "visibility": sp["visibility"],
                      "description": f"{len(sp['description'])} chars, {len(sp['description'].split())} words",
                      "main_item": sp["main_item"], "item_order": sp["item_order"],
                      "milestones": [m["title"] for m in sp["milestones"]]}, indent=1, ensure_ascii=False))
    missing = [it["name"] for it in sp["items"] if it["kind"] != "reference" and not it.get("readback")]
    print("read-backs missing for:", missing or "none")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--status", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--fields", help="comma-separated field slugs")
    ap.add_argument("--name", help="override the mission name")
    a = ap.parse_args()
    sp = spec()
    if a.name:
        sp["name"] = a.name
    if a.dry_run:
        dry_run(sp)
        return
    st = load_state()
    up.AUTH = up.Auth()
    code, me = up.request("GET", "/me")
    log(f"account {me.get('username')}" if code == 200 else f"GET /me: {code}")
    if a.status:
        status(sp, st)
        return
    field_ids = choose_fields(sp, st, a.fields)
    pid = ensure_proposal(sp, st, field_ids)
    ensure_items(sp, st, pid)
    set_main_and_order(sp, st, pid)
    ensure_milestones(sp, st, pid)
    status(sp, st)


if __name__ == "__main__":
    main()
