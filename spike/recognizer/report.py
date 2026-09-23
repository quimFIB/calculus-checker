"""Score the recognizer tables against the corpus (DESIGN.md §17).

    python3 report.py            V1 and V2 side by side, then the scores
    python3 report.py --ladder   also print rungs 1–3 for every entry under V2

A verdict is one of:

  agree    the first matching row's family is the course's technique
  alt      it is one of the entry's acceptable alternatives (lenient only)
  wrong    a row fired, but for a different technique
  silent   no row fired, though the table has a row for the technique
  gap      no row fired, and the table has no row for the technique at all
"""

import sys

from corpus import CORPUS
from rows import V1, V2, recognize
from terms import parse

try:
    from corpus import HELD_OUT
except ImportError:
    HELD_OUT = []


def verdict(entry, table):
    hits = recognize(parse(entry["integrand"]), entry["x"], table)
    families = {r.family for r in table}
    if not hits:
        return ("gap" if entry["technique"] not in families else "silent"), None, hits
    top = hits[0][0]
    if top.family == entry["technique"]:
        return "agree", top, hits
    if top.family in entry.get("also", []):
        return "alt", top, hits
    return "wrong", top, hits


def score(entries, table):
    vs = [verdict(e, table)[0] for e in entries]
    n = len(vs)
    strict = vs.count("agree")
    lenient = strict + vs.count("alt")
    return strict, lenient, n, {k: vs.count(k) for k in ("wrong", "silent", "gap")}


def print_table(entries, title):
    print(title)
    head = f"{'id':<10} {'course says':<26} {'V1 names':<24} {'':<7} {'V2 names':<24}"
    print(head)
    print("-" * (len(head) + 7))
    for e in entries:
        v1, t1, _ = verdict(e, V1)
        v2, t2, _ = verdict(e, V2)
        n1 = t1.family if t1 else "—"
        n2 = t2.family if t2 else "—"
        print(f"{e['id']:<10} {e['technique']:<26} {n1:<24} {v1:<7} {n2:<24} {v2}")
    print()
    for name, table in (("V1", V1), ("V2", V2)):
        s, l, n, rest = score(entries, table)
        tail = ", ".join(f"{k} {v}" for k, v in rest.items() if v)
        print(f"{name}: strict {s}/{n}, lenient {l}/{n}" + (f"   ({tail})" if tail else ""))
    print()


def main():
    print_table(CORPUS, "Corpus — readiness P1/P2/P5 and unit 00 (what V2 was fitted to)")
    if HELD_OUT:
        print_table(HELD_OUT, "Held out — not looked at while writing V2")
    if "--ladder" in sys.argv:
        for e in CORPUS + HELD_OUT:
            _, top, hits = verdict(e, V2)
            print(f"{e['id']}  ∫ {e['integrand']} d{e['x']}")
            if not hits:
                print("   (no row)")
            else:
                row, p = hits[0]
                print(f"   rung 1  {row.category}")
                print(f"   rung 2  {row.technique}")
                print(f"   rung 3  {row.detail(p)}")
                print(f"   costs   {row.cost}")
                if len(hits) > 1:
                    print("   also    " + ", ".join(r.name for r, _ in hits[1:]))
            print()


if __name__ == "__main__":
    main()
