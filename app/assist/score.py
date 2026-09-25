"""The recognizer's scores (RECOGNIZER.md, Scoring), printed.

    python3.12 app/assist/score.py            the development set
    python3.12 app/assist/score.py heldout    the held-out set (version 2's)
    python3.12 app/assist/score.py heldout-v1 version 1's, development now

For each labelled integral: strict when the first row's family is the
label; lenient when it is the label or one of `also`; wrong when a row
matched but neither; silent when no row matched; no row when the label is
a family without a row. Strict and lenient are counted over the entries
whose label has a row. test_recognizer.py pins both scores.
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if os.path.dirname(HERE) not in sys.path:
    sys.path.insert(0, os.path.dirname(HERE))

from assist import corpus, recognizer as R  # noqa: E402
from assist.shapes import KERNEL  # noqa: E402,F401  (puts kernel on the path)
from terms import parse_term  # noqa: E402

# RECOGNIZER.md revision 2: version 1's held-out set was scored once and
# joined the development set; version 2 is scored once on a fresh set.
HELDOUT_V1 = os.path.join(HERE, "heldout_2026_09_25.json")
HELDOUT = os.path.join(HERE, "heldout_2026_09_25_v2.json")


def heldout(path=HELDOUT):
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    return data["entries"] if isinstance(data, dict) else data


def development():
    """The spike's sets (corpus.DEVELOPMENT) and version 1's held-out set."""
    return list(corpus.DEVELOPMENT) + heldout(HELDOUT_V1)


def verdict(entry):
    """(verdict, family of the first row or None) for one entry."""
    label = entry["technique"]
    hit = R.first(parse_term(entry["integrand"]), entry["x"])
    fam = hit[0].family if hit else None
    if label in R.NO_ROW:
        return "no row", fam
    if fam is None:
        return "silent", None
    if fam == label:
        return "strict", fam
    if fam in entry.get("also", ()):
        return "lenient", fam
    return "wrong", fam


def score(entries):
    rows, counts = [], {}
    for e in entries:
        v, fam = verdict(e)
        counts[v] = counts.get(v, 0) + 1
        rows.append((e["id"], e["technique"], fam, v))
    rowed = len(entries) - counts.get("no row", 0)
    strict = counts.get("strict", 0)
    return {"rows": rows, "counts": counts, "rowed": rowed,
            "strict": strict, "lenient": strict + counts.get("lenient", 0)}


def main(which):
    entries = (heldout() if which == "heldout" else
               heldout(HELDOUT_V1) if which == "heldout-v1" else development())
    s = score(entries)
    for id_, label, fam, v in s["rows"]:
        print(f"{v:8} {id_:14} label {label!r:28} row {fam!r}")
    print(f"\n{which}: {len(entries)} integrals, {s['rowed']} with a row "
          f"family; strict {s['strict']}/{s['rowed']}, lenient "
          f"{s['lenient']}/{s['rowed']}; " + ", ".join(
              f"{k} {v}" for k, v in sorted(s["counts"].items())))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "development")
