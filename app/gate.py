"""The gate report (DESIGN.md §17; app/GATE.md).

Reads the work files `./calc` saves (PERSIST.md) for the gate's corpus, in
GATE.md's order, and prints the maximum hint rung per problem, whether each
replays to a proof, whether the recognizer fires on it, and §17's reading:
is the last third's mean rung below the first third's? Untrusted, like the
rest of app/: every "proved" is the kernel's report on replay.

    python3 app/gate.py [DIR] [--json]
"""

import json
import os
import sys

import api
import work
from assist import recognizer
from session import K, Refusal, loader
from terms import Integral, trees

# GATE.md: the corpus, in the order it is worked
CORPUS = (
    ("parts.P1_PARTS", "readiness P1(1)"),
    ("readiness.P1_2", "readiness P1(2)"),
    ("improper.P2", "readiness P2"),
    ("taylor.P3_LOWER", "readiness P3 part 1, lower"),
    ("taylor.P3_UPPER", "readiness P3 part 1, upper"),
    ("improper.P5", "readiness P5"),
    ("unit00.P1C_REDUCE", "unit 00 P1(c)"),
    ("unit00.P3A_SEPARATE", "unit 00 P3(a), separate"),
    ("unit00.P3A_V_ODE", "unit 00 P3(a), v(t)"),
    ("unit00.P3A_V_INIT", "unit 00 P3(a), v(0)"),
    ("unit00.P3A_TOP", "unit 00 P3(a), t_up"),
    ("unit00.P3A_HEIGHT", "unit 00 P3(a), h"),
    ("unit00.P4A_SEPARATE", "unit 00 P4(a), separate"),
    ("unit00.P4A_V_ODE", "unit 00 P4(a), v(t)"),
    ("unit00.P4A_V_INIT", "unit 00 P4(a), v(0)"),
    ("unit00.P4A_X", "unit 00 P4(a), x(t)"),
    ("unit00.P9A_V", "unit 00 P9(a), V(x)"),
)
NOT_READ = (
    "readiness P4: series (DESIGN.md §6.7), stage 2",
    "readiness P3 parts 2-3: certified numbers and big_O, stage 2",
    "unit 00 P1(a), (b), (d), (e): a classification, worked in the "
    "Classify box, which records no rung (CLASSIFY.md)",
    "unit 00's other parts: see UNIT00.md",
)
LABELS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "assist",
                      "gate_labels.json")
MIN_WORKED = 6  # two per third at least
FALSIFIER = ("If the average rung over the last third of the corpus is not "
             "below the average over the first third, the tool is a crutch "
             "rather than a trainer and §1's central claim has failed.")


def _problems():
    return {p.id: p for p, _, _ in api._problem_files().values()}


def _ladder(problem):
    ints = [t for t in trees(problem.goal()) if isinstance(t, Integral)]
    return recognizer.ladder(ints[0].body, ints[0].var) if ints else None


def fires(problem):
    """The recognizer row for the goal's first Int, as GET /hint reads it,
    or None: no Int, or no row."""
    step = _ladder(problem)
    return step["row"] if step else None


def recognizer_score(probs, path=LABELS):
    """GATE.md: the first row's family against gate_labels.json, as
    score.py scores a held-out set; None when there are no labels."""
    try:
        with open(path, encoding="utf-8") as f:
            entries = json.load(f)["entries"]
    except (OSError, ValueError, KeyError, TypeError):
        return None
    out = {"strict": 0, "lenient": 0, "wrong": [], "silent": [],
           "labelled": len(entries)}
    for e in entries:
        p = probs.get(e.get("id"))
        step = _ladder(p) if p else None
        fam = step["family"] if step else None
        if fam is None:
            out["silent"].append(e.get("id"))
        elif fam == e.get("technique"):
            out["strict"] += 1
            out["lenient"] += 1
        elif fam in e.get("also", ()):
            out["lenient"] += 1
        else:
            out["wrong"].append(f"{e.get('id')}: {fam}, course "
                                f"{e.get('technique')}")
    return out


def _proved(doc, problem):
    """The report at the end of the file's checked path, on replay, or
    None when it does not replay or is not closed."""
    try:
        sess, resumed = work.replay(doc, "gate", problem.goal_text,
                                    problem.sig, problem.id)
    except Refusal:
        return None
    last = sess.nodes[resumed["path"][-1]].state
    return K.report(last) if last.goal is None else None


def _read(path):
    try:
        with open(path, encoding="utf-8") as f:
            doc = json.load(f)
    except (OSError, ValueError):
        return None
    ok = (isinstance(doc, dict) and doc.get("format") == "calc-work"
          and doc.get("version") == 1 and type(doc.get("max_rung")) is int)
    return doc if ok else None


def _mean(xs):
    return sum(xs) / len(xs) if xs else None


def report(work_dir):
    """GATE.md's report as a dict."""
    probs, rows = _problems(), []
    for pid, part in CORPUS:
        p = probs.get(pid)
        row = {"problem": pid, "part": part, "worked": False,
               "max_rung": None, "proved": None, "saved": None,
               "fires": fires(p) if p else None}
        doc = _read(os.path.join(work_dir, pid + ".json")) if p else None
        if doc is not None:
            row.update(worked=True, max_rung=max(0, min(3, doc["max_rung"])),
                       proved=_proved(doc, p), saved=doc.get("saved"))
        rows.append(row)
    read = [r for r in rows if r["worked"] and r["fires"]]
    n, k = len(read), len(read) // 3
    first = _mean([r["max_rung"] for r in read[:k]]) if k else None
    last = _mean([r["max_rung"] for r in read[n - k:]]) if k else None
    if n < MIN_WORKED:
        verdict = "not enough data"
    else:
        verdict = "passes" if last < first else "fails"
    worked = [r for r in rows if r["worked"]]
    return {"rows": rows, "n": n, "first_third": first, "last_third": last,
            "verdict": verdict,
            "histogram": {str(i): sum(r["max_rung"] == i for r in worked)
                          for i in range(4)},
            "no_row": [r["problem"] for r in worked if not r["fires"]],
            "recognizer": recognizer_score(probs),
            "not_read": list(NOT_READ)}


def text(rep):
    out = ["The gate (DESIGN.md §17, app/GATE.md)", ""]
    w = max(len(r["problem"]) for r in rep["rows"])
    for i, r in enumerate(rep["rows"], 1):
        state = ("not worked" if not r["worked"] else
                 f"rung {r['max_rung']}  " + (r["proved"] or "open"))
        fire = f"row: {r['fires']}" if r["fires"] else "no row fires"
        out.append(f"{i:>2}. {r['problem']:<{w}}  {state:<34} {fire}")
    out += ["", f"Read over {rep['n']} worked problems where a row fires."]
    if rep["first_third"] is not None:
        out.append(f"First third: mean rung {rep['first_third']:.2f}; "
                   f"last third: {rep['last_third']:.2f}.")
    out.append(f"Verdict: {rep['verdict']}.")
    if rep["verdict"] == "fails":
        out.append(FALSIFIER)
    h = rep["histogram"]
    out += ["", "Rungs used (worked problems): " + ", ".join(
        f"{h[str(i)]} at {i}" for i in range(4))]
    if rep["no_row"]:
        out.append("Worked, no row fires (not averaged in): "
                   + ", ".join(rep["no_row"]))
    sc = rep["recognizer"]
    if sc is None:
        out.append("The recognizer on this corpus: no labels "
                   "(app/assist/gate_labels.json).")
    else:
        out.append(f"The recognizer on this corpus: strict {sc['strict']}/"
                   f"{sc['labelled']}, lenient {sc['lenient']}/"
                   f"{sc['labelled']}.")
        out += [f"  wrong: {w}" for w in sc["wrong"]]
        out += [f"  silent: {w}" for w in sc["silent"]]
    out += ["", "Not in the reading:"] + [f"- {s}" for s in rep["not_read"]]
    return "\n".join(out)


def main(argv):
    args = [a for a in argv if a != "--json"]
    work_dir = args[0] if args else "calc-work"
    rep = report(work_dir)
    print(json.dumps(rep, indent=2) if "--json" in argv else text(rep))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
