"""A .dx file's header sentence (app/DX.md): read and print.

Untrusted. The header names the goal a .dx script proves: `problem ID.`
or `goal G [functions f/1, g/2].` The goal itself is read by the trusted
parser when /session installs it.
"""

import re

import script

FORMS = ("'problem ID.' or 'goal G.' (optionally 'goal G functions f/1, "
         "g/2 assuming name: J for s in I; ...')")
_ID = re.compile(r"[A-Za-z0-9_.-]+\Z")
_FN = re.compile(r"([A-Za-z][A-Za-z0-9_]*)\s*/\s*([0-9]+)\Z")


class HeaderError(Exception):
    """Not a header: refused 'bad-header' by the API."""


def _last_functions(text, word="functions"):
    """The start of the last depth-0 word `functions` (or `word`), or -1
    (DX.md review 3: a declared function may itself be called
    functions)."""
    found = -1
    for i, c, d in script._depth_scan(text):
        j = i + len(word)
        if (d == 0 and text.startswith(word, i)
                and (i == 0 or text[i - 1].isspace())
                and (j == len(text) or text[j].isspace())):
            found = i
    return found


_REG = re.compile(r"([A-Za-z][A-Za-z0-9_]*)\s+in\s+C\^([0-9]+)\Z")
_ITEM = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*)\s*:(?!=)\s*(.*)\Z", re.S)


def assumption(text):
    """'name: J for s in I' -> a problem file's assume item (p1_expected
    E155); J is a law or order judgement, or 'v in C^k' for a reg."""
    m = _ITEM.match(text)
    if not m:
        raise HeaderError(f"assuming: {text.strip()!r} is not 'name: J for "
                          "s in I'")
    name, rest = m.group(1), m.group(2).strip()
    k = _last_functions(rest, "for")
    if k <= 0:
        raise HeaderError(f"assuming {name}: expected 'J for s in I'")
    j, where = rest[:k].strip(), rest[k + 3:].strip()
    var, _, iv = where.partition(" in ")
    if not script._NAME.match(var.strip()) or not iv.strip():
        raise HeaderError(f"assuming {name}: expected 'for s in I', not "
                          f"{where!r}")
    item = {"name": name, "var": var.strip(), "in": iv.strip()}
    r = _REG.match(j)
    if r:
        item["reg"] = {"fn": r.group(1), "class": int(r.group(2))}
    else:
        item["law"] = j
    return item


def header(sentence):
    """{"problem": id} or {"goal": g, "functions": {name: arity}}."""
    text = script.strip_sentence(sentence)
    word, _, rest = text.partition(" ")
    rest = rest.strip()
    if word == "problem":
        if not _ID.match(rest):
            raise HeaderError(f"problem: {rest!r} is not a problem id")
        return {"problem": rest}
    if word == "goal":
        fns, assume = {}, []
        a = _last_functions(rest, "assuming")
        if a > 0:
            assume = [assumption(t) for t in
                      script._split_top(rest[a + len("assuming"):], ";")
                      if t.strip()]
            if not assume:
                raise HeaderError("assuming: no assumption follows")
            rest = rest[:a].strip()
        k = _last_functions(rest)
        if k > 0:
            for item in rest[k + len("functions"):].split(","):
                m = _FN.match(item.strip())
                if not m or int(m.group(2)) < 1:
                    raise HeaderError(f"functions: {item.strip()!r} is not "
                                      "name/arity")
                fns[m.group(1)] = int(m.group(2))
            rest = rest[:k].strip()
        if not rest:
            raise HeaderError("goal: the goal is missing")
        out = {"goal": rest, "functions": fns}
        return dict(out, assume=assume) if assume else out
    raise HeaderError(f"the first sentence of a .dx file names the goal: "
                      f"{FORMS}")


def show_header(h):
    """The header sentence for h, with its final '.'."""
    if "problem" in h:
        return f"problem {h['problem']}."
    fns = ", ".join(f"{k}/{v}" for k, v in h.get("functions", {}).items())
    items = "; ".join(show_assumption(a) for a in h.get("assume", ()))
    return (f"goal {h['goal']}" + (f" functions {fns}" if fns else "")
            + (f" assuming {items}" if items else "") + ".")


def show_assumption(a):
    j = a["law"] if "law" in a else \
        f"{a['reg']['fn']} in C^{a['reg']['class']}"
    return f"{a['name']}: {j} for {a['var']} in {a['in']}"
