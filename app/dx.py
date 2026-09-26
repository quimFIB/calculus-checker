"""A .dx file's header sentence (app/DX.md): read and print.

Untrusted. The header names the goal a .dx script proves: `problem ID.`
or `goal G [functions f/1, g/2].` The goal itself is read by the trusted
parser when /session installs it.
"""

import re

import script

FORMS = "'problem ID.' or 'goal G.' (optionally 'goal G functions f/1, g/2.')"
_ID = re.compile(r"[A-Za-z0-9_.-]+\Z")
_FN = re.compile(r"([A-Za-z][A-Za-z0-9_]*)\s*/\s*([0-9]+)\Z")


class HeaderError(Exception):
    """Not a header: refused 'bad-header' by the API."""


def _last_functions(text):
    """The start of the last depth-0 word `functions`, or -1 (DX.md
    review 3: a declared function may itself be called functions)."""
    found = -1
    for i, c, d in script._depth_scan(text):
        j = i + len("functions")
        if (d == 0 and text.startswith("functions", i)
                and (i == 0 or text[i - 1].isspace())
                and (j == len(text) or text[j].isspace())):
            found = i
    return found


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
        fns = {}
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
        return {"goal": rest, "functions": fns}
    raise HeaderError(f"the first sentence of a .dx file names the goal: "
                      f"{FORMS}")


def show_header(h):
    """The header sentence for h, with its final '.'."""
    if "problem" in h:
        return f"problem {h['problem']}."
    fns = ", ".join(f"{k}/{v}" for k, v in h.get("functions", {}).items())
    return f"goal {h['goal']}" + (f" functions {fns}" if fns else "") + "."
