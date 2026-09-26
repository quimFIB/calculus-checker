"""The tactic script (app/SCRIPT.md): one sentence <-> (move, args).

Untrusted. `parse` turns a tactic into the problem-file shapes the loader
reads (ARCHITECTURE.md §9); `show` prints them back. Terms stay strings
here: the trusted parser reads them when the step is fed.
"""

import re

KEYWORDS = ("by", "using", "with", "at", "occurrence", "as", "from", "to",
            "reverse", "in", "derivs", "increasing", "decreasing",
            "strictly", "scale")
SENSES = ("increasing", "decreasing")  # taylor_lagrange's flag clauses
_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")

# move -> (clauses allowed, clauses required)
FORMS = {
    "ftc": ({"occurrence", "by", "using"}, set()),
    "int_improper": ({"occurrence", "by", "using"}, set()),
    "close": ({"by", "using"}, set()),
    "rewrite": ({"with", "at", "occurrence"}, {"at"}),
    "fact": ({"with"}, set()),
    "int_subst": ({"as", "from", "to", "reverse", "occurrence", "by",
                   "using"}, {"as", "from", "to"}),
    "int_flip": ({"occurrence"}, set()),
    "int_parts": ({"in", "with", "occurrence", "by", "using"},
                  {"in", "with"}),
    "taylor_lagrange": ({"in", "from", "to", "at", "derivs", *SENSES,
                         "strictly", "by", "using"},
                        {"in", "from", "to", "at", "derivs"}),
    "bound": ({"scale", "by", "using"}, {"using"}),
    "verify": ({"by", "using"}, set()),
}
USAGE = {
    "ftc": "ftc T [occurrence N] [by ring|field] [using h, ...]",
    "int_improper": "int_improper T [occurrence N] [by ring|field] "
                    "[using h, ...]",
    "close": "close T [by ring|field] [using h, ...]",
    "rewrite": "rewrite E [with x := T; ...] at T [occurrence N]",
    "fact": "fact h := E [with x := T; ...]",
    "int_subst": "int_subst x := T as y from T to T [reverse T] "
                 "[occurrence N] [by ring|field] [using h, ...]",
    "int_flip": "int_flip [occurrence N]",
    "int_parts": "int_parts in x with u := T; v := T [occurrence N] "
                 "[by ring|field] [using h, ...]",
    "taylor_lagrange": "taylor_lagrange h := lower|upper of T in u from T "
                       "to T at T derivs T; T; ... [strictly] "
                       "increasing|decreasing [by ring|field] [using h, ...]",
    "bound": "bound [scale T] [by ring|field] using h, ...",
    "verify": "verify [by ring|field] [using h, ...]",
}

# PRETTY.md, autocomplete: each move's shape with a `_` hole for every
# required term; names are placeholders to overwrite. Every template parses.
TEMPLATES = {
    "ftc": "ftc _ by ring.",
    "int_improper": "int_improper _ by field.",
    "close": "close _ by ring.",
    "rewrite": "rewrite entry at _.",
    "fact": "fact h := entry with a := _.",
    "int_subst": "int_subst x := _ as t from _ to _ by ring.",
    "int_flip": "int_flip.",
    "int_parts": "int_parts in x with u := _; v := _ by ring.",
    "taylor_lagrange": "taylor_lagrange h := lower of _ in u from _ to _ at _ "
                       "derivs _; _ increasing by field.",
    "bound": "bound by field using h.",
    "verify": "verify by field.",
}


class TacticError(Exception):
    """A sentence that fits no form: refused 'bad-tactic' by the API."""


def _depth_scan(text):
    """(index, char, depth before it) for each char of text."""
    depth = 0
    for i, c in enumerate(text):
        yield i, c, depth
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)


def _split_top(text, sep):
    """text split at `sep` (one char) at bracket depth 0."""
    parts, start = [], 0
    for i, c, d in _depth_scan(text):
        if c == sep and d == 0:
            parts.append(text[start:i])
            start = i + 1
    parts.append(text[start:])
    return parts


def _clauses(text, allowed):
    """(head, {clause: text}): text split at the allowed clause words, whole
    words at depth 0 only (SCRIPT.md)."""
    cuts = []
    n = len(text)
    for i, c, d in _depth_scan(text):
        if d or (i and not text[i - 1].isspace()):
            continue
        for w in allowed:
            j = i + len(w)
            if text.startswith(w, i) and (j == n or text[j].isspace()):
                cuts.append((i, w))
                break
    head_end = cuts[0][0] if cuts else n
    out = {}
    for k, (i, w) in enumerate(cuts):
        end = cuts[k + 1][0] if k + 1 < len(cuts) else n
        if w in out:
            raise TacticError(f"'{w}' appears twice")
        out[w] = text[i + len(w):end].strip()
    return text[:head_end].strip(), out


def _term(s, what):
    if not s:
        raise TacticError(f"{what}: a term is missing")
    return s


def _name(s, what):
    if not _NAME.match(s):
        raise TacticError(f"{what}: {s!r} is not a name")
    return s


def _assign(s, what):
    """'x := T' -> (x, T)."""
    parts = s.split(":=", 1)
    if len(parts) != 2:
        raise TacticError(f"{what}: expected 'name := term'")
    return _name(parts[0].strip(), what), _term(parts[1].strip(), what)


def _inst(s):
    out = {}
    for item in _split_top(s, ";"):
        if item.strip():
            k, v = _assign(item.strip(), "with")
            if k in out:
                raise TacticError(f"with: {k} is bound twice")
            out[k] = v
    return out


def _facts(s):
    return [["handle", _name(h.strip(), "using")]
            for h in _split_top(s, ",") if h.strip()] if s else []


def _occurrence(s):
    if not s.isdigit():
        raise TacticError(f"occurrence: {s!r} is not a natural number")
    return int(s)


def strip_sentence(text):
    """The tactic without comments, surrounding space and its final '.'."""
    text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S).strip()
    if text.endswith(".") and not text.endswith(".."):
        text = text[:-1].rstrip()
    return text


def parse(text):
    """One sentence -> (move, args). Raises TacticError."""
    text = strip_sentence(text)
    if not text:
        raise TacticError("an empty sentence")
    move, _, rest = text.partition(" ")
    if move not in FORMS:
        raise TacticError(f"{move!r} is not a move; the moves are "
                          + ", ".join(FORMS))
    allowed, required = FORMS[move]
    try:
        head, cl = _clauses(rest.strip(), allowed)
        missing = required - set(cl)
        if missing:
            raise TacticError(f"missing {', '.join(sorted(missing))}")
        args = _build(move, head, cl)
    except TacticError as e:
        raise TacticError(f"{e} (expected: {USAGE[move]})") from None
    return move, args


def _checked(args, cl):
    c = cl.get("by", "ring")
    if c not in ("ring", "field"):
        raise TacticError(f"by: {c!r} is neither ring nor field")
    args["check"] = c
    args["facts"] = _facts(cl.get("using", ""))
    return args


def _build(move, head, cl):
    occ = {"occurrence": _occurrence(cl["occurrence"])} \
        if "occurrence" in cl else {}
    if move in ("ftc", "int_improper"):
        return _checked({"F": _term(head, move), **occ}, cl)
    if move == "close":
        return _checked({"value": _term(head, move)}, cl)
    if move == "rewrite":
        return {"entry": _name(head, "rewrite"),
                "inst": _inst(cl.get("with", "")),
                "at": _term(cl["at"], "at"), **occ}
    if move == "fact":
        h, e = _assign(head, "fact")
        return {"entry": _name(e, "fact"), "inst": _inst(cl.get("with", "")),
                "bind": h}
    if move == "int_subst":
        var, sub = _assign(head, "int_subst")
        args = {"var": var, "sub": sub, "new_var": _name(cl["as"], "as"),
                "lo": _term(cl["from"], "from"), "hi": _term(cl["to"], "to")}
        if "reverse" in cl:
            args = {"mode": "reverse", **args,
                    "f": _term(cl["reverse"], "reverse")}
        return _checked({**args, **occ}, cl)
    if move == "int_flip":
        if head:
            raise TacticError(f"unexpected {head!r}")
        return occ
    if move == "taylor_lagrange":
        return _taylor(head, cl)
    if move in ("bound", "verify"):  # p1_expected E99, E112
        if head:
            raise TacticError(f"unexpected {head!r}")
        scale = ({"scale": _term(cl["scale"], "scale")} if "scale" in cl
                 else {})  # E139
        return _checked(scale, cl)
    # int_parts
    if head:
        raise TacticError(f"unexpected {head!r}")
    inst = _inst(cl["with"])
    if set(inst) != {"u", "v"}:
        raise TacticError("with: name exactly u and v")
    return _checked({"var": _name(cl["in"], "in"), "u": inst["u"],
                     "v": inst["v"], **occ}, cl)


def _taylor(head, cl):
    """'h := lower of T' plus the clauses; exactly one sense flag, which
    takes no text."""
    h, rest = _assign(head, "taylor_lagrange")
    side, _, f = rest.partition(" ")
    f = f.strip()
    if side not in ("lower", "upper") or not f.startswith("of "):
        raise TacticError("expected 'h := lower of T' or 'h := upper of T'")
    senses = [s for s in SENSES if s in cl]
    if len(senses) != 1 or cl[senses[0]]:
        raise TacticError("say increasing or decreasing, once, alone")
    if cl.get("strictly"):
        raise TacticError("strictly takes no text: 'strictly increasing'")
    sense = ("strictly " if "strictly" in cl else "") + senses[0]  # E138
    derivs = [_term(d.strip(), "derivs") for d in _split_top(cl["derivs"], ";")
              if d.strip()]
    return _checked({"bind": h, "f": _term(f[3:].strip(), "of"),
                     "var": _name(cl["in"], "in"),
                     "lo": _term(cl["from"], "from"),
                     "hi": _term(cl["to"], "to"), "at": _term(cl["at"], "at"),
                     "derivs": derivs, "side": side, "sense": sense}, cl)


# ---------------------------------------------------------------- printing

def _show_inst(inst):
    return "; ".join(f"{k} := {v}" for k, v in inst.items())


def _tail(args):
    out = f" by {args.get('check', 'ring')}"
    facts = args.get("facts") or []
    if facts:
        out += " using " + ", ".join(f[1] for f in facts)
    return out


def show(move, args):
    """(move, args) -> the canonical sentence, with its final '.'."""
    occ = (f" occurrence {args['occurrence']}"
           if "occurrence" in args else "")
    if move in ("ftc", "int_improper"):
        s = f"{move} {args['F']}{occ}{_tail(args)}"
    elif move == "close":
        s = f"close {args['value']}{_tail(args)}"
    elif move == "rewrite":
        w = f" with {_show_inst(args['inst'])}" if args.get("inst") else ""
        s = f"rewrite {args['entry']}{w} at {args['at']}{occ}"
    elif move == "fact":
        w = f" with {_show_inst(args['inst'])}" if args.get("inst") else ""
        s = f"fact {args['bind']} := {args['entry']}{w}"
    elif move == "int_subst":
        rev = f" reverse {args['f']}" if args.get("mode") == "reverse" else ""
        s = (f"int_subst {args['var']} := {args['sub']} as {args['new_var']}"
             f" from {args['lo']} to {args['hi']}{rev}{occ}{_tail(args)}")
    elif move == "int_flip":
        s = f"int_flip{occ}"
    elif move == "int_parts":
        s = (f"int_parts in {args['var']} with u := {args['u']}; "
             f"v := {args['v']}{occ}{_tail(args)}")
    elif move == "taylor_lagrange":
        s = (f"taylor_lagrange {args['bind']} := {args['side']} of "
             f"{args['f']} in {args['var']} from {args['lo']} to "
             f"{args['hi']} at {args['at']} derivs "
             f"{'; '.join(args['derivs'])} {args['sense']}{_tail(args)}")
    elif move in ("bound", "verify"):
        sc = f" scale {args['scale']}" if "scale" in args else ""
        s = f"{move}{sc}{_tail(args)}"
    else:
        raise ValueError(f"no tactic form for {move!r}")
    return s + "."


# ---------------------------------------------------------------- splitting

# the whitespace both splitters use: ASCII only, so that Python's isspace
# and JavaScript's \s cannot disagree (PERSIST.md)
SPACE = " \t\n\r\f\v"


def next_sentence(text, start_at=0):
    """The page's nextSentence, ported (PERSIST.md): (start, end) of the
    first sentence at or after start_at, or None. A sentence ends at a '.'
    followed by whitespace or the end, outside (* *) comments, never inside
    '..'; start is its first character outside a comment."""
    i, start = start_at, -1
    while i < len(text):
        if text.startswith("(*", i):
            j = text.find("*)", i + 2)
            if j < 0:
                return None
            i = j + 2
            continue
        c = text[i]
        if start < 0 and c not in SPACE:
            start = i
        if (c == "." and (i == 0 or text[i - 1] != ".")
                and text[i + 1:i + 2] != "."
                and (i + 1 == len(text) or text[i + 1] in SPACE)):
            return None if start < 0 else (start, i + 1)
        i += 1
    return None


def spans(text):
    """(start, end) of every complete sentence of a script, in order."""
    out, at = [], 0
    while True:
        s = next_sentence(text, at)
        if s is None:
            return out
        out.append(s)
        at = s[1]


def sentences(text):
    """Every complete sentence of a script, as its text, in order."""
    return [text[a:b] for a, b in spans(text)]


# ---------------------------------------------------------------- layout

def _trim(text, a, b):
    """(a, b) shrunk past whitespace at both ends."""
    while a < b and text[a] in SPACE:
        a += 1
    while b > a and text[b - 1] in SPACE:
        b -= 1
    return a, b


def _cuts(text, a, b, allowed):
    """(start, word) of each clause word in text[a:b], as _clauses finds
    them: whole words at bracket depth 0, after whitespace."""
    out = []
    for i, c, d in _depth_scan(text[a:b]):
        if d or (i and not text[a + i - 1].isspace()):
            continue
        for w in allowed:
            j = a + i + len(w)
            if text.startswith(w, a + i) and (j == b or text[j].isspace()):
                out.append((a + i, w))
                break
    return out


def _items(text, a, b):
    """The value span of each `name := T` item (or bare T) in text[a:b],
    split at depth-0 ';'."""
    out, start = [], a
    for i, c, d in _depth_scan(text[a:b] + ";"):
        if c == ";" and d == 0:
            s, e = start, a + i
            k = text.find(":=", s, e)
            out.append(_trim(text, k + 2 if k >= 0 else s, e))
            start = a + i + 1
    return [x for x in out if x[0] < x[1]]


def layout(sentence):
    """PRETTY.md: the sentence cut into segments {"text": s}, {"term": s},
    {"name": s} and {"choice": s, "options": [...]}, in order, whose texts
    concatenate to the sentence exactly. A sentence that
    parse refuses, or that holds a comment, is one text segment."""
    whole = [{"text": sentence}]
    if "(*" in sentence:
        return whole
    try:
        move, _ = parse(sentence)
    except TacticError:
        return whole
    a, end = _trim(sentence, 0, len(sentence))
    if sentence[end - 1:end] == "." and sentence[end - 2:end] != "..":
        end -= 1
    start = a + len(move)
    cuts = _cuts(sentence, start, end, FORMS[move][0])
    bounds = [c[0] for c in cuts] + [end]
    head = _trim(sentence, start, bounds[0])
    clause = {w: _trim(sentence, i + len(w), bounds[k + 1])
              for k, (i, w) in enumerate(cuts)}
    spans = []  # (start, end, kind): term, name or choice

    def term(span):
        spans.append((*span, "term"))

    def name(span):
        spans.append((*span, "name"))

    def before_assign(span):
        """The name before ':=' in span, and the text after it."""
        k = sentence.find(":=", *span)
        name(_trim(sentence, span[0], k))
        return _trim(sentence, k + 2, span[1])

    if move in ("ftc", "int_improper", "close"):
        term(head)
    elif move == "rewrite":
        name(head)
        for it in _items(sentence, *clause.get("with", (0, 0))):
            term(it)
        term(clause["at"])
    elif move == "fact":
        name(before_assign(head))
        for it in _items(sentence, *clause.get("with", (0, 0))):
            term(it)
    elif move == "int_subst":
        term(before_assign(head))
        name(clause["as"])
        for w in ("from", "to", "reverse"):
            if w in clause:
                term(clause[w])
    elif move == "int_parts":
        name(clause["in"])
        for it in _items(sentence, *clause["with"]):
            term(it)
    elif move == "taylor_lagrange":
        rest = before_assign(head)
        k = sentence.find(" of ", *rest)
        spans.append((rest[0], k, "choice:lower|upper"))
        term(_trim(sentence, k + 4, rest[1]))
        name(clause["in"])
        for w in ("from", "to", "at"):
            term(clause[w])
        for it in _items(sentence, *clause["derivs"]):
            term(it)
        for i, w in cuts:
            if w in SENSES:
                spans.append((i, i + len(w), "choice:increasing|decreasing"))
    if move == "bound" and "scale" in clause:
        term(clause["scale"])
    if "occurrence" in clause:
        name(clause["occurrence"])
    if "by" in clause:
        spans.append((*clause["by"], "choice:ring|field"))
    if "using" in clause:
        base, b0 = clause["using"]
        a0 = base
        for i, c, d in _depth_scan(sentence[base:b0] + ","):
            if c == "," and d == 0:
                name(_trim(sentence, a0, base + i))
                a0 = base + i + 1
    out, at = [], 0
    for s, e, kind in sorted(spans):
        if s >= e:
            continue
        if s > at:
            out.append({"text": sentence[at:s]})
        if kind.startswith("choice:"):
            out.append({"choice": sentence[s:e],
                        "options": kind[7:].split("|")})
        else:
            out.append({kind: sentence[s:e]})
        at = e
    if at < len(sentence):
        out.append({"text": sentence[at:]})
    return out
