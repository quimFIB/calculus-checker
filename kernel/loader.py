"""Problem files (DESIGN.md §16.4): read one, and feed its proofs to the kernel.

Untrusted. It parses strings into terms and passes them to `kernel.install`
and `kernel.step`, and nothing else: it never builds a state, an obligation,
a handle or a verdict, so no bug here can produce a theorem. A misread file
is a different problem, which the kernel then checks as it would any other.
The goal still parses through `terms.parse_goal`, which is trusted
(§15.2 item 8).

A file is JSON with the keys kernel/problems/stage0/expected.py's PF2 lists:

  format          "calc-problem/0"
  id, title, source, statement, notes    prose, not read here
  goal            GRAMMAR.md syntax, parsed with sig = declarations.functions
  answer_schema   "closed", the only schema the kernel has (E23)
  declarations    {"functions": {name: arity}}
  reference_proof [step, ...]
  alternative_proofs (optional) {name: {"why": prose, "steps": [step, ...]}}
  assume          (optional) Γ, p1_expected E155: [{name, var, in, law | reg}]

Every object's key set is closed, at every level (a step is exactly {id,
move, args}, declarations exactly {functions}, an alternative exactly {why,
steps}), a repeated key is refused, and no alternative is named
"reference". A step is {"id", "move", "args"}. args is kernel/ARCHITECTURE.md §4's, with
every term as a GRAMMAR.md string (int_subst's sub, lo, hi and f among them,
its var, new_var and mode names as strings) and a fact as ["handle", name]: the handle
the earlier fact step with that `bind` minted. The client must never show
reference_proof to a learner (PF1); nothing here reads it except to replay.
"""

import json
from dataclasses import dataclass

import kernel as K
from terms import Call, Reg, Var, parse_goal, parse_judgement, parse_term

FORMAT = "calc-problem/0"
KEYS = frozenset(("format", "id", "title", "source", "statement", "goal",
                  "answer_schema", "declarations", "reference_proof",
                  "alternative_proofs", "notes", "assume"))
OPTIONAL = frozenset(("alternative_proofs", "notes", "assume"))
STEP_KEYS = frozenset(("id", "move", "args"))
ALT_KEYS = frozenset(("why", "steps"))
DECL_KEYS = frozenset(("functions",))
REFERENCE = "reference"  # the name `proofs` gives reference_proof
# The type of each args value step_args reads (ARCHITECTURE.md §4). Any
# other key passes through, for the kernel to refuse 'bad-args'.
ARG_TYPES = {"at": str, "F": str, "value": str, "inst": dict, "facts": list,
             "entry": str, "bind": str, "check": str, "occurrence": int,
             # int_subst's (p1_expected INT_SUBST_ARGS, _REVERSE, _OPTIONAL)
             "var": str, "new_var": str, "sub": str, "lo": str, "hi": str,
             "f": str, "mode": str,
             "u": str, "v": str,  # int_parts' (p1_expected section 19)
             "derivs": list, "side": str, "sense": str,  # section 25
             "scale": str,  # section 28 (E139)
             # section 30's ODE rules (E149)
             "law": str, "kin": str, "regs": list, "using": list,
             "range": str}
# The args that are GRAMMAR.md strings for terms, parsed with the file's sig.
TERM_ARGS = ("at", "F", "value", "sub", "lo", "hi", "f", "u", "v", "scale")


@dataclass(frozen=True)
class Problem:
    id: str
    goal_text: str
    sig: dict  # declarations.functions, the parser's sig
    proofs: dict  # REFERENCE or an alternative's name -> tuple of step dicts
    assume: tuple = ()  # the file's 'assume' items, as written (E155)

    def goal(self):
        return parse_goal(self.goal_text, self.sig)

    def assumptions(self):
        """Γ as kernel.Assumption values (E155)."""
        return assumptions(list(self.assume), self.sig)


def _no_duplicates(pairs):
    """json's object_pairs_hook: a repeated key is refused, never
    last-one-wins, so a file cannot carry two goals."""
    out = {}
    for k, v in pairs:
        if k in out:
            raise ValueError(f"duplicate key {k!r}")
        out[k] = v
    return out


def _is(v, t):
    """isinstance, with bool not counting as int."""
    return isinstance(v, t) and not (t is int and isinstance(v, bool))


def _obj(v, keys, optional, what):
    """v is a JSON object with the keys `keys`, those in `optional` allowed
    to be absent, and no others."""
    if not isinstance(v, dict):
        raise ValueError(f"{what} is not an object")
    missing, extra = keys - optional - set(v), set(v) - keys
    if missing or extra:
        raise ValueError(f"{what}: missing {sorted(missing)}, unknown "
                         f"{sorted(extra)}")
    return v


def _steps(v, what):
    """A proof: a list of {id, move, args} with distinct string ids, and
    each args value step_args reads of the type it reads."""
    if not isinstance(v, list):
        raise ValueError(f"{what} is not a list of steps")
    ids = set()
    for n, s in enumerate(v):
        _obj(s, STEP_KEYS, frozenset(), f"{what} step {n}")
        if not (_is(s["id"], str) and _is(s["move"], str)
                and isinstance(s["args"], dict)) or s["id"] in ids:
            raise ValueError(f"{what} step {n}: id and move are strings, ids "
                             "are distinct, and args is an object")
        ids.add(s["id"])
        for k, t in ARG_TYPES.items():
            if k in s["args"] and not _is(s["args"][k], t):
                raise ValueError(f"{what} {s['id']}: {k} is not a {t.__name__}")
        inst, facts = s["args"].get("inst", {}), s["args"].get("facts", [])
        if not all(_is(x, str) for kv in inst.items() for x in kv):
            raise ValueError(f"{what} {s['id']}: inst maps names to terms")
        if not all(isinstance(f, list) and len(f) == 2 and f[0] == "handle"
                   and _is(f[1], str) for f in facts):
            raise ValueError(f"{what} {s['id']}: a fact is ['handle', name]")
    return tuple(v)


def load(path):
    """Read and shape-check one problem file. Every way a file can be
    malformed raises ValueError: bad JSON, a repeated key, a missing or
    unknown key at any level, a value of the wrong type, a duplicate step
    id, or an alternative named REFERENCE. Its terms are parsed only when
    used, by the trusted parser, whose refusals keep their GRAMMAR codes."""
    try:
        with open(path, encoding="utf-8") as f:
            raw = json.load(f, object_pairs_hook=_no_duplicates)
        return _problem(raw)
    except ValueError as e:  # json.JSONDecodeError is one
        raise ValueError(f"{path}: not a {FORMAT} file: {e}") from None


def _problem(raw):
    _obj(raw, KEYS, OPTIONAL, "the file")
    # "none": an order goal has no ?A (p1_expected E96)
    if raw["format"] != FORMAT or raw["answer_schema"] not in ("closed", "none"):
        raise ValueError(f"format {raw['format']!r}, answer schema "
                         f"{raw['answer_schema']!r}")
    for k in ("id", "title", "source", "statement", "goal"):
        if not _is(raw[k], str):
            raise ValueError(f"{k} is not a string")
    if not (isinstance(raw.get("notes", []), list)
            and all(_is(n, str) for n in raw.get("notes", []))):
        raise ValueError("notes is not a list of strings")
    fns = _obj(raw["declarations"], DECL_KEYS, frozenset(),
               "declarations")["functions"]
    if not (isinstance(fns, dict)
            and all(_is(a, int) and a > 0 for a in fns.values())):
        raise ValueError("declarations.functions maps names to arities")
    proofs = {REFERENCE: _steps(raw["reference_proof"], "reference_proof")}
    alts = raw.get("alternative_proofs", {})
    if not isinstance(alts, dict):
        raise ValueError("alternative_proofs is not an object")
    for name, alt in alts.items():
        if name == REFERENCE:
            raise ValueError(f"an alternative may not be named {REFERENCE!r}")
        _obj(alt, ALT_KEYS, frozenset(), f"alternative {name}")
        if not _is(alt["why"], str):
            raise ValueError(f"alternative {name}: why is not a string")
        proofs[name] = _steps(alt["steps"], f"alternative {name}")
    assume = raw.get("assume", [])
    if not isinstance(assume, list):
        raise ValueError("assume is not a list")
    return Problem(raw["id"], raw["goal"], dict(fns), proofs, tuple(assume))


def step_args(args, handles, sig):
    """A file's args dict as kernel.step takes it: terms parsed with `sig`,
    and each ["handle", name] replaced by handles[name]. Every other value
    passes through unchanged, for the kernel to check."""
    out = {}
    for k, v in args.items():
        if k in TERM_ARGS:
            out[k] = parse_term(v, sig)
        elif k == "inst":
            out[k] = {var: parse_term(s, sig) for var, s in v.items()}
        elif k == "facts":
            out[k] = [_fact_ref(f, handles) for f in v]
        elif k == "derivs" and isinstance(v, list) \
                and all(isinstance(s, str) for s in v):  # section 25
            out[k] = [parse_term(s, sig) for s in v]
        elif k == "range" and isinstance(v, str) \
                and isinstance(args.get("var"), str):  # section 30
            out[k] = interval(args["var"], v, sig)
        else:  # entry, bind, check, occurrence, and int_subst's var,
            out[k] = v  # new_var and mode, which the kernel reads as names
    return out


def interval(var, text, sig):
    """An interval as a domain item writes it ('[0, oo)'), on var: parsed
    as the one item of `var == var @ var in TEXT`."""
    g = parse_goal(f"{var} == {var} @ {var} in {text}", sig)
    if len(g[0].dom) != 1:
        raise ValueError(f"{text!r} is not one interval")
    return g[0].dom[0]


ASSUME_KEYS = frozenset(("name", "var", "in", "law", "reg"))
REG_KEYS = frozenset(("fn", "class"))


def assumptions(items, sig):
    """A file's 'assume' list (p1_expected E155) as kernel.Assumption
    values: each {name, var, in, and law or reg}, `in` an interval as a
    domain item writes it, `law` a judgement, `reg` {fn, class}. Shapes are
    checked here; what the items say, the kernel checks at install
    (E148)."""
    if not isinstance(items, list):
        raise ValueError("assume is not a list")
    out = []
    for n, a in enumerate(items):
        if not isinstance(a, dict) or set(a) - ASSUME_KEYS \
                or not {"name", "var", "in"} <= set(a) \
                or ("law" in a) == ("reg" in a):
            raise ValueError(f"assume {n}: {{name, var, in, and law or "
                             "reg}}")
        if not all(_is(a[k], str) for k in ("name", "var", "in")):
            raise ValueError(f"assume {n}: name, var and in are strings")
        i = interval(a["var"], a["in"], sig)
        if "law" in a:
            if not _is(a["law"], str):
                raise ValueError(f"assume {n}: law is a string")
            j = parse_judgement(a["law"], sig)
        else:
            r = a["reg"]
            if not (isinstance(r, dict) and set(r) == REG_KEYS
                    and _is(r["fn"], str) and _is(r["class"], int)):
                raise ValueError(f"assume {n}: reg is {{fn, class}}")
            j = Reg(Call(r["fn"], (Var(a["var"]),)), r["class"])
        out.append(K.Assumption(a["name"], a["var"], i, j))
    return tuple(out)


def _fact_ref(ref, handles):
    if not (isinstance(ref, list) and len(ref) == 2 and ref[0] == "handle"):
        raise ValueError(f"a fact is ['handle', name], not {ref!r}")
    if ref[1] not in handles:
        raise ValueError(f"no earlier fact step binds {ref[1]!r}")
    return handles[ref[1]]


def feed(state, s, handles, sig):
    """One step dict to kernel.step. Returns what the kernel returned, a
    ProofState or a Refusal. A fact step's handle is recorded under its
    `bind`, read from the kernel's own StepRecord."""
    r = K.step(state, s["move"], step_args(s["args"], handles, sig))
    if s["move"] in ("fact", "taylor_lagrange", "quad_t", "sep_autonomous",
                     "energy_integral") and isinstance(r, K.ProofState):
        handles[s["args"]["bind"]] = r.last.handle
    return r


def replay(problem, proof=REFERENCE, through=None):
    """Install the problem's goal and feed `proof`'s steps in order, up to
    and including the step with id `through` (all of them when None).

    Returns (results, handles). results is a list of (step id, result):
    ("goal", install's result) first, then one pair per step fed. It stops
    after the first Refusal, which is the last result."""
    steps = problem.proofs[proof]
    if through is not None and through not in [s["id"] for s in steps]:
        raise ValueError(f"{problem.id} {proof} has no step {through!r}")
    st = K.install(problem.goal(), problem.assumptions())
    results, handles = [("goal", st)], {}
    for s in steps:
        if not isinstance(st, K.ProofState) or results[-1][0] == through:
            break
        st = feed(st, s, handles, problem.sig)
        results.append((s["id"], st))
    return results, handles
