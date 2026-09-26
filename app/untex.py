"""MathLive's LaTeX -> GRAMMAR.md text (app/PRETTY.md).

Untrusted. The pretty editor's fields hold LaTeX; this reads a term out of
it, writes GRAMMAR.md text with every group parenthesised, and the trusted
parser has the last word (`terms.show` of its result is the answer). A
reading never guesses where the grammar refuses: D4's `xy`, D5's `x(…)` and
D6's `sin(x)^2` are refused here too (PRETTY.md, review 1 and 2).
"""

import re

from session import KERNEL  # noqa: F401  (puts kernel/ on the path)
from terms import parse_term

GREEK = ("alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu "
         "nu xi rho sigma tau upsilon phi chi psi omega").split()
FNS = {r"\sin": "sin", r"\cos": "cos", r"\tan": "tan", r"\exp": "exp",
       r"\ln": "ln", r"\arcsin": "asin", r"\arccos": "acos",
       r"\arctan": "atan", r"\sinh": "sinh", r"\cosh": "cosh",
       r"\tanh": "tanh", r"\log": "ln"}
BUILTIN = ("sin cos tan asin acos atan exp ln sqrt abs sinh cosh tanh asinh "
           "acosh atanh").split()
NAMED = {"arsinh": "asinh", "arcosh": "acosh", "artanh": "atanh",
         "arcsinh": "asinh", "arccosh": "acosh", "arctanh": "atanh",
         "arcsin": "asin", "arccos": "acos", "arctan": "atan"}
SKIP = {r"\,", r"\;", r"\:", r"\!", r"\ ", r"\quad", r"\qquad",
        r"\displaystyle", r"\textstyle", r"\limits", r"\nolimits"}
OPEN = {"(": ")", "[": "]", "{": "}"}
LEFT = {"(": ")", "[": "]", r"\lbrack": r"\rbrack", r"\{": r"\}"}
ABS = {"|": "|", r"\vert": r"\vert", r"\lvert": r"\rvert", r"\|": r"\|"}
DIFF = ("d", r"\differentialD")

_TOKEN = re.compile(r"\\[A-Za-z]+|\\.|[0-9]+|[A-Za-z]|\S")


class TexError(Exception):
    """LaTeX that is no term: refused 'bad-tex' by the API."""


def _p(s):
    return "(" + s + ")"


class _Reader:
    def __init__(self, latex, sig):
        self.toks = [t for t in _TOKEN.findall(latex) if t not in SKIP]
        self.i = 0
        self.sig = sig or {}
        self.in_int = 0

    # -------------------------------------------------- tokens

    def peek(self, k=0):
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else None

    def take(self, want=None):
        tok = self.peek()
        if tok is None or want is not None and tok != want:
            raise TexError(f"expected {want or 'more'}, found "
                           f"{tok or 'the end'}")
        self.i += 1
        return tok

    def raw_group(self):
        """A {...} group's tokens joined (names, \\operatorname)."""
        if self.peek() != "{":
            return self.take()
        self.take("{")
        depth, out = 0, []
        while not (self.peek() == "}" and depth == 0):
            tok = self.take()
            depth += {"{": 1, "}": -1}.get(tok, 0)
            out.append(tok)
        self.take("}")
        return "".join(out).replace("\\_", "_")

    def arg(self):
        """A command's argument: a {...} group, or one token. One token is
        one digit: MathLive writes \\frac{4}{2} as \\frac42."""
        tok = self.peek()
        if tok is not None and tok.isdigit() and len(tok) > 1:
            self.toks[self.i:self.i + 1] = [tok[0], tok[1:]]
        if self.peek() == "{":
            self.take("{")
            out = self.expr("}")
            self.take("}")
            return out
        return self.factor()

    # -------------------------------------------------- grammar

    def expr(self, stop=None):
        out = self.product(stop)
        while self.peek() in ("+", "-"):
            op = self.take()
            out += " + " if op == "+" else " - "
            out += self.product(stop)
        return out

    def _at_stop(self, stop):
        tok = self.peek()
        if tok is None or tok == stop or tok in (
                "+", "-", "}", ")", "]", r"\right", "|", ",", r"\rvert",
                r"\vert", r"\|", r"\rbrack", "=", "<", ">", r"\le", r"\ge",
                r"\leq", r"\geq"):
            return True
        return self.in_int and self._differential()

    def _differential(self):
        """At `d x`, `\\mathrm{d}x`, `\\differentialD x`: the end of an
        integrand."""
        tok, nxt = self.peek(), self.peek(1)
        if tok in DIFF:
            return nxt is not None and (re.fullmatch(r"[A-Za-z]", nxt)
                                        or nxt[1:] in GREEK or nxt == "{")
        if tok in (r"\mathrm", r"\operatorname", r"\mathit") and \
                self.toks[self.i + 1:self.i + 4] == ["{", "d", "}"]:
            return True
        return False

    def product(self, stop=None):
        out, kind = self.unary(stop)
        while not self._at_stop(stop):
            tok = self.peek()
            if tok in (r"\cdot", r"\times", "*"):
                self.take()
                rhs, kind = self.unary(stop)
                out = f"{out} * {rhs}"
            elif tok in ("/", r"\div"):
                self.take()
                rhs, kind = self.unary(stop)
                out = f"({out}) / ({rhs})"
            else:  # juxtaposition (PRETTY.md review 2)
                if kind == "name" and re.fullmatch(r"[A-Za-z]", tok):
                    raise TexError(f"{out}{tok} is not a name: write "
                                   f"{out}\\cdot {tok} (no implicit "
                                   f"multiplication between letters, D4)")
                rhs, kind = self.unary(stop)
                out = f"{out} * {rhs}"
        return out

    def unary(self, stop=None):
        if self.peek() == "-":
            self.take()
            inner, _ = self.unary(stop)
            return "-" + _p(inner), "neg"
        return self.power()

    def power(self):
        base, kind = self.factor_kind()
        if self.peek() == "^":
            if kind == "app":
                raise TexError("ambiguous: write \\sin(x^2) or "
                               "(\\sin x)^2 (D6)")
            self.take("^")
            exp = self.arg()
            if kind == "e":
                return "exp" + _p(exp), "app"
            return f"({base})^({exp})", "power"
        if kind == "e":
            return base, "name"
        return base, kind

    def factor(self):
        return self.power()[0]

    def _name_suffix(self, base):
        """Digits and a _{...} subscript glued to a letter: one name."""
        if self.peek() is not None and self.peek().isdigit():
            base += self.take()
        if self.peek() == "_":
            self.take("_")
            sub = self.raw_group()
            if not re.fullmatch(r"[A-Za-z0-9_]+", sub):
                raise TexError(f"subscript {sub!r}: letters and digits only")
            base += "_" + sub
        return base

    def _call_or_refuse(self, name):
        """A name right before an open group: a call if declared (D5)."""
        opens = self.peek() == "(" or (self.peek() == r"\left"
                                        and self.peek(1) == "(")
        if opens and name in self.sig:
            return self._call(name)
        if opens:
            raise TexError(f"{name} is not a declared function symbol: "
                           f"write {name}\\cdot(…) (D5)")
        return None

    def _call(self, name):
        inner = self._group_items()
        return f"{name}(" + ", ".join(inner) + ")"

    def _group_items(self):
        """A ( … ) or \\left( … \\right) group, split at depth-0 commas."""
        left = self.take() == r"\left"
        if left:
            self.take("(")
        items = [self.expr()]
        while self.peek() == ",":
            self.take(",")
            items.append(self.expr())
        if left:
            self.take(r"\right")
        self.take(")")
        return items

    def factor_kind(self):
        tok = self.peek()
        if tok is None:
            raise TexError("a term is missing")
        if tok.isdigit():
            self.take()
            if self.peek() == "." and (self.peek(1) or "").isdigit():
                raise TexError("no decimals: write a fraction, as 1/2 (D1)")
            return tok, "num"
        if tok == r"\placeholder":
            raise TexError("fill in the empty box")
        if re.fullmatch(r"[A-Za-z]", tok):
            self.take()
            if tok == "e" and self.peek() == "^":
                return "e", "e"
            name = self._name_suffix(tok)
            call = self._call_or_refuse(name)
            if call is not None:
                return call, "atom"
            # a subscript sets the name off, as v₀t is drawn (not D4's xy)
            return name, "subname" if "_" in name else "name"
        if tok[1:] in GREEK and tok[0] == "\\":
            self.take()
            name = self._name_suffix(tok[1:])
            if self.peek() is not None and self.peek().isdigit():
                name += self.take()
            return name, "greek"
        if tok in (r"\varepsilon", r"\vartheta", r"\varphi"):
            self.take()
            return self._name_suffix(tok[4:]), "greek"
        if tok == r"\pi":
            self.take()
            return "pi", "atom"
        if tok == r"\infty":
            self.take()
            return "oo", "atom"
        if tok == r"\exponentialE":
            self.take()
            return ("e", "e") if self.peek() == "^" else ("e_const", "atom")
        if tok == r"\frac":
            return self._frac()
        if tok in (r"\dfrac", r"\tfrac"):
            self.toks[self.i] = r"\frac"
            return self._frac()
        if tok == r"\sqrt":
            self.take()
            if self.peek() == "[":
                raise TexError("only square roots: \\sqrt[n]{…} is not a "
                               "term here")
            return "sqrt" + _p(self.arg()), "atom"
        if tok == r"\int":
            return self._int(), "atom"
        if tok in FNS:
            self.take()
            return self._apply(FNS[tok])
        if tok in (r"\operatorname", r"\mathrm", r"\mathit",
                   r"\operatorname*"):
            self.take()
            g = self.raw_group()
            if g == "e":
                return ("e", "e") if self.peek() == "^" \
                    else ("e_const", "atom")
            g = NAMED.get(g, g)
            if g in BUILTIN:
                return self._apply(g)
            if g in self.sig:
                if self.peek() not in ("(", r"\left"):
                    raise TexError(f"{g} is a declared function: apply it, "
                                   f"{g}(…)")
                return self._call(g), "atom"
            if tok == r"\mathit" and re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*",
                                                  g):
                call = self._call_or_refuse(g)
                return (call, "atom") if call else (g, "name")
            raise TexError(f"{tok}{{{g}}} is not a function here")
        if tok == r"\left":
            self.take()
            o = self.take()
            if o in ABS:
                inner = self.expr()
                self.take(r"\right")
                self.take(ABS[o])
                return "abs" + _p(inner), "atom"
            if o not in LEFT:
                raise TexError(f"\\left{o} … is not a group here")
            inner = self.expr()
            self.take(r"\right")
            self.take(LEFT[o])
            return _p(inner), "group"
        if tok in OPEN:
            self.take()
            inner = self.expr(OPEN[tok])
            self.take(OPEN[tok])
            return _p(inner), "group"
        if tok in (r"\lbrack",):
            self.take()
            inner = self.expr()
            self.take(r"\rbrack")
            return _p(inner), "group"
        if tok in ABS:
            self.take()
            inner = self.expr(ABS[tok])
            self.take(ABS[tok])
            return "abs" + _p(inner), "atom"
        raise TexError(f"{tok} is not part of a term here")

    def _frac(self):
        self.take(r"\frac")
        # \frac{d}{dx} and \frac{\mathrm{d}}{\mathrm{d}x}: D[x] of what follows
        save = self.i
        num = self._diff_group()
        if num == "":
            den = self._diff_group()
            if den:
                body, _ = self.power()
                return f"(D[{den}] ({body}))", "atom"
        self.i = save
        a = self.arg()
        b = self.arg()
        return f"(({a})/({b}))", "atom"

    def _diff_group(self):
        """Inside {…}: `d` alone -> "", `d x` -> "x"; anything else None."""
        if self.peek() != "{":
            return None
        j = self.i + 1
        toks = []
        depth = 0
        while j < len(self.toks) and not (self.toks[j] == "}" and depth == 0):
            depth += {"{": 1, "}": -1}.get(self.toks[j], 0)
            toks.append(self.toks[j])
            j += 1
        flat = "".join(t for t in toks if t not in ("{", "}"))
        flat = flat.replace(r"\mathrm", "").replace(r"\differentialD", "d")
        m = re.fullmatch(r"d([A-Za-z](?:[0-9]*)|(?:\\[a-z]+))?", flat)
        if not m:
            return None
        self.i = j + 1
        v = m.group(1) or ""
        return v.lstrip("\\")

    def _apply(self, fn):
        """A builtin applied: to the group after it, else to the juxtaposed
        factors up to the next operator or function (PRETTY.md)."""
        if self.peek() == "^":
            raise TexError(f"ambiguous: write \\{fn}(x^k) or (\\{fn} x)^k "
                           f"(D6)")
        if self.peek() in ("(", r"\left") and (
                self.peek() == "(" or self.peek(1) == "("):
            inner = self._group_items()
            if len(inner) != 1:
                raise TexError(f"{fn} takes one argument")
            if self.peek() == "^":
                raise TexError(f"ambiguous: write \\{fn}(x^k) or "
                               f"(\\{fn} x)^k (D6)")
            return fn + _p(inner[0]), "app"
        parts = [self.factor()]
        while not self._at_stop(None) and self.peek() not in (
                r"\cdot", r"\times", "*", "/", r"\div") \
                and self.peek() not in FNS \
                and self.peek() not in (r"\operatorname", r"\int"):
            parts.append(self.factor())
        return fn + _p(" * ".join(parts)), "app"

    def _int(self):
        self.take(r"\int")
        lo = hi = None
        for _ in range(2):
            if self.peek() == "_":
                self.take()
                lo = self._end()
            elif self.peek() == "^":
                self.take()
                hi = self._end()
        if lo is None or hi is None:
            raise TexError("an integral needs both bounds")
        self.in_int += 1
        try:
            if self.peek() == "{" and self._group_then_diff():
                self.take("{")
                body = self.expr("}")
                self.take("}")
            else:
                body = self.expr()
            if not self._differential():
                raise TexError("the integral has no dx")
        finally:
            self.in_int -= 1
        tok = self.take()
        if tok in (r"\mathrm", r"\operatorname", r"\mathit"):
            self.raw_group()
        v = self.raw_group() if self.peek() == "{" else self.take()
        v = v.lstrip("\\")
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", v):
            raise TexError(f"d{v}: not a variable")
        return f"(Int[{v} = {lo} .. {hi}] ({body}))"

    def _group_then_diff(self):
        """tex.tex's `{body} \\,\\mathrm{d}{x}`: a braced integrand."""
        depth, j = 0, self.i
        while j < len(self.toks):
            depth += {"{": 1, "}": -1}.get(self.toks[j], 0)
            j += 1
            if depth == 0:
                break
        save, self.i = self.i, j
        ok = self._differential()
        self.i = save
        return ok

    def _end(self):
        """A bound: a {...} group, or one token (as in \\int_0^1)."""
        if self.peek() == "{":
            s = self.arg()
        elif self.peek() == "-":
            self.take()
            s = "-(" + self.factor_kind()[0] + ")"
        else:
            s = self.factor_kind()[0]
        s = s.strip()
        if s == "oo":
            return "oo"
        if s in ("-(oo)", "-oo"):
            return "-oo"
        return _p(s)


def ascii_of(latex, sig=None):
    """GRAMMAR.md text for a term written in LaTeX. Raises TexError."""
    if not latex.strip():
        raise TexError("fill in the empty box")
    r = _Reader(latex, sig)
    out = r.expr()
    if r.peek() is not None:
        raise TexError(f"unexpected {r.peek()}")
    return out


def read(latex, sig=None):
    """The term a field holds: the trusted parser's reading of ascii_of.
    Raises TexError, or terms.Refused from the parser."""
    return parse_term(ascii_of(latex, sig), sig)
