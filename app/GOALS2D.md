# Goals drawn in two dimensions, for text editors

The owner asked (2026-09-26) for fractions and square roots to be
prettified in Emacs' `*dx-goals*` buffer, as KaTeX does on the page.
Written before the code.

## What

`app/pretty2d.py` lays a Term, Judgement or goal out as lines of Unicode
text, the way SymPy's pretty printer does, with no dependency beyond the
standard library:

```
 0
⌠
⎮  ⎛    2⎞   ________________
⎮  ⎝1 - t ⎠⋅╲╱ 1 - ⎛1 - t ⎞ ⋅ ...  dt = ?A
⌡
1
```

- `a/b` is a fraction: `a` centred over a bar `─` over `b`.
- `sqrt(a)` is `╲╱` with a bar over `a`; a taller `a` gets a longer
  diagonal.
- `Int[x = a .. b] f` is `⌠ ⎮ ⌡` as tall as `f` needs, `b` above, `a`
  below, then `f dx`.
- `D[x] f` is `d` over `dx`, then `(f)`.
- `u^n` for an integer `n` is a superscript (`t²`, `x⁻¹`); `u^e` for any
  other `e` raises `e` a row above `u`.
- `abs(a)` is `│a│`; parentheses around something taller than a line are
  `⎛ ⎜ ⎝` and `⎞ ⎟ ⎠`.
- `*` is `⋅`, `pi` is `π`, `oo` is `∞`, `<=` `>=` are `≤` `≥`, `==` is
  `=`, `#` is `≠`, a conjunction of judgements is `∧`, and `C^k(...)`
  keeps its domain inline.
- Parentheses follow `tex.py`'s rules (`terms.show`'s precedence), since a
  fraction and a root group by themselves.

It is untrusted and only draws. Like `goal_tex`, a failure never fails a
response: the field is null instead.

## Where

`api.render` adds `"goal_2d"` and `"theorem_2d"` (str | null, the lines
joined by `\n`, every line the same width) beside `goal_tex`. `/dx/goals`
returns the rendered node, so the LSP carries them with no change.

`dx-mode` shows them under `Goal` and `Theorem` in `*dx-goals*` when
`dx-goals-2d` is non-nil (the default). The one-line form stays as the
fallback: when the drawing is wider than the goals window, when the field
is null, and when `dx-goals-2d` is nil. The buffer does not wrap lines, so
a drawing never breaks across rows. Obligations stay one line each.

## Tests

`app/test_pretty2d.py`: fixed drawings for a fraction, a root, an
integral and a power; every problem's goal and a generated family of
terms lay out without error, as rectangles. The ERT suite checks that
`*dx-goals*` shows the 2D goal, and the one-line goal when it is off.
