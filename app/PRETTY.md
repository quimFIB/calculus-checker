# Pretty mode — 2D input on the page

The owner's ask (2026-09-26): "a toggleable mode where things get
prettified and for instance when inputting a fraction you get two text
boxes one on top of the other to fill, prettified integral symbol etc."
Written before the code. The Emacs side of the same ask is `DX.md`.

Untrusted, like all of `app/`. Pretty mode is another way of **writing the
same script**: the textarea's text stays the only model (SCRIPT.md), every
edit in pretty mode rewrites it, and stepping, saving, export and the
checked region work on that text exactly as in text mode. A translation
bug can put the wrong term in a sentence; the kernel checks that sentence
like any other, and the page shows the term it sent (below), so a wrong
reading is visible, never silent.

## Where it sits

```
app/page/mathlive/     MathLive 0.110.0 (MIT), vendored like KaTeX: mathlive.min.js,
                       fonts/, LICENSE.txt, SOURCE (URL and sha256). No sounds.
app/script.py          gains layout(sentence): the sentence cut into text and terms
app/untex.py           MathLive's LaTeX -> GRAMMAR.md text (new)
app/api.py             POST /layout, POST /untex
app/server.py          serves /mathlive/... as it serves /katex/...
app/page/index.html    the toggle and the pretty editor
```

MathLive is loaded only when pretty mode is first turned on, so text mode
loads exactly what it loads today.

## Two routes

```
POST /layout {text, session?}  -> {pieces: [{kind, start, end, segments}]}
POST /untex  {latex, session?} -> {term, tex} | refusal bad-tex (or the parser's code)
```

**`/layout`** cuts a whole script into pieces, in order, covering it
exactly (the pieces' texts concatenated are the script): `sentence` for
each complete sentence (`script.spans`), `gap` for the text between them
(whitespace and comments), and `open` for the unfinished text after the
last sentence, if any. A sentence's `segments` are
`script.layout(sentence)`; a gap's and an open piece's are one text
segment. The session, when given, supplies the declared functions for
parsing terms.

**`script.layout(sentence)`** returns segments `{text}` or
`{term, tex}` whose texts concatenate to the sentence exactly. A term
segment is each place SCRIPT.md's form has a term (T), in the order they
appear: ftc/int_improper/close's head; rewrite's and fact's `with` values
and rewrite's `at`; int_subst's `:=` value, `from`, `to` and `reverse`;
int_parts' `u` and `v`; taylor_lagrange's `of`, `from`, `to`, `at` and
each `derivs` item. Names, entries, numbers after `occurrence`, `by C`
and `using` stay text. A sentence that `parse` refuses, or that holds a
comment, is one text segment. `tex` is `tex.tex` of the parsed term, or
null when the term does not parse; the page then keeps that term as text,
where the learner can fix it. The term `_` (the palette's hole) has
`tex` `""`, an empty box.

**`/untex`** reads the LaTeX a MathLive field holds and answers the
canonical GRAMMAR text (`terms.show` of the trusted parser's result) and
its TeX. `untex.py` is a small recursive-descent reader for the LaTeX
MathLive emits, and for everything `tex.tex` emits (so a field filled by
`/layout` and left alone reads back to the same term):

| LaTeX | read as |
|---|---|
| `\frac{a}{b}` | `(a)/(b)` |
| `a^{b}`, `a^b` | `(a)^(b)`; the parser decides Pow or RPow as usual (D8) |
| `e^{u}`, `\exponentialE^{u}`, `\mathrm{e}^{u}` | `exp(u)` (the textbook reading of eᵘ) |
| `\mathrm{e}`, `\exponentialE` alone | `e_const`; a bare `e` is passed on and the parser refuses it (D3) |
| `\sqrt{a}` | `sqrt(a)`; `\sqrt[n]{a}` is refused |
| `\left( … \right)`, `( … )`, `\left[`, `\lbrack` | a group |
| `\left| … \right|`, `\lvert … \rvert`, `| … |` | `abs(…)` |
| `\sin`, …, `\arctan`, `\operatorname{name}`, `\mathrm{name}` for a builtin or a declared function | an application: with a group after it, of that group; otherwise of the juxtaposed factors up to the next `+`, `-`, `\cdot`, `\times`, `/`, relation, or function name (so `\sin 2t` is sin(2*t), `\sin x\cos x` is (sin x)*(cos x)) |
| juxtaposition `2x`, `2\left(…\right)` | `*` (in two dimensions it is unambiguous); a declared function name followed by a group is a call |
| `\cdot`, `\times`, `*` | `*` |
| `\int_{a}^{b} body \,dx` (also `\mathrm{d}x`, `\differentialD x`, `d x`, spacing commands anywhere) | `Int[x = a .. b] (body)`; the body runs to the first `d<var>` at its own group level, and a missing `dx` is refused |
| `\infty` | `oo`; `-\infty` as an endpoint is `-oo` |
| `\pi`, `\theta` and the other spelled Greek letters | `pi`, `theta`, … |
| `x_0`, `x_{10}`, `v_{inf}` | the name `x_0`, `x_10`, `v_inf` |
| `\placeholder{}`, an empty field | refused `bad-tex`: "fill in the empty box" |
| `\frac{\mathrm{d}}{\mathrm{d}x}` | `D[x]` of the next factor |
| anything else (`\sum`, `\lim`, matrices, `\text{…}`) | refused `bad-tex` naming the command |

Multi-letter names typed as letters (`ab`) are juxtaposition, `a*b`, as
MathLive draws them.

## The page

A **Pretty** button in the script toolbar toggles the mode; the choice is
remembered per browser (`localStorage`, which may be unavailable; the page
then starts in text mode). The toggle changes the view only: nothing is
stepped, retracted or saved by it.

In pretty mode the textarea is hidden and the script is drawn as **rows**,
one per `/layout` piece:

- a **sentence** row is its segments in a line that wraps: text segments
  are editable text, term segments are MathLive fields, where `/` makes a
  stacked fraction with two boxes, `sqrt` a root, `^` an exponent box and
  `int` an integral with its two bound boxes (MathLive's own inline
  shortcuts). Under each field, in small monospace, the GRAMMAR text the
  kernel will get (`/untex`'s `term`), so the reading is always visible;
- a **gap** that is only whitespace is not drawn and is kept verbatim; a
  gap with a comment is a muted, read-only line (comments are edited in
  text mode);
- the **open** row is always last: editable text where a new sentence is
  typed, with the placeholder "type a tactic, end it with a full stop".

Editing: typing in a text segment or a field rewrites the textarea from the
rows (a field contributes its last `/untex` term; while its LaTeX does not
read, the field is outlined red with the refusal as its title, and the row
is marked unreadable). **Enter** in a row, or leaving a text segment,
re-lays the unchecked rows out with `/layout`, so a sentence typed as text
in the open row gets its fields as soon as it ends with a full stop. Tab
and the arrow keys at a field's edge move to the next or previous segment.
The palette's sentences and "Use this" insert into the textarea as today,
then re-lay out.

The **checked rows** are shaded as the checked region is, and read-only
(Proof General's strict locked region); to change one, put the focus on it
and press To cursor, or Undo. A refused row is underlined red, a running one
amber, a stopped one dashed, as in text mode. Next, Undo, To cursor and the
Alt and Ctrl keys work unchanged; To cursor steps or retracts to the end of
the row that has the focus. Stepping a row marked unreadable does not send
it: the response box shows the `bad-tex` refusal and nothing is checked.

Turning pretty mode off shows the textarea with the same text.

## Done when

1. `app/test_pretty.py`: `layout` covers every sentence exactly and its
   terms are the parsed args' terms, in text order, for every step of every
   problem file; `untex(tex(t))` gives `show(t)` for every term in every
   problem file; a table of MathLive LaTeX (including strings captured from
   MathLive itself) reads as expected; each refusal above is `bad-tex`.
2. `test_api.py` covers `/layout` and `/untex`, and `/mathlive/` serves the
   vendored files and nothing outside them.
3. `test_page.py`: the toggle shows rows and hides the textarea; S1 is
   proved in pretty mode by typing `x^3+x^2` into the `ftc` field and
   stepping; a fraction typed with `/` in a field reaches the script as a
   quotient; a checked row is read-only; toggling back shows the same text;
   no page errors.
4. Nothing under `kernel/` changes.

## Review (2026-09-26), folded in before the code

A skeptic read this file and DX.md before any code. What changed:

1. **No reading may change a term's meaning.** `\frac{a}{b}` is read
   `((a)/(b))` and an integral `(Int[x = a .. b] (body))`, so both stay
   one factor. `\fn\left(…\right)^{k}` and `\fn^{k} …` are refused
   `bad-tex` with D6's "ambiguous: write \fn(x^k) or (\fn x)^k".
2. **Juxtaposition respects D4 and D5.** A letter followed by digits, or
   by `_{…}`, is one name, as `tex._name` prints it (`x1`, `v_{0}`). A
   letter directly followed by another letter is refused (D4: "write
   a\cdot b"); a name directly followed by an open group is a call when
   the name is declared and refused otherwise (D5). Every other
   juxtaposition (a digit, a group, a fraction, a root, π, a Greek
   letter or an application before the next factor) is `*`.
3. **One reader was considered and not taken.** `tex.py`'s reader stays:
   it reads judgements and intervals, whose unbalanced `[0, 1)` a
   structural reader cannot, and it exists to test the printer. `untex`
   reads terms only, and its test includes `untex(tex(t)) == show(t)`
   for every term, so the two cannot drift on what the page shows.
4. **`/layout` and `/untex` never wait for a step.** They only parse, so
   the server answers them in its own process, outside TIMEOUT.md's
   worker lock (a Cancel can never hit one). They take `functions?` (as
   `/parse` does) instead of `session`. The page numbers its `/untex`
   requests per field and drops stale answers; Next, To cursor and
   leaving pretty mode first wait for the reads in flight. A field that
   was never edited contributes its sentence's original text, not a
   reprint.
5. **MathLive's inline shortcuts are an allow-list**: the builtin
   function names, `sqrt`, `int`, `pi`, `oo` and `infty`, and the
   spelled Greek letters. MathLive's defaults (`in` → ∈, `ne`, …) are off.
6. **Tab and arrow navigation between segments is left to a second
   cut**; MathLive's own keys work inside a field, and a click moves
   between segments. Re-layout on Enter stays.
7. **The page fixes its own locked-region edge** (DX.md review 2): an
   insertion that does not start with whitespace, right after the last
   checked `.`, edits that sentence and retracts it; while a request
   runs, an edit inside the checked region is blocked, not let through.
8. Test notes: fields are filled by typing with ArrowRight out of an
   exponent, or by setting the value; the ftc field comes from typing
   `ftc _.` in the open row; the MathLive strings are a committed fixture
   (`app/assist/`-free: `app/untex_cases.json`), captured from MathLive
   by a page test that fails if MathLive's output drifts.

## Revision 2: slot boxes and autocomplete (owner, 2026-09-26)

"Also, an autocomplete for the tactics with the shape of the tactic as
inputable fields should be provided." Written with the first build, before
its tests.

- **Every slot is a box.** `script.layout` also marks the non-term slots:
  `{"name": s}` for a variable, a fact or an entry name (int_subst's `x`
  and `as`, int_parts' `in`, taylor_lagrange's bind and `in`, fact's bind
  and entry, rewrite's entry, each `using` name, the `occurrence` number)
  and `{"choice": s, "options": [...]}` for `by ring|field`,
  taylor_lagrange's `lower|upper` and `increasing|decreasing`. The page
  draws a name as a small text box and a choice as a menu. Keywords stay
  plain text. Concatenation still gives the sentence exactly.
- **`script.TEMPLATES`**: one sentence per move, the move's required shape
  with `_` for each term, placeholder names (`x`, `t`, `h`, `entry`) and
  `by ring` (`by field` where the course's uses need it). Every template
  parses. `GET /templates -> {templates: [{move, template, usage}]}`,
  answered in the server process like `/layout`.
- **Autocomplete.** Typing a move's first letters in the open row shows a
  list of the matching templates, each with its usage line (SCRIPT.md);
  ArrowUp and ArrowDown move, Enter or Tab takes one, Escape closes,
  a click takes one. Taking one puts the template in the open row, lays it
  out, and puts the focus in its first empty box. Nothing is stepped.
- Done when, added: `test_pretty.py` checks every template parses and
  that its `_` holes are term segments; `test_page.py` takes `int_subst`
  from the list by typing `int_s` and Enter, fills its three boxes, and
  steps P1_PARTS.
