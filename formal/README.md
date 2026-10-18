# A formal companion to *On Completed Infinity*

Two Lean 4 developments, both core-only and neither containing a `sorry`:

| File | What it checks | Of the note |
| --- | --- | --- |
| [`Digits.lean`](Digits.lean) | The digit argument: where it is right, and the one quantifier that breaks it | §2–§3 |
| [`HF.lean`](HF.lean) | The hereditarily finite sets satisfy the other ZF axioms and refute Infinity | §5 |

## Digits.lean — the digit argument

The note's opening intuition is that *n* digit places express at most 10ⁿ values,
so an infinite set would need infinitely many digit places somewhere.

**The premise is correct, and it is a theorem.** `finite_of_uniform_digit_bound`
shows that if a single *n* bounds the digit count of every member of a set, that
set has at most 10ⁿ members, witnessed by an explicit list of that length.
`numDigits_le_iff` gives the exact correspondence — *at most n digits* is the same
condition as *below 10ⁿ* — so the count is not merely an upper bound.

**The conclusion does not follow, and the gap is one quantifier.**
`the_quantifier_swap` proves both halves at once:

| Statement | |
| --- | --- |
| `∀ x, ∃ n, numDigits x ≤ n` — every natural has a finite digit count | **true** |
| `∃ n, ∀ x, numDigits x ≤ n` — one bound covers every natural | **false** |

The argument needs the second. The naturals supply only the first. So the claim as
literally stated is false in standard mathematics, and
`unbounded_set_of_finite_digit_numbers` gives the counterexample: ℕ is unbounded,
yet every member has a finite digit count, and no member has infinitely many
digits because there is no such natural number.

The note's closing question — *where, then, are the infinitely many digit places?*
— has an exact answer in `unbounded_digit_lengths`: an infinite set must contain
numbers of more than *n* digits, for every *n*. The unboundedly many digit places
are real, and they are in the set — distributed across its members, never
accumulated inside one. Each member stops; the lengths do not.

That answer is given inside the framework it defends. To say the digit places are
*in the set* presupposes a completed set to hold them, which is exactly what the
note declines to grant. To a reader who denies completed infinity, it restates
unboundedness rather than meeting the objection.

This is the formal form of the concession §3 of the note already makes. It does not
support the thesis — and, for the reason just given, it does not refute it either.
What it adds is precision about which half of the intuition was tracking something
true.

Base ten is used throughout to match the note; nothing depends on the base.

## HF.lean — the hereditarily finite universe

[`HF.lean`](HF.lean) is a machine-checked verification of one sentence from §5
of [the note](../on-completed-infinity.md):

> If you remove it, the remaining axioms are satisfied by the hereditarily
> finite sets — a perfectly coherent universe in which every set is finite.

Checked by Lean 4.23.0, using Lean core only — no mathlib — with no `sorry`.

### The model

The universe is `Nat`. Membership is the Ackermann interpretation:

> `a` is a member of `b`  ⟺  the `a`-th binary digit of `b` is 1.

So `0` is `∅`, `1 = 2⁰` is `{∅}`, `3 = 2⁰ + 2¹` is `{∅, {∅}}`, and every natural
number codes a distinct hereditarily finite set. The whole development turns on
one lemma, `mem_lt`: **every member of a set has a strictly smaller code.** That
is what makes every set finite, and it is what kills Infinity.

### What is verified

| Axiom | Result | Note |
| --- | --- | --- |
| Extensionality | `ext` | |
| Empty set | `empty_exists` | |
| Pairing | `pairing_exists` | |
| Union | `mem_sUnion` | |
| Separation | `mem_sep` | for *arbitrary* predicates, not merely decidable ones |
| Power set | `mem_powerset` | |
| Replacement | `mem_repl` | for *arbitrary* functions, not merely definable ones |
| Foundation | `regularity`, `mem_induction`, `not_mem_self` | both minimal-element and induction forms |
| **Infinity** | **`infinity_fails`** | **refuted — there is no inductive set** |

Two further results:

- **`cantor_diagonal`** — the diagonal argument over an arbitrary type, finite or
  not, using no infinity whatsoever. Rejecting Infinity does not touch Cantor's
  construction. It only removes the infinite object to apply it to. This is the
  formal counterpart of the note's "I am not claiming Cantor made an error."
- **`no_universal_set`** — nothing contains everything.

The file ends with an axiom audit. Every result depends only on Lean's own
`propext` and `Quot.sound`, plus `Classical.choice` exactly where classical
reasoning was used on purpose. **`sorryAx` appears nowhere**: nothing is assumed
or left open. A `Sanity` section computes `P(∅) = {∅}`, `succ 3 = 11`,
`powerset 7 = 255` and similar, so the theorems cannot be vacuously true of a
mis-stated encoding.

### What this establishes — and what it does not

**It does establish the §5 claim.** A theory with a model is consistent, so
ZF−Infinity does not prove Infinity. Infinity is not a theorem. It is an axiom,
exactly as the note says. The position is not confused, and it is not a mistake
about mathematics.

**It does not establish that completed infinity is incoherent**, and no formal
development could. That is worth stating flatly, because it is the thing a
reader might hope a "formal proof" would deliver here.

### Three caveats, stated plainly

1. **Soundness is not formalized here.** Lean verifies that this *structure*
   satisfies these *sentences*. The step from there to "the first-order theory
   does not prove Infinity" is the soundness theorem. It is entirely standard,
   but it is taken outside the machine, and this directory does not check it.

2. **Semantic, not schematic.** Separation and Replacement are axiom *schemas*
   over formulas in the language of set theory. What is verified here is the
   semantic version, quantifying over arbitrary Lean predicates and functions.
   For this purpose that is at least as strong — every first-order definable
   predicate is in particular a predicate — but it is a statement in Lean's type
   theory about a structure, not a derivation inside a formalized first-order
   calculus.

3. **The independence is two-sided, and only one side is cheap.** That
   ZF−Infinity cannot *prove* Infinity is witnessed by this file: the finitist
   universe can be written down and checked by a computer. That ZF−Infinity
   cannot *refute* Infinity needs a model of ZF, and by Gödel's second
   incompleteness theorem ZF cannot prove one exists; that half rests on
   assuming Con(ZF) and cannot be exhibited the way `HF.lean` exhibits V<sub>ω</sub>.
   The asymmetry is real and it is mildly congenial to the note. But it is an
   asymmetry about the cost of exhibiting models of weaker versus stronger
   theories, which is generic, and it is not evidence that the stronger theory
   describes nothing.

### Consistent is not the same as coherent

The note's thesis is that a completed infinite totality is *incoherent*. Formal
consistency is a different and weaker notion. This file shows that **denying**
Infinity is consistent. It says nothing about whether **asserting** it is
coherent — and on the narrow formal reading the record runs the other way: if
ZF is consistent, Infinity cannot be refuted, so "incoherent" cannot mean
"inconsistent" here.

What formal work can do is locate a disagreement exactly. It cannot settle one.
The note already says this — "This is a disagreement about an axiom, not a claim
of error" — and nothing in this directory changes it.

## Checking it yourself

```sh
elan toolchain install leanprover/lean4:v4.23.0   # or: lake build
lean HF.lean
lean Digits.lean
```

A clean run prints the axiom audit and nothing else. Any `sorry`, any gap, or
any appeal to an extra axiom would show up in that output.
