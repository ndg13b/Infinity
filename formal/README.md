# A formal companion to *On Completed Infinity*

[`HF.lean`](HF.lean) is a machine-checked verification of one sentence from §5
of [the note](../on-completed-infinity.md):

> If you remove it, the remaining axioms are satisfied by the hereditarily
> finite sets — a perfectly coherent universe in which every set is finite.

Checked by Lean 4.23.0, using Lean core only — no mathlib — with no `sorry`.

## The model

The universe is `Nat`. Membership is the Ackermann interpretation:

> `a` is a member of `b`  ⟺  the `a`-th binary digit of `b` is 1.

So `0` is `∅`, `1 = 2⁰` is `{∅}`, `3 = 2⁰ + 2¹` is `{∅, {∅}}`, and every natural
number codes a distinct hereditarily finite set. The whole development turns on
one lemma, `mem_lt`: **every member of a set has a strictly smaller code.** That
is what makes every set finite, and it is what kills Infinity.

## What is verified

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

## What this establishes — and what it does not

**It does establish the §5 claim.** A theory with a model is consistent, so
ZF−Infinity does not prove Infinity. Infinity is not a theorem. It is an axiom,
exactly as the note says. The position is not confused, and it is not a mistake
about mathematics.

**It does not establish that completed infinity is incoherent**, and no formal
development could. That is worth stating flatly, because it is the thing a
reader might hope a "formal proof" would deliver here.

## Three caveats, stated plainly

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

## Consistent is not the same as coherent

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
```

A clean run prints the axiom audit and nothing else. Any `sorry`, any gap, or
any appeal to an extra axiom would show up in that output.
