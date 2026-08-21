# On Completed Infinity

*A short position note. Not a proof, and not a claim that anyone else is mistaken.*

---

## What this is

This is a statement of a position I hold about the foundations of mathematics,
written down mostly so that it exists somewhere outside my own head.

I am not a mathematician. I have no result to announce and nothing here is
new — the position I describe has been held, in various forms, for a very long
time. What follows is my own route to it, an honest account of the standard
objection, and a statement of where I think the disagreement actually lies.

I want to be clear at the outset about what I am **not** claiming. I am not
claiming Cantor made an error. I am not claiming standard set theory is
inconsistent. Both of those claims are made frequently by amateurs and both are
wrong. My disagreement is with a starting assumption, not with any inference
drawn from it.

---

## The intuition that started it

The usual proof that some infinities are larger than others is Cantor's
diagonal argument. Given any proposed list of the real numbers between 0 and 1,
you construct a new real number by taking the first digit of the first number,
the second digit of the second, and so on, and changing each one. The result
differs from every number on the list, so no such list can be complete. The
reals are therefore said to be uncountable, in contrast to the natural numbers,
which are countable.

The obvious question is why the same construction cannot be run on the natural
numbers. The answer given is that the diagonal construction produces an object
with infinitely many nonzero digits, and every natural number has finitely many
digits. The constructed object is therefore not a natural number, and no
contradiction follows.

That answer is correct, and I accept it. But it raised a different question for
me.

A finite number of digit places can only express finitely many distinct values.
Ten digits per place, *n* places, at most 10ⁿ values. So if a set contains
infinitely many distinct elements, it seemed to me that infinitely many digit
places must be in use somewhere. Yet every natural number is said to have
finitely many digits. Where, then, are the infinitely many digit places?

---

## The standard reply, stated fairly

The reply is that I had conflated two different claims:

1. Every natural number has finitely many digits.
2. There is a finite bound on how many digits a natural number may have.

The first is true. The second is false. For any bound you propose, some natural
number exceeds it. The set therefore uses **unboundedly many** digit places
without any individual member using infinitely many. Each element is finite; the
collection of lengths has no maximum.

Put another way: the set is not claimed to be infinite because some member is
infinite. It is claimed to be infinite because the successor function never
produces anything outside the set. There is no natural number *n* for which
*n* + 1 fails to be a natural number.

This is a good answer to the question I asked, and my original argument does not
survive it. If you accept the framework, the naturals are infinite and no
individual number needs infinitely many digits.

---

## Where I actually disagree

What the reply revealed is that my objection was never really about digits. It
was about the word *never* in "the successor function never terminates."

The same thing bothers me about the ordinary notation `{1, 2, 3, ...}`. The
ellipsis stands in for a listing that has no end, and then the closing brace
asserts that the listing is nonetheless one object. I take the point that this
is only informal shorthand, and that the formal definition does not list
anything: ℕ is defined as the smallest *inductive* set, a set containing ∅ and
closed under the successor operation.

But that reformulation does not touch what I am objecting to. The closure
property replaces the dots; it does not replace the existential claim. Something
still has to assert that a set with that property exists, and in
Zermelo–Fraenkel set theory that assertion is the Axiom of Infinity. So my
objection is not to the notation, and it is not a misreading of the shorthand.
It is to the step — in whatever notation — that closes the brace.

Two readings are available:

**Potential infinity.** The process of counting has no stopping point. However
far you have gone, you can go further. At any stage, what you have produced is
finite.

**Actual (completed) infinity.** There exists a single object — the set ℕ —
containing every natural number at once, as a finished totality.

The first reading I find unproblematic. It says something about a process and
its lack of a limit. The second reading asserts the existence of a completed
object, and it is that assertion I do not accept.

My position is that these are the only two coherent options, and that standard
mathematics occupies an uncomfortable middle position between them: the
successor process is treated as completed, while every product of it remains
finite. If the process is genuinely completed, I would expect the completion to
be reflected somewhere in the resulting object. It is not. If it is not
completed, then what we have is unboundedness, not infinity.

I recognise that mainstream mathematics does not see this as a middle position
at all, and regards "infinitely many finite things" as perfectly coherent. I
simply do not, and I have not encountered an argument that dissolves the
difficulty rather than restating the framework in which it does not arise.

---

## The honest status of the disagreement

The thing that took me longest to find out, and that I think is worth stating
plainly, is this: the existence of a completed infinite set is not a theorem of
standard mathematics. It is an axiom.

In Zermelo–Fraenkel set theory it is called the Axiom of Infinity, and it
asserts, in effect, that a set containing all the natural numbers exists. It
cannot be derived from the other axioms. If you remove it, the remaining axioms
are satisfied by the hereditarily finite sets — a perfectly coherent universe in
which every set is finite. Rejecting completed infinity does not produce a
contradiction. It produces a different, smaller mathematics.

So the disagreement is not between a proof and a mistake. It is between two
starting points, one of which was adopted because of what could be built on top
of it.

I think that is a legitimate reason to adopt it. I do not think it is the same
thing as being shown that it is true.

---

## What accepting this costs

I want to be honest that the cost is real and I am not in a position to pay it.

Standard analysis — limits, continuity, integration, measure theory — is
constructed on the real numbers, which are built from completed infinite sets.
Most of modern probability and much of theoretical physics inherits this. It is
sometimes suggested that constructive or predicative mathematics rescues most of
this, and a surprising amount can indeed be recovered in weak systems; but those
systems still take the natural numbers as an infinite totality. Strict finitism
gives up considerably more.

I am not proposing that mathematics should be rebuilt. I am recording that I do
not believe one of its starting assumptions, while continuing to use the
mathematics that rests on it, in the same way one might use a map known to be a
projection.

---

## The tradition this belongs to

I arrived at this on my own and found out only afterwards that it has a name.
Anyone reaching the same place should know the following names earlier than I
did:

- **Aristotle** drew the distinction between potential and actual infinity in
  the *Physics*, and accepted only the former.
- **Gauss**, in an 1831 letter to Schumacher, objected to the use of an infinite
  magnitude as a completed thing, calling it a manner of speaking rather than a
  legitimate object.
- **Poincaré** was a sustained critic of Cantorian set theory.
- **Brouwer** founded intuitionism, which admits potential but not actual
  infinity.
- **Weyl**, in *Das Kontinuum*, attempted a predicative reconstruction of
  analysis out of similar misgivings.
- **Yessenin-Volpin** and, more recently, **Zeilberger** and **Nelson** have
  defended stricter forms — ultrafinitism — in which even very large finite
  numbers are treated with suspicion.

The relevant survey articles are the Stanford Encyclopedia of Philosophy entries
on *finitism*, *intuitionism*, and *the philosophy of mathematics*. They are
free, and they are better than anything I could write.

---

## Summary

- Cantor's diagonal argument is a valid derivation within ZFC. I deny one of its
  premises, so I do not accept its conclusion. This is not a claim that the
  derivation contains an error.
- My original objection, that an infinite set requires infinitely many digit
  places, does not survive contact with the distinction between *unbounded* and
  *infinite*. I record it here because it is what led me to the real question.
- The real question is whether a completed infinite totality is coherent. I do
  not think it is. A process with no stopping point cannot, in my view, be
  treated as having stopped.
- This is a disagreement about an axiom, not a claim of error.
- The position has a long history and I make no claim to originality.

Anyone who wants to tell me where this goes wrong is welcome to. I would rather
know.

---

*Written 2026. No affiliation, no credential, no claim.*
