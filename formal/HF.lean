/-
# The hereditarily finite universe, machine-checked

A companion to the note *On Completed Infinity*. It verifies one sentence of §5:

  "If you remove it, the remaining axioms are satisfied by the hereditarily
   finite sets -- a perfectly coherent universe in which every set is finite."

The model is the Ackermann interpretation: the universe is `Nat`, and

  a is a member of b   iff   the a-th binary digit of b is 1.

Lean 4 core only; no mathlib, no `sorry`, no axioms beyond Lean's own.
-/

namespace HF

/-- Ackermann membership: `a` is a member of `b` iff bit `a` of `b` is set. -/
def Mem (a b : Nat) : Prop := b.testBit a = true

@[inherit_doc] scoped infix:50 " ∈ᴴ " => Mem

/-- Inclusion, defined from membership exactly as in ZF. -/
def Subset (a b : Nat) : Prop := ∀ x, x ∈ᴴ a → x ∈ᴴ b

@[inherit_doc] scoped infix:50 " ⊆ᴴ " => Subset

instance (a b : Nat) : Decidable (a ∈ᴴ b) := inferInstanceAs (Decidable (b.testBit a = true))

/-! ## The one fact that makes the universe finite

Every member of a set has a strictly smaller code. This single lemma is what
forces every set to be finite, and it is what kills the Axiom of Infinity. -/

theorem mem_lt {a b : Nat} (h : a ∈ᴴ b) : a < b :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.ge_two_pow_of_testBit h)

/-! ## Extensionality -/

theorem ext {a b : Nat} (h : ∀ x, x ∈ᴴ a ↔ x ∈ᴴ b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := h i
  unfold Mem at hi
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp [ha, hb] at hi ⊢

/-! ## Empty set -/

theorem not_mem_zero (x : Nat) : ¬ (x ∈ᴴ 0) := by
  simp [Mem, Nat.zero_testBit]

theorem empty_exists : ∃ e, ∀ x, ¬ (x ∈ᴴ e) := ⟨0, not_mem_zero⟩

/-! ## Pairing -/

/-- The unordered pair `{a, b}`. -/
def pair (a b : Nat) : Nat := 2 ^ a ||| 2 ^ b

theorem mem_pair {x a b : Nat} : x ∈ᴴ pair a b ↔ (x = a ∨ x = b) := by
  simp [Mem, pair, Nat.testBit_or, Nat.testBit_two_pow]
  constructor
  · rintro (h | h) <;> simp [h.symm]
  · rintro (h | h) <;> simp [h]

theorem pairing_exists (a b : Nat) : ∃ p, ∀ x, x ∈ᴴ p ↔ (x = a ∨ x = b) :=
  ⟨pair a b, fun _ => mem_pair⟩

/-! ## Binary union -/

/-- `a ∪ b`. -/
def cup (a b : Nat) : Nat := a ||| b

theorem mem_cup {x a b : Nat} : x ∈ᴴ cup a b ↔ (x ∈ᴴ a ∨ x ∈ᴴ b) := by
  simp [Mem, cup, Nat.testBit_or]

/-! ## Foundation

No set is a member of itself, and `∈` supports induction. Both follow from
`mem_lt` together with well-foundedness of `<` on `Nat`. -/

theorem not_mem_self (a : Nat) : ¬ (a ∈ᴴ a) := fun h => Nat.lt_irrefl a (mem_lt h)

theorem mem_induction {P : Nat → Prop} (ih : ∀ a, (∀ x, x ∈ᴴ a → P x) → P a) (a : Nat) :
    P a := by
  have H : ∀ n, ∀ m, m < n → P m := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ k IH =>
      intro m hm
      exact ih m fun x hx => IH x (Nat.lt_of_lt_of_le (mem_lt hx) (Nat.le_of_lt_succ hm))
  exact H (a + 1) a (Nat.lt_succ_self a)

/-- **Regularity**, in its minimal-element form, derived from `∈`-induction. -/
theorem regularity {a : Nat} (h : a ≠ 0) : ∃ x, x ∈ᴴ a ∧ ∀ y, y ∈ᴴ x → ¬ (y ∈ᴴ a) := by
  refine Classical.byContradiction (fun hc => ?_)
  have hc' : ∀ x, x ∈ᴴ a → ∃ y, y ∈ᴴ x ∧ y ∈ᴴ a := by
    intro x hx
    refine Classical.byContradiction (fun hy => ?_)
    exact hc ⟨x, hx, fun y hyx hya => hy ⟨y, hyx, hya⟩⟩
  have hall : ∀ x, ¬ (x ∈ᴴ a) :=
    mem_induction (fun x ih hx => by
      obtain ⟨y, hyx, hya⟩ := hc' x hx
      exact ih y hyx hya)
  exact h (ext (fun x => ⟨fun hx => absurd hx (hall x), fun hx => absurd hx (not_mem_zero x)⟩))

/-- There is no universal set: the finitist universe is not itself an object in it. -/
theorem no_universal_set : ¬ ∃ U, ∀ x, x ∈ᴴ U := fun ⟨U, h⟩ => not_mem_self U (h U)


/-! ## A set-builder, and the axioms that need one

`build f n` collects every `x < n` with `f x = true`. Because every member of a
set has a strictly smaller code (`mem_lt`), a bound is always available, so this
one construction yields Separation, Power set, Union and Replacement. -/

/-- `2 ^ n` if `b`, else `0`. -/
def bitAt (b : Bool) (n : Nat) : Nat := if b then 2 ^ n else 0

theorem testBit_bitAt (b : Bool) (n i : Nat) : (bitAt b n).testBit i = (b && decide (n = i)) := by
  cases b <;> simp [bitAt, Nat.testBit_two_pow, Nat.zero_testBit]

/-- The set of all `x < n` satisfying `f`. -/
def build (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bitAt (f n) n ||| build f n

theorem testBit_build (f : Nat → Bool) :
    ∀ n i, (build f n).testBit i = (decide (i < n) && f i) := by
  intro n
  induction n with
  | zero => intro i; simp [build, Nat.zero_testBit]
  | succ k IH =>
    intro i
    show ((bitAt (f k) k ||| build f k).testBit i) = _
    rw [Nat.testBit_or, testBit_bitAt, IH]
    rcases Nat.lt_trichotomy i k with h | h | h
    · rw [decide_eq_false (show ¬ (k = i) by omega), decide_eq_true h,
          decide_eq_true (show i < k + 1 by omega)]
      simp
    · subst h
      rw [decide_eq_true (rfl : i = i), decide_eq_false (show ¬ (i < i) by omega),
          decide_eq_true (show i < i + 1 by omega)]
      simp
    · rw [decide_eq_false (show ¬ (k = i) by omega), decide_eq_false (show ¬ (i < k) by omega),
          decide_eq_false (show ¬ (i < k + 1) by omega)]
      simp

theorem mem_build {f : Nat → Bool} {n x : Nat} : x ∈ᴴ build f n ↔ (x < n ∧ f x = true) := by
  unfold Mem; rw [testBit_build]; simp

/-! ## Separation

Stated for an *arbitrary* predicate, not merely a decidable one: the resulting
subset is finite whatever the predicate, so a code for it always exists. -/

open Classical in
/-- `{x ∈ a : P x}`. -/
noncomputable def sep (a : Nat) (P : Nat → Prop) : Nat :=
  build (fun x => decide (x ∈ᴴ a ∧ P x)) a

open Classical in
theorem mem_sep {a x : Nat} {P : Nat → Prop} : x ∈ᴴ sep a P ↔ (x ∈ᴴ a ∧ P x) := by
  unfold sep; rw [mem_build]
  constructor
  · rintro ⟨_, h⟩; exact of_decide_eq_true h
  · intro h; exact ⟨mem_lt h.1, decide_eq_true h⟩

/-! ## Power set -/

theorem subset_iff_and {x a : Nat} : x ⊆ᴴ a ↔ (x &&& a = x) := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i with
    | false => simp
    | true =>
      have ha := h i hx
      unfold Mem at ha
      simp [ha]
  · intro h i hi
    unfold Mem at hi ⊢
    have hc := congrArg (fun m => Nat.testBit m i) h
    simp only [Nat.testBit_and] at hc
    rw [hi] at hc
    simpa using hc

theorem subset_le {x a : Nat} (h : x ⊆ᴴ a) : x ≤ a :=
  (subset_iff_and.mp h) ▸ Nat.and_le_right

/-- The power set of `a`. -/
def powerset (a : Nat) : Nat := build (fun x => decide (x &&& a = x)) (a + 1)

theorem mem_powerset {x a : Nat} : x ∈ᴴ powerset a ↔ x ⊆ᴴ a := by
  unfold powerset; rw [mem_build]
  constructor
  · rintro ⟨_, h⟩; exact subset_iff_and.mpr (of_decide_eq_true h)
  · intro h
    exact ⟨Nat.lt_succ_of_le (subset_le h), decide_eq_true (subset_iff_and.mp h)⟩

/-! ## Union -/

/-- `⋃ a`, the set of members of members of `a`. -/
def sUnion (a : Nat) : Nat :=
  build (fun x => (List.range a).any (fun y => a.testBit y && y.testBit x)) a

theorem mem_sUnion {x a : Nat} : x ∈ᴴ sUnion a ↔ ∃ y, y ∈ᴴ a ∧ x ∈ᴴ y := by
  unfold sUnion; rw [mem_build]
  constructor
  · rintro ⟨_, h⟩
    rw [List.any_eq_true] at h
    obtain ⟨y, _, hy⟩ := h
    rw [Bool.and_eq_true] at hy
    exact ⟨y, hy.1, hy.2⟩
  · rintro ⟨y, hya, hxy⟩
    have hy : y < a := mem_lt hya
    refine ⟨Nat.lt_trans (mem_lt hxy) hy, ?_⟩
    rw [List.any_eq_true]
    exact ⟨y, List.mem_range.mpr hy, by rw [Bool.and_eq_true]; exact ⟨hya, hxy⟩⟩

/-! ## Replacement

Again for an arbitrary function, not merely a definable one. -/

/-- A bound for the image of `{x : x < n}` under `F`. -/
def imgBound (F : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (F n) (imgBound F n)

theorem le_imgBound (F : Nat → Nat) : ∀ n x, x < n → F x ≤ imgBound F n := by
  intro n
  induction n with
  | zero => intro x h; exact absurd h (Nat.not_lt_zero x)
  | succ k IH =>
    intro x h
    rcases Nat.lt_or_ge x k with hx | hx
    · exact Nat.le_trans (IH x hx) (Nat.le_max_right _ _)
    · have hxk : x = k := by omega
      subst hxk
      exact Nat.le_max_left _ _

open Classical in
/-- The image `{F x : x ∈ a}`. -/
noncomputable def repl (a : Nat) (F : Nat → Nat) : Nat :=
  build (fun y => decide (∃ x, x ∈ᴴ a ∧ F x = y)) (imgBound F a + 1)

open Classical in
theorem mem_repl {a y : Nat} {F : Nat → Nat} : y ∈ᴴ repl a F ↔ ∃ x, x ∈ᴴ a ∧ F x = y := by
  unfold repl; rw [mem_build]
  constructor
  · rintro ⟨_, h⟩; exact of_decide_eq_true h
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Nat.lt_succ_of_le (le_imgBound F a x (mem_lt hx)), decide_eq_true ⟨x, hx, rfl⟩⟩

/-! ## The Axiom of Infinity fails -/

/-- The von Neumann successor `a ∪ {a}`. -/
def succ (a : Nat) : Nat := a ||| 2 ^ a

theorem mem_succ {x a : Nat} : x ∈ᴴ succ a ↔ (x ∈ᴴ a ∨ x = a) := by
  unfold Mem succ
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (of_decide_eq_true h).symm
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (decide_eq_true h.symm)

theorem self_mem_succ (a : Nat) : a ∈ᴴ succ a := mem_succ.mpr (Or.inr rfl)

theorem lt_succ (a : Nat) : a < succ a := mem_lt (self_mem_succ a)

/-- `I` is inductive: it contains the empty set and is closed under successor. -/
def Inductive (I : Nat) : Prop := (0 ∈ᴴ I) ∧ ∀ x, x ∈ᴴ I → succ x ∈ᴴ I

/-- `0, succ 0, succ (succ 0), …` -/
def iter : Nat → Nat
  | 0 => 0
  | n + 1 => succ (iter n)

theorem iter_mem {I : Nat} (h : Inductive I) : ∀ n, iter n ∈ᴴ I
  | 0 => h.1
  | n + 1 => h.2 _ (iter_mem h n)

theorem le_iter : ∀ n, n ≤ iter n
  | 0 => Nat.le_refl 0
  | n + 1 => Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (le_iter n) (lt_succ (iter n)))

/-- **There is no inductive set.** The Axiom of Infinity is false in this universe. -/
theorem infinity_fails : ¬ ∃ I, Inductive I := by
  rintro ⟨I, h⟩
  have key : ∀ n, n < I := fun n =>
    Nat.lt_of_le_of_lt (le_iter n) (mem_lt (iter_mem h n))
  exact Nat.lt_irrefl I (key I)

/-! ## The diagonal argument needs no infinity

Cantor's construction is finitary. It is valid over *any* type, finite or not,
so rejecting Infinity leaves it untouched -- it simply has nothing infinite
left to be applied to. -/

theorem cantor_diagonal {α : Type} (f : α → (α → Bool)) : ¬ ∀ g : α → Bool, ∃ a, f a = g := by
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (fun x => !(f x x))
  have h : f a a = !(f a a) := congrFun ha a
  cases hv : f a a <;> rw [hv] at h <;> simp at h

/-- Inside the finitist universe: every `a` has a subset that is not a member of `a`.
    The power set always escapes. -/
theorem exists_subset_not_mem (a : Nat) : ∃ s, s ⊆ᴴ a ∧ ¬ (s ∈ᴴ a) :=
  ⟨a, fun _ h => h, not_mem_self a⟩

/-! ## Sanity checks

The theorems above would all be vacuously true of a mis-stated encoding, so here
are concrete computations confirming that this really is the HF universe:
`0 = ∅`, `1 = {∅}`, `2 = {{∅}}`, `3 = {∅,{∅}}`, and so on. -/

section Sanity

example : ¬ (0 ∈ᴴ 0) := by decide
example : (0 ∈ᴴ 1) ∧ ¬ (1 ∈ᴴ 1) := by decide
example : ¬ (0 ∈ᴴ 2) ∧ (1 ∈ᴴ 2) := by decide
example : (0 ∈ᴴ 3) ∧ (1 ∈ᴴ 3) ∧ ¬ (2 ∈ᴴ 3) := by decide

-- The von Neumann naturals: ∅, {∅}, {∅,{∅}}, … come out as 0, 1, 3, 11, 2059.
example : succ 0 = 1 := by decide
example : succ 1 = 3 := by decide
example : succ 3 = 11 := by decide
example : iter 4 = 2059 := by decide

example : pair 0 1 = 3 := by decide
example : cup 1 2 = 3 := by decide
example : sUnion 3 = 1 := by decide           -- ⋃{∅,{∅}} = {∅}
example : sUnion 11 = 3 := by decide          -- ⋃3 = 2, in von Neumann terms

example : powerset 0 = 1 := by decide         -- P(∅) = {∅}
example : powerset 1 = 3 := by decide         -- P({∅}) = {∅,{∅}}
example : powerset 3 = 15 := by decide        -- P({∅,{∅}}) has four members
example : powerset 7 = 255 := by decide       -- a three-member set has eight subsets

-- Exhaustive check of `mem_lt` over the first 64 codes.
example : ∀ b < 64, ∀ a < 64, (a ∈ᴴ b) → a < b := by decide

end Sanity

end HF

/-! ## Axiom audit

Run this file and Lean reports exactly what each result rests on. The only
entries are Lean's own three axioms. `Classical.choice` appears precisely where
it was used on purpose -- Separation and Replacement are stated for *arbitrary*
predicates and functions, not merely decidable ones. Crucially, `sorryAx`
appears nowhere: nothing here is assumed or left open. -/

#print axioms HF.ext
#print axioms HF.not_mem_zero
#print axioms HF.mem_pair
#print axioms HF.mem_cup
#print axioms HF.mem_sUnion
#print axioms HF.mem_sep
#print axioms HF.mem_powerset
#print axioms HF.mem_repl
#print axioms HF.mem_induction
#print axioms HF.regularity
#print axioms HF.not_mem_self
#print axioms HF.no_universal_set
#print axioms HF.infinity_fails
#print axioms HF.cantor_diagonal
