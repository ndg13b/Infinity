/-
# The digit argument, made precise

A companion to §2 and §3 of *On Completed Infinity*. The note opens with this:

  "A finite number of digit places can only express finitely many distinct
   values. Ten digits per place, n places, at most 10^n values. So if a set
   contains infinitely many distinct elements, it seemed to me that infinitely
   many digit places must be in use somewhere. Yet every natural number is said
   to have finitely many digits. Where, then, are the infinitely many digit
   places?"

The premise is correct, and it is proved below as `finite_of_uniform_digit_bound`.
The conclusion does not follow, and the exact point of failure is a swap of two
quantifiers, isolated below as `the_quantifier_swap`. The closing question has a
precise answer, `unbounded_digit_lengths`: the digit places are distributed across
the set, not concentrated in any member.

Base ten is used to match the note. Nothing below depends on the base.

Lean 4 core only; no mathlib, no `sorry`.
-/

namespace Digits

/-- The number of decimal digits of `x`. Zero is written with one digit. -/
def numDigits (x : Nat) : Nat :=
  if x < 10 then 1 else 1 + numDigits (x / 10)
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem numDigits_pos (x : Nat) : 1 ≤ numDigits x := by
  rw [numDigits]; split <;> omega

/-! ## The premise: `n` digit places express at most `10 ^ n` values -/

/-- A number written with at most `n` digits is below `10 ^ n`. -/
theorem lt_pow_of_numDigits_le : ∀ x n, numDigits x ≤ n → x < 10 ^ n := by
  have H : ∀ m x, x < m → ∀ n, numDigits x ≤ n → x < 10 ^ n := by
    intro m
    induction m with
    | zero => intro x hx; exact absurd hx (Nat.not_lt_zero x)
    | succ k IH =>
      intro x hx n h
      rw [numDigits] at h
      split at h
      · -- fewer than ten: one digit, so `n ≥ 1` and `10 ^ n ≥ 10`
        rename_i hlt
        have h10 : (10:Nat) ^ 1 ≤ 10 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.pow_one] at h10
        omega
      · -- ten or more: strip the last digit and recurse
        rename_i hge
        have hd : x / 10 < x := Nat.div_lt_self (by omega) (by omega)
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have key : x / 10 < 10 ^ m := IH (x / 10) (by omega) m (by omega)
        have step : (10:Nat) ^ (m + 1) = 10 ^ m * 10 := Nat.pow_succ 10 m
        have hmod : 10 * (x / 10) + x % 10 = x := Nat.div_add_mod x 10
        have hm : x % 10 < 10 := Nat.mod_lt _ (by omega)
        omega
  intro x n h
  exact H (x + 1) x (Nat.lt_succ_self x) n h

/-- Conversely, every number below `10 ^ n` is written with at most `n` digits. -/
theorem numDigits_le_of_lt_pow : ∀ n x, 1 ≤ n → x < 10 ^ n → numDigits x ≤ n := by
  intro n
  induction n with
  | zero => intro x h; exact absurd h (by omega)
  | succ k IH =>
    intro x _ hx
    rw [numDigits]
    split
    · omega
    · rename_i hge
      cases k with
      | zero =>
        -- `x < 10 ^ 1 = 10` contradicts being in the ten-or-more branch
        simp [Nat.pow_succ, Nat.pow_zero] at hx
        omega
      | succ j =>
        have step : (10:Nat) ^ (j + 1 + 1) = 10 ^ (j + 1) * 10 := Nat.pow_succ 10 (j + 1)
        have hdiv : x / 10 < 10 ^ (j + 1) := by omega
        have := IH (x / 10) (by omega) hdiv
        omega

/-- The exact characterisation, for `n ≥ 1`: *at most `n` digits* is the same
    condition as *below `10 ^ n`*. So there are exactly `10 ^ n` such numbers. -/
theorem numDigits_le_iff {n : Nat} (hn : 1 ≤ n) (x : Nat) :
    numDigits x ≤ n ↔ x < 10 ^ n :=
  ⟨lt_pow_of_numDigits_le x n, numDigits_le_of_lt_pow n x hn⟩

/-! ## Finiteness -/

/-- `S` is bounded. For a set of naturals this is exactly finiteness. -/
def Bounded (S : Nat → Prop) : Prop := ∃ b, ∀ x, S x → x < b

/-- `S` is unbounded: it has members above every bound. For a set of naturals
    this is exactly infinitude. -/
def Unbounded (S : Nat → Prop) : Prop := ∀ b, ∃ x, S x ∧ b ≤ x

theorem not_bounded_of_unbounded {S : Nat → Prop} (h : Unbounded S) : ¬ Bounded S := by
  rintro ⟨b, hb⟩
  obtain ⟨x, hx, hbx⟩ := h b
  exact Nat.lt_irrefl x (Nat.lt_of_lt_of_le (hb x hx) hbx)

/-- Bounded means finite in the concrete sense: one explicit list holds all of it. -/
theorem listed_of_bounded {S : Nat → Prop} (h : Bounded S) :
    ∃ l : List Nat, ∀ x, S x → x ∈ l := by
  obtain ⟨b, hb⟩ := h
  exact ⟨List.range b, fun x hx => List.mem_range.mpr (hb x hx)⟩

/-! ## The note's argument, and where it holds

This is the intuition stated correctly, and it is a theorem: if *one* `n` bounds
the digit count of every member, the set has at most `10 ^ n` members. -/

theorem finite_of_uniform_digit_bound {S : Nat → Prop} {n : Nat}
    (h : ∀ x, S x → numDigits x ≤ n) :
    ∃ l : List Nat, (∀ x, S x → x ∈ l) ∧ l.length = 10 ^ n :=
  ⟨List.range (10 ^ n),
   fun x hx => List.mem_range.mpr (lt_pow_of_numDigits_le x n (h x hx)),
   List.length_range⟩

/-! ## And where it fails

Two statements that look alike and are not. The first is true of the naturals.
The second is what the argument needs, and it is false. -/

/-- Every natural number has a finite digit count. `∀ x, ∃ n`. -/
theorem each_has_finite_digits : ∀ x : Nat, ∃ n, numDigits x ≤ n :=
  fun x => ⟨numDigits x, Nat.le_refl _⟩

/-- No single `n` bounds the digit count of every natural. `¬ ∃ n, ∀ x`. -/
theorem no_uniform_digit_bound : ¬ ∃ n, ∀ x : Nat, numDigits x ≤ n := by
  rintro ⟨n, hn⟩
  exact Nat.lt_irrefl _ (lt_pow_of_numDigits_le (10 ^ n) n (hn _))

/-- **The swap.** Moving the quantifier is the whole distance between the note's
    premise and its conclusion. -/
theorem the_quantifier_swap :
    (∀ x : Nat, ∃ n, numDigits x ≤ n) ∧ ¬ (∃ n, ∀ x : Nat, numDigits x ≤ n) :=
  ⟨each_has_finite_digits, no_uniform_digit_bound⟩

/-- **The claim as literally stated is false.** The naturals are unbounded, hence
    infinite, and yet every one of their members has a finite digit count. No
    member has infinitely many digits -- there is no such natural number. -/
theorem unbounded_set_of_finite_digit_numbers :
    Unbounded (fun _ : Nat => True) ∧ ∀ x : Nat, ∃ n, numDigits x = n ∧ x < 10 ^ n :=
  ⟨fun b => ⟨b, trivial, Nat.le_refl b⟩,
   fun x => ⟨numDigits x, rfl, lt_pow_of_numDigits_le x _ (Nat.le_refl _)⟩⟩

/-! ## Where the infinitely many digit places are -/

/-- **The answer to the note's question.** An unbounded set must contain numbers of
    more than `n` digits, for every `n`. The unboundedly many digit places are
    spread across the set; no member holds infinitely many of them. -/
theorem unbounded_digit_lengths {S : Nat → Prop} (h : Unbounded S) :
    ∀ n, ∃ x, S x ∧ n < numDigits x := by
  intro n
  obtain ⟨x, hx, hge⟩ := h (10 ^ n)
  refine ⟨x, hx, Nat.lt_of_not_le (fun hle => ?_)⟩
  exact absurd (lt_pow_of_numDigits_le x n hle) (Nat.not_lt.mpr hge)

/-- The contrapositive, which is the note's premise doing its proper work: a set
    whose digit lengths *are* bounded is finite. -/
theorem bounded_of_bounded_digit_lengths {S : Nat → Prop} {n : Nat}
    (h : ∀ x, S x → numDigits x ≤ n) : Bounded S :=
  ⟨10 ^ n, fun x hx => lt_pow_of_numDigits_le x n (h x hx)⟩

/-! ## Sanity checks

The theorems above would be worthless if `numDigits` did not count digits, so
here it is doing so. -/

section Sanity

example : numDigits 0 = 1 := by simp [numDigits]
example : numDigits 9 = 1 := by simp [numDigits]
example : numDigits 10 = 2 := by simp [numDigits]
example : numDigits 99 = 2 := by simp [numDigits]
example : numDigits 100 = 3 := by simp [numDigits]
example : numDigits 999999 = 6 := by simp [numDigits]
example : numDigits 1000000 = 7 := by simp [numDigits]

/-- The `1 ≤ n` side condition on `numDigits_le_iff` is load-bearing, not
    decoration: at `n = 0` the two conditions come apart, because zero is
    written with one digit. Everywhere else they agree. -/
theorem le_iff_fails_only_at_zero : ¬ (numDigits 0 ≤ 0) ∧ (0 : Nat) < 10 ^ 0 := by
  refine ⟨by simp [numDigits], by simp⟩

end Sanity

end Digits

/-! ## Axiom audit

Nothing here rests on anything but Lean's own axioms, and `sorryAx` -- the marker
for a result that was assumed rather than proved -- appears nowhere. -/

#print axioms Digits.lt_pow_of_numDigits_le
#print axioms Digits.numDigits_le_of_lt_pow
#print axioms Digits.numDigits_le_iff
#print axioms Digits.finite_of_uniform_digit_bound
#print axioms Digits.each_has_finite_digits
#print axioms Digits.no_uniform_digit_bound
#print axioms Digits.the_quantifier_swap
#print axioms Digits.unbounded_set_of_finite_digit_numbers
#print axioms Digits.unbounded_digit_lengths
#print axioms Digits.bounded_of_bounded_digit_lengths
#print axioms Digits.listed_of_bounded
