import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4610

-- A chain obtains each value by a binary operation on previously available values.
def Chain (base xs : List ℕ) : Prop :=
  ∀ i : Fin xs.length, ∃ a ∈ base ++ xs.take i.val, ∃ b ∈ base ++ xs.take i.val,
    xs.get i = a &&& b ∨ xs.get i = a ||| b

private theorem chainCons (base : List ℕ) (x : ℕ) (xs : List ℕ) :
    Chain base (x :: xs) ↔
      (∃ a ∈ base, ∃ b ∈ base, x = a &&& b ∨ x = a ||| b) ∧
        Chain (base ++ [x]) xs := by
  constructor
  · intro h
    refine ⟨?_, fun i ↦ ?_⟩
    · simpa using h ⟨0, by simp⟩
    · simpa [List.append_assoc] using h i.succ
  · intro ⟨hx, hxs⟩ i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hx
    · simpa [List.append_assoc] using hxs j

-- Replay a chain over the original inputs before projecting its values through the mask.
theorem liftChain (base : List ℕ) (mask : ℕ) (xs : List ℕ)
    (h : Chain (base.map (fun v => v &&& mask)) xs) :
    ∃ ys : List ℕ, ys.length = xs.length ∧ Chain base ys ∧
      ys.map (fun v => v &&& mask) = xs := by
  induction xs generalizing base with
  | nil => exact ⟨[], rfl, fun i ↦ Fin.elim0 i, rfl⟩
  | cons x xs ih =>
    obtain ⟨⟨a, ha, b, hb, hop⟩, htail⟩ := (chainCons _ _ _).mp h
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    have step (y : ℕ) (hy : y &&& mask = x) (ho : y = a' &&& b' ∨ y = a' ||| b') :
        ∃ ys : List ℕ, ys.length = (x :: xs).length ∧ Chain base ys ∧
          ys.map (fun v ↦ v &&& mask) = x :: xs := by
      have ht : Chain ((base ++ [y]).map (fun v ↦ v &&& mask)) xs := by
        simpa [List.map_append, hy] using htail
      obtain ⟨ys, hlen, hchain, hmap⟩ := ih (base ++ [y]) ht
      refine ⟨y :: ys, by simp [hlen], (chainCons _ _ _).mpr ?_, by simp [hy, hmap]⟩
      exact ⟨⟨a', ha', b', hb', ho⟩, hchain⟩
    rcases hop with hop | hop
    · refine step (a' &&& b') (?_ : (a' &&& b') &&& mask = x) (Or.inl rfl)
      rw [hop]
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_and]
      generalize a'.testBit i = u, b'.testBit i = v, mask.testBit i = m
      decide +revert
    · exact step (a' ||| b') ((Nat.and_or_distrib_right _ _ _).trans hop.symm)
        (Or.inr rfl)


theorem chainClosed {base xs : List ℕ} (chain : Chain base xs) (P : ℕ → Prop)
    (initial : ∀ a ∈ base, P a)
    (andClosed : ∀ a b, P a → P b → P (a &&& b))
    (orClosed : ∀ a b, P a → P b → P (a ||| b)) :
    ∀ a ∈ base ++ xs, P a := by
  have atGate (i : ℕ) (hi : i < xs.length) : P xs[i] := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      obtain ⟨a, ha, b, hb, hab⟩ := chain ⟨i, hi⟩
      have operand (v : ℕ) (hv : v ∈ base ++ xs.take i) : P v := by
        rcases List.mem_append.mp hv with h | h
        · exact initial v h
        · obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp h
          exact ih j (lt_of_lt_of_le hj (min_le_left _ _)) _
      change xs[i] = _ ∨ xs[i] = _ at hab
      rcases hab with h | h
      · rw [h]
        exact andClosed a b (operand a ha) (operand b hb)
      · rw [h]
        exact orClosed a b (operand a ha) (operand b hb)
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact initial a h
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
    exact atGate i hi

theorem bitImplication {base xs : List ℕ} (chain : Chain base xs) (j i : ℕ)
    (initial : ∀ v ∈ base, v.testBit j = true → v.testBit i = true) :
    ∀ v ∈ base ++ xs, v.testBit j = true → v.testBit i = true := by
  apply chainClosed chain _ initial
  · intro a b ha hb h
    simp only [Nat.testBit_and, Bool.and_eq_true] at h ⊢
    exact ⟨ha h.1, hb h.2⟩
  · intro a b ha hb h
    simp only [Nat.testBit_or, Bool.or_eq_true] at h ⊢
    exact h.imp ha hb

theorem recover {base xs : List ℕ} {mask target v : ℕ} (chain : Chain base xs)
    (rows : ∀ i : ℕ, ∃ j : ℕ, mask.testBit j = true ∧ target.testBit j = target.testBit i ∧
      ∀ a ∈ base, if target.testBit i = true then a.testBit j = true → a.testBit i = true
        else a.testBit i = true → a.testBit j = true)
    (hv : v ∈ base ++ xs) (hm : v &&& mask = target &&& mask) :
    v = target := by
  apply Nat.eq_of_testBit_eq
  intro i
  obtain ⟨j, retained, same, entails⟩ := rows i
  have hj : v.testBit j = target.testBit i := by
    have h := congrArg (fun t : ℕ => t.testBit j) hm
    simpa only [Nat.testBit_and, retained, Bool.and_true, same] using h
  cases bit : target.testBit i with
  | false =>
    simp only [bit, Bool.false_eq_true, ite_false] at entails
    cases h : v.testBit i with
    | false => rfl
    | true =>
      have bad := bitImplication chain i j entails v hv h
      simp [bad, bit] at hj
  | true =>
    simp only [bit, ite_true] at entails
    exact bitImplication chain j i entails v hv (hj.trans bit)

end PEqualNP.Outside.L_meta_4610

open PEqualNP.Outside.L_meta_4610

-- A retained bit with the same target value forces each discarded bit.
theorem PEqualNP.Outside.L_meta_4610 :
    have x1 : List ℕ → List ℕ → Prop := fun x1 x2 =>
      ∀ x3 : Fin x2.length, ∃ x4 ∈ x1 ++ x2.take x3.val, ∃ x5 ∈ x1 ++ x2.take x3.val,
        x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5
    have x2 : List ℕ → ℕ → ℕ → Prop := fun x2 x3 x4 =>
      ∀ x5 : ℕ, ∃ x6 : ℕ, x3.testBit x6 = true ∧ x4.testBit x6 = x4.testBit x5 ∧
        ∀ x7 ∈ x2, if x4.testBit x5 = true then x7.testBit x6 = true → x7.testBit x5 = true
          else x7.testBit x5 = true → x7.testBit x6 = true
    ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x2 x3 x4 x5 →
      have x8 := x3.map (fun x8 => x8 &&& x4)
      x1 x8 x6 → x5 &&& x4 ∈ x8 ++ x6 →
        ∃ x11 : List ℕ, x11.length ≤ x6.length ∧ x1 x3 x11 ∧ x5 ∈ x3 ++ x11 := by
  dsimp only
  intro base mask target xs rows chain output
  obtain ⟨ys, length_eq, lifted, proj⟩ := liftChain base mask xs chain
  refine ⟨ys, length_eq.le, lifted, ?_⟩
  change target &&& mask ∈ base.map (fun v => v &&& mask) ++ xs at output
  rw [← proj, ← List.map_append] at output
  obtain ⟨v, hv, hm⟩ := List.mem_map.mp output
  exact recover lifted rows hv hm ▸ hv
