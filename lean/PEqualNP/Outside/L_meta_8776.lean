import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8776_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      exact ih j (by have : j.val < i.val := hji; omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) :=
  (fuel_succ C U C.size i i.isLt).symm

theorem and_ne_zero_iff (a b : ℕ) :
    a &&& b ≠ 0 ↔ ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  constructor
  · intro h
    by_contra hne
    simp only [not_exists, not_and] at hne
    apply h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases ha : a.testBit i with
    | false => simp
    | true =>
      have hb := hne i ha
      simp [hb]
  · rintro ⟨i, ha, hb⟩ h
    have h2 := congrArg (fun n => n.testBit i) h
    simp [Nat.testBit_and, ha, hb] at h2

abbrev mkC (x1 x2 : Fin 6 → ℕ) (x3 : Finset (Fin 6)) : AndCountCircuit 10 :=
  { size := 6
    leftVars := fun x5 : Fin 6 => {x6 : Fin 10 | (x1 x5).testBit ↑x6 = true}
    leftGates := fun x5 : Fin 6 => {x6 : Fin 6 | x6 < x5 ∧ (x1 x5).testBit (10 + ↑x6) = true}
    rightVars := fun x5 : Fin 6 => {x6 : Fin 10 | (x2 x5).testBit ↑x6 = true}
    rightGates := fun x5 : Fin 6 => {x6 : Fin 6 | x6 < x5 ∧ (x2 x5).testBit (10 + ↑x6) = true}
    outVars := ∅
    outGates := x3 }

def stepF (x1 x2 : Fin 6 → ℕ) (s : ℕ) (g : Fin 6) : ℕ :=
  if s &&& x1 g ≠ 0 ∧ s &&& x2 g ≠ 0 then s ||| 2 ^ (10 + (g : ℕ)) else s

def uSet (x7 : ℕ) : Finset (Fin 10) := {x8 : Fin 10 | x7.testBit ↑x8 = true}

def Inv (x1 x2 : Fin 6 → ℕ) (x3 : Finset (Fin 6)) (x7 k s : ℕ) : Prop :=
  (∀ b : ℕ, b < 10 → s.testBit b = x7.testBit b) ∧
    ∀ j : Fin 6, s.testBit (10 + (j : ℕ)) =
      (decide ((j : ℕ) < k) && (mkC x1 x2 x3).gateVal (uSet x7) j)

theorem side_iff (x1 x2 : Fin 6 → ℕ) (x3 : Finset (Fin 6)) (x7 s : ℕ) (g : Fin 6)
    (m : ℕ) (hm : m < 2 ^ (10 + (g : ℕ)))
    (B : Finset (Fin 10)) (F : Finset (Fin 6))
    (hB : ∀ v : Fin 10, v ∈ B ↔ m.testBit ↑v = true)
    (hF : ∀ j : Fin 6, j ∈ F ↔ (j < g ∧ m.testBit (10 + ↑j) = true))
    (hinv : Inv x1 x2 x3 x7 g s) :
    s &&& m ≠ 0 ↔
      sideTrue (uSet x7) B F g ((mkC x1 x2 x3).gateVal (uSet x7)) = true := by
  obtain ⟨h1, h2⟩ := hinv
  rw [and_ne_zero_iff, sideTrue_iff]
  constructor
  · rintro ⟨i, hs, hmi⟩
    have hlt : i < 10 + (g : ℕ) := by
      by_contra hge
      have hle : 2 ^ (10 + (g : ℕ)) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hle)
      rw [this] at hmi
      exact absurd hmi (by simp)
    by_cases hi : i < 10
    · left
      refine ⟨⟨i, hi⟩, (hB _).2 hmi, ?_⟩
      simp only [uSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h1 i hi]
      exact hs
    · right
      have hj : i - 10 < 6 := by have := g.isLt; omega
      have hi' : 10 + (i - 10) = i := by omega
      refine ⟨⟨i - 10, hj⟩, (hF _).2 ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Fin.lt_def.2 (by simp only; omega)
      · simp only
        rw [hi']
        exact hmi
      · exact Fin.lt_def.2 (by simp only; omega)
      · have h3 := h2 ⟨i - 10, hj⟩
        simp only at h3
        rw [hi', hs] at h3
        have h4 := h3.symm
        rw [Bool.and_eq_true] at h4
        exact h4.2
  · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hjg, hjv⟩)
    · refine ⟨v, ?_, (hB v).1 hvB⟩
      rw [h1 _ v.isLt]
      simpa [uSet] using hvU
    · refine ⟨10 + (j : ℕ), ?_, ((hF j).1 hjF).2⟩
      rw [h2 j, hjv]
      have : (j : ℕ) < (g : ℕ) := hjg
      simp [this]

theorem step_inv (x1 x2 : Fin 6 → ℕ) (x3 : Finset (Fin 6))
    (hb : ∀ x4 : Fin 6, x1 x4 < 2 ^ (10 + (x4 : ℕ)) ∧ x2 x4 < 2 ^ (10 + (x4 : ℕ)))
    (x7 s : ℕ) (g : Fin 6) (k : ℕ) (hk : k = (g : ℕ))
    (hinv : Inv x1 x2 x3 x7 k s) :
    Inv x1 x2 x3 x7 (k + 1) (stepF x1 x2 s g) := by
  subst hk
  have hL := side_iff x1 x2 x3 x7 s g (x1 g) (hb g).1
    ((mkC x1 x2 x3).leftVars g) ((mkC x1 x2 x3).leftGates g)
    (fun v => by simp) (fun j => by simp) hinv
  have hR := side_iff x1 x2 x3 x7 s g (x2 g) (hb g).2
    ((mkC x1 x2 x3).rightVars g) ((mkC x1 x2 x3).rightGates g)
    (fun v => by simp) (fun j => by simp) hinv
  have hcond : (s &&& x1 g ≠ 0 ∧ s &&& x2 g ≠ 0) ↔
      (mkC x1 x2 x3).gateVal (uSet x7) g = true := by
    rw [gateVal_rec, Bool.and_eq_true, hL, hR]
  obtain ⟨h1, h2⟩ := hinv
  unfold stepF
  by_cases hc : s &&& x1 g ≠ 0 ∧ s &&& x2 g ≠ 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have hgv := hcond.1 hc
    refine ⟨?_, ?_⟩
    · intro b hb10
      rw [Nat.testBit_or, Nat.testBit_two_pow, h1 b hb10]
      have : ¬ (10 + (g : ℕ) = b) := by omega
      simp [this]
    · intro j
      rw [Nat.testBit_or, Nat.testBit_two_pow, h2 j]
      by_cases hjg : j = g
      · subst hjg
        simp [hgv]
      · have hne : (j : ℕ) ≠ (g : ℕ) := fun h => hjg (Fin.ext h)
        have h10 : ¬ (10 + (g : ℕ) = 10 + (j : ℕ)) := by omega
        have hd : decide ((j : ℕ) < (g : ℕ) + 1) = decide ((j : ℕ) < (g : ℕ)) := by
          apply decide_eq_decide.mpr
          omega
        have e1 : decide (10 + (g : ℕ) = 10 + (j : ℕ)) = false := decide_eq_false h10
        rw [e1, hd, Bool.or_false]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have hgv : (mkC x1 x2 x3).gateVal (uSet x7) g = false := by
      cases hv : (mkC x1 x2 x3).gateVal (uSet x7) g with
      | false => rfl
      | true => exact absurd (hcond.2 hv) hc
    refine ⟨h1, ?_⟩
    intro j
    rw [h2 j]
    by_cases hjg : j = g
    · subst hjg
      simp [hgv]
    · have hne : (j : ℕ) ≠ (g : ℕ) := fun h => hjg (Fin.ext h)
      have hd : decide ((j : ℕ) < (g : ℕ) + 1) = decide ((j : ℕ) < (g : ℕ)) := by
        apply decide_eq_decide.mpr
        omega
      rw [hd]

theorem main (x1 x2 : Fin 6 → ℕ) (x3 : Finset (Fin 6))
    (hb : ∀ x4 : Fin 6, x1 x4 < 2 ^ (10 + (x4 : ℕ)) ∧ x2 x4 < 2 ^ (10 + (x4 : ℕ))) (x7 : ℕ) :
    (mkC x1 x2 x3).eval (uSet x7) =
      decide (∃ x8 ∈ x3, (List.foldl (stepF x1 x2) (x7 % 1024) (List.finRange 6)).testBit
        (10 + (x8 : ℕ)) = true) := by
  have h0 : Inv x1 x2 x3 x7 0 (x7 % 1024) := by
    refine ⟨?_, ?_⟩
    · intro b hb10
      have e : (1024 : ℕ) = 2 ^ 10 := by norm_num
      rw [e, Nat.testBit_mod_two_pow]
      simp [hb10]
    · intro j
      have e : (1024 : ℕ) = 2 ^ 10 := by norm_num
      rw [e, Nat.testBit_mod_two_pow]
      simp
  have e6 : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide
  rw [e6]
  simp only [List.foldl_cons, List.foldl_nil]
  have h1 := step_inv x1 x2 x3 hb x7 _ 0 0 rfl h0
  have h2 := step_inv x1 x2 x3 hb x7 _ 1 1 rfl h1
  have h3 := step_inv x1 x2 x3 hb x7 _ 2 2 rfl h2
  have h4 := step_inv x1 x2 x3 hb x7 _ 3 3 rfl h3
  have h5 := step_inv x1 x2 x3 hb x7 _ 4 4 rfl h4
  have h6 := step_inv x1 x2 x3 hb x7 _ 5 5 rfl h5
  unfold AndCountCircuit.eval
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨v, hv, _⟩ | ⟨j, hj, hjv⟩)
    · simp at hv
    · refine ⟨j, hj, ?_⟩
      rw [h6.2 j, hjv]
      simp
  · rintro ⟨j, hj, hjs⟩
    right
    refine ⟨j, hj, ?_⟩
    rw [h6.2 j, Bool.and_eq_true] at hjs
    exact hjs.2

end PEqualNP.Outside.L_meta_8776_aux

theorem PEqualNP.Outside.L_meta_8776 : ∀ (x1 x2 : Fin (6 : ℕ) → ℕ) (x3 : Finset (Fin (6 : ℕ))),   (∀ (x4 : Fin (6 : ℕ)), x1 x4 < (2 : ℕ) ^ ((10 : ℕ) + ↑x4) ∧ x2 x4 < (2 : ℕ) ^ ((10 : ℕ) + ↑x4)) →     have x5 : PEqualNP.AndCount.AndCountCircuit (10 : ℕ) := { size := (6 : ℕ), leftVars := fun (x5 : Fin (6 : ℕ)) => {x6 : Fin (10 : ℕ) | (x1 x5).testBit ↑x6 = Bool.true}, leftGates := fun (x5 : Fin (6 : ℕ)) => {x6 : Fin (6 : ℕ) | x6 < x5 ∧ (x1 x5).testBit ((10 : ℕ) + ↑x6) = Bool.true}, rightVars := fun (x5 : Fin (6 : ℕ)) => {x6 : Fin (10 : ℕ) | (x2 x5).testBit ↑x6 = Bool.true}, rightGates := fun (x5 : Fin (6 : ℕ)) => {x6 : Fin (6 : ℕ) | x6 < x5 ∧ (x2 x5).testBit ((10 : ℕ) + ↑x6) = Bool.true}, outVars := ∅, outGates := x3 : PEqualNP.AndCount.AndCountCircuit (10 : ℕ) };     have x6 : ℕ → ℕ := fun (x6 : ℕ) => List.foldl (fun (x7 : ℕ) (x8 : Fin (6 : ℕ)) => if x7 &&& x1 x8 ≠ (0 : ℕ) ∧ x7 &&& x2 x8 ≠ (0 : ℕ) then x7 ||| (2 : ℕ) ^ ((10 : ℕ) + ↑x8) else x7) (x6 % (1024 : ℕ)) (List.finRange (6 : ℕ));     ∀ (x7 : ℕ), x5.eval {x8 : Fin (10 : ℕ) | x7.testBit ↑x8 = Bool.true} = Decidable.decide (∃ x8 ∈ x3, (x6 x7).testBit ((10 : ℕ) + ↑x8) = Bool.true) := by
  intro x1 x2 x3 hb
  exact PEqualNP.Outside.L_meta_8776_aux.main x1 x2 x3 hb
