import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_142
open PEqualNP.MetaComplexity

def vars {n : ℕ} : DMFormula n → Finset (Fin n)
  | .lit i _ => {i}
  | .and A B => vars A ∪ vars B
  | .or A B => vars A ∪ vars B

lemma vars_nonempty {n : ℕ} (A : DMFormula n) : (vars A).Nonempty := by
  induction A with
  | lit i b => exact ⟨i, by simp [vars]⟩
  | and A B hA hB => exact hA.mono Finset.subset_union_left
  | or A B hA hB => exact hA.mono Finset.subset_union_left

lemma vars_card {n : ℕ} (A : DMFormula n) : (vars A).card ≤ A.leaves := by
  induction A with
  | lit i b => simp [vars, DMFormula.leaves]
  | and A B hA hB => exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add hA hB)
  | or A B hA hB => exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add hA hB)

lemma eval_agree {n : ℕ} (A : DMFormula n) (x y : Fin n → Bool) :
    (∀ i ∈ vars A, x i = y i) → A.eval x = A.eval y := by
  induction A with
  | lit i b =>
    intro h
    have hi := h i (by simp [vars])
    simp [DMFormula.eval, hi]
  | and A B hA hB =>
    intro h
    have ha := hA (fun i hi => h i (Finset.mem_union_left _ hi))
    have hb := hB (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [DMFormula.eval, ha, hb]
  | or A B hA hB =>
    intro h
    have ha := hA (fun i hi => h i (Finset.mem_union_left _ hi))
    have hb := hB (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [DMFormula.eval, ha, hb]

lemma vars_univ {n : ℕ} (A : DMFormula n) (f : (Fin n → Bool) → Bool)
    (he : ∀ x, A.eval x = f x)
    (hd : ∀ i, ∃ x, f (Function.update x i (!x i)) ≠ f x) : vars A = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  obtain ⟨x, hx⟩ := hd i
  apply hx
  rw [← he, ← he]
  apply eval_agree
  intro j hj
  have hji : j ≠ i := by rintro rfl; exact hi hj
  simp [hji]

def op (o a b : Bool) : Bool := if o then a && b else a || b

def SplitFails {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ (o : Bool) (m : Fin n → Bool), (∃ i, m i = true) → (∃ i, m i = false) →
    ∃ x y : Fin n → Bool, f x = o ∧ f y = o ∧
      f (fun i => if m i then x i else y i) = !o

lemma split_obstruction {n : ℕ} (o : Bool) (A B : DMFormula n)
    (f : (Fin n → Bool) → Bool)
    (hall : vars A ∪ vars B = Finset.univ)
    (hlen : A.leaves + B.leaves ≤ n)
    (he : ∀ x, op o (A.eval x) (B.eval x) = f x)
    (hfail : SplitFails f) : False := by
  have ha := vars_card A
  have hb := vars_card B
  have hcard := Finset.card_union_add_card_inter (vars A) (vars B)
  rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
  have hdis : Disjoint (vars A) (vars B) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply Finset.card_eq_zero.mp
    omega
  let m : Fin n → Bool := fun i => decide (i ∈ vars A)
  have hm₁ : ∃ i, m i = true := by
    obtain ⟨i, hi⟩ := vars_nonempty A
    exact ⟨i, by simp [m, hi]⟩
  have hm₂ : ∃ i, m i = false := by
    obtain ⟨i, hi⟩ := vars_nonempty B
    have hni : i ∉ vars A := fun h => Finset.disjoint_left.mp hdis h hi
    exact ⟨i, by simp [m, hni]⟩
  obtain ⟨x, y, hx, hy, hz⟩ := hfail o m hm₁ hm₂
  let z : Fin n → Bool := fun i => if m i then x i else y i
  have hAx : A.eval z = A.eval x := by
    apply eval_agree
    intro i hi
    simp [z, m, hi]
  have hBy : B.eval z = B.eval y := by
    apply eval_agree
    intro i hi
    have hni : i ∉ vars A := fun h => Finset.disjoint_left.mp hdis h hi
    simp [z, m, hni]
  have hx' := (he x).trans hx
  have hy' := (he y).trans hy
  change f z = !o at hz
  rw [← he z, hAx, hBy] at hz
  cases o <;> simp [op] at hx' hy' hz <;> simp_all

lemma no_small_formula {n : ℕ} (f : (Fin n → Bool) → Bool) (hn : 2 ≤ n)
    (hd : ∀ i, ∃ x, f (Function.update x i (!x i)) ≠ f x)
    (hfail : SplitFails f) : ¬ HasLeafSize n f n := by
  rintro ⟨A, hs, he⟩
  have hall := vars_univ A f he hd
  cases A with
  | lit i b =>
    have hc := congrArg Finset.card hall
    simp [vars] at hc
    omega
  | and A B => exact split_obstruction true A B f hall hs he hfail
  | or A B => exact split_obstruction false A B f hall hs he hfail

def target (x : Fin 5 → Bool) : Bool :=
  (x 0 && (x 1 || x 2)) || ((x 1 || x 2) && x 3) || (x 3 && x 4)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma essential : ∀ i : Fin 5, ∃ x : Fin 5 → Bool,
    target (Function.update x i (!x i)) ≠ target x := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma split_fails : SplitFails target := by
  unfold SplitFails
  decide

lemma upper : HasLeafSize 5 target 6 := by
  refine ⟨.or (.and (.or (.lit 0 true) (.lit 3 true)) (.or (.lit 1 true) (.lit 2 true)))
    (.and (.lit 3 true) (.lit 4 true)), by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_142

open PEqualNP.Outside.L_meta_142 in
theorem PEqualNP.Outside.L_meta_142 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 5 (fun x : Fin 5 → Bool => (x 0 && (x 1 || x 2)) || ((x 1 || x 2) && x 3) || (x 3 && x 4)) s ↔ 6 ≤ s := by
  intro s
  change PEqualNP.MetaComplexity.HasLeafSize 5 target s ↔ 6 ≤ s
  constructor
  · rintro ⟨A, hs, he⟩
    by_contra h
    exact no_small_formula target (by decide) essential split_fails
      ⟨A, by omega, he⟩
  · intro hs
    obtain ⟨A, hA, he⟩ := upper
    exact ⟨A, le_trans hA hs, he⟩
