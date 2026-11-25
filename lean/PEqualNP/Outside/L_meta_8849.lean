import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8849

open PEqualNP.CircuitLowerBounds

def LeW (w₁ w₂ : List Bool) : Prop :=
  w₁.length = w₂.length ∧ ∀ i, w₁.getD i false = true → w₂.getD i false = true

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Dom (g g' : Gate) : Prop :=
  ∀ w₁ w₂, LeW w₁ w₂ → g.op.eval (g.inputs.map fun i => w₁.getD i false) = true →
    g'.op.eval (g'.inputs.map fun i => w₂.getD i false) = true

theorem step_le (g g' : Gate) (hd : Dom g g') (w₁ w₂ : List Bool) (h : LeW w₁ w₂) :
    LeW (stepW w₁ g) (stepW w₂ g') := by
  refine ⟨by simp [stepW, h.1], ?_⟩
  intro j hj
  unfold stepW at hj ⊢
  by_cases hlt : j < w₁.length
  · rw [List.getD_append _ _ _ _ hlt] at hj
    rw [List.getD_append _ _ _ _ (by rw [← h.1]; exact hlt)]
    exact h.2 j hj
  · by_cases heq : j = w₁.length
    · subst heq
      have e1 : (w₁ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)]).getD w₁.length false
          = g.op.eval (g.inputs.map fun i => w₁.getD i false) := by simp
      have e2 : (w₂ ++ [g'.op.eval (g'.inputs.map fun i => w₂.getD i false)]).getD w₁.length false
          = g'.op.eval (g'.inputs.map fun i => w₂.getD i false) := by rw [h.1]; simp
      rw [e1] at hj
      rw [e2]
      exact hd w₁ w₂ h hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
      exact absurd hj (by simp)

theorem fold_le : ∀ (gs gs' : List Gate), List.Forall₂ Dom gs gs' →
    ∀ w₁ w₂, LeW w₁ w₂ → LeW (gs.foldl stepW w₁) (gs'.foldl stepW w₂)
  | [], [], _, _, _, h => h
  | g :: gs, g' :: gs', List.Forall₂.cons hd hr, w₁, w₂, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact fold_le gs gs' hr _ _ (step_le g g' hd w₁ w₂ h)

theorem eval_and_or (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

theorem dom_self (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) : Dom g g := by
  intro w₁ w₂ h
  apply eval_and_or g.op hg _ _ (by simp)
  intro t ht
  by_cases ht_lt : t < g.inputs.length
  · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
    rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
    simp only [List.getElem_map] at ht ⊢
    exact h.2 _ ht
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
    exact absurd ht (by simp)

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem getD_ofFn {N : ℕ} (y : Fin N → Bool) (i : ℕ) :
    (List.ofFn y).getD i false = if h : i < N then y ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_8849

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_8849 in
theorem PEqualNP.Outside.L_meta_8849 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (n+n) C → ∀ (A B X Y : Finset (Fin n)), A ⊆ X → B ⊆ Y → C.eval (PEqualNP.GenericRejection.incidenceInput A B) = true → C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = true := by
  intro n C hC A B X Y hA hB h
  have hF : List.Forall₂ Dom C.gates C.gates := List.forall₂_same.mpr (fun g hg => dom_self g (hC.1 g hg))
  have hL : LeW (PEqualNP.GenericRejection.incidenceInput A B) (PEqualNP.GenericRejection.incidenceInput X Y) := by
    unfold PEqualNP.GenericRejection.incidenceInput
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases h1 : i < n
    · rw [List.getD_append _ _ _ _ (by simpa using h1)] at hi ⊢
      rw [getD_ofFn, dif_pos h1] at hi ⊢
      simp only [decide_eq_true_eq] at hi ⊢
      exact hA hi
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi ⊢
      simp only [List.length_ofFn] at hi ⊢
      rw [getD_ofFn] at hi ⊢
      split_ifs at hi ⊢ with h2
      simp only [decide_eq_true_eq] at hi ⊢
      exact hB hi
  have hle := fold_le _ _ hF _ _ hL
  unfold Circuit.eval at h ⊢
  exact hle.2 _ h
