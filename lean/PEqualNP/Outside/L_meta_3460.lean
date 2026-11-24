import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3460

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def shG (n m : ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + m) }

lemma getD_snoc (W : List Bool) (s : Bool) (i : ℕ) :
    (W ++ [s]).getD i false = if i = W.length then s else W.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma fold_prefix (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,
      by rw [List.foldl_cons, ht, step]; simp⟩

lemma fold_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step]
    simp
    omega

lemma rel_fold (n m : ℕ) (gs : List Gate) : ∀ (a b : List Bool), n ≤ a.length →
    b.length = a.length + m →
    (∀ i, b.getD (if i < n then i else i + m) false = a.getD i false) →
    ∀ i, ((gs.map (shG n m)).foldl step b).getD (if i < n then i else i + m) false =
      (gs.foldl step a).getD i false := by
  induction gs with
  | nil => intro a b _ _ h; simpa using h
  | cons g gs ih =>
    intro a b ha hb h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [step]; omega
    · simp [step]; omega
    · intro i
      have hv : (shG n m g).op.eval ((shG n m g).inputs.map fun j => b.getD j false) =
          g.op.eval (g.inputs.map fun j => a.getD j false) := by
        simp only [shG, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact h j
      rw [step, step, getD_snoc, getD_snoc, hv]
      have := h i
      split_ifs at this ⊢ <;> first | rfl | exact this | (exfalso; omega)

end PEqualNP.Outside.L_meta_3460

theorem PEqualNP.Outside.L_meta_3460 : ∀ (n : ℕ) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool), (∀ i < G0.length, ∀ w ∈ (G0.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w < n + i) → (∀ i : ℕ, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (if i < n then i else i + G0.length) false = (C.wires (List.ofFn x)).getD i false) ∧ (∀ i < G0.length, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false = ((⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false) := by
  intro n G0 C x _
  have e1 : (⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) =
      (C.gates.map (PEqualNP.Outside.L_meta_3460.shG n G0.length)).foldl
        PEqualNP.Outside.L_meta_3460.step
        (G0.foldl PEqualNP.Outside.L_meta_3460.step (List.ofFn x)) := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [List.foldl_append]
    rfl
  have hlen := PEqualNP.Outside.L_meta_3460.fold_length G0 (List.ofFn x)
  refine ⟨?_, ?_⟩
  · intro i
    rw [e1]
    refine PEqualNP.Outside.L_meta_3460.rel_fold n G0.length C.gates (List.ofFn x)
      (G0.foldl PEqualNP.Outside.L_meta_3460.step (List.ofFn x)) (by simp) (by rw [hlen]) ?_ i
    intro j
    obtain ⟨t, ht⟩ := PEqualNP.Outside.L_meta_3460.fold_prefix G0 (List.ofFn x)
    rw [ht] at hlen ⊢
    simp only [List.length_append, List.length_ofFn] at hlen
    split_ifs with hj
    · exact List.getD_append _ _ _ _ (by simpa using hj)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · intro i hi
    rw [e1]
    obtain ⟨t, ht⟩ := PEqualNP.Outside.L_meta_3460.fold_prefix
      (C.gates.map (PEqualNP.Outside.L_meta_3460.shG n G0.length))
      (G0.foldl PEqualNP.Outside.L_meta_3460.step (List.ofFn x))
    rw [ht, List.getD_append _ _ _ _ (by rw [hlen]; simp; omega)]
    rfl
