import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3460_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (x1 : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map x1⟩

def sh (n m k : ℕ) : ℕ := if k < n then k else k + m

lemma fold_len (gs : List Gate) : ∀ (W : List Bool), (gs.foldl stepW W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma fold_pre (gs : List Gate) : ∀ (W : List Bool) (k : ℕ), k < W.length →
    (gs.foldl stepW W).getD k false = W.getD k false := by
  induction gs with
  | nil => intro W k _; rfl
  | cons g gs ih =>
    intro W k hk
    rw [List.foldl_cons, ih _ k (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hk

lemma step_inv (n m : ℕ) (W Y : List Bool) (g : Gate) (hl : W.length = Y.length + m)
    (hn : n ≤ Y.length)
    (hv : ∀ k, W.getD (sh n m k) false = Y.getD k false) :
    ∀ k, (stepW W (reGate (sh n m) g)).getD (sh n m k) false = (stepW Y g).getD k false := by
  intro k
  have hm : (g.inputs.map (sh n m)).map (fun i => W.getD i false)
      = g.inputs.map (fun i => Y.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hv i)
  show (W ++ [g.op.eval ((g.inputs.map (sh n m)).map fun i => W.getD i false)]).getD (sh n m k) false
    = (Y ++ [g.op.eval (g.inputs.map fun i => Y.getD i false)]).getD k false
  rw [hm]
  by_cases hk : k < Y.length
  · have hs : sh n m k < W.length := by
      unfold sh
      split_ifs <;> omega
    rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hk, hv k]
  · have hs : sh n m k = k + m := by
      unfold sh
      rw [if_neg (by omega)]
    rw [hs, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    congr 1
    omega

lemma fold_inv (n m : ℕ) (gs : List Gate) :
    ∀ (W Y : List Bool), W.length = Y.length + m → n ≤ Y.length →
    (∀ k, W.getD (sh n m k) false = Y.getD k false) →
    ∀ k, ((gs.map (reGate (sh n m))).foldl stepW W).getD (sh n m k) false = (gs.foldl stepW Y).getD k false := by
  induction gs with
  | nil => intro W Y _ _ hv; exact hv
  | cons g gs ih =>
    intro W Y hl hn hv
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_ (step_inv n m W Y g hl hn hv)
    · simp [stepW, hl]; omega
    · simp [stepW]; omega

lemma main (n : ℕ) (G0 gs : List Gate) (x : Fin n → Bool) :
    (∀ i : ℕ, ((G0 ++ gs.map (reGate (sh n G0.length))).foldl stepW (List.ofFn x)).getD (sh n G0.length i) false
      = (gs.foldl stepW (List.ofFn x)).getD i false) ∧
    (∀ i < G0.length, ((G0 ++ gs.map (reGate (sh n G0.length))).foldl stepW (List.ofFn x)).getD (n + i) false
      = (G0.foldl stepW (List.ofFn x)).getD (n + i) false) := by
  have hlen : (G0.foldl stepW (List.ofFn x)).length = n + G0.length := by
    rw [fold_len]; simp
  constructor
  · rw [List.foldl_append]
    refine fold_inv n G0.length gs _ _ (by rw [hlen]; simp) (by simp) ?_
    intro k
    by_cases hk : k < n
    · have hs : sh n G0.length k = k := by unfold sh; rw [if_pos hk]
      rw [hs]
      exact fold_pre G0 _ k (by simpa using hk)
    · have hs : sh n G0.length k = k + G0.length := by unfold sh; rw [if_neg hk]
      rw [hs, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
  · intro i hi
    rw [List.foldl_append]
    exact fold_pre _ _ _ (by omega)

end PEqualNP.Outside.L_meta_3460_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3460_aux in
theorem PEqualNP.Outside.L_meta_3460 : ∀ (n : ℕ) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool), (∀ i < G0.length, ∀ w ∈ (G0.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w < n + i) → (∀ i : ℕ, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (if i < n then i else i + G0.length) false = (C.wires (List.ofFn x)).getD i false) ∧ (∀ i < G0.length, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false = ((⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false) := by
  intro n G0 C x _
  exact main n G0 C.gates x
