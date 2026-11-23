import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354

open PEqualNP.CircuitLowerBounds

def fm (n k r : ℕ) : ℕ := if r < n then r else if r = n then n + k else r - 1

def tr (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => ⟨g.op, g.inputs.map (fm n k)⟩ :: tr n (k + 1) gs

lemma tr_op (n : ℕ) : ∀ (k : ℕ) (gs : List Gate), (tr n k gs).map Gate.op = gs.map Gate.op
  | _, [] => rfl
  | k, g :: gs => by simp [tr, tr_op n (k + 1) gs]

lemma tr_len (n : ℕ) : ∀ (k : ℕ) (gs : List Gate),
    (tr n k gs).map (fun g => g.inputs.length) = gs.map (fun g => g.inputs.length)
  | _, [] => rfl
  | k, g :: gs => by simp [tr, tr_len n (k + 1) gs]

lemma getD_snoc (l : List Bool) (a : Bool) (r : ℕ) :
    (l ++ [a]).getD r false = if r < l.length then l.getD r false
      else if r = l.length then a else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

def Rel (n : ℕ) (W W' : List Bool) : Prop :=
  ∀ r, W.getD r false = if r < n then W'.getD r false
    else if r = n then false else W'.getD (r - 1) false

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma main (n : ℕ) : ∀ (gs : List Gate) (k : ℕ) (W W' : List Bool),
    W.length = n + 1 + k → W'.length = n + k → Rel n W W' →
    Rel n (gs.foldl step W) ((tr n k gs).foldl step W')
  | [], _, _, _, _, _, h => h
  | g :: gs, k, W, W', hW, hW', h => by
    have hv : (g.inputs.map fun i => W.getD i false) =
        ((g.inputs.map (fm n k)).map fun i => W'.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro r _
      simp only [Function.comp, fm]
      rw [h r]
      split_ifs with h1 h2
      · rfl
      · rw [List.getD_eq_default]; omega
      · rfl
    refine main n gs (k + 1) (step W g) (step W' ⟨g.op, g.inputs.map (fm n k)⟩)
      (by simp [step, hW]; omega) (by simp [step, hW']; omega) ?_
    intro r
    simp only [step]
    rw [getD_snoc, getD_snoc, getD_snoc, hW, hW', hv, h r]
    split_ifs <;> first | rfl | omega

end PEqualNP.Outside.L_meta_1354

open PEqualNP.Outside.L_meta_1354 in
theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  refine ⟨tr n 0 gates, tr_op n 0 gates, tr_len n 0 gates, ?_⟩
  intro j x _
  have h := main n gates 0 (List.ofFn x ++ [false]) (List.ofFn x) (by simp) (by simp) (by
    intro r
    rw [getD_snoc]
    simp only [List.length_ofFn]
    split_ifs <;> first | rfl | (rw [List.getD_eq_default]; simp; omega))
    (n + 1 + j)
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  change (List.foldl step (List.ofFn x) (tr n 0 gates)).getD (n + j) false =
    (List.foldl step (List.ofFn x ++ [false]) gates).getD (n + 1 + j) false
  rw [h]
  split_ifs <;> first | omega | (congr 1; omega)
