import Mathlib.Data.List.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4001

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire-list invariant follows the source proof in the PermInputs helper.
-- Input positions follow the map, and gate positions keep their original order.
private def renameWire {n m : ℕ} (π : Fin n → Fin m) (i : ℕ) : ℕ :=
  if hi : i < n then (π ⟨i, hi⟩).val else i - n + m

private def renameGate {n m : ℕ} (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire π)⟩

private def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private def matching {n m : ℕ} (π : Fin n → Fin m) (u v : List Bool) : Prop :=
  n ≤ u.length ∧ v.length + n = u.length + m ∧
    ∀ i, v.getD (renameWire π i) false = u.getD i false

private lemma getD_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by simp

private lemma matching_append {n m : ℕ} (π : Fin n → Fin m) (u v : List Bool) (g : Gate)
    (hm : matching π u v) : matching π (appendGate u g) (appendGate v (renameGate π g)) := by
  obtain ⟨hu, hlen, hagree⟩ := hm
  have value : (renameGate π g).op.eval ((renameGate π g).inputs.map fun i => v.getD i false) =
      g.op.eval (g.inputs.map fun i => u.getD i false) := by
    simp only [renameGate, List.map_map]
    congr 1
    exact List.map_congr_left (fun i _ => hagree i)
  refine ⟨by simp [appendGate]; omega, by simp [appendGate]; omega, ?_⟩
  intro i
  simp only [appendGate, value]
  rcases Nat.lt_trichotomy i u.length with hi | hi | hi
  · have hv : renameWire π i < v.length := by
      unfold renameWire
      split
      · rename_i hin
        have := (π ⟨i, hin⟩).isLt
        omega
      · omega
    rw [List.getD_append _ _ _ _ hv, List.getD_append _ _ _ _ hi]
    exact hagree i
  · have hv : renameWire π i = v.length := by
      unfold renameWire
      split <;> omega
    rw [hv, hi, getD_last, getD_last]
  · have hv : v.length + 1 ≤ renameWire π i := by
      unfold renameWire
      split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma matching_eval {n m : ℕ} (π : Fin n → Fin m) (gs : List Gate) (u v : List Bool)
    (hm : matching π u v) : matching π (gs.foldl appendGate u)
      ((gs.map (renameGate π)).foldl appendGate v) := by
  induction gs generalizing u v with
  | nil => exact hm
  | cons g gs ih => exact ih _ _ (matching_append π u v g hm)

private lemma matching_inputs {n m : ℕ} (π : Fin n → Fin m) (x : Fin m → Bool) :
    matching π (List.ofFn (fun i => x (π i))) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro i
  unfold renameWire
  split
  · rename_i hi
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

private lemma relabelSize {n m : ℕ} (π : Fin n → Fin m) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize n f s) : HasCircuitSize m (fun x => f (fun i => x (π i))) s := by
  obtain ⟨C, hC, hsize, heval⟩ := h
  refine ⟨⟨C.gates.map (renameGate π), renameWire π C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hC g₀ hg₀).1, by simpa [renameGate] using (hC g₀ hg₀).2⟩
  · simpa [Circuit.size] using hsize
  · intro x
    exact ((matching_eval π C.gates _ _ (matching_inputs π x)).2.2 C.output).trans
      (heval (fun i => x (π i)))

end PEqualNP.Outside.L_meta_4001

open PEqualNP.Outside.L_meta_4001 in
theorem PEqualNP.Outside.L_meta_4001 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : (Fin x1 → Bool) → Bool) (x5 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x5 → PEqualNP.MetaComplexity.HasCircuitSize x2 (fun (x7 : Fin x2 → Bool) => x4 fun (x8 : Fin x1) => x7 (x3 x8)) x5 := by
  intro n m π f s h
  exact relabelSize π f s h
