import Mathlib.Data.List.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4671

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


private theorem rename_valid {n m : ℕ} (π : Fin n → Fin m) {i s : ℕ}
    (h : i < n + s) : renameWire π i < m + s := by
  unfold renameWire
  split
  · rename_i hi
    have hp := (π ⟨i, hi⟩).isLt
    omega
  · omega

private theorem rename_circuit {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (w : ℕ)
    (hC : Monotone2 C) (hout : C.output < n + C.size) (hw : w < n + C.size) :
    ∃ (D : Circuit) (v : ℕ), Monotone2 D ∧ D.size = C.size ∧
      D.output < m + D.size ∧ v < m + D.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) ∧
        (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn (x ∘ π))).getD w false := by
  let D : Circuit := ⟨C.gates.map (renameGate π), renameWire π C.output⟩
  have hsize : D.size = C.size := by simp [D, Circuit.size]
  refine ⟨D, renameWire π w, ?_, hsize, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ C.gates.map (renameGate π) at hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hC g₀ hg₀).1, by simpa [renameGate] using (hC g₀ hg₀).2⟩
  · rw [hsize]
    exact rename_valid π hout
  · rw [hsize]
    exact rename_valid π hw
  · intro x
    have hagree := (matching_eval π C.gates _ _ (matching_inputs π x)).2.2
    exact ⟨hagree C.output, hagree w⟩

end PEqualNP.Outside.L_meta_4671

theorem PEqualNP.Outside.L_meta_4671 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size = x4.size ∧ x9.output < x2 + x9.size ∧ x10 < x2 + x9.size ∧ ∀ (x11 : Fin x2 → Bool), x9.eval (List.ofFn x11) = x4.eval (List.ofFn (x11 ∘ x3)) ∧ (x9.wires (List.ofFn x11)).getD x10 Bool.false = (x4.wires (List.ofFn (x11 ∘ x3))).getD x5 Bool.false := by
  intro n m π C w hC hout hw
  exact PEqualNP.Outside.L_meta_4671.rename_circuit π C w hC hout hw
