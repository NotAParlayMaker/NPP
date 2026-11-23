import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354

open PEqualNP.CircuitLowerBounds

-- The removed input is redirected past the final wire, where every read returns false.
def wire (n limit i : ℕ) : ℕ :=
  if i < n then i else if i = n then limit else i - 1

def gate (n limit : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire n limit)⟩

private theorem read_wire (xs ys : List Bool) (limit i : ℕ)
    (h : xs.length + ys.length ≤ limit) :
    (xs ++ ys).getD (wire xs.length limit i) false =
      ((xs ++ [false]) ++ ys).getD i false := by
  by_cases hi : i < xs.length
  · simp only [wire, ite_eq_left hi, List.append_assoc]
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
  by_cases he : i = xs.length
  · subst i
    simp only [wire, lt_self_iff_false, ite_false]
    rw [List.getD_eq_default _ _ (by simpa using h), List.append_assoc,
      List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · have h1 : xs.length ≤ i-1 := by omega
    have h2 : (xs ++ [false]).length ≤ i := by simp; omega
    simp only [wire, ite_eq_right hi, ite_eq_right he]
    rw [List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
    congr 1
    simp
    omega

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_values (xs : List Bool) (limit : ℕ) (gs : List Gate) (ys : List Bool)
    (h : xs.length + ys.length + gs.length ≤ limit) :
    ∃ zs : List Bool,
      (gs.map (gate xs.length limit)).foldl step (xs ++ ys) = xs ++ zs ∧
      gs.foldl step ((xs ++ [false]) ++ ys) = (xs ++ [false]) ++ zs := by
  induction gs generalizing ys with
  | nil => exact ⟨ys,rfl,rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => ((xs ++ [false]) ++ ys).getD i false)
    have hv : step (xs ++ ys) (gate xs.length limit g) = xs ++ (ys ++ [b]) := by
      simp only [step, gate, List.map_map, Function.comp_def]
      simp only [read_wire xs ys limit _ (by omega : xs.length + ys.length ≤ limit),
        List.append_assoc, b]
    have hw : step ((xs ++ [false]) ++ ys) g = (xs ++ [false]) ++ (ys ++ [b]) :=
      List.append_assoc _ _ _
    simp only [List.map_cons, List.foldl_cons, hv, hw]
    apply ih
    simp at h ⊢
    omega

end PEqualNP.Outside.L_meta_1354

open PEqualNP.Outside.L_meta_1354 in
theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  let limit := n + gates.length
  refine ⟨gates.map (gate n limit), ?_, ?_, ?_⟩
  · simp [gate, List.map_map, Function.comp_def]
  · simp [gate, List.map_map, Function.comp_def]
  · intro j x hj
    obtain ⟨zs, hnew, hold⟩ := fold_values (List.ofFn x) limit gates []
      (by simp [limit])
    simp only [List.length_ofFn, List.append_nil] at hnew hold
    change ((gates.map (gate n limit)).foldl step (List.ofFn x)).getD (n+j) false =
      (gates.foldl step (List.ofFn x ++ [false])).getD (n+1+j) false
    rw [hnew, hold]
    rw [List.getD_append_right _ _ _ _ (by simp),
      List.getD_append_right _ _ _ _ (by simp)]
    simp
