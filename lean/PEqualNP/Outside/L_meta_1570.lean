import Mathlib
import PEqualNP.Defs

/-!
# L-meta-1570: the output for the line `L 0` of `Z13` is a gate with the stated values

Every claim is the promise applied to one input: the unit vectors at `0` and `1` (true), the
input that is true exactly off `L 0` (false), and, for `t ≠ 0`, the input that is true exactly
off `L t`, which is true at `0` or at `1` because no other line holds both. An input wire would
be true at only one unit vector, and a missing wire reads `false`, so the output is a gate.
-/

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.MetaComplexity.L_meta_1570

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

-- An input wire carries its input bit.
lemma eval_input (gates : List Gate) (w : ℕ) (x : Fin 13 → Bool) (hw : w < 13) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = x ⟨w, hw⟩ := by
  change (run gates (List.ofFn x)).getD w false = x ⟨w, hw⟩
  have hl : w < (List.ofFn x).length := by simpa using hw
  rw [run_getD _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_ofFn]

-- A wire that does not exist reads false.
lemma eval_missing (gates : List Gate) (w : ℕ) (x : Fin 13 → Bool)
    (hw : 13 + gates.length ≤ w) : Circuit.eval ⟨gates, w⟩ (List.ofFn x) = false := by
  change (run gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

-- No line other than `L 0` holds both `0` and `1`.
lemma zero_or_one (t : Fin 13) (ht : t ≠ 0) :
    (0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∨
      (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  revert t
  decide

theorem main : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ heval
  have m0 : (0 : Fin 13) ∈ L 0 := by rw [hL]; decide
  have m1 : (1 : Fin 13) ∈ L 0 := by rw [hL]; decide
  have h0 : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    rw [heval 0 _ (Or.inl (by decide))]
    exact decide_eq_true ⟨0, m0, by decide⟩
  have h1 : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    rw [heval 0 _ (Or.inr (Or.inl (by decide)))]
    exact decide_eq_true ⟨1, m1, by decide⟩
  have hoff : Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false := by
    rw [heval 0 _ (Or.inr (Or.inr fun v hv => decide_eq_true hv))]
    exact decide_eq_false (by
      rintro ⟨v, hv, h⟩
      exact (of_decide_eq_true h) hv)
  have hother : ∀ t : Fin 13, t ≠ 0 →
      Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
    intro t ht
    have key := zero_or_one t ht
    rw [← hL t] at key
    rcases key with h | h
    · rw [heval 0 _ (Or.inl (decide_eq_true h))]
      exact decide_eq_true ⟨0, m0, decide_eq_true h⟩
    · rw [heval 0 _ (Or.inr (Or.inl (decide_eq_true h)))]
      exact decide_eq_true ⟨1, m1, decide_eq_true h⟩
  have hlt : o 0 < 13 + gates.length := by
    by_contra hge
    rw [eval_missing gates (o 0) _ (by omega)] at h0
    exact absurd h0 (by decide)
  have h13 : 13 ≤ o 0 := by
    by_contra hsmall
    have hs : o 0 < 13 := by omega
    have a := h0
    have b := h1
    rw [eval_input gates (o 0) _ hs] at a b
    have a' := of_decide_eq_true a
    have b' := of_decide_eq_true b
    rw [Fin.ext_iff] at a' b'
    simp at a' b'
    omega
  exact ⟨h13, hlt, h0, h1, hoff, hother⟩

end PEqualNP.MetaComplexity.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true :=
  PEqualNP.MetaComplexity.L_meta_1570.main
