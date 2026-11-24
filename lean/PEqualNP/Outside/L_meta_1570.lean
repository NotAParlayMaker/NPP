import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

lemma suffix (gs : List Gate) (xs : List Bool) :
    ∃ ys : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs = xs ++ ys ∧ ys.length = gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => xs.getD i false)
    obtain ⟨ys, he, hl⟩ := ih (xs ++ [b])
    refine ⟨b :: ys, ?_, by simp [hl]⟩
    simpa [List.foldl_cons, b, List.append_assoc] using he

lemma input_wire (gs : List Gate) (k : ℕ) (hk : k < 13) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gs,k⟩ (List.ofFn x) = x ⟨k,hk⟩ := by
  obtain ⟨ys, he, _⟩ := suffix gs (List.ofFn x)
  unfold Circuit.eval Circuit.wires
  rw [he]
  unfold List.getD
  simp only [List.getElem?_append, List.length_ofFn, hk, ↓reduceIte]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hk)]
  simp only [List.getElem_ofFn, Option.getD_some]

lemma absent_wire (gs : List Gate) (k : ℕ) (hk : 13 + gs.length ≤ k) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gs,k⟩ (List.ofFn x) = false := by
  obtain ⟨ys, he, hl⟩ := suffix gs (List.ofFn x)
  unfold Circuit.eval Circuit.wires
  rw [he]
  unfold List.getD
  have hlen : (List.ofFn x ++ ys).length ≤ k := by simpa only [List.length_append, List.length_ofFn, hl] using hk
  rw [List.getElem?_eq_none hlen]
  rfl

end PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ hc
  have hz : (0 : Fin 13) ∈ L 0 := by rw [hL 0]; decide
  have ho : (1 : Fin 13) ∈ L 0 := by rw [hL 0]; decide
  have e0 := hc 0 (fun v => decide (v = 0)) (Or.inl (by decide))
  have e1 := hc 0 (fun v => decide (v = 1)) (Or.inr (Or.inl (by decide)))
  have s0 : (∃ v ∈ L 0, decide (v = (0 : Fin 13)) = true) := ⟨0,hz,by decide⟩
  have s1 : (∃ v ∈ L 0, decide (v = (1 : Fin 13)) = true) := ⟨1,ho,by decide⟩
  simp only [s0, decide_true] at e0
  simp only [s1, decide_true] at e1
  refine ⟨?_, ?_, e0, e1, ?_, ?_⟩
  · by_contra! h
    rw [PEqualNP.Outside.L_meta_1570.input_wire gates (o 0) h] at e0 e1
    simp only [decide_eq_true_eq] at e0 e1
    have eq : (0 : Fin 13) = 1 := e0.symm.trans e1
    exact (by decide : (0 : Fin 13) ≠ 1) eq
  · by_contra! h
    rw [PEqualNP.Outside.L_meta_1570.absent_wire gates (o 0) h] at e0
    contradiction
  · rw [hc 0 _ (Or.inr (Or.inr (fun v hv => by simpa using hv)))]
    simp
  · intro t ht
    have sep : (0 : Fin 13) ∉ L t ∨ (1 : Fin 13) ∉ L t := by
      rw [hL t]
      fin_cases t <;> first | contradiction | decide
    rcases sep with h | h
    · rw [hc 0 _ (Or.inl (by simpa using h))]
      exact decide_eq_true ⟨0, hz, by simpa using h⟩
    · rw [hc 0 _ (Or.inr (Or.inl (by simpa using h)))]
      exact decide_eq_true ⟨1, ho, by simpa using h⟩
