import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

-- The wires start with the inputs and have one more entry per gate.
lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool, ∃ r : List Bool,
    wiresFrom gs w = w ++ r ∧ r.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨r, hr, hlen⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ r, ?_, ?_⟩
    · have hstep : wiresFrom (g :: gs) w =
          wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) := rfl
      rw [hstep, hr, List.append_assoc]
    · simp [hlen]

lemma eval_input (gs : List Gate) (j : ℕ) (x : Fin 13 → Bool) (hj : j < 13) :
    Circuit.eval ⟨gs, j⟩ (List.ofFn x) = x ⟨j, hj⟩ := by
  obtain ⟨r, hr, _⟩ := wiresFrom_prefix gs (List.ofFn x)
  show (wiresFrom gs (List.ofFn x)).getD j false = x ⟨j, hj⟩
  rw [hr, List.getD_append _ _ _ _ (by simpa using hj)]
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

lemma eval_beyond (gs : List Gate) (j : ℕ) (x : Fin 13 → Bool) (hj : 13 + gs.length ≤ j) :
    Circuit.eval ⟨gs, j⟩ (List.ofFn x) = false := by
  obtain ⟨r, hr, hlen⟩ := wiresFrom_prefix gs (List.ofFn x)
  show (wiresFrom gs (List.ofFn x)).getD j false = false
  rw [hr, List.getD_eq_default]
  simp only [List.length_append, List.length_ofFn]
  omega

lemma not_both : ∀ t : Fin 13, t ≠ 0 →
    (0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∨
    (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  decide

lemma escapes : ∀ t : Fin 13, t ≠ 0 →
    ∃ v ∈ ({0, 0 + 1, 0 + 3, 0 + 9} : Finset (Fin 13)), v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
  decide

end PEqualNP.Outside.L_meta_1570

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o _ _ hcorr
  have h0mem : (0 : Fin 13) ∈ L 0 := by rw [hL]; decide
  have h1mem : (1 : Fin 13) ∈ L 0 := by rw [hL]; decide
  have he0 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    rw [hcorr 0 _ (Or.inl (by simp))]
    simp only [decide_eq_true_eq]
    exact ⟨0, h0mem, by simp⟩
  have he1 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    rw [hcorr 0 _ (Or.inr (Or.inl (by simp)))]
    simp only [decide_eq_true_eq]
    exact ⟨1, h1mem, by simp⟩
  have hge : 13 ≤ o 0 := by
    by_contra hlt
    push_neg at hlt
    have a0 := he0
    have a1 := he1
    rw [PEqualNP.Outside.L_meta_1570.eval_input gates (o 0) _ hlt] at a0 a1
    simp only [decide_eq_true_eq] at a0 a1
    exact absurd (a0.symm.trans a1) (by decide)
  have hlt : o 0 < 13 + gates.length := by
    by_contra hge'
    push_neg at hge'
    rw [PEqualNP.Outside.L_meta_1570.eval_beyond gates (o 0) _ hge'] at he0
    exact Bool.false_ne_true he0
  refine ⟨hge, hlt, he0, he1, ?_, ?_⟩
  · rw [hcorr 0 _ (Or.inr (Or.inr (fun v hv => by simp [hv])))]
    simp only [decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
    intro v hv hv'
    exact hv' hv
  · intro t ht
    have hdom : (fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨
        (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨
        ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true := by
      rw [hL t]
      simp only [decide_eq_true_eq]
      rcases PEqualNP.Outside.L_meta_1570.not_both t ht with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rw [hcorr 0 _ hdom]
    simp only [decide_eq_true_eq]
    obtain ⟨v, hv, hvt⟩ := PEqualNP.Outside.L_meta_1570.escapes t ht
    refine ⟨v, ?_, ?_⟩
    · rw [hL 0]; exact hv
    · rw [hL t]; exact hvt
