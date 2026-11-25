import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6595

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

theorem veq (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) (o : GateOp)
    (s t : ℕ) (e : gs[j] = ⟨o, [s, t]⟩) (hs : s < n + j) (ht : t < n + j) :
    (run gs (List.ofFn x)).getD (n + j) false = o.eval [(run gs (List.ofFn x)).getD s false,
      (run gs (List.ofFn x)).getD t false] := by
  have := run_gate gs (List.ofFn x) j hj
  rw [List.length_ofFn, e] at this
  rw [this]
  simp [hs, ht]

theorem gate_eta {g : Gate} {o : GateOp} {l : List ℕ} (h1 : g.op = o) (h2 : g.inputs = l) :
    g = ⟨o, l⟩ := by
  cases g; cases h1; cases h2; rfl


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6595

theorem PEqualNP.Outside.L_meta_6595 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x3 → ∀ (x5 : Fin x2 × Fin x2 → Fin x1 → Bool) (x6 : Finset (Fin x2) → Fin x1 → Bool), ∃ (x7 : ℕ → Set ((Fin x2 × Fin x2) × Finset (Fin x2))), (∀ (x8 : ℕ), ∃ (x9 : Set (Fin x2 × Fin x2)) (x10 : Set (Finset (Fin x2))), x7 x8 = x9 ×ˢ x10) ∧ (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x2 × Fin x2) × Finset (Fin x2) | x5 x9.1 x8 = Bool.true ∧ x6 x9.2 x8 = Bool.false}) ∧ (∀ (x8 : Fin x3.size), ∃ x9 < x1 + ↑x8, ∃ x10 < x1 + ↑x8, (x3.gates.get x8).inputs = [x9, x10] ∧ x7 (x1 + ↑x8) ⊆ x7 x9 ∪ x7 x10) ∧ (x3.output < x1 + x3.size ∨ x7 x3.output = ∅) ∧ x7 x3.output = {x8 : (Fin x2 × Fin x2) × Finset (Fin x2) | PEqualNP.MetaComplexity.circuitFun x1 x3 (x5 x8.1) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun x1 x3 (x6 x8.2) = Bool.false} := by
  intro n N C hC φ ψ
  let V : (Fin n → Bool) → ℕ → Bool := fun z w => (PEqualNP.Outside.L_meta_6595.run C.gates (List.ofFn z)).getD w false
  have hlen : ∀ z : Fin n → Bool, (PEqualNP.Outside.L_meta_6595.run C.gates (List.ofFn z)).length = n + C.gates.length := by
    intro z; rw [PEqualNP.Outside.L_meta_6595.run_length]; simp
  refine ⟨fun w => {p | V (φ p.1) w = true ∧ V (ψ p.2) w = false}, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    refine ⟨{a | V (φ a) w = true}, {b | V (ψ b) w = false}, ?_⟩
    ext ⟨a, b⟩
    simp
  · intro i
    ext ⟨a, b⟩
    have e : ∀ z : Fin n → Bool, V z i = z i := by
      intro z
      simp only [V]
      rw [PEqualNP.Outside.L_meta_6595.run_input _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    simp only [Set.mem_setOf_eq, e]
  · intro j
    have hj : (j : ℕ) < C.gates.length := j.isLt
    obtain ⟨g1, g2, g3, g4, hop⟩ := PEqualNP.Outside.L_meta_6595.gate2 hC hj
    refine ⟨_, g3, _, g4, ?_, ?_⟩
    · rw [← g2, ← g1]; rfl
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rcases hop with ho | ho
      · have v := fun z : Fin n → Bool => PEqualNP.Outside.L_meta_6595.veq n C.gates z j hj _ _ _ (g1.trans (PEqualNP.Outside.L_meta_6595.gate_eta ho g2)) g3 g4
        have v' : ∀ z, V z (n + j) = (V z (PEqualNP.TopForm.opnd C j 0) && V z (PEqualNP.TopForm.opnd C j 1)) := by
          intro z; simpa [V, PEqualNP.CircuitLowerBounds.GateOp.eval] using v z
        simp only [v', Bool.and_eq_true, Bool.and_eq_false_iff] at ha hb
        rcases hb with hb | hb
        · exact Or.inl ⟨ha.1, hb⟩
        · exact Or.inr ⟨ha.2, hb⟩
      · have v := fun z : Fin n → Bool => PEqualNP.Outside.L_meta_6595.veq n C.gates z j hj _ _ _ (g1.trans (PEqualNP.Outside.L_meta_6595.gate_eta ho g2)) g3 g4
        have v' : ∀ z, V z (n + j) = (V z (PEqualNP.TopForm.opnd C j 0) || V z (PEqualNP.TopForm.opnd C j 1)) := by
          intro z; simpa [V, PEqualNP.CircuitLowerBounds.GateOp.eval] using v z
        simp only [v', Bool.or_eq_true, Bool.or_eq_false_iff] at ha hb
        rcases ha with ha | ha
        · exact Or.inl ⟨ha, hb.1⟩
        · exact Or.inr ⟨ha, hb.2⟩
  · by_cases h : C.output < n + C.gates.length
    · exact Or.inl h
    · right
      ext ⟨a, b⟩
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1
      simp only [V] at h1
      rw [List.getD_eq_default _ _ (by rw [hlen]; omega)] at h1
      cases h1
  · rfl
