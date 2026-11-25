import PEqualNP.Outside.L_meta_11641
import PEqualNP.Outside.L_meta_8646

namespace PEqualNP.Outside.L_meta_14446
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8646_aux

private def edgeFn (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)

private def circuit : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [18, 16]⟩], 19⟩

private theorem basis : ∀ g ∈ circuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [circuit]

set_option maxRecDepth 12000 in
private theorem circuit_eval : ∀ x : Fin 8 → Bool,
    circuit.eval (List.ofFn x) = edgeFn x := by decide +kernel

set_option maxRecDepth 12000 in
private theorem table_eval : ∀ x : Fin 8 → Bool, edgeFn x = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

private def relabelInput : Fin 8 → Fin 8 := ![1, 3, 7, 2, 4, 0, 5, 6]

open PEqualNP.Outside.L_meta_11641 PEqualNP.Outside.L_meta_11641.Signed in
private theorem binary_lower (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = edgeFn x) :
    11 ≤ binaryCost gs := by
  let F : (Fin 8 → Bool) → Bool := fun x => edgeFn (x ∘ relabelInput)
  let gs' := gs.map (relGate 8 8 relabelInput)
  let o' := wmap 8 8 relabelInput o
  have ok : ∀ g ∈ gs', legal g := by
    intro g h
    obtain ⟨g₀, h₀, rfl⟩ := List.mem_map.mp h
    exact ⟨(hg g₀ h₀).1, by simpa [relGate] using (hg g₀ h₀).2⟩
  have ev : ∀ x, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = F x := by
    intro x
    exact ((rel_fold 8 8 relabelInput gs _ _ (rel_init 8 8 relabelInput x)).2.2 o).trans
      (he (x ∘ relabelInput))
  have sz : binaryCost gs' = binaryCost gs := by
    change (List.filter isBinary (gs.map (relGate 8 8 relabelInput))).length = _
    rw [List.filter_map, List.length_map]
    rfl
  obtain ⟨rs, u, hok, hlt, hev⟩ := drop_one_var (7 : Fin 8) F
    (fun j => decide (j.val = 0)) (fun _ => false) (fun _ => true)
    (by decide +kernel) (by decide +kernel) gs' o' ok ev
  have matchBase : ∀ y : Fin 7 → Bool, F (insAt (7 : Fin 8) false y) = F7 y := by
    decide +kernel
  have hb := bound7 rs u hok (fun y => (hev y).trans (matchBase y))
  omega

end PEqualNP.Outside.L_meta_14446

open PEqualNP.Outside.L_meta_14446 PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_11641.Signed in
theorem PEqualNP.Outside.L_meta_14446 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legalG _ computes
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g, hg, hop⟩ := hn
    have short : binaryCost gates < gates.length := by
      exact (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, hg, by simp [isBinary, hop]⟩
    have hb := binary_lower gates o legalG (fun x => (computes x).trans (table_eval x).symm)
    exact ⟨circuit.gates, circuit.output, basis, (show circuit.gates.length = 12 from rfl).le.trans (by omega),
      fun x => (circuit_eval x).trans (table_eval x)⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (legalG g hg).2⟩, le_rfl, computes⟩
    rcases (legalG g hg).1 with ha | ho | hnot
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn ⟨g, hg, hnot⟩).elim
