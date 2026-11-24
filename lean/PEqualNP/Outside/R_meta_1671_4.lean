import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1671_4 :
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → (C.output = 9 ∨ ∃ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some 9) ∨ (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ 9 ∈ g.inputs)) → PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) (C.size - 3)) →
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro h1 h2 h3 C hC h9 hfun
  by_contra hlt
  by_cases hl : (C.output = 9 ∨ ∃ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some 9) ∨ (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ 9 ∈ g.inputs))
  · obtain ⟨D, hD1, hD2, hD3⟩ := h2 C hC h9 hfun hl
    exact h3 ⟨D, hD1, by omega, hD3⟩
  · apply h1
    have ho : C.output ≠ 9 := fun e => hl (Or.inl e)
    have hdead : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.head? ≠ some 9) ∧ (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → 9 ∉ g.inputs) :=
      fun g hg => ⟨fun hn he => hl (Or.inr ⟨g, hg, Or.inl ⟨hn, he⟩⟩), fun hn hm => hl (Or.inr ⟨g, hg, Or.inr ⟨hn, hm⟩⟩)⟩
    obtain ⟨gs, o⟩ := C
    cases gs with
    | nil =>
      exfalso
      have h0 := h9 (fun _ => true)
      change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = (true && true) at h0
      exact absurd h0 (by decide)
    | cons g post =>
      obtain ⟨s, hs⟩ : ∃ s : ℕ → ℕ, ∀ a, s a = if a < 9 then a else a - 1 := ⟨_, fun _ => rfl⟩
      obtain ⟨R, hR⟩ : ∃ R : List Bool → List Bool → Prop, ∀ W W', R W W' ↔ (W.length = W'.length + 1 ∧ 9 ≤ W'.length ∧ ∀ a, a ≠ 9 → W'.getD (s a) false = W.getD a false) := ⟨_, fun _ _ => Iff.rfl⟩
      have key : ∀ ps : List PEqualNP.CircuitLowerBounds.Gate, (∀ g' ∈ ps, (g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2) ∧ (g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → g'.inputs.head? ≠ some 9) ∧ (g'.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → 9 ∉ g'.inputs)) → ∀ W W' : List Bool, R W W' → R (ps.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W) ((ps.map (fun g => (⟨g.op, g.inputs.map s⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W') := by
        intro ps
        induction ps with
        | nil => intro _ W W' h; exact h
        | cons g0 ps ih =>
          intro hgood W W' hRW
          obtain ⟨e1, e2, e3⟩ := (hR W W').1 hRW
          have hv : g0.op.eval ((g0.inputs.map s).map fun i => W'.getD i false) = g0.op.eval (g0.inputs.map fun i => W.getD i false) := by
            obtain ⟨⟨hop, _⟩, hd1, hd2⟩ := hgood g0 List.mem_cons_self
            obtain ⟨op, ins⟩ := g0
            rcases hop with h | h | h
            · have h' : op = PEqualNP.CircuitLowerBounds.GateOp.and := h
              subst h'
              have hn : PEqualNP.CircuitLowerBounds.GateOp.and ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
                intro e; cases e
              show PEqualNP.CircuitLowerBounds.GateOp.eval _ ((ins.map s).map fun i => W'.getD i false) = PEqualNP.CircuitLowerBounds.GateOp.eval _ (ins.map fun i => W.getD i false)
              congr 1
              rw [List.map_map]
              apply List.map_congr_left
              intro a ha
              exact e3 a (fun e => hd2 hn (by subst e; exact ha))
            · have h' : op = PEqualNP.CircuitLowerBounds.GateOp.or := h
              subst h'
              have hn : PEqualNP.CircuitLowerBounds.GateOp.or ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
                intro e; cases e
              show PEqualNP.CircuitLowerBounds.GateOp.eval _ ((ins.map s).map fun i => W'.getD i false) = PEqualNP.CircuitLowerBounds.GateOp.eval _ (ins.map fun i => W.getD i false)
              congr 1
              rw [List.map_map]
              apply List.map_congr_left
              intro a ha
              exact e3 a (fun e => hd2 hn (by subst e; exact ha))
            · have h' : op = PEqualNP.CircuitLowerBounds.GateOp.not := h
              subst h'
              cases ins with
              | nil => rfl
              | cons a rest =>
                have ha9 : a ≠ 9 := fun e => hd1 rfl (by subst e; rfl)
                show (!(W'.getD (s a) false)) = !(W.getD a false)
                rw [e3 a ha9]
          have s1 : (g0 :: ps).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W = ps.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W ++ [g0.op.eval (g0.inputs.map fun i => W.getD i false)]) := rfl
          have s2 : ((g0 :: ps).map (fun g => (⟨g.op, g.inputs.map s⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W' = (ps.map (fun g => (⟨g.op, g.inputs.map s⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W' ++ [g0.op.eval ((g0.inputs.map s).map fun i => W'.getD i false)]) := rfl
          rw [s1, s2, hv]
          apply ih (fun g' hg' => hgood g' (List.mem_cons_of_mem _ hg'))
          refine (hR _ _).2 ⟨by simp; omega, by simp; omega, ?_⟩
          intro a ha
          rcases Nat.lt_trichotomy a W.length with hw | hw | hw
          · have hlt2 : s a < W'.length := by rw [hs a]; split <;> omega
            rw [List.getD_append _ _ _ _ hlt2, List.getD_append _ _ _ _ hw]
            exact e3 a ha
          · have he : s a = W'.length := by rw [hs a]; split <;> omega
            rw [he, hw]
            simp
          · have hge : W'.length + 1 ≤ s a := by rw [hs a]; split <;> omega
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      refine ⟨⟨post.map (fun g => (⟨g.op, g.inputs.map s⟩ : PEqualNP.CircuitLowerBounds.Gate)), s o⟩, ?_, ?_, ?_⟩
      · intro g' hg'
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg'
        obtain ⟨hA, hB⟩ := hC g0 (List.mem_cons_of_mem _ hg0)
        exact ⟨hA, show (g0.inputs.map s).length ≤ 2 by rw [List.length_map]; exact hB⟩
      · have hl2 : ¬ 16 ≤ (g :: post).length := hlt
        show (post.map _).length ≤ 14
        rw [List.length_map]
        rw [List.length_cons] at hl2
        omega
      · intro x
        refine Eq.trans ?_ (congrFun hfun x)
        show ((post.map (fun g => (⟨g.op, g.inputs.map s⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD (s o) false = (post.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD o false
        have hinit : R (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]) (List.ofFn x) := by
          refine (hR _ _).2 ⟨by simp, by simp, ?_⟩
          intro a ha
          rw [hs a]
          split
          · rename_i h
            rw [List.getD_append _ _ _ _ (by simpa using h)]
          · rename_i h
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        have hgood : ∀ g' ∈ post, (g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2) ∧ (g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → g'.inputs.head? ≠ some 9) ∧ (g'.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → 9 ∉ g'.inputs) :=
          fun g' hg' => ⟨hC g' (List.mem_cons_of_mem _ hg'), hdead g' (List.mem_cons_of_mem _ hg')⟩
        exact ((hR _ _).1 (key post hgood _ _ hinit)).2.2 o ho
