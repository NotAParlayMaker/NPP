import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_5284_727
    (prune : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    let exactG := fun C : Circuit => circuitFun n C = NestedCover.graphFun G ∅
    let quiet := fun C : Circuit => ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 1 → gateVal n C j (fun v => decide (v ∈ S)) = false
    let essential := fun C : Circuit => ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∃ a b, G.Adj a b ∧ (Circuit.mk (C.gates.set j ⟨.or, []⟩) C.output).eval
        (List.ofFn (pairInput a b)) = false
    ∀ C : Circuit, Monotone2 C → exactG C → quiet C →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ exactG D ∧ quiet D ∧ essential D)
    (clean : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    let exactG := fun C : Circuit => circuitFun n C = NestedCover.graphFun G ∅
    let quiet := fun C : Circuit => ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 1 → gateVal n C j (fun v => decide (v ∈ S)) = false
    let essential := fun C : Circuit => ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∃ a b, G.Adj a b ∧ (Circuit.mk (C.gates.set j ⟨.or, []⟩) C.output).eval
        (List.ofFn (pairInput a b)) = false
    (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
    (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
    ∀ C : Circuit, Monotone2 C → exactG C → quiet C → essential C →
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ exactG D ∧
      ∀ j g, D.gates[j]? = some g → g.op = GateOp.and →
      ∀ S : Finset (Fin n), S.card ≤ 2 → gateVal n D j (fun v => decide (v ∈ S)) = true →
      ∃ a ∈ S, ∃ b ∈ S, G.Adj a b) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = x4 x11) → x6 x9 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size ≤ x9.size ∧ (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = Bool.true) ∧ (∀ (x14 : Fin x1), x13.eval (List.ofFn (x5 {x14})) = Bool.false) ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x13.gates[x14]? = Option.some x15 → x15.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x18 : Finset (Fin x1)), x18.card ≤ (2 : ℕ) → (x13.wires (List.ofFn (x5 x18))).getD (x1 + x14) Bool.false = Bool.true → ∃ x21 ∈ x18, ∃ x22 ∈ x18, x2.Adj x21 x22 := by

  intro n G inst
  dsimp only
  intro htri hsq C hm hf hq
  have hgraph : circuitFun n C = NestedCover.graphFun G ∅ := by
    funext x
    change C.eval (List.ofFn x) = (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) || _)
    simpa using hf x
  obtain ⟨D,hmD,hsD,hfD,hqD,heD⟩ := prune n G C hm hgraph hq
  obtain ⟨E,hmE,hsE,hout,hsafe⟩ := clean n G htri hsq D hmD hfD hqD heD
  have correct (S : Finset (Fin n)) :
      E.eval (List.ofFn (fun v => decide (v ∈ S))) = decide (∃ a ∈ S, ∃ b ∈ S, G.Adj a b) := by
    have h := congrFun hout (fun v => decide (v ∈ S))
    change E.eval _ = (decide (∃ a ∈ (∅ : Finset (Fin n)), decide (a ∈ S) = true) ||
      decide (∃ a b, G.Adj a b ∧ decide (a ∈ S) = true ∧ decide (b ∈ S) = true)) at h
    simpa [and_comm,and_left_comm,and_assoc,exists_and_left] using h
  refine ⟨E,hmE,hsE.trans hsD,?_,?_,hsafe⟩
  · intro a b h
    rw [correct]
    exact decide_eq_true ⟨a,by simp,b,by simp,h⟩
  · intro a
    rw [correct]
    simp
