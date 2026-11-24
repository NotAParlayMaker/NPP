import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.NotPremium

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_2434_417
    (cleanInputs :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ),
        0 < n → Monotone2 C → j ≤ C.size →
        (∀ k < j, (gateAt C k).op = GateOp.and →
          ∀ u v, ¬ G.Adj u v → gateVal n C k (pairInput u v) = false) →
        ∀ (x : Fin n → Bool), (∀ u v, x u = true → x v = true → ¬ G.Adj u v) →
        ∀ i < n+j, (C.wires (List.ofFn x)).getD i false = true ↔
          ∃ v, x v = true ∧ (C.wires (List.ofFn (pairInput v v))).getD i false = true)
    (price : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) → (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      let ok (C : Circuit) := Monotone2 C ∧ circuitFun n C ≤ graphFun G ∅
      let hits (C : Circuit) := G.edgeFinset.filter (fun e => circuitFun n C (fun v => decide (v ∈ e)) = true)
      let bad (C : Circuit) (j : ℕ) := (gateAt C j).op = GateOp.and ∧
        ∃ u v, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
      ∀ C : Circuit, ok C → (∀ D : Circuit, ok D → D.size < C.size → (hits D).card < (hits C).card) →
        (∃ j, bad C j ∧ ∀ x : Fin n → Bool, graphFun G ∅ x = false → ∀ k < j,
          gateVal n C k x = true ↔ ∃ v, x v = true ∧ gateVal n C k (pairInput v v) = true) →
        ∃ k, bad C k ∧ ∃ D : Circuit, ok D ∧ D.size < C.size ∧
          hits D = hits ⟨replaceByConst C.gates k false,C.output⟩ ∧
          (hits C).card ≤ (hits D).card + c * (C.size-D.size)) :
    ∃ (x1 : ℕ),   ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],     (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →       (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →         have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x7 x8 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ x8 = Bool.true;         have x8 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin x2)) := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => {x9 ∈ x3.edgeFinset | (PEqualNP.MetaComplexity.circuitFun x2 x8 fun (x10 : Fin x2) => Decidable.decide (x10 ∈ x9)) = Bool.true};         have x9 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x11 : Fin x2) (x12 : Fin x2), ¬x3.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.gateVal x2 x9 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true;         ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → x7 x10 → (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 → x7 x13 → x13.size < x10.size → (x8 x13).card < (x8 x10).card) → (∃ (x14 : ℕ), x9 x10 x14) → ∃ (x15 : ℕ), x9 x10 x15 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x16 ∧ x7 x16 ∧ x16.size < x10.size ∧ x8 x16 = x8 { gates := PEqualNP.NotPremium.replaceByConst x10.gates x15 Bool.false, output := x10.output : PEqualNP.CircuitLowerBounds.Circuit } ∧ (x8 x10).card ≤ (x8 x16).card + x1 * (x10.size - x16.size) := by
  classical
  rcases price with ⟨c,price⟩
  refine ⟨c,?_⟩
  intro n G inst degrees girth
  dsimp only
  intro C fan safe minimal hasBad
  let bad (k : ℕ) := (gateAt C k).op = GateOp.and ∧
    ∃ u v, ¬G.Adj u v ∧ gateVal n C k (pairInput u v) = true
  have existsBad : ∃ k, bad k := hasBad
  let j := Nat.find existsBad
  have badJ : bad j := Nat.find_spec existsBad
  have early : ∀ k < j, ¬bad k := fun _ h => Nat.find_min existsBad h
  have jlt : j < C.size := by
    by_contra! h
    have missing : C.gates.length ≤ j := h
    have op := badJ.1
    rw [gateAt, List.getD_eq_default _ _ missing] at op
    cases op
  have nz : 0 < n := by
    obtain ⟨a,b,no,trueOn⟩ := badJ.2
    exact Nat.zero_lt_of_lt a.isLt
  have good (D : Circuit) : circuitFun n D ≤ graphFun G ∅ ↔
      ∀ x, circuitFun n D x = true → graphFun G ∅ x = true := by
    exact ⟨fun h x => Bool.le_iff_imp.mp (h x), fun h x => Bool.le_iff_imp.mpr (h x)⟩
  have clean (k : ℕ) (hk : k < j) (isAnd : (gateAt C k).op = GateOp.and)
      (a b : Fin n) (no : ¬G.Adj a b) : gateVal n C k (pairInput a b) = false := by
    cases truth : gateVal n C k (pairInput a b) with
    | false => rfl
    | true => exact (early k hk ⟨isAnd,a,b,no,truth⟩).elim
  have independent (x : Fin n → Bool) (no : graphFun G ∅ x = false)
      (u v : Fin n) (hu : x u = true) (hv : x v = true) : ¬G.Adj u v := by
    intro adj
    have yes : (decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) = true :=
      decide_eq_true ⟨u,v,adj,hu,hv⟩
    unfold graphFun at no
    simp [yes] at no
  have decomposition (x : Fin n → Bool) (no : graphFun G ∅ x = false) (k : ℕ) (hk : k < j) :=
    cleanInputs n G C j nz fan (Nat.le_of_lt jlt) clean x (independent x no) (n+k) (by omega)
  obtain ⟨k,badK,D,okD,small,eq,loss⟩ := price n G degrees girth C ⟨fan,(good C).mpr safe⟩
    (fun B okB hB => minimal B okB.1 ((good B).mp okB.2) hB) ⟨j,badJ,decomposition⟩
  exact ⟨k,badK,D,okD.1,(good D).mp okD.2,small,eq,loss⟩
