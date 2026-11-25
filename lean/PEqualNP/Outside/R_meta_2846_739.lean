import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2846_739
    (firstDirty : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : Circuit),
      let n := Np + Nl
      let F := fun z : Fin n → Bool => decide (∃ p l, I p l ∧
        z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)
      let valid := fun D : Circuit => IsAO2 n D ∧ circuitFun n D = F
      let gate := gateAt C
      let clean := fun j => ∀ u v : Fin n,
        gateVal n C j (pairInput u v) = true → F (pairInput u v) = true
      (∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      valid C → (∀ D, valid D → C.size ≤ D.size) →
      (∃ T : Finset ℕ,
        (∀ i ∈ T, i < C.gates.length ∧ (gate i).op = .or ∧
          (n + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length,
            (n + i ∈ (gate k').inputs ↔ k' = k))) ∧
        ∀ w : ℕ,
          (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true → F z = true) →
          (∃ k < C.gates.length, (gate k).op = .or ∧ w ∈ (gate k).inputs) →
          ∀ k < C.gates.length, w ∈ (gate k).inputs → k ∈ T) →
      ∀ j < C.gates.length, (∀ i < j, (gate i).op = .and → clean i) →
        (gate j).op = .and → clean j)
    (boundary : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : Circuit),
      let n := Np + Nl
      let F := fun z : Fin n → Bool => decide (∃ p l, I p l ∧
        z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)
      let valid := fun D : Circuit => IsAO2 n D ∧ circuitFun n D = F
      let gate := gateAt C
      valid C → (∀ D, valid D → C.size ≤ D.size) →
      (∃ T : Finset ℕ,
        (∀ i ∈ T, i < C.gates.length ∧ (gate i).op = .or ∧
          (n + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length,
            (n + i ∈ (gate k').inputs ↔ k' = k))) ∧
        ∀ w : ℕ,
          (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true → F z = true) →
          (∃ k < C.gates.length, (gate k).op = .or ∧ w ∈ (gate k).inputs) →
          ∀ k < C.gates.length, w ∈ (gate k).inputs → k ∈ T) →
      (∀ j < C.gates.length, (gate j).op = .and → ∀ u v : Fin n,
        gateVal n C j (pairInput u v) = true → F (pairInput u v) = true) →
      ∀ i < C.gates.length, ∀ j < C.gates.length,
        (gate i).op = .and → (gate j).op = .and → ¬ InCone n C i j)
    (polarity : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : Circuit),
      let n := Np + Nl
      let F := fun z : Fin n → Bool => decide (∃ p l, I p l ∧
        z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)
      let gate := gateAt C
      IsAO2 n C → circuitFun n C = F →
      (∀ D : Circuit, IsAO2 n D → circuitFun n D = F → C.size ≤ D.size) →
      (∀ i < C.gates.length, ∀ j < C.gates.length,
        (gate i).op = .and → (gate j).op = .and → ¬ InCone n C i j) →
      ∃ P L : Finset ℕ,
        (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = n + i ∧ (gate i).op = .or ∧
          ∀ u ∈ (gate i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < n) ∨ ∃ i < C.gates.length, w = n + i ∧ (gate i).op = .or ∧
          ∀ u ∈ (gate i).inputs, u ∈ L) ∧
        ∀ i < C.gates.length, (gate i).op = .and →
          ∃ a b : ℕ, (gate i).inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) :
∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro Np Nl I instI C hC4 hAO hCorrect hLeast hStuck
  let n := Np + Nl
  let F := fun z : Fin n → Bool => decide (∃ p l, I p l ∧
    z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)
  have correct : circuitFun n C = F := funext hCorrect
  have least : ∀ D : Circuit, IsAO2 n D → circuitFun n D = F → C.size ≤ D.size := by
    intro D hD hF
    exact hLeast D hD (fun z => congrFun hF z)
  have least' : ∀ D : Circuit, (IsAO2 n D ∧ circuitFun n D = F) → C.size ≤ D.size :=
    fun D hD => least D hD.1 hD.2
  have terminal :
      ∃ T : Finset ℕ,
        (∀ i ∈ T, i < C.gates.length ∧ (gateAt C i).op = .or ∧
          (n + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length,
            (n + i ∈ (gateAt C k').inputs ↔ k' = k))) ∧
        ∀ w : ℕ,
          (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true → F z = true) →
          (∃ k < C.gates.length, (gateAt C k).op = .or ∧ w ∈ (gateAt C k).inputs) →
          ∀ k < C.gates.length, w ∈ (gateAt C k).inputs → k ∈ T := by
    obtain ⟨T, hT, hReaders⟩ := hStuck
    refine ⟨T, hT, ?_⟩
    intro w below hOr k hk hw
    apply hReaders w ?_ hOr k hk hw
    intro z hz
    exact of_decide_eq_true (below z hz)
  have clean : ∀ j < C.gates.length, (gateAt C j).op = .and → ∀ u v : Fin n,
      gateVal n C j (pairInput u v) = true → F (pairInput u v) = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj hop
      apply firstDirty Np Nl I C hC4 ⟨hAO, correct⟩ least' terminal j hj
      · intro i hij hia
        exact ih i hij (lt_trans hij hj) hia
      · exact hop
  have flat := boundary Np Nl I C ⟨hAO, correct⟩ least' terminal clean
  exact polarity Np Nl I C hAO correct least flat
