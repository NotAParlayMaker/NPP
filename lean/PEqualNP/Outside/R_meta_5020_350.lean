import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
theorem PEqualNP.Outside.R_meta_5020_350
    (budget : ∀ (n : Nat) (A : Finset (Fin n)) (C : Circuit),
    let f := circuitFun n C
    let R := fun (v : Fin n) => C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    FanInTwo C → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ a ∈ A, f (fun i => decide (i=a)) ≠ f (fun _ => false)) →
    A.card + (∑ v ∈ Aᶜ, (R v).length) + (C.gates.filter fun g => g.op.eval [false]).length ≤ C.size+1)
    (hard : ∀ (n k : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    let f := graphFun G A
    let R := fun (v : Fin n) => C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    let e := (∑ v ∈ Aᶜ, ((R v).length - 2)) + (C.gates.filter fun g => g.op.eval [false]).length
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) → 7 ≤ G.egirth →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    (∀ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) → k ≤ T.card) →
    FanInTwo C → circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A, 2 ≤ (R v).length) →
    (∃ v ∉ A, (R v).length = 2 ∧ ∃ g ∈ R v, g.op ≠ GateOp.or) →
    (∀ Z ⊆ Aᶜ, Z.card ≤ 2*e → ¬(G.induce (↑(Aᶜ \ Z) : Set (Fin n))).Colorable 2) →
    A.card + G.edgeSet.ncard + k ≤ C.size+1) :
∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) →     (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →       (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) →         (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →           (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →             (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →               PEqualNP.MetaComplexity.FanInTwo x6 →                 PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →                   (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) →                     (∀ x16 ∉ x4, (2 : ℕ) ≤ (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x16) x6.gates).length) →                       (∃ x17 ∉ x4,                           have x18 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x17) x6.gates;                           x18.length = (2 : ℕ) ∧ ∃ x19 ∈ x18, x19.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →                         x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  classical
  intro n k G A f C deg girth active edge cover law fan eqC optimal twice mixed
  let R := fun (v : Fin n) => C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  let E := (∑ v ∈ Aᶜ, ((R v).length - 2)) + (C.gates.filter fun g => g.op.eval [false]).length
  have two (v) (h : v ∈ Aᶜ) : 2 ≤ (R v).length := twice v (Finset.mem_compl.mp h)
  have sensitive (a) (ha : a ∈ A) : f (fun i => decide (i=a)) ≠ f (fun _ => false) := by
    have yes := (law (fun i => decide (i=a))).mpr (Or.inl ⟨a,ha,by simp⟩)
    intro eq
    have := (law (fun _ => false)).mp (eq ▸ yes)
    simp at this
  have slots := budget n A C fan (eqC ▸ optimal) (eqC ▸ sensitive)
  change A.card + (∑ v ∈ Aᶜ, (R v).length) + _ ≤ _ at slots
  have ide : (∑ v ∈ Aᶜ, (R v).length) = 2 * Aᶜ.card + ∑ v ∈ Aᶜ, ((R v).length - 2) := by
    conv_rhs => rw [Nat.mul_comm 2, ← Nat.nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v hv => by have := two v hv; omega)
  have slack : A.card + 2 * Aᶜ.card + E ≤ C.size+1 := by dsimp only [E]; omega
  have dA : ∀ v ∈ A, G.degree v = 0 := fun v hv => (G.degree_eq_zero v).mpr (fun u h => active v u h hv)
  have dB : ∀ v ∈ Aᶜ, G.degree v = 3 := fun v hv => (G.ncard_neighborSet v).symm.trans (deg v (Finset.mem_compl.mp hv))
  have hand := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at hand
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at hand
  have ne : G.edgeSet.ncard = G.edgeFinset.card := by rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  by_cases cut : ∃ Z ⊆ Aᶜ, Z.card ≤ 2*E ∧ (G.induce (↑(Aᶜ \ Z) : Set (Fin n))).Colorable 2
  · obtain ⟨Z,hz,small,⟨color⟩⟩ := cut
    let S := Aᶜ \ Z
    let bit (v : Fin n) : Fin 2 := if hv : v ∈ S then color ⟨v,hv⟩ else 0
    let left := S.filter fun v => bit v = 0
    let right := S \ left
    have hL : left ⊆ Aᶜ := Finset.Subset.trans (Finset.filter_subset ..) Finset.sdiff_subset
    have hR : right ⊆ Aᶜ := Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset
    have col (u v : Fin n) (hu : u∈S) (hv : v∈S) (adj : G.Adj u v) : bit u ≠ bit v := by
      simpa only [bit,dif_pos hu,dif_pos hv] using color.valid (show (G.induce (↑S : Set (Fin n))).Adj ⟨u,hu⟩ ⟨v,hv⟩ from adj)
    have lower (I : Finset (Fin n)) (sub : I ⊆ Aᶜ) (indep : ∀ u∈I, ∀ v∈I, ¬G.Adj u v) :
        k + I.card ≤ Aᶜ.card := by
      have h := cover (Aᶜ \ I) (by
        intro u v adj
        by_cases hu : u ∈ I
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (active v u adj.symm),fun hv => indep u hu v hv adj⟩)
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (active u v adj),hu⟩))
      have count := Finset.card_sdiff_add_card_eq_card sub
      omega
    have h₀ := lower left hL (by
      intro u hu v hv adj
      obtain ⟨us,bu⟩ := Finset.mem_filter.mp hu
      obtain ⟨vs,bv⟩ := Finset.mem_filter.mp hv
      exact col u v us vs adj (bu.trans bv.symm))
    have h₁ := lower right hR (by
      intro u hu v hv adj
      obtain ⟨us,ul⟩ := Finset.mem_sdiff.mp hu
      obtain ⟨vs,vl⟩ := Finset.mem_sdiff.mp hv
      have ub : bit u ≠ 0 := fun h => ul (Finset.mem_filter.mpr ⟨us,h⟩)
      have vb : bit v ≠ 0 := fun h => vl (Finset.mem_filter.mpr ⟨vs,h⟩)
      exact col u v us vs adj (by omega))
    have sumLR : right.card + left.card = S.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset ..)
    have sumZ : S.card + Z.card = Aᶜ.card := Finset.card_sdiff_add_card_eq_card hz
    omega
  · have eqf : f = graphFun G A := by
      funext x
      apply Bool.eq_iff_iff.mpr
      change (f x = true) ↔ ((decide _ || decide _) = true)
      simpa only [Bool.or_eq_true,decide_eq_true_eq] using law x
    apply hard n k G A C deg (SimpleGraph.le_egirth.mpr (fun v w h => by exact_mod_cast girth v w h)) active edge
      (fun T h => cover T (fun u v adj => h adj)) fan (eqC.trans eqf) (eqf ▸ optimal) twice mixed
    intro Z hz hsize hcol
    exact cut ⟨Z,hz,hsize,hcol⟩
