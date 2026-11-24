import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1764_412
  (price : ∀ (k n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], NoFourCycle G →
    ∀ C : Circuit, Monotone2 C → ∀ T : Finset (Sym2 (Fin n)),
    (∀ e ∈ T, ∃ u v : Fin n, e = s(u,v) ∧ G.Adj u v ∧ ∃ w : ℕ,
        let S := orIn n C w
        v ∈ S ∧ 2 ≤ (S.filter (G.Adj u)).card ∧ (S.filter fun x => ¬G.Adj u x).card ≤ k) → T.card ≤ 2*(k+2)^2*C.size)
  (residual : ∃ k c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) → (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
    ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = NestedCover.graphFun G ∅ →
    ∀ T ⊆ G.edgeFinset, (∀ e ∈ T, ¬(∃ u v : Fin n, e = s(u,v) ∧ G.Adj u v ∧ ∃ w : ℕ,
        let S := orIn n C w
        v ∈ S ∧ 2 ≤ (S.filter (G.Adj u)).card ∧ (S.filter fun x => ¬G.Adj u x).card ≤ k)) → T.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x2 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → {x10 ∈ x3.edgeFinset | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ (x13 : Fin x7.gates.length), PEqualNP.EdgeOwnership.Owns x2 x7 (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x7 (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → x3.Adj x14 x15}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k,c,hard⟩ := residual
  refine ⟨2*(k+2)^2+c,?_⟩
  intro n G inst deg girth original mono computes
  let possible (s : ℕ) := ∃ C : Circuit, C.size = s ∧ Monotone2 C ∧ circuitFun n C = NestedCover.graphFun G ∅
  have existsSize : ∃ s, possible s := ⟨original.size,original,rfl,mono,computes⟩
  obtain ⟨C,sizeEq,allowed,correct⟩ := Nat.find_spec existsSize
  have least : IsMinimalMonoCircuit n C := by
    exact ⟨allowed,fun D hD hF => sizeEq.le.trans (Nat.find_min' existsSize ⟨D,rfl,hD,hF.trans correct⟩)⟩
  have cost := least.2 original mono (computes.trans correct.symm)
  have noFour : NoFourCycle G := by
    intro a b ne
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    obtain ⟨ax,bx⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨ay,by'⟩ := (Finset.mem_filter.mp hy).2
    let w : G.Walk a a := .cons ax (.cons bx.symm (.cons by' (.cons ay.symm .nil)))
    have cycle : w.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,by simp [w]⟩
      simp only [w,SimpleGraph.Walk.tail_cons]
      simp [ax.ne.symm,bx.ne.symm,by'.ne,ay.ne.symm,ne.symm,hxy]
    have len : w.length = 4 := rfl
    have long := girth a w cycle
    omega
  let covered (e : Sym2 (Fin n)) := ∃ u v : Fin n, e = s(u,v) ∧ G.Adj u v ∧ ∃ w : ℕ,
        let S := orIn n C w
        v ∈ S ∧ 2 ≤ (S.filter (G.Adj u)).card ∧ (S.filter fun x => ¬G.Adj u x).card ≤ k
  let A := G.edgeFinset.filter covered
  let B := G.edgeFinset \ A
  have aPrice := price k n G noFour C allowed A (fun e he => (Finset.mem_filter.mp he).2)
  have bPrice := hard n G deg girth C least correct B Finset.sdiff_subset (by
    intro e he cert
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,cert⟩))
  have total : G.edgeFinset.card ≤ B.card + A.card := Finset.card_le_card_sdiff_add_card
  apply le_trans (Finset.card_filter_le _ _)
  apply le_trans _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right cost 1))
  rw [Nat.add_mul,Nat.add_comm (2*(k+2)^2*(C.size+1))]
  exact total.trans (Nat.add_le_add bPrice (aPrice.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))))
