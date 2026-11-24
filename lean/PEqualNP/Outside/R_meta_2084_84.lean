import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2084_84
    (h1 : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
  (∀ a : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j=y j) ∧ circuitFun n C x ≠ circuitFun n C y) →
  let slots := C.output :: C.gates.flatMap Gate.inputs
  (∀ a : Fin n, 1 ≤ slots.count a.val) ∧ (∑ a : Fin n, slots.count a.val) ≤ C.size+1)
    (h2 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit),
  (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
  (∀ (u : Fin n) (w : G.Walk u u), w.IsCycle → 7 ≤ w.length) →
  (∀ u v, G.Adj u v → u ∉ A) →
  (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
  (∀ x : Fin n → Bool, circuitFun n C x=true ↔
    (∃ a ∈ A, x a=true) ∨ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) →
  IsMinimalCircuit n C →
  (let slots := C.output :: C.gates.flatMap Gate.inputs
   ∃ u v : Fin n, G.Adj u v ∧ slots.count u.val ≤ 2 ∧ slots.count v.val ≤ 2) →
  A.card + G.edgeSet.ncard + k ≤ C.size+1) :
∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by
  classical
  intro n k G A f hdeg hgirth hmark hedge hcover hspec s hs
  let q := Nat.find (show ∃ t, HasCircuitSize n f t from ⟨s,hs⟩)
  have hq : HasCircuitSize n f q := Nat.find_spec _
  have hqs : q ≤ s := Nat.find_min' _ hs
  obtain ⟨C,hC,hsize,hfun⟩ := hq
  have hCf : circuitFun n C = f := funext hfun
  have hmin : IsMinimalCircuit n C := by
    refine ⟨hC,?_⟩
    intro D hD hDC
    apply hsize.trans
    apply Nat.find_min'
    exact ⟨D,hD,le_rfl,congrFun (hDC.trans hCf)⟩
  let cnt := fun a : Fin n => (C.output :: C.gates.flatMap Gate.inputs).count a.val
  suffices H : A.card+G.edgeSet.ncard+k ≤ C.size+1 by omega
  by_cases pair : ∃ u v : Fin n, G.Adj u v ∧ cnt u ≤ 2 ∧ cnt v ≤ 2
  · apply h2 n k G A C hdeg hgirth hmark hcover _ hmin pair
    rwa [hCf]
  have pos : ∀ a : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j=y j) ∧
      circuitFun n C x ≠ circuitFun n C y := by
    intro a
    rw [hCf]
    by_cases ha : a ∈ A
    · let x := fun _ : Fin n => false
      let y := fun j : Fin n => decide (j=a)
      refine ⟨x,y,fun j hj => by simp [x,y,hj],?_⟩
      have h0 : f x ≠ true := by simp [hspec,x]
      have h1' := (hspec y).2 (Or.inl ⟨a,ha,by simp [y]⟩)
      exact fun he => h0 (he.trans h1')
    · have h3 : G.degree a=3 := by simpa only [SimpleGraph.ncard_neighborSet] using hdeg a ha
      obtain ⟨b,hab⟩ : (G.neighborFinset a).Nonempty :=
        Finset.card_pos.mp (by rw [G.card_neighborFinset_eq_degree,h3]; decide)
      have hab' : G.Adj a b := by simpa using hab
      have hb := hmark b a hab'.symm
      let x := fun j : Fin n => decide (j=b)
      let y := fun j : Fin n => decide (j=b ∨ j=a)
      refine ⟨x,y,fun j hj => by simp [x,y,hj],?_⟩
      have h0 : f x ≠ true := by
        intro hx
        rcases (hspec x).1 hx with ⟨v,hv,he⟩ | ⟨u,v,huv,hu,hv⟩
        · have he' : v=b := of_decide_eq_true he
          exact hb (he' ▸ hv)
        · have hu' : u=b := of_decide_eq_true hu
          have hv' : v=b := of_decide_eq_true hv
          exact huv.ne (hu'.trans hv'.symm)
      have h1' := (hspec y).2 (Or.inr ⟨a,b,hab',by simp [y],by simp [y]⟩)
      exact fun he => h0 (he.trans h1')
  obtain ⟨hall,hbudget⟩ := h1 n C hmin pos
  change ∀ a : Fin n, 1 ≤ cnt a at hall
  change ∑ a : Fin n, cnt a ≤ C.size+1 at hbudget
  let T : Finset (Fin n) := Aᶜ.filter fun v => 3 ≤ cnt v
  have hTc : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    by_cases h : 3 ≤ cnt u
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr (hmark u v huv),h⟩)
    · apply Or.inr
      refine Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr (hmark v u huv.symm),?_⟩
      by_contra! bad
      exact pair ⟨u,v,huv,by omega,by omega⟩
  have hTk := hcover T hTc
  have htA : T ⊆ Aᶜ := Finset.filter_subset _ _
  have hT3 : ∀ v ∈ T, G.degree v = 3 := fun v hv => by
    simpa only [SimpleGraph.ncard_neighborSet] using hdeg v (Finset.mem_compl.mp (htA hv))
  have hedgeCover : G.edgeFinset ⊆ T.biUnion (fun a => G.incidenceFinset a) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      rcases hTc u v huv with hu | hv
      · exact Finset.mem_biUnion.mpr ⟨u,hu,by simp [huv]⟩
      · exact Finset.mem_biUnion.mpr ⟨v,hv,by rw [Sym2.eq_swap]; simp [huv.symm]⟩
  have heg := (Finset.card_le_card hedgeCover).trans (Finset.card_biUnion_le)
  simp_rw [G.card_incidenceFinset_eq_degree] at heg
  rw [Finset.sum_congr rfl hT3] at heg
  have dA : ∀ a ∈ A, G.degree a=0 :=
    fun a ha => (G.degree_eq_zero a).mpr (fun b h => hmark a b h ha)
  have dN : ∀ a ∈ Aᶜ, G.degree a=3 := fun a ha => by
    simpa only [SimpleGraph.ncard_neighborSet] using hdeg a (Finset.mem_compl.mp ha)
  have hdegSum := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl,Finset.sum_congr rfl dA,Finset.sum_congr rfl dN] at hdegSum
  have high : ∀ a ∈ T, 3 ≤ cnt a := fun a ha => (Finset.mem_filter.mp ha).2
  have hTsum := Finset.sum_le_sum high
  have hRest := Finset.sum_le_sum (s := Tᶜ) (fun a _ => hall a)
  have hparts := T.sum_add_sum_compl cnt
  have hcard := Finset.card_add_card_compl T
  have hcard' := Finset.card_add_card_compl A
  have heq : G.edgeSet.ncard=G.edgeFinset.card := by
    rw [← Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
  simp only [Finset.sum_const,smul_eq_mul,mul_one,mul_zero,zero_add,
    Fintype.card_fin] at hdegSum heg hTsum hRest hparts hcard hcard'
  rw [heq]
  omega
