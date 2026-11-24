import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2638_2
    (peel : ∀ (n s : ℕ) (a : Fin n) (f : (Fin n → Bool) → Bool),
      (∀ x, x a = true → f x = true) →
      (∃ x y, f (Function.update x a false) ≠ f (Function.update y a false)) →
      HasCircuitSize n f s →
      ∃ t, t + 1 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x a false)) t)
    (pureBound : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (v : Fin n) (f : (Fin n → Bool) → Bool),
      (∀ u ∉ A, (G.neighborSet u).ncard = 3) →
      (∀ (u : Fin n) (w : G.Walk u u), w.IsCycle → 7 ≤ w.length) →
      (∀ i j, G.Adj i j → i ∉ A) →
      (∃ i j, G.Adj i j) → v ∉ A →
      (∀ x, f x = true ↔ ∃ i j, (G.deleteEdges (G.incidenceSet v)).Adj i j ∧
        x i = true ∧ x j = true) →
      (∀ T : Finset (Fin n), (∀ i j, (G.deleteEdges (G.incidenceSet v)).Adj i j →
        i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      HasCircuitSize n f s →
      (G.deleteEdges (G.incidenceSet v)).edgeSet.ncard + k ≤ s + 1) :
∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  intro n k s G A v f degree girth separate edge outside computes cover sized
  classical
  let H := G.deleteEdges (G.incidenceSet v)
  have splitEdge : ∀ i j, H.Adj i j ↔ G.Adj i j ∧ i ≠ v ∧ j ≠ v :=
    fun _ _ => SimpleGraph.deleteIncidenceSet_adj
  have survives : ∃ i j, H.Adj i j := by
    by_contra! noEdge
    obtain ⟨i,j,hij⟩ := edge
    have outer : ∃ u ≠ v, ∃ w, G.Adj u w := by
      by_cases e : i = v
      · exact ⟨j, fun eq => hij.ne (e.trans eq.symm), i, hij.symm⟩
      · exact ⟨i,e,j,hij⟩
    obtain ⟨u,uv,w,uw⟩ := outer
    have neighbors : G.neighborSet u ⊆ {v} := by
      intro w hw
      by_contra h
      exact noEdge u w ((splitEdge u w).2 ⟨hw,uv,h⟩)
    have count := Set.ncard_le_ncard neighbors
    rw [degree u (separate u w uw)] at count
    simp at count
  have bound (B : Finset (Fin n)) (inA : B ⊆ A) :
      ∀ (s : ℕ) (f : (Fin n → Bool) → Bool),
        (∀ x, f x = true ↔ (∃ a ∈ B, x a = true) ∨
          ∃ i j, H.Adj i j ∧ x i = true ∧ x j = true) →
        HasCircuitSize n f s → B.card + H.edgeSet.ncard + k ≤ s + 1 := by
    induction B using Finset.strongInductionOn
    rename_i B ih
    intro s f computes sized
    by_cases empty : B = ∅
    · subst B
      simp only [Finset.card_empty, Nat.zero_add]
      exact pureBound n k s G A v f degree girth separate edge outside
        (by simpa [H] using computes) cover sized
    · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      let f' := fun x => f (Function.update x a false)
      have aA := inA ha
      have trueOn (x) (on : x a = true) : f x = true :=
        (computes x).2 (Or.inl ⟨a,ha,on⟩)
      have restricted (x) : f' x = true ↔ (∃ b ∈ B.erase a, x b = true) ∨
          ∃ i j, H.Adj i j ∧ x i = true ∧ x j = true := by
        change f (Function.update x a false) = true ↔ _
        rw [computes]
        constructor
        · rintro (⟨b,hb,on⟩ | ⟨i,j,adj,onI,onJ⟩)
          · have ba : b ≠ a := by intro e; simp [e] at on
            exact Or.inl ⟨b,Finset.mem_erase.mpr ⟨ba,hb⟩,
              by simpa [Function.update_of_ne ba] using on⟩
          · have ia : i ≠ a := fun h => separate i j (splitEdge i j |>.mp adj |>.1) (h ▸ aA)
            have ja : j ≠ a := fun h => separate j i (splitEdge i j |>.mp adj |>.1).symm (h ▸ aA)
            exact Or.inr ⟨i,j,adj,by simpa [Function.update_of_ne ia] using onI,
              by simpa [Function.update_of_ne ja] using onJ⟩
        · rintro (⟨b,hb,on⟩ | ⟨i,j,adj,onI,onJ⟩)
          · obtain ⟨ba,hb⟩ := Finset.mem_erase.mp hb
            exact Or.inl ⟨b,hb,by simpa [Function.update_of_ne ba] using on⟩
          · have ia : i ≠ a := fun h => separate i j (splitEdge i j |>.mp adj |>.1) (h ▸ aA)
            have ja : j ≠ a := fun h => separate j i (splitEdge i j |>.mp adj |>.1).symm (h ▸ aA)
            exact Or.inr ⟨i,j,adj,by simpa [Function.update_of_ne ia] using onI,
              by simpa [Function.update_of_ne ja] using onJ⟩
      have zero : f' (fun _ => false) = false := by
        by_contra bad
        have on : f' (fun _ => false) = true := Bool.eq_true_of_not_eq_false bad
        simpa using (restricted (fun _ => false)).mp on
      obtain ⟨i,j,adj⟩ := survives
      have one : f' (fun _ => true) = true :=
        (restricted (fun _ => true)).mpr (Or.inr ⟨i,j,adj,rfl,rfl⟩)
      obtain ⟨t,lt,small⟩ := peel n s a f trueOn
        ⟨fun _ => false,fun _ => true,by change f' _ ≠ f' _; rw [zero,one]; decide⟩ sized
      have smaller : B.erase a ⊂ B := Finset.erase_ssubset ha
      have sub : B.erase a ⊆ A := (Finset.erase_subset a B).trans inA
      have lower := ih (B.erase a) smaller sub t f' restricted small
      have card := Finset.card_erase_add_one ha
      omega
  exact bound A (Finset.Subset.refl A) s f computes sized
