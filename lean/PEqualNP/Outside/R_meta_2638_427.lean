import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open SimpleGraph

-- The forest case is the project theorem Helpers.Forest.claimQ from ForestBound.
-- On a cyclic residual, pin one vertex. A cover of the deletion always extends
-- by adding that vertex. When a cheapest residual cover already covers the old
-- edges, this extension costs nothing.
theorem PEqualNP.Outside.R_meta_2638_427
    (forest : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
      (A : Finset (Fin n)) (k s : ℕ), (∀ w (p : H.Walk w w), ¬p.IsCycle) →
      (∀ i j, H.Adj i j → i ∉ A) → (∀ T, CoverPromise.IsVertexCover H T → k ≤ T.card) →
      HasCircuitSize n (graphFun H A) s → A.card + H.edgeSet.ncard + k ≤ s+1)
    (peel : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
      (A : Finset (Fin n)) (s : ℕ),
      (∀ w, (H.neighborSet w).ncard ≤ 3) →
      (∀ w (p : H.Walk w w), p.IsCycle → 7 ≤ p.length) →
      (∀ i j, H.Adj i j → i ∉ A) → ¬(∀ w (p : H.Walk w w), ¬p.IsCycle) → HasCircuitSize n (graphFun H A) s →
      ∃ v t, let D := H.deleteEdges (H.incidenceSet v)
        let d := (H.incidenceSet v).ncard
        0 < d ∧ v ∉ A ∧ HasCircuitSize n (fun x => graphFun H A (Function.update x v false)) t ∧
        t+d ≤ s ∧
        (t+d+1 ≤ s ∨ ∃ T, CoverPromise.IsVertexCover H T ∧ ∀ U, CoverPromise.IsVertexCover D U → T.card ≤ U.card)) :
    ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  intro n k s G A z f regular girth outside _ _ computes cover size
  classical
  let F := fun K : SimpleGraph (Fin n) => @graphFun n K (Classical.decRel _) A
  have deg (v : Fin n) : (G.neighborSet v).ncard ≤ 3 := by
    by_cases h : v∈A
    · have empty : G.neighborSet v=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact outside v i hi h
      simp [empty]
    · rw [regular v h]
  have proveAt (m : ℕ) : ∀ (H : SimpleGraph (Fin n)), H ≤ G → H.edgeSet.ncard=m →
      ∀ b r : ℕ, (∀ T, CoverPromise.IsVertexCover H T → b ≤ T.card) →
      HasCircuitSize n (F H) r → A.card + H.edgeSet.ncard + b ≤ r+1 := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro H sub hm b r covers circ
      have outH : ∀ i j, H.Adj i j → i ∉ A := fun i j h => outside i j (sub h)
      by_cases ac : (∀ w (p : H.Walk w w), ¬p.IsCycle)
      · exact forest n H A b r ac outH covers circ
      have dh (i : Fin n) : (H.neighborSet i).ncard ≤ 3 :=
        (Set.ncard_le_ncard (show H.neighborSet i ⊆ G.neighborSet i from fun _ h => sub h)).trans (deg i)
      have gh (i : Fin n) (p : H.Walk i i) (hp : p.IsCycle) : 7 ≤ p.length := by
        simpa using girth i (p.mapLe sub) (hp.mapLe sub)
      obtain ⟨v,t,hd,hv,pinned,saving,fee⟩ := peel n H A r dh gh outH ac circ
      let D := H.deleteEdges (H.incidenceSet v)
      have down : D ≤ H := H.deleteEdges_le _
      have same : (fun x => F H (Function.update x v false)) = F D := by
        funext x
        rw [Bool.eq_iff_iff]
        simp only [F,graphFun,Bool.or_eq_true,decide_eq_true_iff]
        apply or_congr
        · apply exists_congr
          intro i
          by_cases eq : i=v
          · subst i; simp [hv]
          · simp [Function.update_of_ne eq]
        · constructor
          · rintro ⟨i,j,e,hx,hy⟩
            have a : i≠v := by rintro rfl; simp at hx
            have c : j≠v := by rintro rfl; simp at hy
            have he : D.Adj i j := by
              apply SimpleGraph.deleteEdges_adj.mpr
              refine ⟨e,fun hin => ?_⟩
              have mem := hin.2
              simp [Ne.symm a,Ne.symm c] at mem
            exact ⟨i,j,he,by simpa [Function.update_of_ne a] using hx,
              by simpa [Function.update_of_ne c] using hy⟩
          · rintro ⟨i,j,e,hx,hy⟩
            obtain ⟨edge,off⟩ := SimpleGraph.deleteEdges_adj.mp e
            have a : i≠v := by
              rintro rfl
              exact off ((H.mem_incidenceSet _ _).mpr edge)
            have c : j≠v := by
              rintro rfl
              apply off
              exact ⟨H.mem_edgeSet.mpr edge,Sym2.mem_mk_right _ _⟩
            exact ⟨i,j,edge,by simpa [Function.update_of_ne a] using hx,
              by simpa [Function.update_of_ne c] using hy⟩
      have circ' : HasCircuitSize n (F D) t := same ▸ pinned
      have balance : D.edgeSet.ncard + (H.incidenceSet v).ncard = H.edgeSet.ncard := by
        rw [show D.edgeSet=H.edgeSet \ H.incidenceSet v by simp only [D,SimpleGraph.edgeSet_deleteEdges]]
        exact Set.ncard_sdiff_add_ncard_of_subset (H.incidenceSet_subset v)
      have lt : D.edgeSet.ncard < m := by omega
      have next := ih _ lt D (down.trans sub) rfl
      rcases fee with paid | ⟨T,hT,hmin⟩
      · have residual : ∀ U, CoverPromise.IsVertexCover D U → b-1 ≤ U.card := by
          intro U hu
          have extended : CoverPromise.IsVertexCover H (insert v U) := by
            intro i j e
            by_cases a : i=v
            · exact Or.inl (Finset.mem_insert.mpr (Or.inl a))
            by_cases c : j=v
            · exact Or.inr (Finset.mem_insert.mpr (Or.inl c))
            have edge : D.Adj i j := by
              apply (SimpleGraph.deleteEdges_adj).2
              refine ⟨e,?_⟩
              intro hin
              have mem := hin.2
              simp [Ne.symm a,Ne.symm c] at mem
            exact (hu i j edge).imp (fun h => Finset.mem_insert_of_mem h) (fun h => Finset.mem_insert_of_mem h)
          have bound := covers (insert v U) extended
          have count := Finset.card_insert_le v U
          omega
        have smaller := next (b-1) t residual circ'
        omega
      · have residual : ∀ U, CoverPromise.IsVertexCover D U → b ≤ U.card :=
          fun U hu => (covers T hT).trans (hmin U hu)
        have smaller := next b t residual circ'
        omega
  let H := G.deleteEdges (G.incidenceSet z)
  have equals : f=F H := by
    funext x
    rw [Bool.eq_iff_iff]
    simpa only [F,graphFun,Bool.or_eq_true,decide_eq_true_iff,H] using computes x
  exact proveAt _ H (G.deleteEdges_le _) rfl k s cover (equals ▸ size)
