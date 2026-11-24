import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_3574 :
    ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro n xs made A present
  classical
  let eligible (B : Finset (Fin n)) : Bool := decide (1 < B.card ∧ B ⊆ A)
  let Covers (F : Finset (Finset (Fin n))) := ∀ v ∈ A, ∃ B ∈ F, v ∈ B
  let Legal (k : ℕ) (F : Finset (Finset (Fin n))) :=
    ∀ B ∈ F, B ⊆ A ∧ (B.card ≤ 1 ∨ B ∈ xs.take k)
  have bound (k : ℕ) (inside : k ≤ xs.length) (F : Finset (Finset (Fin n)))
      (covers : Covers F) (legal : Legal k F) : A.card ≤ F.card + (xs.take k).countP eligible := by
    induction k generalizing F with
    | zero =>
      have sub : A ⊆ F.biUnion id := by
        intro v hv
        obtain ⟨B,mem,bit⟩ := covers v hv
        exact Finset.mem_biUnion.mpr ⟨B,mem,bit⟩
      have singleton (B : Finset (Fin n)) (mem : B ∈ F) : B.card ≤ 1 := by
        simpa only [List.take_zero,List.not_mem_nil,or_false] using (legal B mem).2
      have finish := (Finset.card_le_card sub).trans (Finset.card_biUnion_le_card_mul F id 1 singleton)
      simpa using finish
    | succ k ih =>
      have hk : k < xs.length := by omega
      let T := xs[k]
      have pref : xs.take (k+1) = xs.take k ++ [T] := by
        rw [← List.take_concat_get hk,List.concat_eq_append]
      have budget : (xs.take (k+1)).countP eligible =
          (xs.take k).countP eligible + (if eligible T then 1 else 0) := by
        rw [pref,List.countP_append]
        simp
      by_cases expand : T ∈ F ∧ 1 < T.card
      · obtain ⟨U,V,merge,uEarly,vEarly⟩ := made k T (getElem?_pos _ k hk)
        let H := insert U (insert V (F.erase T))
        have subT := (legal T expand.1).1
        have su : U ⊆ A := by rw [merge] at subT; exact Finset.subset_union_left.trans subT
        have sv : V ⊆ A := by rw [merge] at subT; exact Finset.subset_union_right.trans subT
        have advanced : Legal k H := by
          intro B hB
          rcases Finset.mem_insert.mp hB with rfl | hB
          · exact ⟨su,uEarly⟩
          rcases Finset.mem_insert.mp hB with rfl | hB
          · exact ⟨sv,vEarly⟩
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hB
          obtain ⟨small,early⟩ := legal B mem
          refine ⟨small,early.imp_right ?_⟩
          intro old
          rw [pref,List.mem_append] at old
          rcases old with old | last
          · exact old
          · exact (ne (List.mem_singleton.mp last)).elim
        have still : Covers H := by
          intro v hv
          obtain ⟨B,mem,bit⟩ := covers v hv
          by_cases same : B = T
          · rw [same,merge] at bit
            rcases Finset.mem_union.mp bit with hu | hv
            · exact ⟨U,Finset.mem_insert_self _ _,hu⟩
            · exact ⟨V,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),hv⟩
          · exact ⟨B,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨same,mem⟩)),bit⟩
        have size : H.card ≤ F.card+1 := by
          have le₁ := Finset.card_insert_le U (insert V (F.erase T))
          have le₂ := Finset.card_insert_le V (F.erase T)
          have removed := Finset.card_erase_add_one expand.1
          change (insert U (insert V (F.erase T))).card ≤ _
          omega
        have used : eligible T = true := decide_eq_true ⟨expand.2,subT⟩
        have e := ih (by omega) H still advanced
        rw [budget,used]
        simp only [ite_true]
        omega
      · have advanced : Legal k F := by
          intro B hB
          obtain ⟨sub,early⟩ := legal B hB
          refine ⟨sub,?_⟩
          rcases early with small | old
          · exact Or.inl small
          · rw [pref,List.mem_append] at old
            rcases old with before | atEnd
            · exact Or.inr before
            · have equal := List.mem_singleton.mp atEnd
              subst B
              exact Or.inl (by by_contra! notSmall; exact expand ⟨hB,notSmall⟩)
        have e := ih (by omega) F covers advanced
        rw [budget]
        omega
  have e := bound xs.length le_rfl {A}
    (fun v h => ⟨A,Finset.mem_singleton_self _,h⟩)
    (fun B h => by
      have eq : B = A := Finset.mem_singleton.mp h
      subst B
      exact ⟨Finset.Subset.refl _,Or.inr (by simpa using present)⟩)
  have counted : xs.countP eligible =
      Fintype.card {i : Fin xs.length // 1 < (xs.get i).card ∧ xs.get i ⊆ A} := by
    let J := Finset.univ.filter (fun i : Fin xs.length => eligible (xs.get i) = true)
    have list : List.ofFn (fun i : Fin xs.length => xs.get i) = xs := List.ofFn_getElem
    conv_lhs => rw [← list]
    rw [List.countP_ofFn]
    change J.card = _
    symm
    apply Fintype.card_of_subtype J
    intro i
    simp [J,eligible]
  simpa only [Finset.card_singleton,List.take_length,counted,Nat.add_comm] using e
