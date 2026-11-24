import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.EdgeOwnership PEqualNP.LowMerge

theorem PEqualNP.Outside.R_meta_2588_739
    (geometry :
      let T := Fin 13
      let V := Fin 26
      let I := fun (u v : V) => u.val < 13 ∧ 13 ≤ v.val ∧
        Fin.ofNat 13 u.val ∈ PEqualNP.HeptadCover.singerLines3 (Fin.ofNat 13 v.val)
      let A := fun (Q : Finset T) =>
        Fin.append (fun p : T => decide (p ∈ Q))
          (fun l : T => decide (l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q))
      ∀ u v : V, ¬ (I u v ∨ I v u) →
        ∃ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
          A Q u = true ∧ A Q v = true)
    (propagation :
      ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
      let W := fun (x : Fin n → Bool) (u : ℕ) => PEqualNP.LowMerge.wireVal C (List.ofFn x) u
      (∀ (x y : Fin n → Bool), (∀ j, x j = true → y j = true) → ∀ u, W x u = true → W y u = true) ∧
      ∀ x : Fin n → Bool,
        (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and → W x (n+j) = false) →
        ∀ u, W x u = true → ∃ v : Fin n, x v = true ∧ W (PEqualNP.EdgeOwnership.pairInput v v) u = true)
    (safe :
      let T := Fin 13
      let V := Fin 26
      let I := fun (u v : V) => u.val < 13 ∧ 13 ≤ v.val ∧
        Fin.ofNat 13 u.val ∈ PEqualNP.HeptadCover.singerLines3 (Fin.ofNat 13 v.val)
      let R := fun u v : V => List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 26 C →
        (∀ u v, C.eval (R u v) = decide (I u v ∨ I v u)) →
        (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and →
          (∀ u v, PEqualNP.LowMerge.wireVal C (R u v) (26+j) = true → I u v ∨ I v u) ∧
          (∀ k ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
            ∃ u : V, PEqualNP.LowMerge.wireVal C (R u u) k = true)) →
        64 ≤ C.size)
    (dirty :
      let T := Fin 13
      let S := PEqualNP.HeptadCover.singerLines3
      let Qs := PEqualNP.HeptadCover.quadrangles S
      let N := fun (Q : Finset T) =>
        PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines S Q)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        let G := PEqualNP.MetaComplexity.NestedCover.gateAt C
        let W := PEqualNP.LowMerge.wireVal C
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        2 ≤ PEqualNP.TopForm.andPairs 26 C →
        (∀ p l : T, p ∈ S l → C.eval (PEqualNP.LowMerge.pointLineInput 13 13 p l) = true) →
        (∀ Q ∈ Qs, C.eval (N Q) = false) →
        (∀ j < C.size, (G j).op = .and → ∀ i ∈ (G j).inputs,
          ∃ Q ∈ Qs, W (N Q) (26+j) ≠ W (N Q) i) →
        (∃ j < C.size, (G j).op = .and ∧ ∃ Q ∈ Qs, W (N Q) (26+j) = true) →
        64 ≤ C.size)
    :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ x4 ∈ x2.gates, x4.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x4.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x2 → (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ PEqualNP.HeptadCover.singerLines3 x7 → x2.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) = Bool.true) → (∀ x7 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x2.eval (x1 x7) = Bool.false) → (∀ x8 < x2.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).inputs, ∃ x13 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, (x2.wires (x1 x13)).getD ((26 : ℕ) + x8) Bool.false ≠ (x2.wires (x1 x13)).getD x11 Bool.false) → (64 : ℕ) ≤ x2.size := by
  intro originalRow C hc hdistinct hpairs hpos hneg hdiff
  let T := Fin 13
  let V := Fin 26
  let I := fun (u v : V) => u.val < 13 ∧ 13 ≤ v.val ∧
    Fin.ofNat 13 u.val ∈ singerLines3 (Fin.ofNat 13 v.val)
  let A := fun (Q : Finset T) =>
    Fin.append (fun p : T => decide (p ∈ Q))
      (fun l : T => decide (l ∈ missLines singerLines3 Q))
  let N := fun (Q : Finset T) =>
    (List.ofFn fun p : T => decide (p ∈ Q)) ++
      List.ofFn fun l : T => decide (l ∈ missLines singerLines3 Q)
  let W := wireVal C
  let G := gateAt C
  let Qs := quadrangles singerLines3
  change (∀ Q ∈ Qs, C.eval (N Q) = false) at hneg
  change (∀ j < C.size, (G j).op = .and → ∀ i ∈ (G j).inputs,
    ∃ Q ∈ Qs, W (N Q) (26+j) ≠ W (N Q) i) at hdiff
  have hrow (Q : Finset T) : List.ofFn (A Q) = N Q := List.ofFn_fin_append _ _
  rcases propagation 26 C hc with ⟨hmono, horigin⟩
  by_cases hbad : ∃ j < C.size, (G j).op = .and ∧ ∃ Q ∈ Qs, W (N Q) (26+j) = true
  · exact dirty C hc hdistinct hpairs hpos hneg hdiff hbad
  have hands (j : ℕ) (hj : j < C.size) (ha : (G j).op = .and) (Q : Finset T) (hQ : Q ∈ Qs) :
      W (N Q) (26+j) = false := by
    cases ht : W (N Q) (26+j) with
    | false => rfl
    | true => exact (hbad ⟨j, hj, ha, Q, hQ, ht⟩).elim
  have rejects (u v : V) (hn : ¬ (I u v ∨ I v u)) (w : ℕ)
      (hw : ∀ Q ∈ Qs, W (N Q) w = false) :
      W (List.ofFn (pairInput u v)) w = false := by
    obtain ⟨Q, hQ, hu, hv⟩ := geometry u v hn
    change A Q u = true at hu
    change A Q v = true at hv
    have hsub (j : V) (hj : pairInput u v j = true) : A Q j = true := by
      change decide (j = u ∨ j = v) = true at hj
      rcases of_decide_eq_true hj with rfl | rfl
      · exact hu
      · exact hv
    cases ht : W (List.ofFn (pairInput u v)) w with
    | false => rfl
    | true =>
      have hf := hmono (pairInput u v) (A Q) hsub w ht
      change W (List.ofFn (A Q)) w = true at hf
      rw [hrow, hw Q hQ] at hf
      exact Bool.noConfusion hf
  have accepted (u v : V) (huv : I u v) :
      C.eval (List.ofFn (pairInput u v)) = true := by
    obtain ⟨hu, hv, hinc⟩ := huv
    let p : T := ⟨u.val, hu⟩
    let l : T := ⟨v.val - 13, by have := v.isLt; omega⟩
    have up : u = p.castAdd 13 := Fin.ext rfl
    have vl : v = Fin.natAdd 13 l := by
      apply Fin.ext
      change v.val = 13 + (v.val - 13)
      omega
    have pp : Fin.ofNat 13 u.val = p := by
      apply Fin.ext
      change u.val % 13 = u.val
      exact Nat.mod_eq_of_lt hu
    have ll : Fin.ofNat 13 v.val = l := by
      apply Fin.ext
      change v.val % 13 = v.val - 13
      have := v.isLt
      omega
    rw [pp, ll] at hinc
    have hleft : (fun j : T => pairInput u v (j.castAdd 13)) = (fun j => decide (j = p)) := by
      funext j
      change decide (j.castAdd 13 = u ∨ j.castAdd 13 = v) = decide (j = p)
      have hn : j.castAdd 13 ≠ v := by
        intro h
        have he := congrArg Fin.val h
        change j.val = v.val at he
        have := j.isLt
        omega
      rw [up]
      simp only [hn, or_false, Fin.castAdd_inj]
    have hright : (fun j : T => pairInput u v (Fin.natAdd 13 j)) = (fun j => decide (j = l)) := by
      funext j
      change decide (Fin.natAdd 13 j = u ∨ Fin.natAdd 13 j = v) = decide (j = l)
      have hn : Fin.natAdd 13 j ≠ u := by
        intro h
        have he := congrArg Fin.val h
        change 13 + j.val = u.val at he
        omega
      rw [vl]
      simp only [hn, false_or, Fin.natAdd_inj]
    have targetRow : List.ofFn (pairInput u v) = pointLineInput 13 13 p l := by
      rw [List.ofFn_add (m := 13) (n := 13)]
      change ((List.ofFn fun j : T => pairInput u v (j.castAdd 13)) ++
        List.ofFn fun j : T => pairInput u v (Fin.natAdd 13 j)) = _
      rw [hleft, hright]
      rfl
    rw [targetRow]
    exact hpos p l hinc
  apply safe C hc
  · intro u v
    change C.eval (List.ofFn (pairInput u v)) = decide (I u v ∨ I v u)
    by_cases e : I u v ∨ I v u
    · rw [decide_eq_true e]
      rcases e with e | e
      · exact accepted u v e
      · have comm : pairInput u v = pairInput v u := by
          funext x
          change decide (x = u ∨ x = v) = decide (x = v ∨ x = u)
          rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
          exact or_comm
        rw [comm]
        exact accepted v u e
    · rw [decide_eq_false_iff_not.mpr e]
      exact rejects u v e C.output hneg
  · intro j hj ha
    refine ⟨?_, ?_⟩
    · intro u v h
      change W (List.ofFn (pairInput u v)) (26+j) = true at h
      by_contra hn
      rw [rejects u v hn (26+j) (hands j hj ha)] at h
      exact Bool.noConfusion h
    · intro i hi
      obtain ⟨Q, hQ, hne⟩ := hdiff j hj ha i hi
      rw [hands j hj ha Q hQ] at hne
      have ht : W (N Q) i = true := by
        cases h : W (N Q) i with
        | false => exact (hne h.symm).elim
        | true => rfl
      have hs (k : ℕ) (hk : k < C.size) (h : (G k).op = .and) :
          W (List.ofFn (A Q)) (26+k) = false := by
        rw [hrow]
        exact hands k hk h Q hQ
      have htest : W (List.ofFn (A Q)) i = true := by rw [hrow]; exact ht
      obtain ⟨v, _, hv⟩ := horigin (A Q) hs i htest
      exact ⟨v, hv⟩
