import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.FactorSubst

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5258_897
    (normalize : ∀ (n : ℕ) (R : Finset (List Bool)) (C : Circuit) (a b : ℕ),
      0 < n → (∀ x ∈ R, x.length = n) → Monotone2 C → ReadsBack n C →
      ∃ (E : Circuit) (c d : ℕ),
        Monotone2 E ∧ ReadsBack n E ∧ E.size ≤ C.size ∧
        (E.size = C.size → E = C ∧ c = a ∧ d = b) ∧
        (∀ x ∈ R, (E.wires x).getD c false = (C.wires x).getD a false ∧
          (E.wires x).getD d false = (C.wires x).getD b false) ∧
        (∀ j < E.size, n + j ∈ c :: d :: E.gates.flatMap Gate.inputs) ∧
        ∀ j < E.size, ∀ r < n + j, ∃ x ∈ R,
          (E.wires x).getD (n + j) false ≠ (E.wires x).getD r false)
    (cleanBound :
      let P := (incidences singerLines3).image
        (fun e => incidenceInput {e.1} {e.2})
      let N := (quadrangles singerLines3).image
        (fun Q => incidenceInput Q (missLines singerLines3 Q))
      ∀ (C : Circuit) (a b : ℕ),
        let V := fun w x => (C.wires x).getD w false
        Monotone2 C → ReadsBack 26 C →
        (∀ x ∈ P, (V a x && V b x) = true) →
        (∀ x ∈ N, (V a x && V b x) = false) →
        (∃ x ∈ N, V a x < V b x) → (∃ x ∈ N, V b x < V a x) →
        (∀ j < C.size, 26 + j ∈ a :: b :: C.gates.flatMap Gate.inputs) →
        (∀ j < C.size, ∀ r < 26 + j, ∃ x ∈ P ∪ N, V (26 + j) x ≠ V r x) →
        (∃ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧ InCone 26 C i j) → 63 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ) =>   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧ (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧ (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧ ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), x5 x6 x7 x8 → x6.size < (63 : ℕ) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x5 x12 x13 x14 ∧ x12.size < x6.size := by
  intro marks pos neg quad paired C a b hpair hsmall hnested
  classical
  let P : Finset (List Bool) := (incidences singerLines3).image
    (fun e => incidenceInput {e.1} {e.2})
  let N : Finset (List Bool) := (quadrangles singerLines3).image
    (fun Q => incidenceInput Q (missLines singerLines3 Q))
  let R := P ∪ N
  have inc (p l : Fin 13) : p ∈ singerLines3 l ↔ p - l ∈ marks := by
    change p ∈ singerLines3 l ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))
    revert p l
    decide
  have quadEq (Q : Finset (Fin 13)) : IsQuadrangle singerLines3 Q ↔ quad Q := by
    have inter (l : Fin 13) :
        Q ∩ singerLines3 l = Q.filter (fun p => p - l ∈ marks) := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_filter, inc]
    change (Q.card = 4 ∧ ∀ l : Fin 13, (Q ∩ singerLines3 l).card ≤ 2) ↔
      (Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ marks)).card ≤ 2)
    simp only [inter]
  have quadMem (Q : Finset (Fin 13)) :
      Q ∈ quadrangles singerLines3 ↔ quad Q := by
    simpa only [quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, IsQuadrangle] using quadEq Q
  have missing (Q : Finset (Fin 13)) (l : Fin 13) :
      l ∈ missLines singerLines3 Q ↔ ∀ p ∈ Q, p - l ∉ marks := by
    simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.disjoint_right, inc]
  have posEq (p l : Fin 13) : incidenceInput {p} {l} = pos p l := by
    simp [incidenceInput, pos]
  have negEq (Q : Finset (Fin 13)) :
      incidenceInput Q (missLines singerLines3 Q) = neg Q := by
    simp [incidenceInput, neg, missing]
  have posMem (p l : Fin 13) (h : p - l ∈ marks) : pos p l ∈ R := by
    refine Finset.mem_union.mpr (Or.inl ?_)
    refine Finset.mem_image.mpr ⟨(p, l), ?_, posEq p l⟩
    simpa only [incidences, Finset.mem_filter, Finset.mem_univ, true_and] using
      (inc p l).mpr h
  have negMem (Q : Finset (Fin 13)) (h : quad Q) : neg Q ∈ R := by
    refine Finset.mem_union.mpr (Or.inr ?_)
    exact Finset.mem_image.mpr ⟨Q, (quadMem Q).mpr h, negEq Q⟩
  have lengths : ∀ x ∈ R, x.length = 26 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hp | hn
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hp
      simp [incidenceInput]
    · obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hn
      simp [incidenceInput]
  rcases hpair with ⟨hm, hr, hp, hn, ha, hb⟩
  obtain ⟨E, c, d, hmE, hrE, hle, identity, values, live, separate⟩ :=
    normalize 26 R C a b (by decide) lengths hm hr
  by_cases hlt : E.size < C.size
  · refine ⟨E, c, d, ?_, hlt⟩
    refine ⟨hmE, hrE, ?_, ?_, ?_, ?_⟩
    · intro p l hi
      obtain ⟨hc, hd⟩ := values (pos p l) (posMem p l hi)
      simpa only [hc, hd] using hp p l hi
    · intro Q hq
      obtain ⟨hc, hd⟩ := values (neg Q) (negMem Q hq)
      simpa only [hc, hd] using hn Q hq
    · obtain ⟨Q, hq, hlt⟩ := ha
      obtain ⟨hc, hd⟩ := values (neg Q) (negMem Q hq)
      exact ⟨Q, hq, by simpa only [hc, hd] using hlt⟩
    · obtain ⟨Q, hq, hlt⟩ := hb
      obtain ⟨hc, hd⟩ := values (neg Q) (negMem Q hq)
      exact ⟨Q, hq, by simpa only [hc, hd] using hlt⟩
  · have heq : E.size = C.size := Nat.le_antisymm hle (Nat.le_of_not_gt hlt)
    obtain ⟨hEC, hca, hdb⟩ := identity heq
    subst E
    subst c
    subst d
    have hpRows : ∀ x ∈ P,
        ((C.wires x).getD a false && (C.wires x).getD b false) = true := by
      intro x hx
      obtain ⟨⟨p, l⟩, hpl, rfl⟩ := Finset.mem_image.mp hx
      have hi : p ∈ singerLines3 l := by
        simpa only [incidences, Finset.mem_filter, Finset.mem_univ, true_and] using hpl
      simpa only [posEq] using hp p l ((inc p l).mp hi)
    have hnRows : ∀ x ∈ N,
        ((C.wires x).getD a false && (C.wires x).getD b false) = false := by
      intro x hx
      obtain ⟨Q, hq, rfl⟩ := Finset.mem_image.mp hx
      simpa only [negEq] using hn Q ((quadMem Q).mp hq)
    have haRows : ∃ x ∈ N, (C.wires x).getD a false < (C.wires x).getD b false := by
      obtain ⟨Q, hq, hlt⟩ := ha
      refine ⟨neg Q, ?_, hlt⟩
      exact Finset.mem_image.mpr ⟨Q, (quadMem Q).mpr hq, negEq Q⟩
    have hbRows : ∃ x ∈ N, (C.wires x).getD b false < (C.wires x).getD a false := by
      obtain ⟨Q, hq, hlt⟩ := hb
      refine ⟨neg Q, ?_, hlt⟩
      exact Finset.mem_image.mpr ⟨Q, (quadMem Q).mpr hq, negEq Q⟩
    have bound : 63 ≤ C.size :=
      cleanBound C a b hm hr hpRows hnRows haRows hbRows live separate hnested
    exact (Nat.not_le_of_gt hsmall bound).elim
