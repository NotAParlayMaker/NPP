import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_3051_713
    (selects : ∀ (n : ℕ) (C : Circuit) (_mc : Monotone2 C) (E : Finset ℕ)
    (G : Finset (Fin n) → Prop) (_initial : G ∅),
    ∃ (A : Finset (Fin n)) (D : Circuit), G A ∧ A.card ≤ 2*E.card ∧
      D.size = C.size ∧ Monotone2 D ∧
      (∀ j g, C.gates[j]? = some g →
        (D.gates[j]? = some g ∧ (j ∉ E ∨ g.op ≠ .and ∨ g.inputs.length ≠ 2)) ∨
        ∃ i ∈ g.inputs, D.gates[j]? = some ⟨.or,[i]⟩) ∧
      (∀ x, C.eval x = true → D.eval x = true) ∧
      (∀ B : Finset (Fin n), B.card ≤ 2 → G (A ∪ B) →
        D.eval (List.ofFn (fun i => decide (i ∈ A ∪ B))) =
        C.eval (List.ofFn (fun i => decide (i ∈ A ∪ B)))))
    (flat : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → n = q^2+q+1 → (∀ l : Fin n, Fintype.card {p // I p l} = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C → (∀ p l, I p l → circuitFun (n+n) C (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) →
      let bin := fun j : ℕ => (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2
      let dep := fun i j : ℕ => i < j ∧ n+n+i ∈ (gateAt C j).inputs
      (¬∃ i j, bin i ∧ bin j ∧ Relation.TransGen dep i j) →
      let free := fun X : Finset (Fin (n+n)) => ¬ ∃ p l, I p l ∧ Fin.castAdd n p ∈ X ∧ Fin.natAdd n l ∈ X
      ∀ A : Finset (Fin (n+n)), free A →
      (∀ B : Finset (Fin (n+n)), B.card ≤ 2 → free (A ∪ B) →
        C.eval (List.ofFn (fun i => decide (i ∈ A ∪ B))) = false) →
      n*(q+1) ≤ C.size+A.card*(q+1)^2)
    (deep : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      300 ≤ q → n = q^2+q+1 → (∀ l : Fin n, Fintype.card {p // I p l} = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C → (∀ p l, I p l → circuitFun (n+n) C (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) → (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      let bin := fun j : ℕ => (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2
      let dep := fun i j : ℕ => i < j ∧ n+n+i ∈ (gateAt C j).inputs
      (∀ S : Finset ℕ, 100*S.card ≤ 49*q →
        ∃ i j, i ∉ S ∧ j ∉ S ∧ bin i ∧ bin j ∧ Relation.TransGen dep i j) →
      n*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n I dec C hq hn degrees uniqueLine mc pos neg
  classical
  let bin := fun (K : Circuit) (j : ℕ) => (gateAt K j).op = GateOp.and ∧ (gateAt K j).inputs.length = 2
  let dep := fun (K : Circuit) (i j : ℕ) => i < j ∧ n+n+i ∈ (gateAt K j).inputs
  by_cases many : ∀ S : Finset ℕ, 100*S.card ≤ 49*q →
      ∃ i j, i ∉ S ∧ j ∉ S ∧ bin C i ∧ bin C j ∧ Relation.TransGen (dep C) i j
  · exact deep q n I C hq hn degrees uniqueLine mc pos neg many
  push Not at many
  obtain ⟨S,few,separate⟩ := many
  let free := fun X : Finset (Fin (n+n)) => ¬ ∃ p l, I p l ∧ Fin.castAdd n p ∈ X ∧ Fin.natAdd n l ∈ X
  obtain ⟨A,D,ok,cost,size,md,edits,above,agree⟩ := selects (n+n) C mc S free (by simp [free])
  have trace (j : ℕ) :
      (gateAt D j = gateAt C j ∧ (j ∉ S ∨ (gateAt C j).op ≠ .and ∨ (gateAt C j).inputs.length ≠ 2)) ∨
      ∃ i ∈ (gateAt C j).inputs, gateAt D j = ⟨.or,[i]⟩ := by
    unfold gateAt
    cases raw : C.gates[j]? with
    | none =>
      have cj : C.gates.length ≤ j := List.getElem?_eq_none_iff.mp raw
      have dj : D.gates.length ≤ j := by change D.size ≤ j; rw [size]; exact cj
      simp only [List.getD_eq_default _ _ cj, List.getD_eq_default _ _ dj]
      exact Or.inl ⟨trivial, Or.inr (Or.inl (by intro impossible; cases impossible))⟩
    | some g =>
      rcases edits j g raw with ⟨h,why⟩ | ⟨i,hi,h⟩
      · simpa only [List.getD,raw,h,Option.getD_some, eq_self, true_and] using Or.inl (b := ∃ i ∈ g.inputs, g = ⟨.or,[i]⟩) why
      · right
        exact ⟨i,by simpa [List.getD,raw] using hi,by simp [List.getD,h]⟩
  have original {i} (hi : bin D i) : i ∉ S ∧ bin C i := by
    rcases trace i with ⟨eq,choice⟩ | ⟨_,_,eq⟩
    · change (gateAt D i).op = .and ∧ (gateAt D i).inputs.length = 2 at hi
      rw [eq] at hi
      exact ⟨choice.elim id (fun h => False.elim (h.elim (fun h => h hi.1) (fun h => h hi.2))),hi⟩
    · have h := hi.1
      rw [eq] at h
      contradiction
  have lift {i j} (h : dep D i j) : dep C i j := by
    refine ⟨h.1,?_⟩
    have input := h.2
    rcases trace j with ⟨eq,_⟩ | ⟨a,ha,eq⟩
    · rwa [eq] at input
    · rw [eq] at input
      exact List.mem_singleton.mp input ▸ ha
  have shallow : ¬∃ i j, bin D i ∧ bin D j ∧ Relation.TransGen (dep D) i j := by
    rintro ⟨i,j,hi,hj,path⟩
    obtain ⟨is,ci⟩ := original hi
    obtain ⟨js,cj⟩ := original hj
    have lifts : dep D ≤ dep C := fun a b edge => lift edge
    exact separate i j is js ci cj (Relation.TransGen.mono lifts i j path)
  have dpos (p l) (h : I p l) := above _ (pos p l h)
  have estimate := flat q n I D (by omega) hn degrees uniqueLine md dpos shallow A ok (by
    intro B small independent
    rw [agree B small independent]
    let x : Fin (n+n) → Bool := fun i => decide (i ∈ A ∪ B)
    apply neg x
    · let f : {l : Fin n // x (Fin.natAdd n l) = true} → ↥(A ∪ B) :=
        fun l => ⟨Fin.natAdd n l.val,of_decide_eq_true l.property⟩
      have inj : Function.Injective f := by
        intro u v eq
        apply Subtype.ext
        apply Fin.ext
        have h := congrArg (fun z : ↥(A ∪ B) => z.val.val) eq
        change n + u.val.val = n + v.val.val at h
        omega
      have bound := Fintype.card_le_of_injective f inj
      rw [Fintype.card_coe] at bound
      have union := Finset.card_union_le A B
      omega
    · rintro ⟨p,l,h,pp,ll⟩
      exact independent ⟨p,l,h,of_decide_eq_true pp,of_decide_eq_true ll⟩)
  rw [size] at estimate
  have budget := Nat.mul_le_mul_right ((q+1)^2) few
  have kept := Nat.mul_le_mul_right ((q+1)^2) cost
  subst n
  nlinarith
