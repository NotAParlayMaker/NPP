import Mathlib
import PEqualNP.Defs

-- Build each line by adding its points one at a time.
-- Pair inputs suffice through order 299; at higher orders use the incident pairs
-- and the largest rejecting point set for each allowed set of lines.
theorem PEqualNP.Outside.R_meta_3572_417
    (low : ∀ (q N : ℕ) (F : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → q < 300 → N = q^2 + q + 1 →
      (∀ l, (F l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ F l ∧ r ∈ F l) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin (N+N) → Bool,
        Fintype.card {i : Fin (N+N) // x i = true} ≤ 2 →
        PEqualNP.MetaComplexity.circuitFun (N+N) C x =
          decide (∃ p l, p ∈ F l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
      N*q ≤ 100*C.size)
    (high : ∀ (q N : ℕ) (F : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      300 ≤ q → N = q^2 + q + 1 →
      (∀ l, (F l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ F l ∧ r ∈ F l) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p l, p ∈ F l → PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ S : Finset (Fin N), S.card ≤ q → PEqualNP.MetaComplexity.circuitFun (N+N) C
        (Fin.append (fun p => decide (∀ l ∈ S, p ∉ F l)) (fun l => decide (l ∈ S))) = false) →
      N*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) → ∃ (x11 : List (Finset (Fin x2))), x11.length ≤ (100 : ℕ) * x4.size ∧ (∀ (x12 : Fin x2), x3 x12 ∈ x11) ∧ ∀ (x12 : ℕ) (x13 : Finset (Fin x2)), x11[x12]? = Option.some x13 → ∃ (x15 : Finset (Fin x2)) (x16 : Finset (Fin x2)), x13 = x15 ∪ x16 ∧ (x15.card ≤ (1 : ℕ) ∨ x15 ∈ List.take x12 x11) ∧ (x16.card ≤ (1 : ℕ) ∨ x16 ∈ List.take x12 x11) := by
  let valid {α : Type} [DecidableEq α] (xs : List (Finset α)) : Prop :=
    ∀ j S, xs[j]? = some S → ∃ A B : Finset α, S = A ∪ B ∧
      (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j)
  have extend {α : Type} [DecidableEq α]
      (work : List α) (start : Finset α) (pre : List (Finset α))
      (available : start.card ≤ 1 ∨ start ∈ pre) (ok : valid pre) :
      ∃ xs : List (Finset α), xs.length = pre.length + work.length ∧
        (∀ A ∈ pre, A ∈ xs) ∧ valid xs ∧
        (work ≠ [] → start ∪ work.toFinset ∈ xs) := by
    induction work generalizing start pre with
    | nil => exact ⟨pre,by simp,fun _ h => h,ok,by simp⟩
    | cons a tail ih =>
      let next := start ∪ {a}
      let longer := pre ++ [next]
      have nextMem : next ∈ longer := by simp [longer]
      have goodOne : valid longer := by
        intro j S h
        change (pre ++ [next])[j]? = some S at h
        by_cases jOld : j < pre.length
        · rw [List.getElem?_append_left jOld] at h
          obtain ⟨A,B,e,left,right⟩ := ok j S h
          have same : longer.take j = pre.take j := List.take_append_of_le_length jOld.le
          rw [same]
          exact ⟨A,B,e,left,right⟩
        · have jTop : j = pre.length := by
            have jRange : j < (pre ++ [next]).length := by
              by_contra hn
              rw [List.getElem?_eq_none (by omega)] at h
              cases h
            simp at jRange
            omega
          subst j
          have p : S = next := by
            rw [List.getElem?_append_right (by omega)] at h
            simpa using h.symm
          change ∃ A B : Finset α, S = A ∪ B ∧ (A.card ≤ 1 ∨ A ∈ (pre ++ [next]).take pre.length) ∧
            (B.card ≤ 1 ∨ B ∈ (pre ++ [next]).take pre.length)
          rw [p,List.take_left]
          exact ⟨start,{a},rfl,available,Or.inl (by simp)⟩
      obtain ⟨xs,xsLen,old,good,ends⟩ := ih next longer (Or.inr nextMem) goodOne
      refine ⟨xs,by simpa [longer,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using xsLen,
        fun A h => old A (List.mem_append_left _ h),good,?_⟩
      intro _
      by_cases empty : tail = []
      · simpa [empty,next] using old next nextMem
      · have same : start ∪ (a :: tail).toFinset = next ∪ tail.toFinset := by
          ext x
          simp [next]
        exact same.symm ▸ ends empty
  have schedule {α : Type} [DecidableEq α] (targets : List (Finset α)) (q : ℕ) (pos : 0 < q)
      (sizes : ∀ A ∈ targets, A.card = q+1) :
      ∃ xs : List (Finset α), xs.length = targets.length*q ∧
        (∀ A ∈ targets, A ∈ xs) ∧ valid xs := by
    induction targets with
    | nil => exact ⟨[],by simp,by simp,by intro i S h; simp at h⟩
    | cons A targets ih =>
      have size := sizes A (by simp)
      obtain ⟨pre,preLen,outputs,preGood⟩ := ih (fun B h => sizes B (List.mem_cons_of_mem _ h))
      have fullLen : A.toList.length = q+1 := by simpa using size
      cases eq : A.toList with
      | nil => simp [eq] at fullLen
      | cons a tail =>
        obtain ⟨xs,xsLen,old,good,ends⟩ := extend tail ({a} : Finset α) pre (Or.inl (by simp)) preGood
        refine ⟨xs,?_,?_,good⟩
        · rw [xsLen,preLen,List.length_cons,Nat.succ_mul]
          simp only [eq,List.length_cons] at fullLen
          omega
        · intro B h
          rcases List.mem_cons.mp h with rfl | earlier
          · have nonempty : tail ≠ [] := by
              intro empty
              simp [eq,empty] at fullLen
              omega
            have same : ({a} : Finset α) ∪ tail.toFinset = B := by
              rw [← Finset.toList_toFinset B,eq]
              ext x
              simp
            exact same ▸ ends nonempty
          · exact old B (outputs B earlier)
  intro q N F C big order sizes unique mono correct
  have cost : N*q ≤ 100*C.size := by
    by_cases large : 300 ≤ q
    · apply high q N F C large order sizes unique mono
      · intro p l pl
        let x : Fin (N+N) → Bool := fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
        have card : Fintype.card {j : Fin N // x (Fin.natAdd N j) = true} ≤ q := by
          let J (j : {j : Fin N // x (Fin.natAdd N j) = true}) : {a : Fin N // a = l} := by
            refine ⟨j.val,?_⟩
            rcases (of_decide_eq_true j.property :
                Fin.natAdd N j.val = Fin.castAdd N p ∨ Fin.natAdd N j.val = Fin.natAdd N l) with h | h
            · have e := congrArg Fin.val h
              change N + j.val.val = p.val at e
              have lt := p.isLt
              omega
            · apply Fin.ext
              have e := congrArg Fin.val h
              change N + j.val.val = N + l.val at e
              omega
          have inj : Function.Injective J := fun a b eq =>
            Subtype.ext (congrArg (fun z : {a : Fin N // a = l} => z.val) eq)
          apply (Fintype.card_le_of_injective J inj).trans
          rw [Fintype.card_of_subtype ({l} : Finset (Fin N)) (fun a => Finset.mem_singleton)]
          simp only [Finset.card_singleton]
          omega
        change PEqualNP.MetaComplexity.circuitFun (N+N) C x = true
        rw [correct x card]
        exact decide_eq_true ⟨p,l,pl,by simp [x],by simp [x]⟩
      · intro S count
        let x : Fin (N+N) → Bool :=
          Fin.append (fun p => decide (∀ l ∈ S, p ∉ F l)) (fun l => decide (l ∈ S))
        have lineAt (l : Fin N) : x (Fin.natAdd N l) = decide (l ∈ S) := Fin.append_right _ _ _
        have card : Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q := by
          have exactCount : Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} = S.card :=
            Fintype.card_of_subtype S (fun l => by rw [lineAt,decide_eq_true_eq])
          exact exactCount.le.trans count
        have excluded : ¬ ∃ p l, p ∈ F l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
          rintro ⟨p,l,pl,pOn,lOn⟩
          have pMisses : ∀ l ∈ S, p ∉ F l := by simpa [x] using pOn
          have chosen : l ∈ S := by rw [lineAt] at lOn; exact of_decide_eq_true lOn
          exact pMisses l chosen pl
        change PEqualNP.MetaComplexity.circuitFun (N+N) C x = false
        rw [correct x card, decide_eq_false excluded]
    · apply low q N F C big (by omega) order sizes unique mono
      intro x few
      apply correct x
      let J (j : {l : Fin N // x (Fin.natAdd N l) = true}) : {i : Fin (N+N) // x i = true} :=
        ⟨Fin.natAdd N j.val,j.property⟩
      have inj : Function.Injective J := by
        intro a b eq
        apply Subtype.ext
        apply Fin.ext
        have same := congrArg (fun y : {i : Fin (N+N) // x i = true} => y.val.val) eq
        change N + a.val.val = N + b.val.val at same
        omega
      exact (Fintype.card_le_of_injective J inj).trans (few.trans (by omega))
  let targets := List.ofFn F
  have each : ∀ A ∈ targets, A.card = q+1 := by
    intro A mem
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
    exact sizes j
  obtain ⟨xs,len,seen,ok⟩ := schedule targets q (by omega) each
  refine ⟨xs,?_,fun l => seen (F l) (List.mem_ofFn.mpr ⟨l,rfl⟩),ok⟩
  rw [len,show targets.length = N by simp [targets]]
  exact cost
