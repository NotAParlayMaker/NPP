import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

-- The dependence-counting argument follows the project support lemmas.
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2782_731
    (clean : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      C.output < n + C.size →
      ∃ D : Circuit, IsAO2 n D ∧ D.output < n + D.size ∧ D.size ≤ C.size ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        (∀ j < D.size, D.output = n + j ∨ ∃ g ∈ D.gates, n + j ∈ g.inputs) ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (large : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (D : Circuit),
      200 ≤ q → n = q^2 + q + 1 → (∀ l, (S l).card = q + 1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n + n) D → D.output < n + n + D.size →
      (∀ g ∈ D.gates, g.inputs.Nodup) →
      (∀ j < D.size, D.output = n + n + j ∨ ∃ g ∈ D.gates, n + n + j ∈ g.inputs) →
      RightOnIncidentPairs S D →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → D.eval (incidenceInput X Y) = false) →
      n * q ≤ 100 * D.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → (∀ x14 < x4.size, x14 ∉ x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Finset (Fin x2) → Bool) (x19 : Finset (Fin x2) → Bool), ∀ (x20 x21 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x20 x21) (x2 + x2 + x14) = (x18 x20 && x19 x21)) → (100 : ℕ) * x5.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  have supportLower (n : ℕ) (C : Circuit)
      (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
      (depends : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j ≠ i, x j = y j) ∧
        C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
      n ≤ C.size + 1 := by
    let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun tape g => tape ++ [g.op.eval (g.inputs.map fun i => tape.getD i false)]) w

    have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
        (L ++ [S]).getD j d = L.getD j d := by
      by_cases hj : j < L.length
      · exact List.getD_append _ _ _ _ hj
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

    have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
      simp

    let gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
      (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

    have mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
        i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
      induction l with
      | nil => simp
      | cons b l ih => simp [ih]

    have mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
        i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
      mem_foldr_union _ _ _

    let suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
      gs.foldl (fun L g => L ++ [gateSupp L g]) L

    let inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

    let Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
      L.length = w.length ∧ w.length = w'.length ∧
        ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

    have agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
        ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
          Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
      induction gs with
      | nil => intro L w w' h; exact h
      | cons g gs ih =>
        intro L w w' h
        obtain ⟨h1, h2, h3⟩ := h
        apply ih (L ++ [gateSupp L g])
          (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
        refine ⟨by simp [h1], by simp [h2], ?_⟩
        intro j hj
        by_cases hjl : j = L.length
        · subst hjl
          rw [getD_snoc_eq] at hj
          rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
        · rw [getD_snoc_ne _ _ _ _ hjl] at hj
          rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
          exact h3 j hj

    have agree_inputs (x y : Fin n → Bool) :
        Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp [inputSupps], by simp, ?_⟩
      intro j hj
      by_cases hjn : j < n
      · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
        simp [hjn, hx]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

    let Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
      ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

    have cnt_inputs : Cnt 0 (inputSupps n) := by
      intro W
      refine le_trans Finset.card_biUnion_le ?_
      rw [zero_add, Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro j _
      by_cases hjn : j < n
      · simp [inputSupps, hjn]
      · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

    have cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
        (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
      intro W
      by_cases hW : L.length ∈ W
      · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
            ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
          intro i hi
          rw [Finset.mem_biUnion] at hi ⊢
          obtain ⟨j, hjW, hij⟩ := hi
          by_cases hjl : j = L.length
          · subst hjl
            rw [getD_snoc_eq] at hij
            obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
            exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
          · rw [getD_snoc_ne _ _ _ _ hjl] at hij
            exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
        have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [Finset.card_erase_of_mem hW]
          exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
        have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
        have := h (W.erase L.length ∪ g.inputs.toFinset)
        have := Finset.card_le_card hsub
        omega
      · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
            = (W.biUnion fun j => L.getD j ∅) := by
          apply Finset.biUnion_congr rfl
          intro j hj
          exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
        rw [heq]
        have := h W
        omega

    have cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
        (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
      induction gs with
      | nil => intro t L _ h; exact h
      | cons g gs ih =>
        intro t L hok h
        have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (cnt_step t L g (hok g List.mem_cons_self) h)
        rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
        exact this

    let S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
    have all : ∀ i : Fin n, i ∈ S := by
      intro i
      by_contra missing
      obtain ⟨x, y, same, different⟩ := depends i
      apply different
      apply (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output
      intro j hj
      exact same j (fun eq => missing (eq ▸ hj))
    have cardinal : S.card = n := by
      rw [Finset.eq_univ_of_forall all]
      simp
    have bound := cnt_suppsFrom C.gates 0 (inputSupps n) arity cnt_inputs {C.output}
    simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at bound
    change S.card ≤ C.size + 1 at bound
    rwa [cardinal] at bound

  have planeSupportBound (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit)
      (qLarge : 100 < q) (plane : n = q^2 + q + 1)
      (lineSize : ∀ l, (S l).card = q + 1)
      (through : ∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l)
      (basis : IsAO2 (n+n) C) (accept : RightOnIncidentPairs S C)
      (reject : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) :
      n + n ≤ C.size + 1 := by
    classical
    have many : 1 < n := by omega
    let vector (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
      Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
    have listForm (X Y : Finset (Fin n)) : List.ofFn (vector X Y) = incidenceInput X Y :=
      List.ofFn_fin_append _ _
    have vl (X Y : Finset (Fin n)) (l : Fin n) :
        vector X Y (Fin.natAdd n l) = decide (l ∈ Y) := Fin.addCases_right ..
    have pointReader (p : Fin n) : ∃ l, p ∈ S l := by
      let a : Fin n := ⟨0, by omega⟩
      let b : Fin n := ⟨1, by omega⟩
      have hab : a ≠ b := by
        intro eq
        have hv : (0 : ℕ) = 1 := congrArg Fin.val eq
        omega
      have other : ∃ r : Fin n, p ≠ r := by
        by_cases eq : p = a
        · exact ⟨b, fun he => hab (eq.symm.trans he)⟩
        · exact ⟨a, eq⟩
      obtain ⟨r, hr⟩ := other
      obtain ⟨l, hl, _⟩ := through p r hr
      exact ⟨l, hl.1⟩
    apply supportLower _ C (fun g hg => le_of_eq (basis.2.2 g hg))
    intro i
    refine Fin.addCases (motive := fun i => ∃ a b : Fin (n+n) → Bool,
      (∀ j ≠ i, a j = b j) ∧ C.eval (List.ofFn a) ≠ C.eval (List.ofFn b)) ?_ ?_ i
    · intro p
      obtain ⟨l, hp⟩ := pointReader p
      refine ⟨vector {p} {l}, vector ∅ {l}, ?_, ?_⟩
      · intro j different
        refine Fin.addCases (motive := fun j => j ≠ Fin.castAdd n p →
          vector {p} {l} j = vector ∅ {l} j) ?_ ?_ j different
        · intro r hr
          have hrp : r ≠ p := fun eq => hr (congrArg (Fin.castAdd n) eq)
          simp [vector, Fin.addCases_left, hrp]
        · intro r hr
          rw [vl, vl]
      · have hfalse := reject ∅ {l} (by simp; omega) (by intro z hz; simp)
        simp [listForm, accept l p hp, hfalse]
    · intro l
      have nonempty : (S l).Nonempty := Finset.card_pos.mp (by rw [lineSize]; omega)
      obtain ⟨p, hp⟩ := nonempty
      refine ⟨vector {p} {l}, vector {p} ∅, ?_, ?_⟩
      · intro j different
        refine Fin.addCases (motive := fun j => j ≠ Fin.natAdd n l →
          vector {p} {l} j = vector {p} ∅ j) ?_ ?_ j different
        · intro p hp
          simp [vector, Fin.addCases_left]
        · intro r hr
          have hrl : r ≠ l := fun eq => hr (congrArg (Fin.natAdd n) eq)
          change vector {p} {l} (Fin.natAdd n r) = vector {p} ∅ (Fin.natAdd n r)
          rw [vl, vl]
          simp [hrl]
      · have hfalse := reject {p} ∅ (by simp) (by intro z hz; simp at hz)
        simp [listForm, accept l p hp, hfalse]

  have smallPlane (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit)
      (qLarge : 100 < q) (qSmall : q < 200) (plane : n = q^2 + q + 1)
      (lineSize : ∀ l, (S l).card = q + 1)
      (through : ∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l)
      (basis : IsAO2 (n+n) C) (accept : RightOnIncidentPairs S C)
      (reject : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) :
      n * q ≤ 100 * C.size := by
    have low := planeSupportBound q n S C qLarge plane lineSize through basis accept reject
    have le : n*q ≤ n*199 := Nat.mul_le_mul_left n (by omega)
    have hn : 100 ≤ n := by omega
    omega

  intro q n S C U qLarge plane lines joins basis output accept reject rectangles smallTags
  by_cases small : q < 200
  · exact smallPlane q n S C qLarge small plane lines joins basis accept reject
  obtain ⟨D, hD, hout, hsize, nodup, live, same⟩ := clean (n+n) C basis output
  have evalInc (X Y : Finset (Fin n)) : D.eval (incidenceInput X Y) = C.eval (incidenceInput X Y) := by
    let vector : Fin (n+n) → Bool :=
      Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
    have listForm : List.ofFn vector = incidenceInput X Y := List.ofFn_fin_append _ _
    rw [← listForm]
    exact same vector
  have hAccept : RightOnIncidentPairs S D := by
    intro l p hp
    rw [evalInc]
    exact accept l p hp
  have hReject (X Y : Finset (Fin n)) (hY : Y.card ≤ q) (hFalse : IsFalseInput S X Y) :
      D.eval (incidenceInput X Y) = false := by
    rw [evalInc]
    exact reject X Y hY hFalse
  have bound := large q n S D (by omega) plane lines joins hD hout nodup live hAccept hReject
  exact bound.trans (Nat.mul_le_mul_left 100 hsize)
