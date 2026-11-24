import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Compress the point masks of sulimma’s finite tests (PR #9976) by their compatible
-- line sets. Complete each distinct line set by every compatible point.
-- A witness for the size-28 search must miss at least six incident singletons.
-- The wire-monotonicity induction follows the gate evaluation in R_meta_4061_704.
theorem PEqualNP.Outside.R_meta_4966_314
    (six :
    let P (a : Fin 25) := a.val < 12 ∧ a.val ∉ ([0, 2, 8] : List ℕ)
    let I (a b : Fin 25) := a.val < 12 ∧ 12 ≤ b.val ∧
      (a.val + b.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ a.val ∉ ([0, 2, 8] : List ℕ)
    ∀ (C : Circuit) (w : Fin 25 → ℕ) (q : ℕ),
      let W (x : Fin 25 → Bool) (j : ℕ) := (C.wires (List.ofFn x)).getD j false
      Monotone2 C → C.size ≤ 28 → (∀ i, w i < 25 + C.size) → q < 25 + C.size →
      (∀ x, (∀ a b, I a b → x a = true → x b = true → W x (w a) = true) ∧
        ((¬∃ a b, I a b ∧ x a = true ∧ x b = true) →
          (∀ a, P a → x a = true → W x (w a) = false) ∧ W x q = (x 13 || x 15 || x 21))) →
      let bad : Finset (Fin 25 × Fin 25) := Finset.univ.filter fun e =>
        I e.1 e.2 ∧ W (fun j => decide (j = e.2)) (w e.1) = false
      6 ≤ bad.card)
    (bank :
    let P (a : Fin 25) := a.val < 12 ∧ a.val ∉ ([0, 2, 8] : List ℕ)
    let I (a b : Fin 25) := a.val < 12 ∧ 12 ≤ b.val ∧
      (a.val + b.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ a.val ∉ ([0, 2, 8] : List ℕ)
    let T := ([13, 15, 21] : List (Fin 25))
    let S : Finset (Fin 25) := Finset.univ.filter P
    let lines (c : Bool) (A : Finset (Fin 25)) : Finset (Fin 25) := Finset.univ.filter fun l =>
      12 ≤ l.val ∧ (c = false ∨ l ∉ T) ∧ (A.filter fun p => I p l) = ∅
    let hi (L : Finset (Fin 25)) (j : Fin 25) := decide (if 12 ≤ j.val then j ∈ L else (L.filter (I j)) = ∅)
    ∃ (C : Circuit) (w : Fin 25 → ℕ) (q : ℕ),
      let W (x : Fin 25 → Bool) (j : ℕ) := (C.wires (List.ofFn x)).getD j false
      Monotone2 C ∧ C.size ≤ 28 ∧ (∀ i, w i < 25 + C.size) ∧ q < 25 + C.size ∧
      (∀ a b, I a b → W (fun j => decide (j = a ∨ j = b)) (w a) = true) ∧
      (∀ t ∈ T, W (fun j => decide (j = t)) q = true) ∧
      ∀ c, ∀ L ∈ S.powerset.image (lines c), if c then W (hi L) q = false
        else ∀ p ∈ S, hi L p = true → W (hi L) (w p) = false) :
    let I := fun p l : Fin 25 => p.val < 12 ∧ 12 ≤ l.val ∧
      (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ)
    ∃ (B : Circuit) (w : Fin 25 → ℕ) (q : ℕ), Monotone2 B ∧ B.size ≤ 28 ∧
      (∀ i, w i < 25+B.size) ∧ q < 25+B.size ∧
      (∃ p l, I p l ∧ (B.wires (List.ofFn (fun j : Fin 25 => decide (j=l)))).getD (w p) false = false) ∧
      ∀ x : Fin 25 → Bool,
        let v := fun a => (B.wires (List.ofFn x)).getD a false
        (∀ p l, I p l → x p = true → x l = true → v (w p) = true) ∧
        ((¬ ∃ p l, I p l ∧ x p = true ∧ x l = true) →
          (∀ p, p.val < 12 → p.val ∉ ([0,2,8] : List ℕ) → x p = true → v (w p) = false) ∧
          v q = (x 13 || x 15 || x 21)) := by
  extract_lets P I T S lines hi at bank
  have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let run (gs : List Gate) (w : List Bool) :=
    gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) w

  let dominates (p q : List Bool) := p.length = q.length ∧
    ∀ i : Nat, p.getD i false = true → q.getD i false = true

  have true_append {p q : List Bool} (h : dominates p q) {a b : Bool}
      (hb : a = true → b = true) : dominates (p ++ [a]) (q ++ [b]) := by
    refine ⟨by simp [h.1], ?_⟩
    intro i
    by_cases hs : i < p.length
    · rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ (h.1 ▸ hs)]
      exact h.2 i
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by have := h.1; omega), ← h.1]
      cases i-p.length with
      | zero => exact hb
      | succ k => simp [List.getD]

  have run_mono (gs : List Gate)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) {p q : List Bool}
      (h : dominates p q) : dominates (run gs p) (run gs q) := by
    induction gs generalizing p q with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))
      apply true_append h
      rcases ops g List.mem_cons_self with hop | hop
      · simp only [hop, andEval, List.all_eq_true, List.mem_map, id_eq]
        intro yes v hv
        obtain ⟨i, hi, rfl⟩ := hv
        exact h.2 i (yes _ ⟨i, hi, rfl⟩)
      · simp only [hop, orEval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
        exact ⟨_, ⟨i, hi, rfl⟩, h.2 i hv⟩

  have bits_dom {n : Nat} {x y : Fin n → Bool}
      (h : ∀ i, x i = true → y i = true) : dominates (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hi : i < (List.ofFn x).length),
          List.getD_eq_getElem _ _ (by simpa using hi : i < (List.ofFn y).length), List.getElem_ofFn, List.getElem_ofFn]
      exact h _
    · simp [hi]

  obtain ⟨C,w,q,model,size,wb,qb,pairs,ones,upper⟩ := bank
  let W (x : Fin 25 → Bool) (j : ℕ) := (C.wires (List.ofFn x)).getD j false
  have mono {x y : Fin 25 → Bool} (h : ∀ j, x j = true → y j = true) (k : ℕ) :
      W x k = true → W y k = true :=
    (run_mono C.gates (fun g hg => (model g hg).1) (bits_dom h)).2 k
  have spec (x : Fin 25 → Bool) :
      (∀ a b, I a b → x a = true → x b = true → W x (w a) = true) ∧
      ((¬∃ a b, I a b ∧ x a = true ∧ x b = true) →
        (∀ a, P a → x a = true → W x (w a) = false) ∧ W x q = (x 13 || x 15 || x 21)) := by
    constructor
    · intro a b e ha hb
      apply mono _ _ (pairs a b e)
      intro j hj
      rcases of_decide_eq_true hj with rfl | rfl
      · exact ha
      · exact hb
    · intro no
      let A := S.filter fun a => x a = true
      have sub : A ⊆ S := Finset.filter_subset _ _
      have mem (a : Fin 25) : a ∈ A ↔ P a ∧ x a = true := by simp [A,S]
      have member (c : Bool) : lines c A ∈ S.powerset.image (lines c) :=
        Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr sub)
      have covers (c : Bool) (off : c = true → ∀ t ∈ T, x t = false) (j : Fin 25) (lit : x j = true) :
          hi (lines c A) j = true := by
        apply decide_eq_true
        by_cases hj : 12 ≤ j.val
        · rw [ite_eq_left hj]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,?_,?_⟩
          · cases hc : c with
            | false => exact Or.inl rfl
            | true => exact Or.inr fun ht => Bool.false_ne_true ((off hc j ht).symm.trans lit)
          · apply Finset.filter_eq_empty_iff.mpr
            intro a ha edge
            exact no ⟨a,j,edge,((mem a).mp ha).2,lit⟩
        · rw [ite_eq_right hj]
          apply Finset.filter_eq_empty_iff.mpr
          intro l hl e
          exact (Finset.filter_eq_empty_iff.mp (Finset.mem_filter.mp hl).2.2.2)
            ((mem j).mpr ⟨⟨e.1,e.2.2.2⟩,lit⟩) e
      have rows := upper false _ (member false)
      have zero := upper true _ (member true)
      change ∀ p ∈ S, hi (lines false A) p = true → W (hi (lines false A)) (w p) = false at rows
      change W (hi (lines true A)) q = false at zero
      constructor
      · intro a hp ha
        apply Bool.eq_false_iff.mpr
        intro yes
        have le := covers false (fun hc => by cases hc)
        exact Bool.false_ne_true ((rows a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
          (le a ha)).symm.trans (mono le _ yes))
      · by_cases ht : ∃ t ∈ T, x t = true
        · obtain ⟨t,ht,hx⟩ := ht
          have le (j : Fin 25) (hj : decide (j=t) = true) : x j = true := by rwa [of_decide_eq_true hj]
          rw [mono le _ (ones t ht)]
          simp only [T,List.mem_cons,List.not_mem_nil,or_false] at ht
          rcases ht with rfl | rfl | rfl <;> simp [hx]
        · have off (t : Fin 25) (ht' : t ∈ T) : x t = false :=
            Bool.eq_false_iff.mpr (fun on => ht ⟨t,ht',on⟩)
          have hq : W x q = false := Bool.eq_false_iff.mpr fun yes =>
            Bool.false_ne_true (zero.symm.trans (mono (covers true (fun _ => off)) _ yes))
          rw [hq,off 13 (by decide),off 15 (by decide),off 21 (by decide)]
          rfl
  have h := six C w q model size wb qb spec
  obtain ⟨⟨a,b⟩,hf⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 6) h)
  obtain ⟨e,miss⟩ := (Finset.mem_filter.mp hf).2
  refine ⟨C,w,q,model,size,wb,qb,⟨a,b,e,miss⟩,?_⟩
  intro x
  refine ⟨(spec x).1,?_⟩
  intro no
  obtain ⟨neg,aux⟩ := (spec x).2 no
  exact ⟨fun i hi hr => neg i ⟨hi,hr⟩,aux⟩
