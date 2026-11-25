import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CrossAnd PEqualNP.GenericRejection PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.SyntacticMultilinear

-- Replace one cross AND with an OR of at most two wires, without increasing its support.
-- Test the new output on maximal false inputs and count the incident singleton pairs it loses.
-- A vertex cover groups the missing edges into stars. A star with d assigned edges
-- costs d-1 disjunctions of leaves, one pure AND, and one OR into the old output.
-- The geometric premise bounds the number of missing edges plus the size of their cover.
-- For example, 24 arbitrary missing edges or 48 sharing one endpoint fit the budget.
theorem PEqualNP.Outside.R_meta_4594_49
    (localBound : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      199 ≤ q → N = q ^ 2 + q + 1 → (∀ l, (S l).card = q + 1) →
      (∀ l k, l ≠ k → (S l ∩ S k).card ≤ 1) → Monotone2 C → ComputesIncidence S C →
      2 * C.size < N * q →
      let M := Finset.univ.map (Fin.natAddEmb N)
      0 < crossCount (N + N) M C →
      ∃ j < C.gates.length, IsCrossAnd (N + N) M C j ∧
        ∃ ws : List ℕ, ws.length ≤ 2 ∧
        let D : Circuit := { C with gates := C.gates.set j ⟨GateOp.or, ws⟩ }
        let E := Finset.univ.filter (fun e : Fin N × Fin N =>
          e.1 ∈ S e.2 ∧ D.eval (incidenceInput {e.1} {e.2}) = false)
        support (N + N) D (N + N + j) ⊆ support (N + N) C (N + N + j) ∧
        (∀ X Y, IsMaximalFalse S X Y → D.eval (incidenceInput X Y) = false) ∧
        ∃ P L : Finset (Fin N), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) ∧
          E.card + P.card + L.card ≤ 49)
    (star : ∀ (N : ℕ) (D : Circuit) (line : Bool) (c : Fin N) (leaves : Finset (Fin N)), Monotone2 D → leaves.Nonempty →
      let count := crossCount (N + N) (Finset.univ.map (Fin.natAddEmb N))
      ∃ B : Circuit, Monotone2 B ∧ count B ≤ count D ∧ B.size ≤ D.size + leaves.card + 1 ∧
        ∀ X Y : Finset (Fin N), B.eval (incidenceInput X Y) =
          (D.eval (incidenceInput X Y) || decide (if line then c∈Y ∧ ∃ p∈leaves, p∈X else c∈X ∧ ∃ l∈leaves, l∈Y))) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → (x3 x8 ∩ x3 x9).card ≤ (1 : ℕ)) →           PEqualNP.MetaComplexity.Monotone2 x4 →             PEqualNP.GenericRejection.ComputesIncidence x3 x4 →               have x11 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.map (Fin.natAddEmb x2) Finset.univ);               (2 : ℕ) * x4.size < x2 * x1 → (0 : ℕ) < x11 x4 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ PEqualNP.GenericRejection.ComputesIncidence x3 x14 ∧ x11 x14 < x11 x4 ∧ x14.size ≤ x4.size + (49 : ℕ) := by
  classical
  let wireLE (x y : List Bool) : Prop :=
    x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true
  let semStep (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have append_bit_le {x y : List Bool} {a b : Bool} (h : wireLE x y)
      (hb : a = true → b = true) : wireLE (x ++ [a]) (y ++ [b]) := by
    obtain ⟨hlen, hxy⟩ := h
    refine ⟨by simp [hlen], ?_⟩
    intro i
    by_cases hi : i < x.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
      exact hxy i
    · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hlen]
      cases i - y.length with
      | zero => simpa using hb
      | succ k => simp
  have semStep_le {x y : List Bool} {g : Gate} (h : wireLE x y)
      (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
      wireLE (semStep x g) (semStep y g) := by
    apply append_bit_le h
    rcases hop with he | he
    · rw [he]
      dsimp only [GateOp.eval]
      simp only [List.all_eq_true, List.mem_map, id_eq]
      intro hall _ hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact h.2 i (hall _ ⟨i, hi, rfl⟩)
    · change g.op = GateOp.or at he
      rw [he]
      dsimp only [GateOp.eval]
      simp only [List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨_, ⟨i, hi, rfl⟩, h.2 i hx⟩
  have fold_semStep_le (gs : List Gate)
      (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      {x y : List Bool} (h : wireLE x y) :
      wireLE (gs.foldl semStep x) (gs.foldl semStep y) := by
    induction gs generalizing x y with
    | nil => exact h
    | cons g gs ih =>
      exact ih (fun h' hh => hm h' (List.mem_cons_of_mem _ hh))
        (semStep_le h (hm g List.mem_cons_self))
  have incidenceInput_length {n : ℕ} (X Y : Finset (Fin n)) :
      (incidenceInput X Y).length = n + n := by
    unfold incidenceInput
    simp
  have incidenceInput_getD_left {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi : i < n) :
      (incidenceInput X Y).getD i false = decide (⟨i, hi⟩ ∈ X) := by
    unfold incidenceInput
    rw [List.getD_append _ _ _ _ (by simp [hi])]
    have hof : (List.ofFn fun p : Fin n => decide (p ∈ X))[i]? = some (decide (⟨i, hi⟩ ∈ X)) := by
      simp [List.getElem?_eq_getElem (by simp [hi] : i < (List.ofFn fun p : Fin n => decide (p ∈ X)).length)]
    rw [List.getD, hof]; rfl
  have incidenceInput_getD_right {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < n + n) :
      (incidenceInput X Y).getD i false = decide (⟨i - n, by omega⟩ ∈ Y) := by
    unfold incidenceInput
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; exact hi1)]
    simp only [List.length_ofFn]
    have hof : (List.ofFn fun l : Fin n => decide (l ∈ Y))[i - n]? = some (decide (⟨i - n, by omega⟩ ∈ Y)) := by
      simp [List.getElem?_eq_getElem (by simp; omega : i - n < (List.ofFn fun l : Fin n => decide (l ∈ Y)).length)]
    rw [List.getD, hof]; rfl
  have incidence_eval_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
      {X₁ X₂ Y₁ Y₂ : Finset (Fin n)} (hX : X₁ ⊆ X₂) (hY : Y₁ ⊆ Y₂) :
      C.eval (incidenceInput X₁ Y₁) = true → C.eval (incidenceInput X₂ Y₂) = true := by
    apply (fold_semStep_le C.gates (fun g hg => (hm g hg).1) _).2 C.output
    refine ⟨by simp only [incidenceInput_length], ?_⟩
    intro i hi
    by_cases hp : i < n
    · rw [incidenceInput_getD_left _ _ _ hp] at hi ⊢
      exact decide_eq_true (hX (of_decide_eq_true hi))
    · by_cases hl : i < n+n
      · rw [incidenceInput_getD_right _ _ _ (by omega) hl] at hi ⊢
        exact decide_eq_true (hY (of_decide_eq_true hi))
      · rw [List.getD_eq_default _ _ (by rw [incidenceInput_length]; omega)] at hi
        contradiction
  have patch : ∀ (N : ℕ) (S : Fin N → Finset (Fin N)) (D : Circuit) (P L : Finset (Fin N)),
        Monotone2 D → (∀ X Y, D.eval (incidenceInput X Y) = true → incidenceFun S X Y = true) →
        let E := Finset.univ.filter (fun e : Fin N × Fin N =>
          e.1 ∈ S e.2 ∧ D.eval (incidenceInput {e.1} {e.2}) = false)
        (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) →
        let count := crossCount (N + N) (Finset.univ.map (Fin.natAddEmb N))
        ∃ B : Circuit, Monotone2 B ∧ ComputesIncidence S B ∧ count B ≤ count D ∧
          B.size ≤ D.size + E.card + P.card + L.card := by
    have computes_of_sound_and_pairs {n : ℕ} {S : Fin n → Finset (Fin n)} {C : Circuit}
        (hm : Monotone2 C)
        (sound : ∀ X Y : Finset (Fin n), C.eval (incidenceInput X Y) = true →
          incidenceFun S X Y = true)
        (pairs : RightOnIncidentPairs S C) : ComputesIncidence S C := by
      intro X Y
      cases hf : incidenceFun S X Y with
      | false =>
        cases he : C.eval (incidenceInput X Y) with
        | false => rfl
        | true => exact (Bool.noConfusion (hf.symm.trans (sound X Y he)))
      | true =>
        obtain ⟨p, hp, l, hl, hpl⟩ := of_decide_eq_true hf
        exact incidence_eval_mono hm (Finset.singleton_subset_iff.mpr hp)
          (Finset.singleton_subset_iff.mpr hl) (pairs l p hpl)
    intro N S D P L hm sound E hcover count
    let touches (a : Fin N ⊕ Fin N) (e : Fin N × Fin N) : Prop :=
      a.elim (fun p => e.1 = p) (fun l => e.2 = l)
    have grow (K : Finset (Fin N ⊕ Fin N)) :
        ∀ (U : Finset (Fin N × Fin N)),
        (∀ e ∈ U, ∃ a ∈ K, touches a e) →
        ∃ B : Circuit, Monotone2 B ∧ count B ≤ count D ∧
          B.size ≤ D.size + U.card + K.card ∧
          ∀ X Y : Finset (Fin N), B.eval (incidenceInput X Y) = true ↔
            D.eval (incidenceInput X Y) = true ∨ ∃ e ∈ U, e.1 ∈ X ∧ e.2 ∈ Y := by
      induction K using Finset.induction_on with
      | empty =>
        intro U covers
        have hu : U = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
          intro e he
          obtain ⟨a, ha, _⟩ := covers e he
          simp at ha)
        exact ⟨D, hm, le_rfl, by simp [hu], by simp [hu]⟩
      | @insert a K ha ih =>
        intro U covers
        let A := U.filter (touches a)
        let R := U.filter (fun e => ¬ touches a e)
        have splitCard : A.card + R.card = U.card :=
          Finset.card_filter_add_card_filter_not (touches a)
        have splitHit (e : Fin N × Fin N) : e ∈ U ↔ e ∈ R ∨ e ∈ A := by
          simp only [R, A, Finset.mem_filter]
          tauto
        have remCover (e) (he : e ∈ R) : ∃ b ∈ K, touches b e := by
          obtain ⟨hu, hn⟩ := Finset.mem_filter.mp he
          obtain ⟨b, hb, ht⟩ := covers e hu
          rcases Finset.mem_insert.mp hb with rfl | h
          · exact False.elim (hn ht)
          · exact ⟨b, h, ht⟩
        obtain ⟨B, bm, bc, bs, bf⟩ := ih R remCover
        rw [Finset.card_insert_of_notMem ha]
        by_cases hA : A.Nonempty
        · let side : Bool := a.elim (fun _ => false) (fun _ => true)
          let center : Fin N := a.elim id id
          let other : Fin N × Fin N → Fin N := a.elim (fun _ => Prod.snd) (fun _ => Prod.fst)
          let leaves := A.image other
          obtain ⟨B', bm', bc', bs', bf'⟩ := star N B side center leaves bm (hA.image other)
          have small : leaves.card ≤ A.card := Finset.card_image_le
          refine ⟨B', bm', le_trans bc' bc, by omega, ?_⟩
          intro X Y
          have active : (if side then center ∈ Y ∧ ∃ p ∈ leaves, p ∈ X else
                center ∈ X ∧ ∃ l ∈ leaves, l ∈ Y) ↔ ∃ e ∈ A, e.1 ∈ X ∧ e.2 ∈ Y := by
            cases a with
            | inl p =>
              change (p ∈ X ∧ ∃ l ∈ A.image Prod.snd, l ∈ Y) ↔ _
              constructor
              · rintro ⟨hp,l,hl,hy⟩
                obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
                have heq : e.1 = p := (Finset.mem_filter.mp he).2
                exact ⟨e, he, heq.symm ▸ hp, hy⟩
              · rintro ⟨e,he,hx,hy⟩
                have heq : e.1 = p := (Finset.mem_filter.mp he).2
                exact ⟨heq ▸ hx, e.2, Finset.mem_image_of_mem Prod.snd he, hy⟩
            | inr l =>
              change (l ∈ Y ∧ ∃ p ∈ A.image Prod.fst, p ∈ X) ↔ _
              constructor
              · rintro ⟨hl,p,hp,hx⟩
                obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
                have heq : e.2 = l := (Finset.mem_filter.mp he).2
                exact ⟨e,he,hx,heq.symm ▸ hl⟩
              · rintro ⟨e,he,hx,hy⟩
                have heq : e.2 = l := (Finset.mem_filter.mp he).2
                exact ⟨heq ▸ hy, e.1, Finset.mem_image_of_mem Prod.fst he, hx⟩
          rw [bf', Bool.or_eq_true, decide_eq_true_eq, active, bf]
          constructor
          · rintro ((old | ⟨e,he,hx,hy⟩) | ⟨e,he,hx,hy⟩)
            · exact Or.inl old
            · exact Or.inr ⟨e, (splitHit e).mpr (Or.inl he), hx, hy⟩
            · exact Or.inr ⟨e, (splitHit e).mpr (Or.inr he), hx, hy⟩
          · rintro (old | ⟨e,he,hx,hy⟩)
            · exact Or.inl (Or.inl old)
            · rcases (splitHit e).mp he with hr | hs
              · exact Or.inl (Or.inr ⟨e,hr,hx,hy⟩)
              · exact Or.inr ⟨e,hs,hx,hy⟩
        · have hR : R = U := by
            ext e
            rw [splitHit e]
            simp [Finset.not_nonempty_iff_eq_empty.mp hA]
          exact ⟨B, bm, bc, by omega, by simpa only [hR] using bf⟩
    have cover' (e) (he : e ∈ E) : ∃ a ∈ P.disjSum L, touches a e := by
      rcases hcover e he with h | h
      · exact ⟨Sum.inl e.1, Finset.inl_mem_disjSum.mpr h, rfl⟩
      · exact ⟨Sum.inr e.2, Finset.inr_mem_disjSum.mpr h, rfl⟩
    obtain ⟨B, bm, bc, bs, bf⟩ := grow (P.disjSum L) E cover'
    refine ⟨B, bm, ?_, bc, by rw [Finset.card_disjSum] at bs; omega⟩
    apply computes_of_sound_and_pairs bm
    · intro X Y hpos
      rcases (bf X Y).mp hpos with old | ⟨e,he,hx,hy⟩
      · exact sound _ _ old
      · have hinc : e.1 ∈ S e.2 := (Finset.mem_filter.mp he).2.1
        exact decide_eq_true ⟨e.1,hx,e.2,hy,hinc⟩
    · intro l p hp
      apply (bf {p} {l}).mpr
      cases h : D.eval (incidenceInput {p} {l}) with
      | true => exact Or.inl rfl
      | false =>
        have he : (p,l) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,h⟩
        exact Or.inr ⟨(p,l),he,by simp,by simp⟩
  intro q N S C hq hN hdegree hthin hmono hexact
  dsimp only
  intro hsize hcross
  obtain ⟨j, hj, hgate, ws, hlen, hsub, reject, P, L, hcover, hcost⟩ :=
    localBound q N S C hq hN hdegree hthin hmono hexact hsize hcross
  let D : Circuit := { C with gates := C.gates.set j ⟨GateOp.or, ws⟩ }
  have replaceGate (n : ℕ) (M : Finset (Fin n)) (C : Circuit) (j : ℕ)
      (ws : List ℕ) (hj : j < C.gates.length) (hc : IsCrossAnd n M C j)
      (hws : support n { C with gates := C.gates.set j ⟨GateOp.or, ws⟩ } (n+j) ⊆ support n C (n+j))
      (hlenWs : ws.length ≤ 2) (hmono : Monotone2 C) :
      Monotone2 ({ C with gates := C.gates.set j ⟨GateOp.or, ws⟩ }) ∧
      crossCount n M ({ C with gates := C.gates.set j ⟨GateOp.or, ws⟩ }) < crossCount n M C := by
    have stepEq (w : List (Finset (Fin n))) (g : Gate) : supportStep w g =
        w ++ [g.inputs.foldr (fun i acc => w.getD i ∅ ∪ acc) ∅] := rfl
    let z : Gate := ⟨GateOp.or, ws⟩
    let D : Circuit := { C with gates := C.gates.set j z }
    change Monotone2 D ∧ crossCount n M D < _
    constructor
    · intro g hg
      change g ∈ C.gates.set j z at hg
      rcases List.mem_or_eq_of_mem_set hg with hold | rfl
      · exact hmono g hold
      · exact ⟨by simp [z], hlenWs⟩
    let rel (u v : List (Finset (Fin n))) := u.length = v.length ∧ ∀ k, u.getD k ∅ ⊆ v.getD k ∅
    have stepRel (u v : List (Finset (Fin n))) (g h : Gate)
        (hUV : rel u v) (hGH : g.inputs ⊆ h.inputs) : rel (supportStep u g) (supportStep v h) := by
      obtain ⟨hlen, hsub⟩ := hUV
      let comb (w : List (Finset (Fin n))) (xs : List ℕ) := xs.foldr (fun i acc => w.getD i ∅ ∪ acc) ∅
      have memComb (w : List (Finset (Fin n))) (xs : List ℕ) (p : Fin n) :
          p ∈ comb w xs ↔ ∃ i ∈ xs, p ∈ w.getD i ∅ := by
        induction xs with
        | nil => simp [comb]
        | cons i xs ih =>
          change p ∈ w.getD i ∅ ∪ comb w xs ↔ _
          simp [ih]
      have outSub : comb u g.inputs ⊆ comb v h.inputs := by
        intro p hp
        obtain ⟨i, hi, hiP⟩ := (memComb _ _ _).mp hp
        exact (memComb _ _ _).mpr ⟨i, hGH hi, hsub i hiP⟩
      change (u ++ [comb u g.inputs]).length = (v ++ [comb v h.inputs]).length ∧ _
      constructor
      · simp [hlen]
      intro k
      change (u ++ [_]).getD k ∅ ⊆ (v ++ [_]).getD k ∅
      by_cases hk : k < u.length
      · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (by omega : k < v.length)]
        exact hsub k
      · rw [List.getD_append_right _ _ _ _ (by omega : u.length ≤ k),
            List.getD_append_right _ _ _ _ (by omega : v.length ≤ k), hlen]
        cases k - v.length with
        | zero => exact outSub
        | succ l => intro x hx; simp at hx
    have foldRel (xs ys : List Gate) (h : List.Forall₂ (fun g h : Gate => g.inputs ⊆ h.inputs) xs ys)
        (u v : List (Finset (Fin n))) (huv : rel u v) :
        rel (xs.foldl supportStep u) (ys.foldl supportStep v) := by
      induction h generalizing u v with
      | nil => exact huv
      | cons h _ ih => exact ih _ _ (stepRel _ _ _ _ huv h)
    have reflList (s : List Gate) : List.Forall₂ (fun g h : Gate => g.inputs ⊆ h.inputs) s s := by
      induction s with
      | nil => exact .nil
      | cons g gs ih => exact .cons (fun _ a => a) ih
    have suffixRead (xs : List Gate) (w : List (Finset (Fin n))) (k : ℕ) (hk : k < w.length) :
        (xs.foldl supportStep w).getD k ∅ = w.getD k ∅ := by
      induction xs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (gs.foldl supportStep (supportStep w g)).getD k ∅ = w.getD k ∅
        rw [ih (supportStep w g) (by simp [stepEq]; omega)]
        exact List.getD_append _ _ _ _ hk
    have edit (xs : List Gate) (i : ℕ) (w : List (Finset (Fin n)))
        (hb : i < xs.length)
        (hnew : ((xs.set i z).foldl supportStep w).getD (w.length+i) ∅ ⊆
          (xs.foldl supportStep w).getD (w.length+i) ∅) :
        rel ((xs.set i z).foldl supportStep w) (xs.foldl supportStep w) := by
      induction xs generalizing i w with
      | nil => simp at hb
      | cons g gs ih =>
        cases i with
        | zero =>
          change (gs.foldl supportStep (supportStep w z)).getD (w.length+0) ∅ ⊆
              (gs.foldl supportStep (supportStep w g)).getD (w.length+0) ∅ at hnew
          simp only [Nat.add_zero] at hnew
          rw [suffixRead gs _ _ (by simp [stepEq]), suffixRead gs _ _ (by simp [stepEq])] at hnew
          apply foldRel gs gs (reflList gs)
          refine ⟨by simp [stepEq], ?_⟩
          intro k
          by_cases h : k < w.length
          · change (w++[_]).getD k ∅ ⊆ (w++[_]).getD k ∅
            rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
          · by_cases he : k = w.length
            · exact he ▸ hnew
            · rw [List.getD_eq_default _ _ (by simp [stepEq]; omega : (supportStep w z).length ≤ k)]
              exact Finset.empty_subset _
        | succ i =>
          apply ih i (supportStep w g) (by simpa using hb)
          change ((gs.set i z).foldl supportStep (supportStep w g)).getD (w.length+(i+1)) ∅ ⊆
              (gs.foldl supportStep (supportStep w g)).getD (w.length+(i+1)) ∅ at hnew
          have he : (supportStep w g).length + i = w.length + (i+1) := by simp [stepEq]; omega
          rw [he]
          exact hnew
    have hsup (k : ℕ) : support n D k ⊆ support n C k := by
      let w := List.ofFn fun i : Fin n => ({i} : Finset (Fin n))
      have hw : w.length = n := by simp [w]
      exact (edit C.gates j w hj (by rw [hw]; exact hws)).2 k
    have hop (i k : ℕ) : operandSupport n D i k ⊆ operandSupport n C i k := by
      unfold operandSupport
      split
      · exact hsup _
      · exact Finset.Subset.refl _
    have same (i : ℕ) (hi : j ≠ i) : gateAt D i = gateAt C i := by
      unfold gateAt
      simp only [D, List.getD_eq_getElem?_getD, List.getElem?_set_ne hi]
    have changed : gateAt D j = z := by
      unfold gateAt
      simp only [D, List.getD_eq_getElem?_getD, List.getElem?_set_self hj, Option.getD_some]
    have keep (i : ℕ) (hi : IsCrossAnd n M D i) : IsCrossAnd n M C i := by
      by_cases he : j = i
      · subst i
        have bad := hi.1
        rw [changed] at bad
        cases bad
      · unfold IsCrossAnd at hi ⊢
        rw [same i he] at hi
        obtain ⟨hAnd, htwo, hparts⟩ := hi
        refine ⟨hAnd, htwo, ?_⟩
        rcases hparts with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨ha.mono (Finset.inter_subset_inter_right (hop _ _)),
                        hb.mono (Finset.inter_subset_inter_right (hop _ _))⟩
        · exact Or.inr ⟨ha.mono (Finset.sdiff_subset_sdiff_left M (hop _ _)),
                        hb.mono (Finset.sdiff_subset_sdiff_left M (hop _ _))⟩
    have dl : D.gates.length = C.gates.length := by simp [D]
    unfold crossCount
    rw [dl]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_of_subset ?_ |>.2 ?_
    · intro i hi
      obtain ⟨hr, h⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hr, keep _ h⟩
    · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hc⟩, ?_⟩
      intro h
      have bad := (Finset.mem_filter.mp h).2.1
      rw [changed] at bad
      cases bad
  obtain ⟨hdmono, hdc⟩ := replaceGate (N + N) (Finset.univ.map (Fin.natAddEmb N)) C j ws hj hgate hsub hlen hmono
  have extendFalse (N : ℕ) (S : Fin N → Finset (Fin N)) (X Y : Finset (Fin N))
      (hFalse : incidenceFun S X Y = false) :
      ∃ X' Y', X ⊆ X' ∧ Y ⊆ Y' ∧ IsMaximalFalse S X' Y' := by
    let X' := zeroSet (n := N) S Y
    let Y' := Finset.univ.filter fun l : Fin N => Disjoint (S l) X'
    have point (p : Fin N) : p ∈ X' ↔ ∀ l ∈ Y, p ∉ S l := by change _ ∈ Finset.univ.filter _ ↔ _; simp
    have line (l : Fin N) : l ∈ Y' ↔ Disjoint (S l) X' := by simp [Y']
    have avoids : ¬ ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l := by exact of_decide_eq_false hFalse
    have hX : X ⊆ X' := by
      intro p hp
      exact (point p).mpr fun l hl hpl => avoids ⟨p, hp, l, hl, hpl⟩
    have hY : Y ⊆ Y' := by
      intro l hl
      exact (line l).mpr (Finset.disjoint_left.mpr fun p hp h => (point p).mp h l hl hp)
    refine ⟨X', Y', hX, hY, (fun l hl => (line l).mp hl), ?_, ?_⟩
    · intro p hp h
      apply hp
      exact (point p).mpr fun l hl hpl =>
        Finset.disjoint_left.mp (h l (hY hl)) hpl (Finset.mem_insert_self p X')
    · intro l hl h
      exact hl ((line l).mpr (h l (Finset.mem_insert_self l Y')))
  have sound (X Y) (h : D.eval (incidenceInput X Y) = true) : incidenceFun S X Y = true := by
    cases bad : incidenceFun S X Y with
    | true => rfl
    | false =>
      obtain ⟨X', Y', hX, hY, maximal⟩ := extendFalse N S X Y bad
      have pos := incidence_eval_mono hdmono hX hY h
      exact Bool.noConfusion (pos.symm.trans (reject X' Y' maximal))
  obtain ⟨B, hbm, hbf, hbc, hbs⟩ := patch N S D P L hdmono sound hcover
  refine ⟨B, hbm, hbf, Nat.lt_of_le_of_lt hbc hdc, ?_⟩
  have hds : D.size = C.size := by change (C.gates.set j _).length = C.gates.length; simp
  change (Finset.univ.filter (fun e : Fin N × Fin N =>
    e.1 ∈ S e.2 ∧ D.eval (incidenceInput {e.1} {e.2}) = false)).card + P.card + L.card ≤ 49 at hcost
  omega
