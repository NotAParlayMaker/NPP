import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5306_217
    (rotation : ∀ (t : Fin 13) (C : Circuit),
    let shift (j : Fin 26) : Fin 26 :=
      Fin.addCases (fun p => Fin.castAdd 13 (p - t)) (fun l => Fin.natAdd 13 (l - t)) j
    let wire (i : ℕ) : ℕ := if h : i < 26 then (shift ⟨i, h⟩).val else i
    let D : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map wire⟩), wire C.output⟩
    D.lineDeg 26 (Finset.Ico 13 26) = C.lineDeg 26 (Finset.Ico 13 26) ∧
    D.lineDeg 26 (Finset.range 13) = C.lineDeg 26 (Finset.range 13) ∧
    ∀ x, circuitFun 26 D x = circuitFun 26 C (fun i => x (shift i)))
    (canonical : let x1 : Fin 13 → Fin 13 → Prop := fun p l => p ∈ PEqualNP.HeptadCover.singerLines3 l; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → (∃ j : Fin x2.gates.length,
      (0 ∈ (x2.gates.get j).inputs ∨ 13 ∈ (x2.gates.get j).inputs) ∧
      ∀ k : Fin x2.gates.length, k < j → ∀ w ∈ (x2.gates.get k).inputs, 26 ≤ w) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x10 : Fin (26 : ℕ) → Bool), (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) → (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x10 : Fin (26 : ℕ) → Bool), (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) → (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true := by

  classical

  let shift (t : Fin 13) (i : Fin 26) : Fin 26 :=
    Fin.addCases (fun p => Fin.castAdd 13 (p - t)) (fun l => Fin.natAdd 13 (l - t)) i

  have shift_left (t p : Fin 13) :
      shift t (Fin.castAdd 13 p) = Fin.castAdd 13 (p - t) := by
    simp [shift]

  have shift_right (t l : Fin 13) :
      shift t (Fin.natAdd 13 l) = Fin.natAdd 13 (l - t) := by
    unfold shift
    rw [Fin.addCases_right]

  have shift_inv (t : Fin 13) (i : Fin 26) : shift (-t) (shift t i) = i := by
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro p
      simp [shift_left, sub_eq_add_neg, add_assoc]
    · intro l
      rw [shift_right, shift_right]
      simp [sub_eq_add_neg, add_assoc]

  let wire (t : Fin 13) (j : ℕ) : ℕ :=
    if h : j < 26 then (shift t ⟨j,h⟩).val else j

  have wire_hi (t : Fin 13) {j : ℕ} (h : 26 ≤ j) : wire t j = j := by
    simp [wire, Nat.not_lt.mpr h]

  let moveGate (t : Fin 13) (g : Gate) : Gate := ⟨g.op, g.inputs.map (wire t)⟩

  let rotate (t : Fin 13) (C : Circuit) : Circuit :=
    ⟨C.gates.map (moveGate t), wire t C.output⟩

  have legal (t : Fin 13) (C : Circuit) (h : Monotone2 C) : Monotone2 (rotate t C) := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [moveGate] using h a ha

  have same_size (t : Fin 13) (C : Circuit) : (rotate t C).size = C.size := by
    simp [rotate, Circuit.size]

  have appendRead {α : Type} (w : List α) (v d : α) (i : ℕ) :
      (w ++ [v]).getD i d = if i = w.length then v else w.getD i d := by
    rcases lt_trichotomy i w.length with h | rfl | h
    · rw [ite_eq_right h.ne, List.getD_append _ _ _ _ h]
    · simp
    · rw [ite_eq_right (ne_of_gt h), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

  let emit {α : Type} (d : α) (op : GateOp → List α → α)
      (w : List α) (g : Gate) : List α :=
    w ++ [op g.op (g.inputs.map fun j => w.getD j d)]

  have eval_rotate (t : Fin 13) (C : Circuit) (x : Fin 26 → Bool) :
      circuitFun 26 (rotate t C) x = circuitFun 26 C (fun i => x (shift t i)) := by
    exact (rotation t C).2.2 x

  let inc (p l : Fin 13) : Prop :=
    p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

  have shifted (t p l : Fin 13) : inc (p + t) (l + t) ↔ inc p l := by
    have cancel (k : Fin 13) : p + t = l + t + k ↔ p = l + k := by
      rw [add_right_comm l t k, add_right_cancel_iff]
    simp only [inc, add_right_cancel_iff, cancel]

  have separate (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro eq
    have v := congrArg Fin.val eq
    have h := p.isLt
    simp only [Fin.val_castAdd, Fin.val_natAdd] at v
    omega

  let pair (p l : Fin 13) (x : Fin 26) : Bool :=
    decide (x = Fin.castAdd 13 p ∨ x = Fin.natAdd 13 l)

  have pair_shift (t p l : Fin 13) :
      (fun x => pair p l (shift t x)) = pair (p + t) (l + t) := by
    funext x
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ x
    · intro q
      rw [shift_left]
      simp only [pair, separate, or_false]
      congr 1
      apply propext
      rw [Fin.castAdd_inj, Fin.castAdd_inj, sub_eq_iff_eq_add]
    · intro q
      rw [shift_right]
      simp only [pair, Ne.symm (separate _ _), false_or]
      congr 1
      apply propext
      rw [Fin.natAdd_inj, Fin.natAdd_inj, sub_eq_iff_eq_add]

  let advance (t : Fin 13) (S : Finset (Fin 13)) : Finset (Fin 13) :=
    S.image (fun u => u + t)

  have filter_left (t l : Fin 13) (U : Finset (Fin 13)) :
      {p ∈ advance t U | inc p (l + t)}.card = {p ∈ U | inc p l}.card := by
    classical
    unfold advance
    rw [Finset.filter_image, Finset.card_image_of_injective _ (fun _ _ e => add_right_cancel e)]
    congr 1
    ext i
    simp only [Finset.mem_filter, shifted]

  have filter_right (t p : Fin 13) (V : Finset (Fin 13)) :
      {l ∈ advance t V | inc (p + t) l}.card = {l ∈ V | inc p l}.card := by
    classical
    unfold advance
    rw [Finset.filter_image, Finset.card_image_of_injective _ (fun _ _ e => add_right_cancel e)]
    congr 1
    ext i
    simp only [Finset.mem_filter, shifted]

  have back (t : Fin 13) (C : Circuit) (U V : Finset (Fin 13))
      (noEdge : ∀ p ∈ U, ∀ l ∈ V, ¬inc p l)
      (capP : ∀ l, {p ∈ U | inc p l}.card ≤ 2)
      (capL : ∀ p, {l ∈ V | inc p l}.card ≤ 2)
      (firing : ∀ x : Fin 26 → Bool, (∀ p ∈ U, x (Fin.castAdd 13 p) = true) →
        (∀ l ∈ V, x (Fin.natAdd 13 l) = true) → circuitFun 26 (rotate t C) x = true) :
      (∀ p ∈ advance t U, ∀ l ∈ advance t V, ¬ inc p l) ∧
      (∀ l, {p ∈ advance t U | inc p l}.card ≤ 2) ∧
      (∀ p, {l ∈ advance t V | inc p l}.card ≤ 2) ∧
      ∀ x : Fin 26 → Bool, (∀ p ∈ advance t U, x (Fin.castAdd 13 p) = true) →
        (∀ l ∈ advance t V, x (Fin.natAdd 13 l) = true) → circuitFun 26 C x = true := by
    classical
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp l hl h
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hl
      exact noEdge p' hp' l' hl' ((shifted t _ _).mp h)
    · intro l
      have eq : (l - t) + t = l := sub_add_cancel _ _
      rw [← eq]
      rw [filter_left]
      exact capP _
    · intro p
      have eq : (p - t) + t = p := sub_add_cancel _ _
      rw [← eq]
      rw [filter_right]
      exact capL _
    · intro x hx hy
      have f := firing (fun j => x (shift (-t) j)) ?_ ?_
      · rw [eval_rotate] at f
        simpa only [shift_inv] using f
      · intro p hp
        rw [shift_left, sub_neg_eq_add]
        exact hx _ (Finset.mem_image_of_mem _ hp)
      · intro l hl
        rw [shift_right, sub_neg_eq_add]
        exact hy _ (Finset.mem_image_of_mem _ hl)

  have keepRead {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
      (x : List α) {i : ℕ} (hi : i < x.length) :
      (gs.foldl (emit d op) x).getD i d = x.getD i d := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      let y := emit d op x g
      have lt : i < y.length := by simp [y,emit]; omega
      change (gs.foldl (emit d op) y).getD i d = x.getD i d
      rw [ih y lt]
      exact List.getD_append _ _ _ _ hi

  have input_value (C : Circuit) (x : Fin 26 → Bool) (h : C.output < 26) :
      circuitFun 26 C x = x ⟨C.output,h⟩ := by
    change (C.gates.foldl (emit false GateOp.eval) (List.ofFn x)).getD C.output false = _
    rw [keepRead _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_ofFn]

  have sameHigh (gs : List Gate) (noRaw : ∀ g ∈ gs, ∀ i ∈ g.inputs, 26 ≤ i)
      (x y : List Bool) (hy : x.length = y.length)
      (same : ∀ i ≥ 26, x.getD i false = y.getD i false) :
      ∀ i ≥ 26,
        (gs.foldl (emit false GateOp.eval) x).getD i false =
          (gs.foldl (emit false GateOp.eval) y).getD i false := by
    induction gs generalizing x y with
    | nil => exact same
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have value : g.inputs.map (fun i => x.getD i false) =
          g.inputs.map (fun i => y.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact same i (noRaw g (by simp) i hi)
      apply ih (fun g hg => noRaw g (by simp [hg])) _ _ (by simp [emit,hy])
      intro i hi
      simp only [emit,appendRead,hy,value,same i hi]

  have noReader (C : Circuit)
      (none : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, 26 ≤ i)
      (yes : ∀ p l, inc p l → circuitFun 26 C (pair p l) = true) :
      ∀ x : Fin 26 → Bool, circuitFun 26 C x = true := by
    intro x
    have h0 := yes 0 0 (Or.inl rfl)
    by_cases low : C.output < 26
    · have h1 := yes 1 1 (Or.inl rfl)
      rw [input_value _ _ low] at h0 h1
      change decide ((⟨C.output,low⟩ : Fin 26) = Fin.castAdd 13 (0 : Fin 13) ∨
        (⟨C.output,low⟩ : Fin 26) = Fin.natAdd 13 (0 : Fin 13)) = true at h0
      change decide ((⟨C.output,low⟩ : Fin 26) = Fin.castAdd 13 (1 : Fin 13) ∨
        (⟨C.output,low⟩ : Fin 26) = Fin.natAdd 13 (1 : Fin 13)) = true at h1
      rcases of_decide_eq_true h0 with u | u <;>
          rcases of_decide_eq_true h1 with v | v <;>
          have a := congrArg Fin.val u <;> have b := congrArg Fin.val v <;>
          norm_num [Fin.val_castAdd, Fin.val_natAdd] at a b <;> omega
    · have agree : ∀ j ≥ 26,
          (List.ofFn x).getD j false = (List.ofFn (pair 0 0)).getD j false := by
        intro i hi
        rw [List.getD_eq_default _ _ (by simpa using hi),
          List.getD_eq_default _ _ (by simpa using hi)]
      have h := sameHigh C.gates none (List.ofFn x) (List.ofFn (pair 0 0))
        (by simp) agree C.output (Nat.le_of_not_gt low)
      exact h.trans h0

  have wire_left (t p : Fin 13) : wire t p.val = (p-t).val := by
    unfold wire
    have hp : p.val < 26 := by have := p.isLt; omega
    rw [dite_eq_left hp]
    change (shift t (Fin.castAdd 13 p)).val = _
    rw [shift_left]
    rfl

  have wire_right (t l : Fin 13) : wire t (13 + l.val) = 13 + (l-t).val := by
    unfold wire
    have hp : 13 + l.val < 26 := by have := l.isLt; omega
    rw [dite_eq_left hp]
    change (shift t (Fin.natAdd 13 l)).val = _
    rw [shift_right]
    rfl

  let anchor (C : Circuit) : Prop :=
    ∃ j : Fin C.gates.length,
      (0 ∈ (C.gates[j.val]'j.isLt).inputs ∨ 13 ∈ (C.gates[j.val]'j.isLt).inputs) ∧
      ∀ k : Fin C.gates.length, k.val < j.val →
        ∀ a ∈ (C.gates[k.val]'k.isLt).inputs, 26 ≤ a

  let passes (C : Circuit) : Prop :=
    ∀ p l : Fin 13, inc p l → circuitFun 26 C (pair p l) = true

  let leaks (C : Circuit) : Prop :=
    ∃ U V : Finset (Fin 13), (∀ p ∈ U, ∀ l ∈ V, ¬inc p l) ∧
      (∀ l, {p ∈ U | inc p l}.card ≤ 2) ∧
      (∀ p, {l ∈ V | inc p l}.card ≤ 2) ∧
      ∀ x : Fin 26 → Bool, (∀ p ∈ U, x (Fin.castAdd 13 p) = true) →
        (∀ l ∈ V, x (Fin.natAdd 13 l) = true) → circuitFun 26 C x = true

  have combine
      (law : ∀ (t : Fin 13) (C : Circuit),
        (rotate t C).lineDeg 26 (Finset.Ico 13 26) = C.lineDeg 26 (Finset.Ico 13 26) ∧
        (rotate t C).lineDeg 26 (Finset.range 13) = C.lineDeg 26 (Finset.range 13) ∧
        ∀ x, circuitFun 26 (rotate t C) x = circuitFun 26 C (fun i => x (shift t i)))
      (normalized : ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 →
        ¬ HasLineDegree 26 (Finset.range 13) C 1 →
        passes C → anchor C → leaks C)
      (C : Circuit) (hM : Monotone2 C) (hs : C.size ≤ 63)
      (hR : ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1)
      (hL : ¬ HasLineDegree 26 (Finset.range 13) C 1)
      (pos : passes C) : leaks C := by
    classical
    let use (j : ℕ) : Prop :=
      ∃ hj : j < C.gates.length, ∃ a ∈ (C.gates[j]'hj).inputs, a < 26
    by_cases existsUse : ∃ j, use j
    · let j := Nat.find existsUse
      obtain ⟨hj,a,ha,haBound⟩ := Nat.find_spec existsUse
      let first : Fin C.gates.length := ⟨j,hj⟩
      have earlier (k : Fin C.gates.length) (before : k.val < j)
          (v : ℕ) (hv : v ∈ (C.gates[k.val]'k.isLt).inputs) : 26 ≤ v := by
        by_contra h
        exact Nat.find_min existsUse before ⟨k.isLt,v,hv,by omega⟩
      have useShift (t : Fin 13) (mark : wire t a = 0 ∨ wire t a = 13) : leaks C := by
        let D := rotate t C
        let newFirst : Fin D.gates.length :=
          ⟨first.val, by simpa only [D, rotate, List.length_map] using first.isLt⟩
        have hAnch : anchor D := by
          refine ⟨newFirst, ?_, ?_⟩
          · change 0 ∈ (C.gates.map (moveGate t))[first.val].inputs ∨
              13 ∈ (C.gates.map (moveGate t))[first.val].inputs
            rw [List.getElem_map]
            have m : wire t a ∈ (moveGate t (C.gates[first.val]'first.isLt)).inputs :=
              List.mem_map.mpr ⟨a,ha,rfl⟩
            rcases mark with q | q
            · exact Or.inl (q ▸ m)
            · exact Or.inr (q ▸ m)
          · intro k earlierD v hv
            have hk : k.val < C.gates.length := by
              simpa only [D,rotate,List.length_map] using k.isLt
            change v ∈ (C.gates.map (moveGate t))[k.val].inputs at hv
            rw [List.getElem_map] at hv
            obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
            have ge := earlier ⟨k.val,hk⟩ earlierD w hw
            rwa [wire_hi t ge]
        obtain ⟨dR,dL,eval⟩ := law t C
        have passed : passes D := by
          intro p l e
          rw [eval, pair_shift]
          exact pos _ _ ((shifted t p l).mpr e)
        have dsize : D.size ≤ 63 := by
          rwa [same_size]
        have dRight : ¬HasLineDegree 26 (Finset.Ico 13 26) D 1 := by
          unfold HasLineDegree at hR ⊢
          rwa [dR]
        have dLeft : ¬HasLineDegree 26 (Finset.range 13) D 1 := by
          unfold HasLineDegree at hL ⊢
          rwa [dL]
        obtain ⟨P,L,hI,hp,hl,hf⟩ := normalized D (legal t C hM) dsize dRight dLeft passed hAnch
        exact ⟨advance t P, advance t L, back t C P L hI hp hl hf⟩
      by_cases isPoint : a < 13
      · let t : Fin 13 := ⟨a,isPoint⟩
        apply useShift t
        left
        change wire t t.val = 0
        rw [wire_left, sub_self]
        rfl
      · let t : Fin 13 := ⟨a-13,by omega⟩
        apply useShift t
        right
        have aEq : 13 + t.val = a := by dsimp [t]; omega
        rw [← aEq, wire_right, sub_self]
        rfl
    · have none : ∀ g ∈ C.gates, ∀ a ∈ g.inputs, 26 ≤ a := by
        intro g hg a ha
        by_contra h
        obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
        exact existsUse ⟨i,hi,a,ha,by omega⟩
      exact ⟨∅,∅,by simp,by simp,by simp,fun x _ _ => noReader C none pos x⟩

  have incidenceBridge : ∀ p l : Fin 13, inc p l ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l := by
    decide +kernel
  have canonicalInc : ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
      ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 →
      ¬ HasLineDegree 26 (Finset.range 13) C 1 →
      passes C → anchor C → leaks C := by
    intro C mono small lines points yes first
    obtain ⟨U,V,no,capU,capV,fire⟩ := canonical C mono small lines points
      (fun p l h => yes _ _ ((incidenceBridge p l).mpr h)) first
    refine ⟨U,V,?_,?_,?_,fire⟩
    · intro p hp l hl h
      exact no p hp l hl ((incidenceBridge p l).mp h)
    · intro l
      have eq : U.filter (fun p => inc p l) =
          U.filter (fun p => p ∈ PEqualNP.HeptadCover.singerLines3 l) := by
        ext p
        simp only [Finset.mem_filter, incidenceBridge]
      rw [eq]
      exact capU l
    · intro p
      have eq : V.filter (fun l => inc p l) =
          V.filter (fun l => p ∈ PEqualNP.HeptadCover.singerLines3 l) := by
        ext l
        simp only [Finset.mem_filter, incidenceBridge]
      rw [eq]
      exact capV p
  exact combine rotation canonicalInc
