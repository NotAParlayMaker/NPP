import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5300

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (k : Gate) : List Bool :=
  w ++ [k.op.eval (k.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

def inp (d b z : Bool) : List Bool :=
  [b, d, false, !d, z, false, false, false, false, !b]

lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons k gs ih =>
    change (run gs (step w k)).length = w.length + (gs.length + 1)
    rw [ih]
    simp [step]
    omega

lemma run_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons k gs ih =>
    change (run gs (step w k)).getD i false = w.getD i false
    have hi' : i < (step w k).length := by simp [step]; omega
    rw [ih (step w k) hi']
    exact List.getD_append w [k.op.eval (k.inputs.map fun j => w.getD j false)] false i hi

lemma step_append_agree (w₁ w₂ : List Bool) (v₁ v₂ : Bool)
    (hlen : w₁.length = w₂.length) (hv : v₁ = v₂)
    (hag : ∀ i, i ≠ 0 → i ≠ 4 → i ≠ 9 → w₁.getD i false = w₂.getD i false) :
    (w₁ ++ [v₁]).length = (w₂ ++ [v₂]).length ∧
      ∀ i, i ≠ 0 → i ≠ 4 → i ≠ 9 → (w₁ ++ [v₁]).getD i false = (w₂ ++ [v₂]).getD i false := by
  refine ⟨by simp [hlen], fun i h0 h4 h9 => ?_⟩
  by_cases hi : i < w₁.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hlen ▸ hi)]
    exact hag i h0 h4 h9
  · by_cases he : i = w₁.length
    · subst he
      rw [List.getD_append_right _ _ _ _ (le_refl _),
        List.getD_append_right _ _ _ _ (by omega)]
      simp [hlen, hv]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma step_agree (w₁ w₂ : List Bool) (k : Gate)
    (hlen : w₁.length = w₂.length)
    (hag : ∀ i, i ≠ 0 → i ≠ 4 → i ≠ 9 → w₁.getD i false = w₂.getD i false)
    (hk : 0 ∉ k.inputs ∧ 4 ∉ k.inputs ∧ 9 ∉ k.inputs) :
    (step w₁ k).length = (step w₂ k).length ∧
      ∀ i, i ≠ 0 → i ≠ 4 → i ≠ 9 → (step w₁ k).getD i false = (step w₂ k).getD i false := by
  have hmaps : (k.inputs.map fun j => w₁.getD j false) = (k.inputs.map fun j => w₂.getD j false) := by
    apply List.map_congr_left
    intro j hj
    exact hag j (fun h => hk.1 (h ▸ hj)) (fun h => hk.2.1 (h ▸ hj)) (fun h => hk.2.2 (h ▸ hj))
  exact step_append_agree w₁ w₂ _ _ hlen (congrArg k.op.eval hmaps) hag

lemma run_agree (gs : List Gate) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length)
    (hag : ∀ i, i ≠ 0 → i ≠ 4 → i ≠ 9 → w₁.getD i false = w₂.getD i false)
    (hgs : ∀ k ∈ gs, 0 ∉ k.inputs ∧ 4 ∉ k.inputs ∧ 9 ∉ k.inputs) :
    (run gs w₁).length = (run gs w₂).length ∧
      ∀ i, i ≠ 0 → i ≠ 4 → i ≠ 9 → (run gs w₁).getD i false = (run gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hag⟩
  | cons k gs ih =>
    have hstep := step_agree w₁ w₂ k hlen hag (hgs k (List.Mem.head gs))
    exact ih (step w₁ k) (step w₂ k) hstep.1 hstep.2 (fun q hq => hgs q (List.Mem.tail k hq))

lemma inp_agree (d b₁ z₁ b₂ z₂ : Bool) (i : ℕ) (h0 : i ≠ 0) (h4 : i ≠ 4) (h9 : i ≠ 9) :
    (inp d b₁ z₁).getD i false = (inp d b₂ z₂).getD i false := by
  match i with
  | 0 => exact False.elim (h0 rfl)
  | 1 | 2 | 3 | 5 | 6 | 7 | 8 => rfl
  | 4 => exact False.elim (h4 rfl)
  | 9 => exact False.elim (h9 rfl)
  | _ + 10 => rfl

def evalModel (op : Fin 3) (s has2 : Bool) (kb : Fin 4) (ext b z : Bool) : Bool :=
  let a := if s then !b else b
  if op = 2 then !a
  else if !has2 then a
  else
    let y := match kb.val with
      | 0 => b
      | 1 => !b
      | 2 => z
      | _ => ext
    if op = 0 then a && y else a || y

lemma gate_model (k : Gate)
    (hfan : k.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ k.inputs.length ≤ 2)
    (hnot : k.op = GateOp.not → k.inputs.length ≤ 1)
    (hctl : (0 : ℕ) ∈ k.inputs ∨ (9 : ℕ) ∈ k.inputs) :
    ∃ (op : Fin 3) (s has2 : Bool) (kb : Fin 4) (extIdx : ℕ),
      (kb = 3 → extIdx ≠ 0 ∧ extIdx ≠ 4 ∧ extIdx ≠ 9) ∧
      ∀ (w : List Bool) (b z : Bool),
        w.getD 0 false = b → w.getD 4 false = z → w.getD 9 false = !b →
        k.op.eval (k.inputs.map fun i => w.getD i false) =
          evalModel op s has2 kb (w.getD extIdx false) b z := by
  obtain ⟨hop, hlen⟩ := hfan
  cases hin : k.inputs with
  | nil =>
    rw [hin] at hctl
    rcases hctl with h0 | h9
    · cases h0
    · cases h9
  | cons i t =>
    cases t with
    | nil =>
      rw [hin] at hctl
      have hi : i = 0 ∨ i = 9 := by
        rcases hctl with h0 | h9
        · exact Or.inl (List.mem_singleton.mp h0).symm
        · exact Or.inr (List.mem_singleton.mp h9).symm
      rcases hop with hand | hor | hnotop
      · refine ⟨0, decide (i = 9), false, 0, 1, by simp, fun w b z hw0 _ hw9 => ?_⟩
        rw [hand]
        rcases hi with rfl | rfl <;> simp only [List.map_cons, List.map_nil, GateOp.eval,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, evalModel, beq_self_eq_true,
          decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.not_true]
        · exact hw0
        · exact hw9
      · refine ⟨1, decide (i = 9), false, 0, 1, by simp, fun w b z hw0 _ hw9 => ?_⟩
        rw [hor]
        rcases hi with rfl | rfl <;> simp only [List.map_cons, List.map_nil, GateOp.eval,
          List.any_cons, List.any_nil, id_eq, Bool.or_false, evalModel, beq_self_eq_true,
          decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.not_true]
        · exact hw0
        · exact hw9
      · refine ⟨2, decide (i = 9), false, 0, 1, by simp, fun w b z hw0 _ hw9 => ?_⟩
        have hnop : k.op = GateOp.not := hnotop
        rw [hnop]
        rcases hi with rfl | rfl <;> simp only [List.map_cons, List.map_nil, GateOp.eval,
          List.headD_cons, evalModel, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
        · exact congrArg Bool.not hw0
        · exact congrArg Bool.not hw9
    | cons j t2 =>
      cases t2 with
      | nil =>
        have hnot_op : k.op = GateOp.and ∨ k.op = GateOp.or := by
          rcases hop with hand | hor | hnotop
          · exact Or.inl hand
          · exact Or.inr hor
          · have hl := hnot hnotop
            rw [hin] at hl
            simp at hl
        rw [hin] at hctl
        have hctl_eq : (i = 0 ∨ i = 9) ∨ (j = 0 ∨ j = 9) := by
          rcases hctl with h0 | h9
          · rcases List.mem_cons.mp h0 with rfl | hm
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr (Or.inl (List.mem_singleton.mp hm).symm)
          · rcases List.mem_cons.mp h9 with rfl | hm
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr (Or.inr (List.mem_singleton.mp hm).symm)
        rcases hctl_eq with (rfl | rfl) | (rfl | rfl)
        · by_cases hj0 : j = 0
          · subst hj0
            rcases hnot_op with hop' | hop'
            · refine ⟨0, false, true, 0, 1, by decide, fun w b z hw0 _ _ => ?_⟩
              rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0]; rfl
            · refine ⟨1, false, true, 0, 1, by decide, fun w b z hw0 _ _ => ?_⟩
              rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0]; rfl
          · by_cases hj9 : j = 9
            · subst hj9
              rcases hnot_op with hop' | hop'
              · refine ⟨0, false, true, 1, 1, by decide, fun w b z hw0 _ hw9 => ?_⟩
                rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hw9]; rfl
              · refine ⟨1, false, true, 1, 1, by decide, fun w b z hw0 _ hw9 => ?_⟩
                rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, hw9]; rfl
            · by_cases hj4 : j = 4
              · subst hj4
                rcases hnot_op with hop' | hop'
                · refine ⟨0, false, true, 2, 1, by decide, fun w b z hw0 hw4 _ => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hw4]; rfl
                · refine ⟨1, false, true, 2, 1, by decide, fun w b z hw0 hw4 _ => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, hw4]; rfl
              · rcases hnot_op with hop' | hop'
                · refine ⟨0, false, true, 3, j, fun _ => ⟨hj0, hj4, hj9⟩, fun w b z hw0 _ _ => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0]; rfl
                · refine ⟨1, false, true, 3, j, fun _ => ⟨hj0, hj4, hj9⟩, fun w b z hw0 _ _ => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0]; rfl
        · by_cases hj0 : j = 0
          · subst hj0
            rcases hnot_op with hop' | hop'
            · refine ⟨0, true, true, 0, 1, by decide, fun w b z hw0 _ hw9 => ?_⟩
              rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hw9]; rfl
            · refine ⟨1, true, true, 0, 1, by decide, fun w b z hw0 _ hw9 => ?_⟩
              rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, hw9]; rfl
          · by_cases hj9 : j = 9
            · subst hj9
              rcases hnot_op with hop' | hop'
              · refine ⟨0, true, true, 1, 1, by decide, fun w b z _ _ hw9 => ?_⟩
                rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw9]; rfl
              · refine ⟨1, true, true, 1, 1, by decide, fun w b z _ _ hw9 => ?_⟩
                rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw9]; rfl
            · by_cases hj4 : j = 4
              · subst hj4
                rcases hnot_op with hop' | hop'
                · refine ⟨0, true, true, 2, 1, by decide, fun w b z _ hw4 hw9 => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw4, hw9]; rfl
                · refine ⟨1, true, true, 2, 1, by decide, fun w b z _ hw4 hw9 => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw4, hw9]; rfl
              · rcases hnot_op with hop' | hop'
                · refine ⟨0, true, true, 3, j, fun _ => ⟨hj0, hj4, hj9⟩, fun w b z _ _ hw9 => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw9]; rfl
                · refine ⟨1, true, true, 3, j, fun _ => ⟨hj0, hj4, hj9⟩, fun w b z _ _ hw9 => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw9]; rfl
        · by_cases hi0 : i = 0
          · subst hi0
            rcases hnot_op with hop' | hop'
            · refine ⟨0, false, true, 0, 1, by decide, fun w b z hw0 _ _ => ?_⟩
              rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0]; rfl
            · refine ⟨1, false, true, 0, 1, by decide, fun w b z hw0 _ _ => ?_⟩
              rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0]; rfl
          · by_cases hi9 : i = 9
            · subst hi9
              rcases hnot_op with hop' | hop'
              · refine ⟨0, false, true, 1, 1, by decide, fun w b z hw0 _ hw9 => ?_⟩
                rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hw9, Bool.and_comm]; rfl
              · refine ⟨1, false, true, 1, 1, by decide, fun w b z hw0 _ hw9 => ?_⟩
                rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, hw9, Bool.or_comm]; rfl
            · by_cases hi4 : i = 4
              · subst hi4
                rcases hnot_op with hop' | hop'
                · refine ⟨0, false, true, 2, 1, by decide, fun w b z hw0 hw4 _ => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hw4, Bool.and_comm]; rfl
                · refine ⟨1, false, true, 2, 1, by decide, fun w b z hw0 hw4 _ => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, hw4, Bool.or_comm]; rfl
              · rcases hnot_op with hop' | hop'
                · refine ⟨0, false, true, 3, i, fun _ => ⟨hi0, hi4, hi9⟩, fun w b z hw0 _ _ => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, Bool.and_comm]; rfl
                · refine ⟨1, false, true, 3, i, fun _ => ⟨hi0, hi4, hi9⟩, fun w b z hw0 _ _ => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, Bool.or_comm]; rfl
        · by_cases hi0 : i = 0
          · subst hi0
            rcases hnot_op with hop' | hop'
            · refine ⟨0, true, true, 0, 1, by decide, fun w b z hw0 _ hw9 => ?_⟩
              rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hw9, evalModel]; cases b <;> rfl
            · refine ⟨1, true, true, 0, 1, by decide, fun w b z hw0 _ hw9 => ?_⟩
              rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw0, hw9, evalModel]; cases b <;> rfl
          · by_cases hi9 : i = 9
            · subst hi9
              rcases hnot_op with hop' | hop'
              · refine ⟨0, true, true, 1, 1, by decide, fun w b z _ _ hw9 => ?_⟩
                rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw9]; rfl
              · refine ⟨1, true, true, 1, 1, by decide, fun w b z _ _ hw9 => ?_⟩
                rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw9]; rfl
            · by_cases hi4 : i = 4
              · subst hi4
                rcases hnot_op with hop' | hop'
                · refine ⟨0, true, true, 2, 1, by decide, fun w b z _ hw4 hw9 => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw4, hw9, evalModel]; cases b <;> cases z <;> rfl
                · refine ⟨1, true, true, 2, 1, by decide, fun w b z _ hw4 hw9 => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw4, hw9, evalModel]; cases b <;> cases z <;> rfl
              · rcases hnot_op with hop' | hop'
                · refine ⟨0, true, true, 3, i, fun _ => ⟨hi0, hi4, hi9⟩, fun w b z _ _ hw9 => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw9, Bool.and_comm]; rfl
                · refine ⟨1, true, true, 3, i, fun _ => ⟨hi0, hi4, hi9⟩, fun w b z _ _ hw9 => ?_⟩
                  rw [hop']; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw9, Bool.or_comm]; rfl
      | cons c t3 =>
        rw [hin] at hlen
        simp at hlen

def sepB (op4 : Fin 3) (s4 h24 : Bool) (k4 : Fin 4) (c : Bool)
    (op5 : Fin 3) (s5 h25 : Bool) (k5 : Fin 4) (u0 u1 : Bool) : Bool :=
  ([false, true]).all fun b1 =>
  ([false, true]).all fun z1 =>
  ([false, true]).all fun b2 =>
  ([false, true]).all fun z2 =>
    let v4_1 := evalModel op4 s4 h24 k4 c b1 z1
    let v4_2 := evalModel op4 s4 h24 k4 c b2 z2
    let v5_1 := evalModel op5 s5 h25 k5 (if v4_1 then u1 else u0) b1 z1
    let v5_2 := evalModel op5 s5 h25 k5 (if v4_2 then u1 else u0) b2 z2
    !(v4_1 == v4_2 && v5_1 == v5_2) || (b1 == b2)

def sepZ (op4 : Fin 3) (s4 h24 : Bool) (k4 : Fin 4) (c : Bool)
    (op5 : Fin 3) (s5 h25 : Bool) (k5 : Fin 4) (u0 u1 : Bool) : Bool :=
  ([false, true]).all fun b1 =>
  ([false, true]).all fun z1 =>
  ([false, true]).all fun b2 =>
  ([false, true]).all fun z2 =>
    let v4_1 := evalModel op4 s4 h24 k4 c b1 z1
    let v4_2 := evalModel op4 s4 h24 k4 c b2 z2
    let v5_1 := evalModel op5 s5 h25 k5 (if v4_1 then u1 else u0) b1 z1
    let v5_2 := evalModel op5 s5 h25 k5 (if v4_2 then u1 else u0) b2 z2
    !(v4_1 == v4_2 && v5_1 == v5_2) || (z1 == z2)

def okModel : Bool :=
  ([(0 : Fin 3), 1, 2]).all fun op4 =>
  ([false, true]).all fun s4 =>
  ([false, true]).all fun h24 =>
  ([(0 : Fin 4), 1, 2, 3]).all fun k4 =>
  ([(0 : Fin 3), 1, 2]).all fun op5 =>
  ([false, true]).all fun s5 =>
  ([false, true]).all fun h25 =>
  ([(0 : Fin 4), 1, 2, 3]).all fun k5 =>
  (!(([false, true]).any fun cT => ([false, true]).any fun u0T => ([false, true]).any fun u1T =>
      sepB op4 s4 h24 k4 cT op5 s5 h25 k5 u0T u1T) ||
   !(([false, true]).any fun cF => ([false, true]).any fun u0F => ([false, true]).any fun u1F =>
      sepZ op4 s4 h24 k4 cF op5 s5 h25 k5 u0F u1F))

private theorem okModel_true : okModel = true := by decide +kernel

lemma not_both_sep
    (op4 : Fin 3) (s4 h24 : Bool) (k4 : Fin 4)
    (op5 : Fin 3) (s5 h25 : Bool) (k5 : Fin 4)
    (cT u0T u1T cF u0F u1F : Bool)
    (hB : sepB op4 s4 h24 k4 cT op5 s5 h25 k5 u0T u1T = true)
    (hZ : sepZ op4 s4 h24 k4 cF op5 s5 h25 k5 u0F u1F = true) : False := by
  have h1 := List.all_eq_true.mp okModel_true op4 (by fin_cases op4 <;> decide)
  have h2 := List.all_eq_true.mp h1 s4 (by cases s4 <;> decide)
  have h3 := List.all_eq_true.mp h2 h24 (by cases h24 <;> decide)
  have h4 := List.all_eq_true.mp h3 k4 (by fin_cases k4 <;> decide)
  have h5 := List.all_eq_true.mp h4 op5 (by fin_cases op5 <;> decide)
  have h6 := List.all_eq_true.mp h5 s5 (by cases s5 <;> decide)
  have h7 := List.all_eq_true.mp h6 h25 (by cases h25 <;> decide)
  have h8 := List.all_eq_true.mp h7 k5 (by fin_cases k5 <;> decide)
  have anyB : (([false, true]).any fun c => ([false, true]).any fun u0 => ([false, true]).any fun u1 =>
      sepB op4 s4 h24 k4 c op5 s5 h25 k5 u0 u1) = true :=
    List.any_eq_true.mpr ⟨cT, by cases cT <;> decide,
      List.any_eq_true.mpr ⟨u0T, by cases u0T <;> decide,
        List.any_eq_true.mpr ⟨u1T, by cases u1T <;> decide, hB⟩⟩⟩
  have anyZ : (([false, true]).any fun c => ([false, true]).any fun u0 => ([false, true]).any fun u1 =>
      sepZ op4 s4 h24 k4 c op5 s5 h25 k5 u0 u1) = true :=
    List.any_eq_true.mpr ⟨cF, by cases cF <;> decide,
      List.any_eq_true.mpr ⟨u0F, by cases u0F <;> decide,
        List.any_eq_true.mpr ⟨u1F, by cases u1F <;> decide, hZ⟩⟩⟩
  rw [anyB, anyZ] at h8
  cases h8

theorem main5300 (x1 x2 x3 : List Gate) (x4 x5 : Gate) (x6 : ℕ)
    (hfan : FanInTwo { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 })
    (hnot : ∀ x9 ∈ ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).gates,
      x9.op = GateOp.not → x9.inputs.length ≤ 1)
    (havoid : ∀ x10 ∈ x1 ++ x2 ++ x3, 0 ∉ x10.inputs ∧ 9 ∉ x10.inputs)
    (hctrl : ∀ x11 ∈ [x4, x5], 0 ∈ x11.inputs ∨ 9 ∈ x11.inputs)
    (hmux : ∀ (x12 x13 x14 : Bool),
      ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).eval
        [x13, x12, false, !x12, x14, false, false, false, false, !x13] =
      if x12 = true then x13 else x14) :
    ∃ x13 ∈ x1 ++ x2 ++ x3, 4 ∈ x13.inputs := by
  by_contra hno4
  push Not at hno4
  have hclean : ∀ k ∈ x1 ++ x2 ++ x3, 0 ∉ k.inputs ∧ 4 ∉ k.inputs ∧ 9 ∉ k.inputs := fun k hk =>
    ⟨(havoid k hk).1, hno4 k hk, (havoid k hk).2⟩
  have ha_clean : ∀ k ∈ x1, 0 ∉ k.inputs ∧ 4 ∉ k.inputs ∧ 9 ∉ k.inputs := fun k hk =>
    hclean k (List.mem_append_left _ (List.mem_append_left _ hk))
  have hm_clean : ∀ k ∈ x2, 0 ∉ k.inputs ∧ 4 ∉ k.inputs ∧ 9 ∉ k.inputs := fun k hk =>
    hclean k (List.mem_append_left _ (List.mem_append_right _ hk))
  have ht_clean : ∀ k ∈ x3, 0 ∉ k.inputs ∧ 4 ∉ k.inputs ∧ 9 ∉ k.inputs := fun k hk =>
    hclean k (List.mem_append_right _ hk)
  have ho0 : x6 ≠ 0 := by
    intro he
    have hv := hmux false true false
    change (run (x1 ++ x4 :: (x2 ++ x5 :: x3)) (inp false true false)).getD x6 false = false at hv
    rw [he, run_getD_lt _ _ 0 (by simp [inp])] at hv
    simp [inp] at hv
  have ho4 : x6 ≠ 4 := by
    intro he
    have hv := hmux true true false
    change (run (x1 ++ x4 :: (x2 ++ x5 :: x3)) (inp true true false)).getD x6 false = true at hv
    rw [he, run_getD_lt _ _ 4 (by simp [inp])] at hv
    simp [inp] at hv
  have ho9 : x6 ≠ 9 := by
    intro he
    have hv := hmux true true false
    change (run (x1 ++ x4 :: (x2 ++ x5 :: x3)) (inp true true false)).getD x6 false = true at hv
    rw [he, run_getD_lt _ _ 9 (by simp [inp])] at hv
    simp [inp] at hv
  let wA (d b z : Bool) : List Bool := run x1 (inp d b z)
  let vg (d b z : Bool) : Bool := x4.op.eval (x4.inputs.map fun i => (wA d b z).getD i false)
  let wM (d b z : Bool) : List Bool := run x2 (step (wA d b z) x4)
  let vh (d b z : Bool) : Bool := x5.op.eval (x5.inputs.map fun i => (wM d b z).getD i false)
  have hwA_ag (d b₁ z₁ b₂ z₂ : Bool) :
      (wA d b₁ z₁).length = (wA d b₂ z₂).length ∧
      ∀ i, i ≠ 0 → i ≠ 4 → i ≠ 9 → (wA d b₁ z₁).getD i false = (wA d b₂ z₂).getD i false :=
    run_agree x1 (inp d b₁ z₁) (inp d b₂ z₂) rfl (inp_agree d b₁ z₁ b₂ z₂) ha_clean
  have hwA_pin (d b z : Bool) :
      (wA d b z).getD 0 false = b ∧ (wA d b z).getD 4 false = z ∧ (wA d b z).getD 9 false = !b := by
    refine ⟨?_, ?_, ?_⟩
    · rw [run_getD_lt _ _ 0 (by simp [inp])]; rfl
    · rw [run_getD_lt _ _ 4 (by simp [inp])]; rfl
    · rw [run_getD_lt _ _ 9 (by simp [inp])]; rfl
  have hwM_ag (d b₁ z₁ b₂ z₂ : Bool) (hvg : vg d b₁ z₁ = vg d b₂ z₂) :
      (wM d b₁ z₁).length = (wM d b₂ z₂).length ∧
      ∀ i, i ≠ 0 → i ≠ 4 → i ≠ 9 → (wM d b₁ z₁).getD i false = (wM d b₂ z₂).getD i false := by
    have hA := hwA_ag d b₁ z₁ b₂ z₂
    have hst := step_append_agree (wA d b₁ z₁) (wA d b₂ z₂) (vg d b₁ z₁) (vg d b₂ z₂) hA.1 hvg hA.2
    exact run_agree x2 (step (wA d b₁ z₁) x4) (step (wA d b₂ z₂) x4) hst.1 hst.2 hm_clean
  have hwM_pin (d b z : Bool) :
      (wM d b z).getD 0 false = b ∧ (wM d b z).getD 4 false = z ∧ (wM d b z).getD 9 false = !b := by
    have hA9 : 9 < (wA d b z).length := by
      dsimp only [wA]
      rw [run_length]
      have h10 : (inp d b z).length = 10 := rfl
      omega
    have h9lt : 9 < (step (wA d b z) x4).length := by simp [step]; omega
    have h4lt : 4 < (step (wA d b z) x4).length := by omega
    have h0lt : 0 < (step (wA d b z) x4).length := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [run_getD_lt _ _ 0 h0lt]; dsimp only [step]
      rw [List.getD_append _ _ _ _ (by omega)]; exact (hwA_pin d b z).1
    · rw [run_getD_lt _ _ 4 h4lt]; dsimp only [step]
      rw [List.getD_append _ _ _ _ (by omega)]; exact (hwA_pin d b z).2.1
    · rw [run_getD_lt _ _ 9 h9lt]; dsimp only [step]
      rw [List.getD_append _ _ _ _ hA9]; exact (hwA_pin d b z).2.2
  have hC_eq (d b₁ z₁ b₂ z₂ : Bool) (hvg : vg d b₁ z₁ = vg d b₂ z₂) (hvh : vh d b₁ z₁ = vh d b₂ z₂) :
      ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).eval (inp d b₁ z₁) =
      ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).eval (inp d b₂ z₂) := by
    have hM := hwM_ag d b₁ z₁ b₂ z₂ hvg
    have hst := step_append_agree (wM d b₁ z₁) (wM d b₂ z₂) (vh d b₁ z₁) (vh d b₂ z₂) hM.1 hvh hM.2
    have hrun := run_agree x3 (step (wM d b₁ z₁) x5) (step (wM d b₂ z₂) x5) hst.1 hst.2 ht_clean
    have hsplit : ∀ b z : Bool,
        ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).eval (inp d b z) =
        (run x3 (step (wM d b z) x5)).getD x6 false := by
      intro b z
      change (run (x1 ++ x4 :: (x2 ++ x5 :: x3)) (inp d b z)).getD x6 false = _
      rw [run_append]
      change (run (x2 ++ x5 :: x3) (step (wA d b z) x4)).getD x6 false = _
      rw [run_append]
      rfl
    rw [hsplit b₁ z₁, hsplit b₂ z₂]
    exact hrun.2 x6 ho0 ho4 ho9
  have hx4_mem : x4 ∈ ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).gates :=
    List.mem_append_right _ (List.Mem.head _)
  have hx5_mem : x5 ∈ ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).gates :=
    List.mem_append_right _ (List.Mem.tail _ (List.mem_append_right _ (List.Mem.head _)))
  obtain ⟨op4, s4, h24, k4, ext4, hext4, hgm4⟩ := gate_model x4 (hfan x4 hx4_mem) (hnot x4 hx4_mem)
    (hctrl x4 (List.Mem.head _))
  obtain ⟨op5, s5, h25, k5, ext5, hext5, hgm5⟩ := gate_model x5 (hfan x5 hx5_mem) (hnot x5 hx5_mem)
    (hctrl x5 (List.Mem.tail _ (List.Mem.head _)))
  let cT : Bool := (wA true false false).getD ext4 false
  let cF : Bool := (wA false false false).getD ext4 false
  have hvg_eval (d b z : Bool) : vg d b z =
      evalModel op4 s4 h24 k4 (if d then cT else cF) b z := by
    have hraw := hgm4 (wA d b z) b z (hwA_pin d b z).1 (hwA_pin d b z).2.1 (hwA_pin d b z).2.2
    change vg d b z = _ at hraw
    rw [hraw]
    by_cases hk4 : k4 = 3
    · have hneq := hext4 hk4
      have hc : (wA d b z).getD ext4 false = (if d then cT else cF) := by
        cases d
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact (hwA_ag false b z false false).2 ext4 hneq.1 hneq.2.1 hneq.2.2
        · simp only [↓reduceIte]
          exact (hwA_ag true b z false false).2 ext4 hneq.1 hneq.2.1 hneq.2.2
      rw [hc]
    · cases d <;> fin_cases k4 <;> first | rfl | exact False.elim (hk4 rfl)
  have hvg_T (b z : Bool) : vg true b z = evalModel op4 s4 h24 k4 cT b z := by
    simpa using hvg_eval true b z
  have hvg_F (b z : Bool) : vg false b z = evalModel op4 s4 h24 k4 cF b z := by
    simpa using hvg_eval false b z
  have pick_u : ∀ d : Bool, ∃ u0 u1 : Bool, ∀ b z : Bool,
      evalModel op5 s5 h25 k5 ((wM d b z).getD ext5 false) b z =
      evalModel op5 s5 h25 k5 (if vg d b z then u1 else u0) b z := by
    intro d
    classical
    refine ⟨if h : ∃ b z, vg d b z = false then (wM d h.choose h.choose_spec.choose).getD ext5 false else false,
      if h : ∃ b z, vg d b z = true then (wM d h.choose h.choose_spec.choose).getD ext5 false else false, ?_⟩
    intro b z
    by_cases hk5 : k5 = 3
    · have hneq := hext5 hk5
      cases hval : vg d b z
      · have hex : ∃ b' z', vg d b' z' = false := ⟨b, z, hval⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · rename_i h
          exact congrArg (fun x => evalModel op5 s5 h25 k5 x b z)
            ((hwM_ag d b z h.choose h.choose_spec.choose (hval.trans h.choose_spec.choose_spec.symm)).2
              ext5 hneq.1 hneq.2.1 hneq.2.2)
        · rename_i h
          exact False.elim (h hex)
      · have hex : ∃ b' z', vg d b' z' = true := ⟨b, z, hval⟩
        simp only [↓reduceIte]
        split
        · rename_i h
          exact congrArg (fun x => evalModel op5 s5 h25 k5 x b z)
            ((hwM_ag d b z h.choose h.choose_spec.choose (hval.trans h.choose_spec.choose_spec.symm)).2
              ext5 hneq.1 hneq.2.1 hneq.2.2)
        · rename_i h
          exact False.elim (h hex)
    · fin_cases k5 <;> first | rfl | exact False.elim (hk5 rfl)
  obtain ⟨u0T, u1T, huT⟩ := pick_u true
  obtain ⟨u0F, u1F, huF⟩ := pick_u false
  have hvh_T (b z : Bool) : vh true b z =
      evalModel op5 s5 h25 k5 (if evalModel op4 s4 h24 k4 cT b z then u1T else u0T) b z := by
    have hraw := hgm5 (wM true b z) b z (hwM_pin true b z).1 (hwM_pin true b z).2.1 (hwM_pin true b z).2.2
    change vh true b z = _ at hraw
    rw [hraw, huT b z, hvg_T b z]
  have hvh_F (b z : Bool) : vh false b z =
      evalModel op5 s5 h25 k5 (if evalModel op4 s4 h24 k4 cF b z then u1F else u0F) b z := by
    have hraw := hgm5 (wM false b z) b z (hwM_pin false b z).1 (hwM_pin false b z).2.1 (hwM_pin false b z).2.2
    change vh false b z = _ at hraw
    rw [hraw, huF b z, hvg_F b z]
  have hsepB : sepB op4 s4 h24 k4 cT op5 s5 h25 k5 u0T u1T = true := by
    refine List.all_eq_true.mpr fun b1 _ => List.all_eq_true.mpr fun z1 _ =>
      List.all_eq_true.mpr fun b2 _ => List.all_eq_true.mpr fun z2 _ => ?_
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
    by_cases h4 : evalModel op4 s4 h24 k4 cT b1 z1 = evalModel op4 s4 h24 k4 cT b2 z2
    · by_cases h5 : evalModel op5 s5 h25 k5 (if evalModel op4 s4 h24 k4 cT b1 z1 then u1T else u0T) b1 z1 =
          evalModel op5 s5 h25 k5 (if evalModel op4 s4 h24 k4 cT b2 z2 then u1T else u0T) b2 z2
      · right
        have hvg' : vg true b1 z1 = vg true b2 z2 := by rw [hvg_T, hvg_T]; exact h4
        have hvh' : vh true b1 z1 = vh true b2 z2 := by rw [hvh_T, hvh_T]; exact h5
        have hev := hC_eq true b1 z1 b2 z2 hvg' hvh'
        have hm1 : ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).eval (inp true b1 z1) = b1 :=
          hmux true b1 z1
        have hm2 : ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).eval (inp true b2 z2) = b2 :=
          hmux true b2 z2
        rw [hm1, hm2] at hev
        exact hev
      · left; exact Or.inr (Bool.eq_false_of_ne_true (fun heq => h5 (beq_iff_eq.mp heq)))
    · left; exact Or.inl (Bool.eq_false_of_ne_true (fun heq => h4 (beq_iff_eq.mp heq)))
  have hsepZ : sepZ op4 s4 h24 k4 cF op5 s5 h25 k5 u0F u1F = true := by
    refine List.all_eq_true.mpr fun b1 _ => List.all_eq_true.mpr fun z1 _ =>
      List.all_eq_true.mpr fun b2 _ => List.all_eq_true.mpr fun z2 _ => ?_
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
    by_cases h4 : evalModel op4 s4 h24 k4 cF b1 z1 = evalModel op4 s4 h24 k4 cF b2 z2
    · by_cases h5 : evalModel op5 s5 h25 k5 (if evalModel op4 s4 h24 k4 cF b1 z1 then u1F else u0F) b1 z1 =
          evalModel op5 s5 h25 k5 (if evalModel op4 s4 h24 k4 cF b2 z2 then u1F else u0F) b2 z2
      · right
        have hvg' : vg false b1 z1 = vg false b2 z2 := by rw [hvg_F, hvg_F]; exact h4
        have hvh' : vh false b1 z1 = vh false b2 z2 := by rw [hvh_F, hvh_F]; exact h5
        have hev := hC_eq false b1 z1 b2 z2 hvg' hvh'
        have hm1 : ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).eval (inp false b1 z1) = z1 :=
          hmux false b1 z1
        have hm2 : ({ gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 } : Circuit).eval (inp false b2 z2) = z2 :=
          hmux false b2 z2
        rw [hm1, hm2] at hev
        exact hev
      · left; exact Or.inr (Bool.eq_false_of_ne_true (fun heq => h5 (beq_iff_eq.mp heq)))
    · left; exact Or.inl (Bool.eq_false_of_ne_true (fun heq => h4 (beq_iff_eq.mp heq)))
  exact not_both_sep op4 s4 h24 k4 op5 s5 h25 k5 cT u0T u1T cF u0F u1F hsepB hsepZ

end PEqualNP.Outside.L_meta_5300

theorem PEqualNP.Outside.L_meta_5300 :
    ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → (∀ x9 ∈ x7.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.not → x9.inputs.length ≤ (1 : ℕ)) → (∀ x10 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x10.inputs ∧ (9 : ℕ) ∉ x10.inputs) → (∀ x11 ∈ [x4, x5], (0 : ℕ) ∈ x11.inputs ∨ (9 : ℕ) ∈ x11.inputs) → (∀ (x12 x13 x14 : Bool), x7.eval [x13, x12, Bool.false, !x12, x14, Bool.false, Bool.false, Bool.false, Bool.false, !x13] = if x12 = Bool.true then x13 else x14) → ∃ x13 ∈ x1 ++ x2 ++ x3, (4 : ℕ) ∈ x13.inputs := by
  dsimp only
  intro x1 x2 x3 x4 x5 x6 hfan hnot havoid hctrl hmux
  exact PEqualNP.Outside.L_meta_5300.main5300 x1 x2 x3 x4 x5 x6 hfan hnot havoid hctrl hmux
