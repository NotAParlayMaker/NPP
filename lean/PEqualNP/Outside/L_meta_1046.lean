import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1046_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val (gs : List Gate) (x : Fin 6 → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, step, List.length_append, List.length_nil]
    omega

lemma fold_append_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlen]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma val_lt_6 (gs : List Gate) (x : Fin 6 → Bool) (i : ℕ) (hi : i < 6) :
    val gs x i = x ⟨i, hi⟩ := by
  unfold val
  have hlen : i < (List.ofFn x).length := by simp [hi]
  rw [fold_append_getD_lt gs (List.ofFn x) i hlen]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_ofFn]

lemma val_ge_len (gs : List Gate) (x : Fin 6 → Bool) (i : ℕ) (hi : 6 + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hlen : (gs.foldl step (List.ofFn x)).length = 6 + gs.length := by
    rw [fold_length]
    simp
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma val_take (gs : List Gate) (k : ℕ) (x : Fin 6 → Bool) (i : ℕ) (hi : i < 6 + min k gs.length) :
    val gs x i = val (gs.take k) x i := by
  unfold val
  conv_lhs => rw [← List.take_append_drop k gs]
  rw [List.foldl_append]
  have hlen : i < ((gs.take k).foldl step (List.ofFn x)).length := by
    rw [fold_length]
    simp only [List.length_ofFn, List.length_take]
    omega
  exact fold_append_getD_lt (gs.drop k) ((gs.take k).foldl step (List.ofFn x)) i hlen

lemma val_at_gate (gs : List Gate) (q : Fin gs.length) (x : Fin 6 → Bool) :
    val gs x (6 + q.val) =
      (gs.get q).op.eval ((gs.get q).inputs.map fun j =>
        if j < 6 + q.val then val gs x j else false) := by
  have hsplit : gs = gs.take q.val ++ [gs.get q] ++ gs.drop (q.val + 1) := by
    have h2 : gs.drop q.val = gs.get q :: gs.drop (q.val + 1) := by
      rw [List.drop_eq_getElem_cons q.isLt]
      rfl
    calc gs = gs.take q.val ++ gs.drop q.val := (List.take_append_drop q.val gs).symm
      _ = gs.take q.val ++ (gs.get q :: gs.drop (q.val + 1)) := by rw [h2]
      _ = gs.take q.val ++ [gs.get q] ++ gs.drop (q.val + 1) := by simp
  have hpref_len : ((gs.take q.val).foldl step (List.ofFn x)).length = 6 + q.val := by
    rw [fold_length]
    simp only [List.length_ofFn, List.length_take]
    omega
  have hstep_len : 6 + q.val < ((gs.take q.val ++ [gs.get q]).foldl step (List.ofFn x)).length := by
    rw [fold_length]
    simp only [List.length_ofFn, List.length_append, List.length_take, List.length_cons,
      List.length_nil]
    omega
  have hfold : gs.foldl step (List.ofFn x) =
      (gs.take q.val ++ [gs.get q] ++ gs.drop (q.val + 1)).foldl step (List.ofFn x) :=
    congrArg (fun l => l.foldl step (List.ofFn x)) hsplit
  change (gs.foldl step (List.ofFn x)).getD (6 + q.val) false = _
  rw [hfold, List.foldl_append, fold_append_getD_lt _ _ _ hstep_len]
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp only [hpref_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases hj : j < 6 + q.val
  · rw [if_pos hj]
    have hmin : j < 6 + min q.val gs.length := by omega
    rw [← List.getD_eq_getElem?_getD]
    exact (val_take gs q.val x j hmin).symm
  · rw [if_neg hj]
    rw [List.getElem?_eq_none (by omega)]
    rfl

lemma op_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ i (h1 : i < l1.length) (h2 : i < l2.length), l1[i] = true → l2[i] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have h1 : i < l1.length := by omega
    exact hle i h1 hi (h l1[i] (List.getElem_mem h1))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hb
    have h2 : i < l2.length := by omega
    exact ⟨l2[i], List.getElem_mem h2, hle i hi h2 hget⟩

lemma val_mono_before (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length)
    (hno : ∀ i : Fin gs.length, i.val < k → (gs.get i).op = GateOp.and ∨ (gs.get i).op = GateOp.or)
    (x y : Fin 6 → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ i < 6 + k, val gs x i = true → val gs y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hik hval
    by_cases h6 : i < 6
    · rw [val_lt_6 gs x i h6] at hval
      rw [val_lt_6 gs y i h6]
      exact hxy ⟨i, h6⟩ hval
    · have hq : i - 6 < gs.length := by omega
      let q : Fin gs.length := ⟨i - 6, hq⟩
      have hiq : i = 6 + q.val := by dsimp [q]; omega
      have hqk : q.val < k := by dsimp [q]; omega
      rw [hiq, val_at_gate gs q x] at hval
      rw [hiq, val_at_gate gs q y]
      refine op_eval_mono (gs.get q).op (hno q hqk) _ _ (by simp) ?_ hval
      intro idx h1 h2 hget
      simp only [List.getElem_map] at hget ⊢
      by_cases hj : (gs.get q).inputs[idx]'(by simpa using h1) < 6 + q.val
      · rw [if_pos hj] at hget ⊢
        exact ih ((gs.get q).inputs[idx]'(by simpa using h1)) (by omega) (by omega) hget
      · rw [if_neg hj] at hget
        simp at hget

lemma val_antimono_not (gs : List Gate) (q0 : Fin gs.length)
    (hno : ∀ i : Fin gs.length, i.val < q0.val → (gs.get i).op = GateOp.and ∨ (gs.get i).op = GateOp.or)
    (hnot : (gs.get q0).op = GateOp.not)
    (x y : Fin 6 → Bool) (hxy : ∀ v, x v = true → y v = true) :
    val gs y (6 + q0.val) = true → val gs x (6 + q0.val) = true := by
  rw [val_at_gate gs q0 y, val_at_gate gs q0 x, hnot]
  cases hins : (gs.get q0).inputs with
  | nil => simp [GateOp.eval]
  | cons j rest =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hy
    by_cases hj : j < 6 + q0.val
    · rw [if_pos hj] at hy ⊢
      cases hx : val gs x j
      · rfl
      · have := val_mono_before gs q0.val (by omega) hno x y hxy j hj hx
        rw [this] at hy
        simp at hy
    · rw [if_neg hj]

lemma min_wire_is_two_bin (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (q0 : Fin gs.length)
    (hnot_only : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = q0)
    (φ : (Fin 6 → Bool) → Bool)
    (k : ℕ) (hk : ∀ x, val gs x k = φ x)
    (htrue : ∃ x, φ x = true)
    (hfalse : ∃ x, φ x = false)
    (hnot_in : ∀ v : Fin 6, ∃ x, φ x ≠ x v)
    (hnot_anti : ¬ (∀ x y : Fin 6 → Bool, (∀ v, x v = true → y v = true) → φ y = true → φ x = true)) :
    ∃ q : Fin gs.length,
      6 + q.val ≤ k ∧
      (∀ x, val gs x (6 + q.val) = φ x) ∧
      (∀ j < 6 + q.val, ¬ ∀ x, val gs x j = φ x) ∧
      ((gs.get q).op = GateOp.and ∨ (gs.get q).op = GateOp.or) ∧
      (gs.get q).inputs.length = 2 := by
  classical
  have hex : ∃ i, ∀ x, val gs x i = φ x := ⟨k, hk⟩
  let m := Nat.find hex
  have hm_eq : ∀ x, val gs x m = φ x := Nat.find_spec hex
  have hm_le : m ≤ k := Nat.find_min' hex hk
  have hm_min : ∀ j < m, ¬ ∀ x, val gs x j = φ x := fun j hj => Nat.find_min hex hj
  have hm_ge6 : 6 ≤ m := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨x, hx⟩ := hnot_in ⟨m, hlt⟩
    have := hm_eq x
    rw [val_lt_6 gs x m hlt] at this
    exact hx this.symm
  have hm_lt : m < 6 + gs.length := by
    by_contra hge
    push_neg at hge
    obtain ⟨x, hx⟩ := htrue
    have := hm_eq x
    rw [val_ge_len gs x m hge] at this
    rw [hx] at this
    simp at this
  let q : Fin gs.length := ⟨m - 6, by omega⟩
  have hmq : 6 + q.val = m := by
    dsimp [q]
    omega
  have hmem : gs.get q ∈ gs := List.get_mem gs q
  obtain ⟨hop3, hlen2⟩ := hg (gs.get q) hmem
  have hno_not : (gs.get q).op ≠ GateOp.not := by
    intro hnot
    have hqq0 : q = q0 := hnot_only q hnot
    subst hqq0
    have hbefore : ∀ i : Fin gs.length, i.val < q.val → (gs.get i).op = GateOp.and ∨ (gs.get i).op = GateOp.or := by
      intro i hi
      obtain ⟨ho, -⟩ := hg (gs.get i) (List.get_mem gs i)
      rcases ho with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have := hnot_only i h
        omega
    apply hnot_anti
    intro x y hxy hy
    rw [← hm_eq x, ← hmq]
    apply val_antimono_not gs q hbefore hnot x y hxy
    rw [hmq, hm_eq y]
    exact hy
  have hop : (gs.get q).op = GateOp.and ∨ (gs.get q).op = GateOp.or := by
    rcases hop3 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hno_not
  have hlen : (gs.get q).inputs.length = 2 := by
    match hins : (gs.get q).inputs with
    | [] =>
      exfalso
      rcases hop with hand | hor
      · obtain ⟨x, hx⟩ := hfalse
        have h1 := hm_eq x
        rw [← hmq, val_at_gate gs q x, hand, hins] at h1
        simp [GateOp.eval] at h1
        rw [hx] at h1
        simp at h1
      · obtain ⟨x, hx⟩ := htrue
        have h1 := hm_eq x
        rw [← hmq, val_at_gate gs q x, hor, hins] at h1
        simp [GateOp.eval] at h1
        rw [hx] at h1
        simp at h1
    | [a] =>
      exfalso
      by_cases ha : a < 6 + q.val
      · apply hm_min a (by omega)
        intro x
        have h1 := hm_eq x
        rw [← hmq, val_at_gate gs q x, hins] at h1
        rcases hop with hand | hor
        · rw [hand] at h1
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            Bool.and_true, id_eq, if_pos ha] at h1
          exact h1
        · rw [hor] at h1
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            Bool.or_false, id_eq, if_pos ha] at h1
          exact h1
      · obtain ⟨x, hx⟩ := htrue
        have h1 := hm_eq x
        rw [← hmq, val_at_gate gs q x, hins] at h1
        rcases hop with hand | hor
        · rw [hand] at h1
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            Bool.and_true, id_eq, if_neg ha] at h1
          rw [hx] at h1
          simp at h1
        · rw [hor] at h1
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            Bool.or_false, id_eq, if_neg ha] at h1
          rw [hx] at h1
          simp at h1
    | [a, b] => rfl
    | _ :: _ :: _ :: _ =>
      rw [hins] at hlen2
      simp at hlen2
  refine ⟨q, by omega, ?_, ?_, hop, hlen⟩
  · intro x; rw [hmq]; exact hm_eq x
  · intro j hj; exact hm_min j (by omega)

def fam : Fin 7 → Finset (Fin 6) :=
  ![{0, 2}, {3, 4}, {1, 5}, {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {0, 4, 5}]

def target (o : Fin 7) (x : Fin 6 → Bool) : Bool :=
  decide (∃ v ∈ fam o, x v = true)

def eof (u : Fin 6) : Fin 6 → Bool :=
  fun c => decide (c = u)

def zof (T : Finset (Fin 6)) : Fin 6 → Bool :=
  fun c => decide (c ∉ T)

lemma target_false (o : Fin 7) : target o (fun _ => false) = false := by
  simp [target]

lemma target_true (o : Fin 7) : target o (fun _ => true) = true := by
  revert o
  decide

lemma target_eof (o : Fin 7) (u : Fin 6) : target o (eof u) = decide (u ∈ fam o) := by
  simp [target, eof]

lemma target_zof (o : Fin 7) : target o (zof (fam o)) = false := by
  simp [target, zof]

lemma fam_card_ge_two (o : Fin 7) : 2 ≤ (fam o).card := by
  revert o
  decide

lemma fam_inter_le_one (a b : Fin 7) (hab : a ≠ b) : (fam a ∩ fam b).card ≤ 1 := by
  revert a b hab
  decide

lemma fam_diff_exists (a b : Fin 7) (hab : a ≠ b) : ∃ u ∈ fam a, u ∉ fam b := by
  revert a b hab
  decide

lemma fam_triple_card (t : Fin 4) : (fam ⟨t.val + 3, by omega⟩).card = 3 := by
  revert t
  decide

lemma fam_not_input (o : Fin 7) (v : Fin 6) : ∃ u ∈ fam o, u ≠ v := by
  revert o v
  decide

lemma not_input_of_two_eof (φ : (Fin 6 → Bool) → Bool) (T : Finset (Fin 6))
    (h2 : 2 ≤ (T.filter (fun u => φ (eof u) = true)).card) :
    ∀ v : Fin 6, ∃ x, φ x ≠ x v := by
  intro v
  have hex : ∃ u ∈ T.filter (fun u => φ (eof u) = true), u ≠ v := by
    by_contra h
    push_neg at h
    have hsub : T.filter (fun u => φ (eof u) = true) ⊆ {v} := by
      intro u hu
      exact Finset.mem_singleton.mpr (h u hu)
    have := Finset.card_le_card hsub
    simp at this
    omega
  obtain ⟨u, hu, huv⟩ := hex
  refine ⟨eof u, ?_⟩
  have h1 : φ (eof u) = true := (Finset.mem_filter.mp hu).2
  have h2 : eof u v = false := by simp [eof, Ne.symm huv]
  rw [h1, h2]
  simp

lemma not_anti_of_0_1 (φ : (Fin 6 → Bool) → Bool)
    (h0 : φ (fun _ => false) = false) (h1 : φ (fun _ => true) = true) :
    ¬ (∀ x y : Fin 6 → Bool, (∀ v, x v = true → y v = true) → φ y = true → φ x = true) := by
  intro hanti
  have := hanti (fun _ => false) (fun _ => true) (fun _ h => by simp at h) h1
  rw [h0] at this
  simp at this

lemma witness_exists (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (q0 : Fin gs.length)
    (hnot_only : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = q0)
    (t : Fin 4) (gt : Fin gs.length)
    (hgt_eq : ∀ x, val gs x (6 + gt.val) = target ⟨t.val + 3, by omega⟩ x)
    (hgt_min : ∀ j < 6 + gt.val, ¬ ∀ x, val gs x j = target ⟨t.val + 3, by omega⟩ x)
    (hgt_op : (gs.get gt).op = GateOp.and ∨ (gs.get gt).op = GateOp.or)
    (hgt_len : (gs.get gt).inputs.length = 2) :
    ∃ r : Fin gs.length,
      r.val < gt.val ∧
      ((gs.get r).op = GateOp.and ∨ (gs.get r).op = GateOp.or) ∧
      (gs.get r).inputs.length = 2 ∧
      (((∀ x, val gs x (6 + r.val) = true → target ⟨t.val + 3, by omega⟩ x = true) ∧
        2 ≤ ((fam ⟨t.val + 3, by omega⟩).filter (fun u => val gs (eof u) (6 + r.val) = true)).card) ∨
       ((∀ x, target ⟨t.val + 3, by omega⟩ x = true → val gs x (6 + r.val) = true) ∧
        val gs (zof (fam ⟨t.val + 3, by omega⟩)) (6 + r.val) = false)) := by
  let ot : Fin 7 := ⟨t.val + 3, by omega⟩
  match hins : (gs.get gt).inputs with
  | [a, b] =>
    have heval : ∀ x, target ot x =
        (gs.get gt).op.eval
          [if a < 6 + gt.val then val gs x a else false,
           if b < 6 + gt.val then val gs x b else false] := by
      intro x
      rw [← hgt_eq x, val_at_gate gs gt x, hins]
      rfl
    rcases hgt_op with hand | hor
    · have ha_lt : a < 6 + gt.val := by
        by_contra ha
        have h1 := heval (fun _ => true)
        rw [hand, if_neg ha, target_true] at h1
        simp [GateOp.eval] at h1
      have hb_lt : b < 6 + gt.val := by
        by_contra hb
        have h1 := heval (fun _ => true)
        rw [hand, if_neg hb, target_true] at h1
        simp [GateOp.eval] at h1
      have hband : ∀ x, target ot x = (val gs x a && val gs x b) := by
        intro x
        have h1 := heval x
        rw [hand, if_pos ha_lt, if_pos hb_lt] at h1
        simpa [GateOp.eval] using h1
      have hz := hband (zof (fam ot))
      rw [target_zof] at hz
      have hpick : ∃ k : ℕ, k < 6 + gt.val ∧
          (∀ x, target ot x = true → val gs x k = true) ∧
          val gs (zof (fam ot)) k = false := by
        cases hza : val gs (zof (fam ot)) a
        · exact ⟨a, ha_lt, fun x hx => by have := hband x; rw [hx] at this; exact (Bool.and_eq_true _ _ |>.mp this.symm).1, hza⟩
        · have hzb : val gs (zof (fam ot)) b = false := by
            rw [hza, Bool.true_and] at hz
            exact hz.symm
          exact ⟨b, hb_lt, fun x hx => by have := hband x; rw [hx] at this; exact (Bool.and_eq_true _ _ |>.mp this.symm).2, hzb⟩
      obtain ⟨k, hk_lt, hk_ge, hk_zof⟩ := hpick
      have hk_2 : 2 ≤ ((fam ot).filter (fun u => val gs (eof u) k = true)).card := by
        have hfeq : (fam ot).filter (fun u => val gs (eof u) k = true) = fam ot := by
          ext u
          simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro hu
          apply hk_ge
          rw [target_eof]
          exact decide_eq_true hu
        rw [hfeq, fam_triple_card t]
        omega
      have hk_anti : ¬ (∀ x y : Fin 6 → Bool, (∀ v, x v = true → y v = true) →
          val gs y k = true → val gs x k = true) := by
        intro hanti
        have h1 : val gs (fun _ => true) k = true := hk_ge (fun _ => true) (target_true ot)
        have h2 := hanti (zof (fam ot)) (fun _ => true) (fun _ _ => rfl) h1
        rw [hk_zof] at h2
        simp at h2
      obtain ⟨r, hr_le, hr_eq, _, hr_op, hr_len⟩ :=
        min_wire_is_two_bin gs hg q0 hnot_only (fun x => val gs x k) k (fun _ => rfl)
          ⟨fun _ => true, hk_ge _ (target_true ot)⟩
          ⟨zof (fam ot), hk_zof⟩
          (not_input_of_two_eof (fun x => val gs x k) (fam ot) hk_2)
          hk_anti
      refine ⟨r, by omega, hr_op, hr_len, Or.inr ⟨?_, ?_⟩⟩
      · intro x hx; rw [hr_eq x]; exact hk_ge x hx
      · rw [hr_eq]; exact hk_zof
    · have ha_lt : a < 6 + gt.val := by
        by_contra ha
        by_cases hb : b < 6 + gt.val
        · apply hgt_min b hb
          intro x
          have h1 := heval x
          rw [hor, if_neg ha, if_pos hb] at h1
          simpa [GateOp.eval] using h1.symm
        · have h1 := heval (fun _ => true)
          rw [hor, if_neg ha, if_neg hb, target_true] at h1
          simp [GateOp.eval] at h1
      have hb_lt : b < 6 + gt.val := by
        by_contra hb
        apply hgt_min a ha_lt
        intro x
        have h1 := heval x
        rw [hor, if_pos ha_lt, if_neg hb] at h1
        simpa [GateOp.eval] using h1.symm
      have hbor : ∀ x, target ot x = (val gs x a || val gs x b) := by
        intro x
        have h1 := heval x
        rw [hor, if_pos ha_lt, if_pos hb_lt] at h1
        simpa [GateOp.eval] using h1
      have hcov : fam ot ⊆ (fam ot).filter (fun u => val gs (eof u) a = true) ∪
          (fam ot).filter (fun u => val gs (eof u) b = true) := by
        intro u hu
        have h1 := hbor (eof u)
        rw [target_eof, decide_eq_true hu] at h1
        rcases Bool.or_eq_true _ _ |>.mp h1.symm with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, h⟩)
      have hcard_sum : 3 ≤ ((fam ot).filter (fun u => val gs (eof u) a = true)).card +
          ((fam ot).filter (fun u => val gs (eof u) b = true)).card := by
        have h1 := Finset.card_le_card hcov
        have h2 := Finset.card_union_le ((fam ot).filter (fun u => val gs (eof u) a = true))
          ((fam ot).filter (fun u => val gs (eof u) b = true))
        have h3 : (fam ot).card = 3 := fam_triple_card t
        omega
      have hpick : ∃ k : ℕ, k < 6 + gt.val ∧
          (∀ x, val gs x k = true → target ot x = true) ∧
          2 ≤ ((fam ot).filter (fun u => val gs (eof u) k = true)).card := by
        by_cases hca : 2 ≤ ((fam ot).filter (fun u => val gs (eof u) a = true)).card
        · refine ⟨a, ha_lt, ?_, hca⟩
          intro x hx
          rw [hbor x, hx, Bool.true_or]
        · refine ⟨b, hb_lt, ?_, by omega⟩
          intro x hx
          rw [hbor x, hx, Bool.or_true]
      obtain ⟨k, hk_lt, hk_le, hk_2⟩ := hpick
      have hk_false0 : val gs (fun _ => false) k = false := by
        cases h0 : val gs (fun _ => false) k
        · rfl
        · have := hk_le (fun _ => false) h0
          rw [target_false] at this
          simp at this
      have hk_has_true : ∃ x, val gs x k = true := by
        have hne : ((fam ot).filter (fun u => val gs (eof u) k = true)).Nonempty :=
          Finset.card_pos.mp (by omega)
        obtain ⟨u, hu⟩ := hne
        exact ⟨eof u, (Finset.mem_filter.mp hu).2⟩
      have hk_anti : ¬ (∀ x y : Fin 6 → Bool, (∀ v, x v = true → y v = true) →
          val gs y k = true → val gs x k = true) := by
        intro hanti
        obtain ⟨y, hy⟩ := hk_has_true
        have := hanti (fun _ => false) y (fun _ h => by simp at h) hy
        rw [hk_false0] at this
        simp at this
      obtain ⟨r, hr_le, hr_eq, _, hr_op, hr_len⟩ :=
        min_wire_is_two_bin gs hg q0 hnot_only (fun x => val gs x k) k (fun _ => rfl)
          hk_has_true
          ⟨fun _ => false, hk_false0⟩
          (not_input_of_two_eof (fun x => val gs x k) (fam ot) hk_2)
          hk_anti
      refine ⟨r, by omega, hr_op, hr_len, Or.inl ⟨?_, ?_⟩⟩
      · intro x hx; apply hk_le; rw [← hr_eq x]; exact hx
      · have hfeq : (fam ot).filter (fun u => val gs (eof u) (6 + r.val) = true) =
            (fam ot).filter (fun u => val gs (eof u) k = true) := by
          ext u
          simp only [Finset.mem_filter, hr_eq]
        rw [hfeq]
        exact hk_2
  | [] => rw [hins] at hgt_len; simp at hgt_len
  | [_] => rw [hins] at hgt_len; simp at hgt_len
  | _ :: _ :: _ :: _ => rw [hins] at hgt_len; simp at hgt_len

end PEqualNP.Outside.L_meta_1046_aux

open PEqualNP.Outside.L_meta_1046_aux in
theorem PEqualNP.Outside.L_meta_1046 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (o : Fin 7) (x : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ (![{0, 2}, {3, 4}, {1, 5}, {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {0, 4, 5}] : Fin 7 → Finset (Fin 6)) o, x v = true)) → ∀ I : Finset (Fin gates.length), (∀ q : Fin gates.length, ((gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q).inputs.length = 2 → q ∈ I) → 11 ≤ I.card := by
  classical
  intro gates out hg hnot hev I hI
  obtain ⟨ι, hι⟩ := hnot
  let q0 : Fin gates.length := ι 0
  have hnot_only : ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = q0 := by
    intro i hi
    obtain ⟨j, hj⟩ := hι i hi
    have hj0 : j = 0 := Fin.eq_zero j
    rw [← hj, hj0]
  have hval_out : ∀ (o : Fin 7) (x : Fin 6 → Bool), val gates x (out o) = target o x :=
    fun o x => hev o x
  have hmin_out : ∀ o : Fin 7, ∃ q : Fin gates.length,
      (∀ x, val gates x (6 + q.val) = target o x) ∧
      (∀ j < 6 + q.val, ¬ ∀ x, val gates x j = target o x) ∧
      ((gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gates.get q).inputs.length = 2 := by
    intro o
    have hnot_in : ∀ v : Fin 6, ∃ x, target o x ≠ x v := by
      intro v
      obtain ⟨u, hu, huv⟩ := fam_not_input o v
      refine ⟨eof u, ?_⟩
      rw [target_eof, decide_eq_true hu]
      simp [eof, Ne.symm huv]
    obtain ⟨q, _, hq_eq, hq_min, hq_op, hq_len⟩ :=
      min_wire_is_two_bin gates hg q0 hnot_only (target o) (out o) (hval_out o)
        ⟨fun _ => true, target_true o⟩
        ⟨fun _ => false, target_false o⟩
        hnot_in
        (not_anti_of_0_1 (target o) (target_false o) (target_true o))
    exact ⟨q, hq_eq, hq_min, hq_op, hq_len⟩
  choose g hg_eq hg_min hg_op hg_len using hmin_out
  have hwit : ∀ t : Fin 4, ∃ r : Fin gates.length,
      r.val < (g ⟨t.val + 3, by omega⟩).val ∧
      ((gates.get r).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (gates.get r).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gates.get r).inputs.length = 2 ∧
      (((∀ x, val gates x (6 + r.val) = true → target ⟨t.val + 3, by omega⟩ x = true) ∧
        2 ≤ ((fam ⟨t.val + 3, by omega⟩).filter (fun u => val gates (eof u) (6 + r.val) = true)).card) ∨
       ((∀ x, target ⟨t.val + 3, by omega⟩ x = true → val gates x (6 + r.val) = true) ∧
        val gates (zof (fam ⟨t.val + 3, by omega⟩)) (6 + r.val) = false)) := by
    intro t
    exact witness_exists gates hg q0 hnot_only t (g ⟨t.val + 3, by omega⟩)
      (hg_eq _) (hg_min _) (hg_op _) (hg_len _)
  choose w hw_lt hw_op hw_len hw_prop using hwit
  have hg_inj : Function.Injective g := by
    intro a b hab
    by_contra hne
    obtain ⟨u, hua, hub⟩ := fam_diff_exists a b hne
    have h1 := hg_eq a (eof u)
    have h2 := hg_eq b (eof u)
    rw [hab] at h1
    rw [h1] at h2
    rw [target_eof, target_eof, decide_eq_true hua, decide_eq_false hub] at h2
    simp at h2
  have hdisj_gw : ∀ (o : Fin 7) (t : Fin 4), g o ≠ w t := by
    intro o t heq
    let ot : Fin 7 := ⟨t.val + 3, by omega⟩
    by_cases hot : o = ot
    · have hlt : (w t).val < (g ot).val := hw_lt t
      rw [← hot, ← heq] at hlt
      omega
    · rcases hw_prop t with ⟨hle, h2⟩ | ⟨hge, hz⟩
      · obtain ⟨u, huo, hut⟩ := fam_diff_exists o ot hot
        have h1 : val gates (eof u) (6 + (w t).val) = true := by
          rw [← heq, hg_eq o (eof u), target_eof]
          exact decide_eq_true huo
        have h2' := hle (eof u) h1
        rw [target_eof, decide_eq_false hut] at h2'
        simp at h2'
      · obtain ⟨u, hut, huo⟩ := fam_diff_exists ot o (Ne.symm hot)
        have h1 : val gates (eof u) (6 + (w t).val) = true := by
          apply hge
          rw [target_eof]
          exact decide_eq_true hut
        rw [← heq, hg_eq o (eof u), target_eof, decide_eq_false huo] at h1
        simp at h1
  have hw_inj : Function.Injective w := by
    intro t1 t2 heq
    by_contra hne
    let o1 : Fin 7 := ⟨t1.val + 3, by omega⟩
    let o2 : Fin 7 := ⟨t2.val + 3, by omega⟩
    have ho : o1 ≠ o2 := by
      intro h
      apply hne
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [o1, o2] at this
      omega
    rcases hw_prop t1 with ⟨hle1, hc1⟩ | ⟨hge1, hz1⟩ <;>
      rcases hw_prop t2 with ⟨hle2, hc2⟩ | ⟨hge2, hz2⟩
    · have hsub : (fam o1).filter (fun u => val gates (eof u) (6 + (w t1).val) = true) ⊆
          fam o1 ∩ fam o2 := by
        intro u hu
        obtain ⟨hu1, hval⟩ := Finset.mem_filter.mp hu
        refine Finset.mem_inter.mpr ⟨hu1, ?_⟩
        rw [heq] at hval
        have := hle2 (eof u) hval
        rw [target_eof, decide_eq_true_eq] at this
        exact this
      have hle := Finset.card_le_card hsub
      have hint := fam_inter_le_one o1 o2 ho
      have hc1' : 2 ≤ ((fam o1).filter (fun u => val gates (eof u) (6 + (w t1).val) = true)).card := hc1
      omega
    · obtain ⟨u, hu2, hu1⟩ := fam_diff_exists o2 o1 (Ne.symm ho)
      have h1 : val gates (eof u) (6 + (w t2).val) = true :=
        hge2 (eof u) (by rw [target_eof]; exact decide_eq_true hu2)
      rw [← heq] at h1
      have h2 := hle1 (eof u) h1
      rw [target_eof, decide_eq_false hu1] at h2
      simp at h2
    · obtain ⟨u, hu1, hu2⟩ := fam_diff_exists o1 o2 ho
      have h1 : val gates (eof u) (6 + (w t1).val) = true :=
        hge1 (eof u) (by rw [target_eof]; exact decide_eq_true hu1)
      rw [heq] at h1
      have h2 := hle2 (eof u) h1
      rw [target_eof, decide_eq_false hu2] at h2
      simp at h2
    · obtain ⟨u, hu2, hu1⟩ := fam_diff_exists o2 o1 (Ne.symm ho)
      have ht2 : target o2 (zof (fam o1)) = true := by
        simp only [target, zof, decide_eq_true_eq]
        exact ⟨u, hu2, hu1⟩
      have h1 : val gates (zof (fam o1)) (6 + (w t2).val) = true := hge2 _ ht2
      rw [← heq, hz1] at h1
      simp at h1
  let Sg : Finset (Fin gates.length) := Finset.univ.image g
  let Sw : Finset (Fin gates.length) := Finset.univ.image w
  have hdisj : Disjoint Sg Sw := by
    rw [Finset.disjoint_left]
    intro q hqg hqw
    obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hqg
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hqw
    exact hdisj_gw o t ht.symm
  have hsubI : Sg ∪ Sw ⊆ I := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hq
      exact hI (g o) ⟨hg_op o, hg_len o⟩
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hq
      exact hI (w t) ⟨hw_op t, hw_len t⟩
  have hcg : Sg.card = 7 := by
    rw [Finset.card_image_of_injective _ hg_inj]
    simp
  have hcw : Sw.card = 4 := by
    rw [Finset.card_image_of_injective _ hw_inj]
    simp
  have hcu : (Sg ∪ Sw).card = 11 := by
    rw [Finset.card_union_of_disjoint hdisj, hcg, hcw]
  calc 11 = (Sg ∪ Sw).card := hcu.symm
    _ ≤ I.card := Finset.card_le_card hsubI
