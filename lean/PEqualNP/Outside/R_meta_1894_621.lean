import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1894_621
    (rename : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (e : Fin n ≃ Fin n),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size ∧
        (∀ j : ℕ, D.gates[j]?.map PEqualNP.CircuitLowerBounds.Gate.op =
          C.gates[j]?.map PEqualNP.CircuitLowerBounds.Gate.op) ∧
        (∀ (x : Fin n → Bool) j,
          (D.wires (List.ofFn x)).getD (n + j) false =
            (C.wires (List.ofFn (x ∘ e))).getD (n + j) false) ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e)))
    (orbit :
      let E := fun (u v : Fin 42) =>
        u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let canonical : Finset (Finset (Fin 42)) := {∅, {0}, {0, 1}, {0, 24}}
      ∀ Y : Finset (Fin 42), Y.card ≤ 2 →
        (∀ u ∈ Y, u.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) →
        ∃ e : Fin 42 ≃ Fin 42, (∀ u v, (E (e u) (e v) ∨ E (e v) (e u)) ↔ (E u v ∨ E v u)) ∧
          Y.map e.toEmbedding ∈ canonical)
    (bound :
      let E := fun (u v : Fin 42) =>
        u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let canonical : Finset (Finset (Fin 42)) := {∅, {0}, {0, 1}, {0, 24}}
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin 42)), Y ∈ canonical →
        PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 124 →
        (∃ j g, D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (D.wires (List.ofFn fun i => decide (i ∈ Y))).getD (42 + j) false = true) →
        ∃ x : Fin 42 → Bool, ¬ (D.eval (List.ofFn x) = true ↔
          ∃ u v, E u v ∧ x u = true ∧ x v = true)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
    (gs.foldl step (List.ofFn x)).getD i false

  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, List.length_cons]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

  have val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
      val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
    unfold val
    by_cases h : i < n
    · simp [List.getD_eq_getElem?_getD, h]
    · simp [List.getD_eq_getElem?_getD, h]

  have val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
      val (gs ++ [g]) x i =
        if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
        else val gs x i := by
    unfold val
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, step]
    have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
      rw [fold_length]
      simp
    simp only [step, List.getD_eq_getElem?_getD] at hl
    rcases lt_trichotomy i (n + gs.length) with h | h | h
    · rw [ite_eq_right (by omega)]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · rw [ite_eq_left h]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp [hl, h]
    · rw [ite_eq_right (by omega)]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

  have val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
      val gs x i = false := by
    unfold val
    have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
      rw [fold_length]
      simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

  have val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
      val gs x i = x ⟨i, hi⟩ := by
    induction gs using List.reverseRecOn with
    | nil =>
      rw [val_nil]
      simp [hi]
    | append_singleton gs g ih =>
      rw [val_snoc, ite_eq_right (by omega)]
      exact ih

  have val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
      ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
        gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
    induction gs using List.reverseRecOn with
    | nil =>
      intro k hk
      simp at hk
    | append_singleton gs g ih =>
      intro k hk
      by_cases hkl : k = gs.length
      · subst hkl
        have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
        rw [hgl, val_snoc, ite_eq_left rfl]
        congr 1
        apply List.map_congr_left
        intro j _
        by_cases hj : j < n + gs.length
        · rw [ite_eq_left hj, val_snoc, ite_eq_right (by omega)]
        · rw [ite_eq_right hj, val_ge gs x j (by omega)]
      · have hk' : k < gs.length + 1 := by simpa using hk
        have hk2 : k < gs.length := by omega
        have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
        rw [hget, val_snoc, ite_eq_right (by omega), ih k hk2]
        congr 1
        apply List.map_congr_left
        intro j _
        by_cases hj : j < n + k
        · rw [ite_eq_left hj, ite_eq_left hj, val_snoc, ite_eq_right (by omega)]
        · rw [ite_eq_right hj, ite_eq_right hj]

  have eval_and (values : List Bool) : GateOp.and.eval values = values.all id := rfl
  have eval_or (values : List Bool) : GateOp.or.eval values = values.any id := rfl

  have eval_mono (op : GateOp) (hop : op = .and ∨ op = .or)
      (inputs : List ℕ) (f g : ℕ → Bool)
      (hfg : ∀ a ∈ inputs, f a = true → g a = true)
      (hf : op.eval (inputs.map f) = true) : op.eval (inputs.map g) = true := by
    rcases hop with rfl | rfl
    · simp only [eval_and, List.all_eq_true, id_eq] at hf ⊢
      intro z hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact hfg a ha (hf _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
    · simp only [eval_or, List.any_eq_true, id_eq] at hf ⊢
      obtain ⟨z, hz, htrue⟩ := hf
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact ⟨g a, List.mem_map.mpr ⟨a, ha, rfl⟩, hfg a ha htrue⟩

  have mono {n : ℕ} (gs : List Gate)
      (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
      ∀ i, val gs x i = true → val gs x' i = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h₀ : i < n
      · rw [val_lt gs x i h₀] at hi
        rw [val_lt gs x' i h₀]
        exact hle _ hi
      by_cases h₁ : n + gs.length ≤ i
      · rw [val_ge gs x i h₁] at hi
        contradiction
      obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      have hk : k < gs.length := by omega
      rw [val_gate gs x k hk] at hi
      rw [val_gate gs x' k hk]
      refine eval_mono _ (hg _ (List.getElem_mem hk)).1 _ _ _ ?_ hi
      intro a _ ha
      by_cases hl : a < n + k
      · rw [ite_eq_left hl] at ha ⊢
        exact ih a hl ha
      · simp [hl] at ha

  let ga (G : List Gate) (j : ℕ) : Gate := G.getD j ⟨GateOp.or, []⟩

  have ga_lt (G : List Gate) (j : ℕ) (hj : j < G.length) : ga G j = G[j] := by
    unfold ga
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl

  have ga_ge (G : List Gate) (j : ℕ) (hj : G.length ≤ j) : ga G j = ⟨GateOp.or, []⟩ := by
    unfold ga
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
    rfl

  have val_ga {n : ℕ} (G : List Gate) (x : Fin n → Bool) (k : ℕ) :
      val G x (n + k) =
        (ga G k).op.eval ((ga G k).inputs.map fun j => if j < n + k then val G x j else false) := by
    by_cases hk : k < G.length
    · rw [ga_lt G k hk]
      exact val_gate G x k hk
    · rw [ga_ge G k (by omega), val_ge G x _ (by omega)]
      rfl

  have op_ao (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) (j : ℕ) :
      (ga C.gates j).op = GateOp.and ∨ (ga C.gates j).op = GateOp.or := by
    by_cases hj : j < C.gates.length
    · rw [ga_lt _ _ hj]
      have h := (hM _ (List.getElem_mem hj)).1
      simpa using h
    · rw [ga_ge _ _ (by omega)]
      exact Or.inr rfl

  let inputOf {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : Bool :=
    decide (v ∈ S)

  have trace_or {n : ℕ} (C : Circuit) (hM : Monotone2 C)
      (x : Fin n → Bool) (j : ℕ)
      (hearlier : ∀ k < j, (ga C.gates k).op = GateOp.and → val C.gates x (n + k) ≠ true) :
      ∀ i < n + j, val C.gates x i = true →
        ∃ v : Fin n, x v = true ∧ val C.gates (inputOf {v}) i = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi hx
      by_cases hin : i < n
      · exact ⟨⟨i, hin⟩, by simpa only [val_lt _ _ _ hin] using hx,
          by simp [val_lt _ _ _ hin, inputOf]⟩
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < j := by omega
        rcases op_ao C hM k with hAnd | hOr
        · exact False.elim (hearlier k hk hAnd hx)
        · rw [val_ga, hOr, eval_or, List.any_eq_true] at hx
          obtain ⟨b, hb, hv⟩ := hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
          split at hv
          next ha' =>
            obtain ⟨v, hv₀, hv₁⟩ := ih a ha' (by omega) hv
            refine ⟨v, hv₀, ?_⟩
            rw [val_ga, hOr, eval_or, List.any_eq_true]
            exact ⟨true, List.mem_map.mpr ⟨a, ha, by simp [ha', hv₁]⟩, rfl⟩
          next => contradiction

  have first_true_and_has_two_inputs {n : ℕ} (C : Circuit) (hM : Monotone2 C)
      (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length)
      (hAnd : (ga C.gates j).op = GateOp.and)
      (hx : val C.gates x (n + j) = true)
      (hearlier : ∀ k < j, (ga C.gates k).op = GateOp.and → val C.gates x (n + k) ≠ true) :
      ∃ S : Finset (Fin n), S.card ≤ 2 ∧ (∀ v ∈ S, x v = true) ∧
        val C.gates (inputOf S) (n + j) = true := by
    classical
    rw [val_ga, hAnd, eval_and, List.all_eq_true] at hx
    have hWitness (a : ℕ) (ha : a ∈ (ga C.gates j).inputs) :
        ∃ v : Fin n, x v = true ∧ a < n + j ∧ val C.gates (inputOf {v}) a = true := by
      have hv := hx _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
      split at hv
      next ha' =>
        obtain ⟨v, hxv, hval⟩ := trace_or C hM x j hearlier a ha' (by simpa using hv)
        exact ⟨v, hxv, ha', hval⟩
      next => simp at hv
    let U := (ga C.gates j).inputs.toFinset
    choose witness hSub hBackward hVal using
      fun a : U => hWitness a.val (List.mem_toFinset.mp a.property)
    let S := U.attach.image fun a => witness a
    have hLen := (hM _ (List.getElem_mem hj)).2
    have hLen' : U.card ≤ 2 := by
      exact (List.toFinset_card_le _).trans (by simpa [ga_lt _ _ hj] using hLen)
    refine ⟨S, (Finset.card_image_le.trans (by simpa using hLen')), ?_, ?_⟩
    · intro v hv
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
      exact hSub w
    · rw [val_ga, hAnd, eval_and, List.all_eq_true]
      intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      let a' : U := ⟨a, by simpa [U] using ha⟩
      rw [ite_eq_left (hBackward a')]
      have hOps : ∀ g ∈ C.gates,
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        simpa using hM g hg
      have hMon : ∀ v, inputOf {witness a'} v = true → inputOf S v = true := by
        intro v hv
        have heq : v = witness a' := by simpa [inputOf] using hv
        subst v
        exact decide_eq_true (Finset.mem_image.mpr ⟨a', Finset.mem_attach _ _, rfl⟩)
      simpa using mono C.gates hOps _ _ hMon a (hVal a')

  have no_true_and_if_all_small_inputs_fail {n : ℕ} (C : Circuit) (hM : Monotone2 C)
      (x : Fin n → Bool)
      (hSmall : ∀ (S : Finset (Fin n)), S.card ≤ 2 → (∀ v ∈ S, x v = true) →
        ∀ j < C.gates.length, (ga C.gates j).op = GateOp.and →
          val C.gates (inputOf S) (n + j) ≠ true) :
      ∀ j < C.gates.length, (ga C.gates j).op = GateOp.and → val C.gates x (n + j) ≠ true := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hAnd hx
      obtain ⟨S, hCard, hSub, hVal⟩ :=
        first_true_and_has_two_inputs C hM x hj hAnd hx
          (fun k hk => ih k hk (hk.trans hj))
      exact hSmall S hCard hSub j hj hAnd hVal


  have sparse_support (n : ℕ) (C : Circuit) (hM : Monotone2 C) :
      let active := fun (X : Finset (Fin n)) => ∃ j g,
        C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (C.wires (List.ofFn fun i => decide (i ∈ X))).getD (n + j) false = true
      ∀ X : Finset (Fin n), active X → ∃ Y ⊆ X, Y.card ≤ 2 ∧ active Y := by
    dsimp only
    intro X hX
    by_contra notSmall
    obtain ⟨j, g, hg, hAnd, hv⟩ := hX
    have hj : j < C.gates.length := by
      by_contra H
      rw [List.getElem?_eq_none (by omega)] at hg
      contradiction
    have hg' : C.gates[j] = g := Option.some.inj (by simpa [List.getElem?_eq_getElem hj] using hg)
    have hf : ∀ k < C.gates.length, (ga C.gates k).op = GateOp.and →
        val C.gates (inputOf X) (n + k) ≠ true := by
      apply no_true_and_if_all_small_inputs_fail C hM (inputOf X)
      intro S hcard hsub k hk hAnd' hVal
      apply notSmall
      exact ⟨S, fun v hv' => of_decide_eq_true (hsub v hv'), hcard, k, C.gates[k],
        List.getElem?_eq_getElem hk, by simpa only [ga_lt _ _ hk] using hAnd', hVal⟩
    exact hf j hj (by rw [ga_lt _ _ hj, hg']; exact hAnd) hv
  intro C hMono hsize active
  by_contra bad
  let E := fun (u v : Fin 42) =>
    u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  let S : Finset (Fin 42) := Finset.univ.filter
    (fun v => v.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))
  have correct (x : Fin 42 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true := by
    by_contra h
    exact bad ⟨x, h⟩
  have hS : ∃ j g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (C.wires (List.ofFn fun i => decide (i ∈ S))).getD (42 + j) false = true := by
    have he : (fun i : Fin 42 => decide (i ∈ S)) =
        fun i : Fin 42 => decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) := by
      funext i
      simp [S]
    rw [he]
    exact active
  obtain ⟨Y, hYS, hCard, j, g, hg, hAnd, hVal⟩ := sparse_support 42 C hMono S hS
  obtain ⟨e, hPreserves, hCanon⟩ :=
    orbit Y hCard (fun i hi => (Finset.mem_filter.mp (hYS hi)).2)
  obtain ⟨D, hDmono, hDsize, hOps, hWires, hEval⟩ := rename 42 C e hMono
  have hDactive : ∃ j g, D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (D.wires (List.ofFn fun i => decide (i ∈ Y.map e.toEmbedding))).getD (42 + j) false = true := by
    have he : (fun i : Fin 42 => decide (i ∈ Y.map e.toEmbedding)) ∘ e =
        fun i : Fin 42 => decide (i ∈ Y) := by
      funext i
      simp [Function.comp_apply]
    have hv := hWires (fun i : Fin 42 => decide (i ∈ Y.map e.toEmbedding)) j
    rw [he, hVal] at hv
    have hOp := hOps j
    rw [hg] at hOp
    cases hd : D.gates[j]? with
    | none => simp [hd] at hOp
    | some g' =>
      exact ⟨j, g', hd, by simpa [hd] using hOp.trans (congrArg some hAnd), hv⟩
  have hDcorrect (x : Fin 42 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true := by
    rw [hEval, correct]
    constructor
    · rintro ⟨u, v, hu, hx, hy⟩
      rcases (hPreserves u v).2 (Or.inl hu) with h | h
      · exact ⟨e u, e v, h, hx, hy⟩
      · exact ⟨e v, e u, h, hy, hx⟩
    · rintro ⟨u, v, hu, hx, hy⟩
      have hsym : E (e.symm u) (e.symm v) ∨ E (e.symm v) (e.symm u) := by
        apply (hPreserves (e.symm u) (e.symm v)).1
        change E (e (e.symm u)) (e (e.symm v)) ∨ E (e (e.symm v)) (e (e.symm u))
        simpa only [Equiv.apply_symm_apply] using Or.inl hu
      have hx' : (x ∘ e) (e.symm u) = true := by simpa using hx
      have hy' : (x ∘ e) (e.symm v) = true := by simpa using hy
      rcases hsym with h | h
      · exact ⟨e.symm u, e.symm v, h, hx', hy'⟩
      · exact ⟨e.symm v, e.symm u, h, hy', hx'⟩
  obtain ⟨x, hx⟩ := bound D (Y.map e.toEmbedding) hCanon hDmono (hDsize ▸ hsize) hDactive
  exact hx (hDcorrect x)
