import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3122_319
    (h14 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5))
    (hNine : ∀ (a : Fin 9),
      (a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 4 ∨ a.val = 6) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, !x 0 || x a]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5))
    (hNot : ∀ (a b : Fin 9),
      ((a < b ∧ a.val ≠ 5 ∧ b.val ≠ 5 ∧ b.val ≠ 7 ∧ b.val ≠ 8) ∨
       (a.val = 1 ∧ (b.val = 5 ∨ b.val = 7 ∨ b.val = 8)) ∨
       (a.val = 2 ∧ (b.val = 7 ∨ b.val = 8)) ∨
       (a.val = 6 ∧ b.val = 7)) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x a || x b]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5))
    (hMono : ∀ (a b : Fin 9),
      ((a < b ∧ a.val ≠ 5 ∧ b.val ≠ 5 ∧ b.val ≠ 7 ∧ b.val ≠ 8) ∨
       (a.val = 1 ∧ (b.val = 5 ∨ b.val = 7 ∨ b.val = 8)) ∨
       (a.val = 2 ∧ (b.val = 7 ∨ b.val = 8)) ∨
       (a.val = 6 ∧ b.val = 7)) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x a || x b]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  classical
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
  intro x1 hlen C hCfan hCsize _
  let edgeF (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have eval_not (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len_foldW : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepW]
      omega
  have getD_app_lt : ∀ (w : List Bool) (b : Bool) (i : ℕ), i < w.length →
      (w ++ [b]).getD i false = w.getD i false := by
    intro w b i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_app_self : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have ofFn_read (x : Fin 9 → Bool) (i : Fin 9) :
      (List.ofFn x).getD i.val false = x i := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
      ↓reduceDIte, Option.getD_some]
  have x8_read_lt (x : Fin 9 → Bool) (i : Fin 9) :
      (List.ofFn x ++ [!x 0]).getD i.val false = x i := by
    rw [getD_app_lt (List.ofFn x) (!x 0) i.val (by simp [i.isLt])]
    exact ofFn_read x i
  have x8_read_9 (x : Fin 9 → Bool) :
      (List.ofFn x ++ [!x 0]).getD 9 false = !x 0 := by
    have h9 := getD_app_self (List.ofFn x) (!x 0)
    rwa [List.length_ofFn] at h9
  have x8_read_ge (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) :
      (List.ofFn x ++ [!x 0]).getD i false = false := by
    have hle : (List.ofFn x ++ [!x 0]).length ≤ i := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle, Option.getD_none]
  let evalSym (w' : List Bool) (sv : Bool ⊕ ℕ) : Bool :=
    Sum.elim id (fun i => w'.getD i false) sv
  let stepRes (syms : List (Bool ⊕ ℕ)) (gs : List Gate) (g : Gate) : (Bool ⊕ ℕ) × Option Gate :=
    let getS (i : ℕ) : Bool ⊕ ℕ := syms.getD i (Sum.inl false)
    GateOp.casesOn g.op
      (List.casesOn g.inputs (Sum.inl true, none) fun a rest =>
        List.casesOn rest (getS a, none) fun b _ =>
          Sum.elim
            (fun ba => bif ba then (getS b, none) else (Sum.inl false, none))
            (fun wa => Sum.elim
              (fun bb => bif bb then (Sum.inr wa, none) else (Sum.inl false, none))
              (fun wb => (Sum.inr (10 + gs.length), some ⟨GateOp.and, [wa, wb]⟩))
              (getS b))
            (getS a))
      (List.casesOn g.inputs (Sum.inl false, none) fun a rest =>
        List.casesOn rest (getS a, none) fun b _ =>
          Sum.elim
            (fun ba => bif ba then (Sum.inl true, none) else (getS b, none))
            (fun wa => Sum.elim
              (fun bb => bif bb then (Sum.inl true, none) else (Sum.inr wa, none))
              (fun wb => (Sum.inr (10 + gs.length), some ⟨GateOp.or, [wa, wb]⟩))
              (getS b))
            (getS a))
      (List.casesOn g.inputs (Sum.inl true, none) fun a _ =>
        Sum.elim
          (fun ba => (Sum.inl (!ba), none))
          (fun wa => (Sum.inr (10 + gs.length), some ⟨GateOp.not, [wa]⟩))
          (getS a))
      (fun _ => (Sum.inl false, none))
      (Sum.inl false, none)
  let stepSym (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
      List (Bool ⊕ ℕ) × List Gate :=
    let r := stepRes st.1 st.2 g
    Option.elim r.2 (st.1 ++ [r.1], st.2) (fun ng => (st.1 ++ [r.1], st.2 ++ [ng]))
  have elimWire10 : ∀ (s10 : Bool ⊕ ℕ),
      (∀ w, s10 = Sum.inr w → w < 10) →
      (∀ x : Fin 9 → Bool,
        let x8 := List.ofFn x ++ [!x 0]
        GateOp.or.eval (x1.map fun i => x8.getD i false) = evalSym x8 s10) →
      ∃ x : Fin 9 → Bool,
        let x8 := List.ofFn x ++ [!x 0]
        C.eval (x8 ++ [GateOp.or.eval (x1.map fun i => x8.getD i false)]) ≠ edgeF x := by
    intro s10 hs10_lt hs10_eq
    let syms0 : List (Bool ⊕ ℕ) := (List.range 10).map Sum.inr ++ [s10]
    have hfold_inv : ∀ pre : List Gate,
        (∀ g ∈ pre, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        let st := pre.foldl stepSym (syms0, [])
        st.1.length = 11 + pre.length ∧
        st.2.length ≤ pre.length ∧
        FanInTwo ⟨st.2, 0⟩ ∧
        (∀ i w, st.1.getD i (Sum.inl false) = Sum.inr w → w < 10 + st.2.length) ∧
        (∀ (x : Fin 9 → Bool) (i : ℕ),
          let x8 := List.ofFn x ++ [!x 0]
          (pre.foldl stepW (x8 ++ [evalSym x8 s10])).getD i false =
          evalSym (st.2.foldl stepW x8) (st.1.getD i (Sum.inl false))) := by
      intro pre
      induction pre using List.reverseRecOn with
      | nil =>
        intro _
        dsimp only [List.foldl_nil]
        refine ⟨by simp [syms0], le_refl 0, (fun g hg => by cases hg), ?_, ?_⟩
        · intro i w hi
          by_cases hlt : i < 10
          · have hget : syms0.getD i (Sum.inl false) = Sum.inr i := by
              rw [List.getD_eq_getElem?_getD]
              dsimp only [syms0]
              rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; exact hlt),
                List.getElem?_map, List.getElem?_range hlt]
              rfl
            rw [hget] at hi; cases hi; omega
          · by_cases heq : i = 10
            · subst heq
              have hget : syms0.getD 10 (Sum.inl false) = s10 := rfl
              rw [hget] at hi; have := hs10_lt w hi; omega
            · have hge : syms0.length ≤ i := by simp [syms0]; omega
              simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hi
              cases hi
        · intro x i
          set x8 := List.ofFn x ++ [!x 0]
          have hx8_len : x8.length = 10 := by simp [x8]
          by_cases hlt : i < 10
          · have hget : syms0.getD i (Sum.inl false) = Sum.inr i := by
              rw [List.getD_eq_getElem?_getD]
              dsimp only [syms0]
              rw [List.getElem?_append_left (by simp only [List.length_map, List.length_range]; exact hlt),
                List.getElem?_map, List.getElem?_range hlt]
              rfl
            rw [hget, getD_app_lt x8 _ i (by omega)]
            rfl
          · by_cases heq : i = 10
            · subst heq
              have hget : syms0.getD 10 (Sum.inl false) = s10 := rfl
              rw [hget, ← hx8_len, getD_app_self x8 _]
            · have hge1 : (x8 ++ [evalSym x8 s10]).length ≤ i := by simp [hx8_len]; omega
              have hge2 : syms0.length ≤ i := by simp [syms0]; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
                List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
              rfl
      | append_singleton pre g ih =>
        intro hfan
        have hpre_fan : ∀ g' ∈ pre, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
        have hg_fan := hfan g (by simp)
        obtain ⟨hlen1, hlen2, hfan_gs, hbound, hsem⟩ := ih hpre_fan
        set st := pre.foldl stepSym (syms0, [])
        dsimp only
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        set r := stepRes st.1 st.2 g with hr_def
        have hstep_sem : ∀ x : Fin 9 → Bool,
            let x8 := List.ofFn x ++ [!x 0]
            g.op.eval (g.inputs.map fun a => (pre.foldl stepW (x8 ++ [evalSym x8 s10])).getD a false) =
            evalSym ((Option.elim r.2 st.2 (fun ng => st.2 ++ [ng])).foldl stepW x8) r.1 ∧
            (∀ ng, r.2 = some ng →
              ng.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ng.inputs.length ≤ 2) ∧
            (∀ w, r.1 = Sum.inr w → w < 10 + (Option.elim r.2 st.2 (fun ng => st.2 ++ [ng])).length) := by
          intro x
          dsimp only
          set x8 := List.ofFn x ++ [!x 0]
          have hx8_len : x8.length = 10 := by simp [x8]
          set wNew := st.2.foldl stepW x8
          have hwNew_len : wNew.length = 10 + st.2.length := by rw [len_foldW, hx8_len]
          have hget : ∀ a : ℕ, (pre.foldl stepW (x8 ++ [evalSym x8 s10])).getD a false =
              evalSym wNew (st.1.getD a (Sum.inl false)) := hsem x
          have hop := hg_fan.1
          have hlen_in := hg_fan.2
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop_eq | hop_eq | hop_eq
          · rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · simp [hr_def, stepRes, hop_eq, hins, eval_and, evalSym]
            · simp only [hr_def, stepRes, hop_eq, hins, eval_and, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true, hget a]
              exact ⟨rfl, fun _ h => (by cases h), fun w hw => hbound a w hw⟩
            · simp only [hr_def, stepRes, hop_eq, hins, eval_and, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true, hget a, hget b]
              cases hsa : st.1.getD a (Sum.inl false) with
              | inl ba =>
                cases ba with
                | false => simp [evalSym]
                | true =>
                  cases hsb : st.1.getD b (Sum.inl false) with
                  | inl bb => cases bb <;> simp [evalSym]
                  | inr wb =>
                    refine ⟨by simp [evalSym, wNew], fun _ h => (by cases h), ?_⟩
                    intro w hw; cases hw; exact hbound b wb hsb
              | inr wa =>
                cases hsb : st.1.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb with
                  | false => simp [evalSym]
                  | true =>
                    refine ⟨by simp [evalSym, wNew], fun _ h => (by cases h), ?_⟩
                    intro w hw; cases hw; exact hbound a wa hsa
                | inr wb =>
                  refine ⟨?_, ?_, ?_⟩
                  · change (evalSym wNew (Sum.inr wa) && evalSym wNew (Sum.inr wb)) =
                      ((st.2 ++ [Gate.mk GateOp.and [wa, wb]]).foldl stepW x8).getD (10 + st.2.length) false
                    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                    change (evalSym wNew (Sum.inr wa) && evalSym wNew (Sum.inr wb)) =
                      (stepW wNew (Gate.mk GateOp.and [wa, wb])).getD (10 + st.2.length) false
                    rw [← hwNew_len]; dsimp only [stepW]; rw [getD_app_self wNew _]
                    simp only [eval_and, List.map_cons, List.map_nil, List.all_cons,
                      List.all_nil, id_eq, Bool.and_true, evalSym]
                    rfl
                  · intro ng hng; cases hng; simp
                  · intro w hw; cases hw; simp
            · rw [hins] at hlen_in; simp at hlen_in
          · rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · simp [hr_def, stepRes, hop_eq, hins, eval_or, evalSym]
            · simp only [hr_def, stepRes, hop_eq, hins, eval_or, List.map_cons, List.map_nil,
                List.any_cons, List.any_nil, id_eq, Bool.or_false, hget a]
              exact ⟨rfl, fun _ h => (by cases h), fun w hw => hbound a w hw⟩
            · simp only [hr_def, stepRes, hop_eq, hins, eval_or, List.map_cons, List.map_nil,
                List.any_cons, List.any_nil, id_eq, Bool.or_false, hget a, hget b]
              cases hsa : st.1.getD a (Sum.inl false) with
              | inl ba =>
                cases ba with
                | true => simp [evalSym]
                | false =>
                  cases hsb : st.1.getD b (Sum.inl false) with
                  | inl bb => cases bb <;> simp [evalSym]
                  | inr wb =>
                    refine ⟨by simp [evalSym, wNew], fun _ h => (by cases h), ?_⟩
                    intro w hw; cases hw; exact hbound b wb hsb
              | inr wa =>
                cases hsb : st.1.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb with
                  | true => simp [evalSym]
                  | false =>
                    refine ⟨by simp [evalSym, wNew], fun _ h => (by cases h), ?_⟩
                    intro w hw; cases hw; exact hbound a wa hsa
                | inr wb =>
                  refine ⟨?_, ?_, ?_⟩
                  · change (evalSym wNew (Sum.inr wa) || evalSym wNew (Sum.inr wb)) =
                      ((st.2 ++ [Gate.mk GateOp.or [wa, wb]]).foldl stepW x8).getD (10 + st.2.length) false
                    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                    change (evalSym wNew (Sum.inr wa) || evalSym wNew (Sum.inr wb)) =
                      (stepW wNew (Gate.mk GateOp.or [wa, wb])).getD (10 + st.2.length) false
                    rw [← hwNew_len]; dsimp only [stepW]; rw [getD_app_self wNew _]
                    simp only [eval_or, List.map_cons, List.map_nil, List.any_cons,
                      List.any_nil, id_eq, Bool.or_false, evalSym]
                    rfl
                  · intro ng hng; cases hng; simp
                  · intro w hw; cases hw; simp
            · rw [hins] at hlen_in; simp at hlen_in
          · rcases hins : g.inputs with _ | ⟨a, rest⟩
            · simp [hr_def, stepRes, hop_eq, hins, eval_not, evalSym]
            · simp only [hr_def, stepRes, hop_eq, hins, eval_not, List.map_cons, List.headD_cons, hget a]
              cases hsa : st.1.getD a (Sum.inl false) with
              | inl ba => simp [evalSym]
              | inr wa =>
                refine ⟨?_, ?_, ?_⟩
                · change (!(evalSym wNew (Sum.inr wa))) =
                    ((st.2 ++ [Gate.mk GateOp.not [wa]]).foldl stepW x8).getD (10 + st.2.length) false
                  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                  change (!(evalSym wNew (Sum.inr wa))) =
                    (stepW wNew (Gate.mk GateOp.not [wa])).getD (10 + st.2.length) false
                  rw [← hwNew_len]; dsimp only [stepW]; rw [getD_app_self wNew _]
                  simp only [eval_not, List.map_cons, List.map_nil, List.headD_cons, evalSym]
                  rfl
                · intro ng hng; cases hng; simp
                · intro w hw; cases hw; simp
        cases hr2 : r.2 with
        | none =>
          have hst_eq : stepSym st g = (st.1 ++ [r.1], st.2) := by simp [stepSym, ← hr_def, hr2]
          rw [hst_eq]
          dsimp only
          refine ⟨by simp [hlen1]; omega, by simp; omega, hfan_gs, ?_, ?_⟩
          · intro i w hi
            by_cases hlt : i < st.1.length
            · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
                ← List.getD_eq_getElem?_getD] at hi
              exact hbound i w hi
            · by_cases heq : i = st.1.length
              · subst heq
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)] at hi
                simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
                simpa [hr2] using (hstep_sem (fun _ => false)).2.2 w hi
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
                  Option.getD_none] at hi
                cases hi
          · intro x i
            set x8 := List.ofFn x ++ [!x 0]
            have hx8_len : x8.length = 10 := by simp [x8]
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            by_cases hlt : i < 11 + pre.length
            · have hltW : i < (pre.foldl stepW (x8 ++ [evalSym x8 s10])).length := by
                rw [len_foldW]; simp [hx8_len]; omega
              rw [getD_app_lt _ _ i hltW]
              have hget1 : (st.1 ++ [r.1]).getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < st.1.length)]
              rw [hget1]; exact hsem x i
            · by_cases heq : i = 11 + pre.length
              · subst heq
                have hlenW : (pre.foldl stepW (x8 ++ [evalSym x8 s10])).length = 11 + pre.length := by
                  rw [len_foldW]; simp [hx8_len]
                have h1 : (stepW (pre.foldl stepW (x8 ++ [evalSym x8 s10])) g).getD (11 + pre.length) false =
                    g.op.eval (g.inputs.map fun a => (pre.foldl stepW (x8 ++ [evalSym x8 s10])).getD a false) := by
                  rw [← hlenW]; exact getD_app_self _ _
                rw [h1]
                have hget1 : (st.1 ++ [r.1]).getD (11 + pre.length) (Sum.inl false) = r.1 := by
                  rw [List.getD_eq_getElem?_getD, ← hlen1, List.getElem?_append_right (le_refl _)]; simp
                rw [hget1]
                have hst1 := (hstep_sem x).1
                rw [hr2] at hst1
                exact hst1
              · have hgeW : (stepW (pre.foldl stepW (x8 ++ [evalSym x8 s10])) g).length ≤ i := by
                  simp only [stepW, List.length_append, List.length_cons, List.length_nil, len_foldW]
                  simp [hx8_len]; omega
                have hgeS : (st.1 ++ [r.1]).length ≤ i := by simp [hlen1]; omega
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgeW,
                  List.getD_eq_getElem?_getD, List.getElem?_eq_none hgeS]
                rfl
        | some ng =>
          have hst_eq : stepSym st g = (st.1 ++ [r.1], st.2 ++ [ng]) := by simp [stepSym, ← hr_def, hr2]
          rw [hst_eq]
          dsimp only
          refine ⟨by simp [hlen1]; omega, by simp; omega, ?_, ?_, ?_⟩
          · intro g' hg'
            simp only [List.mem_append, List.mem_singleton] at hg'
            rcases hg' with hg' | hg_eq
            · exact hfan_gs g' hg'
            · rw [hg_eq]; exact (hstep_sem (fun _ => false)).2.1 ng hr2
          · intro i w hi
            by_cases hlt : i < st.1.length
            · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
                ← List.getD_eq_getElem?_getD] at hi
              have := hbound i w hi; simp; omega
            · by_cases heq : i = st.1.length
              · subst heq
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)] at hi
                simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
                simpa [hr2] using (hstep_sem (fun _ => false)).2.2 w hi
              · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
                  Option.getD_none] at hi
                cases hi
          · intro x i
            set x8 := List.ofFn x ++ [!x 0]
            have hx8_len : x8.length = 10 := by simp [x8]
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            by_cases hlt : i < 11 + pre.length
            · have hltW : i < (pre.foldl stepW (x8 ++ [evalSym x8 s10])).length := by
                rw [len_foldW]; simp [hx8_len]; omega
              rw [getD_app_lt _ _ i hltW]
              have hget1 : (st.1 ++ [r.1]).getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < st.1.length)]
              rw [hget1, hsem x i]
              cases hsv : st.1.getD i (Sum.inl false) with
              | inl b => rfl
              | inr w =>
                have hw_lt : w < (st.2.foldl stepW x8).length := by
                  rw [len_foldW, hx8_len]; exact hbound i w hsv
                simp only [evalSym, List.foldl_append, List.foldl_cons, List.foldl_nil]
                exact (getD_app_lt _ _ w hw_lt).symm
            · by_cases heq : i = 11 + pre.length
              · subst heq
                have hlenW : (pre.foldl stepW (x8 ++ [evalSym x8 s10])).length = 11 + pre.length := by
                  rw [len_foldW]; simp [hx8_len]
                have h1 : (stepW (pre.foldl stepW (x8 ++ [evalSym x8 s10])) g).getD (11 + pre.length) false =
                    g.op.eval (g.inputs.map fun a => (pre.foldl stepW (x8 ++ [evalSym x8 s10])).getD a false) := by
                  rw [← hlenW]; exact getD_app_self _ _
                rw [h1]
                have hget1 : (st.1 ++ [r.1]).getD (11 + pre.length) (Sum.inl false) = r.1 := by
                  rw [List.getD_eq_getElem?_getD, ← hlen1, List.getElem?_append_right (le_refl _)]; simp
                rw [hget1]
                have hst1 := (hstep_sem x).1
                rw [hr2] at hst1
                exact hst1
              · have hgeW : (stepW (pre.foldl stepW (x8 ++ [evalSym x8 s10])) g).length ≤ i := by
                  simp only [stepW, List.length_append, List.length_cons, List.length_nil, len_foldW]
                  simp [hx8_len]; omega
                have hgeS : (st.1 ++ [r.1]).length ≤ i := by simp [hlen1]; omega
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgeW,
                  List.getD_eq_getElem?_getD, List.getElem?_eq_none hgeS]
                rfl
    obtain ⟨_, hlen2, hfan2, _, hsemF⟩ := hfold_inv C.gates (fun g hg => hCfan g hg)
    set stF := C.gates.foldl stepSym (syms0, [])
    have hevalF : ∀ x : Fin 9 → Bool,
        let x8 := List.ofFn x ++ [!x 0]
        C.eval (x8 ++ [GateOp.or.eval (x1.map fun i => x8.getD i false)]) =
        evalSym (stF.2.foldl stepW x8) (stF.1.getD C.output (Sum.inl false)) := by
      intro x
      dsimp only
      rw [hs10_eq x]
      exact hsemF x C.output
    cases hout : stF.1.getD C.output (Sum.inl false) with
    | inl b =>
      cases b with
      | true =>
        refine ⟨fun _ => false, ?_⟩
        dsimp only
        rw [hevalF (fun _ => false), hout]
        change true ≠ edgeF (fun _ => false)
        decide
      | false =>
        refine ⟨fun i => decide (i.val = 0 ∨ i.val = 1), ?_⟩
        dsimp only
        rw [hevalF (fun i => decide (i.val = 0 ∨ i.val = 1)), hout]
        change false ≠ edgeF (fun i => decide (i.val = 0 ∨ i.val = 1))
        decide
    | inr w =>
      let D : Circuit := ⟨Gate.mk GateOp.not [0] :: stF.2, w⟩
      have hDfan : FanInTwo D := by
        intro g hg
        change g ∈ Gate.mk GateOp.not [0] :: stF.2 at hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨by simp, by simp⟩
        · exact hfan2 g hg
      have hDsize : D.size ≤ 14 := by
        change (Gate.mk GateOp.not [0] :: stF.2).length ≤ 14
        change C.gates.length ≤ 13 at hCsize
        simp only [List.length_cons]
        omega
      obtain ⟨x, hx⟩ := h14 D hDfan hDsize
      refine ⟨x, ?_⟩
      dsimp only
      rw [hevalF x, hout]
      have hDeval : D.eval (List.ofFn x) = evalSym (stF.2.foldl stepW (List.ofFn x ++ [!x 0])) (Sum.inr w) := by
        dsimp only [Circuit.eval, Circuit.wires, D]
        rw [List.foldl_cons]
        have hstep0 : stepW (List.ofFn x) (Gate.mk GateOp.not [0]) = List.ofFn x ++ [!x 0] := by
          dsimp only [stepW]
          rw [List.map_cons, List.map_nil, eval_not, List.headD_cons]
          exact congrArg (fun b => List.ofFn x ++ [!b]) (ofFn_read x 0)
        change (stF.2.foldl stepW (stepW (List.ofFn x) (Gate.mk GateOp.not [0]))).getD w false = _
        rw [hstep0]
        rfl
      rw [← hDeval]
      exact hx
  let perm (i : ℕ) : ℕ := if i < 9 then [0, 5, 8, 3, 4, 1, 7, 6, 2].getD i 0 else i
  have perm_small (i : ℕ) (hi : i < 9) : perm i < 9 := by
    interval_cases i <;> decide
  have perm_large (i : ℕ) (hi : 9 ≤ i) : perm i = i := by
    simp [perm, show ¬i < 9 by omega]
  have perm_lt (i m : ℕ) (hm : 9 ≤ m) : perm i < m ↔ i < m := by
    by_cases hi : i < 9
    · have hp := perm_small i hi; omega
    · rw [perm_large i (by omega)]
  let rho : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  have rho_val (i : Fin 9) : (rho i).val = perm i.val := by
    fin_cases i <;> rfl
  have graph_inv : ∀ x : Fin 9 → Bool, edgeF (fun i => x (rho i)) = edgeF x := by
    dsimp only [edgeF, rho]
    decide +kernel
  let renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map perm⟩
  let renameCircuit (D : Circuit) : Circuit := ⟨D.gates.map renameGate, perm D.output⟩
  have app_rel (v1 v2 : List Bool) (b : Bool) (hlenv : v1.length = v2.length) (h9 : 9 ≤ v1.length)
      (hrel : ∀ i, v1.getD i false = v2.getD (perm i) false) :
      ∀ i, (v1 ++ [b]).getD i false = (v2 ++ [b]).getD (perm i) false := by
    intro i
    by_cases hi : i < v1.length
    · rw [List.getD_append _ _ _ _ hi,
        List.getD_append _ _ _ _ (by rw [← hlenv]; exact (perm_lt i _ h9).2 hi)]
      exact hrel i
    · rw [perm_large i (by omega), List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hlenv]
  have run_rel (gs : List Gate) (v1 v2 : List Bool) (hlenv : v1.length = v2.length) (h9 : 9 ≤ v1.length)
      (hrel : ∀ i, v1.getD i false = v2.getD (perm i) false) :
      ∀ i, (gs.foldl stepW v1).getD i false = ((gs.map renameGate).foldl stepW v2).getD (perm i) false := by
    induction gs generalizing v1 v2 with
    | nil => exact hrel
    | cons g gs ih =>
      have hv : g.op.eval (g.inputs.map fun i => v1.getD i false) =
          (renameGate g).op.eval ((renameGate g).inputs.map fun i => v2.getD i false) := by
        simp only [renameGate, List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => hrel i)
      simp only [List.map_cons, List.foldl_cons]
      change ∀ i, (gs.foldl stepW (v1 ++ [_])).getD i false =
        ((gs.map renameGate).foldl stepW (v2 ++ [_])).getD (perm i) false
      rw [← hv]
      exact ih _ _ (by simp [hlenv]) (by simp; omega) (app_rel v1 v2 _ hlenv h9 hrel)
  have pref_rel (x : Fin 9 → Bool) (b1 b2 : Bool) :
      ∀ i, (List.ofFn (fun j => x (rho j)) ++ [b1, b2]).getD i false =
        (List.ofFn x ++ [b1, b2]).getD (perm i) false := by
    intro i
    by_cases hi : i < 9
    · rw [List.getD_append _ _ _ _ (by simpa),
        List.getD_append _ _ _ _ (by simpa using perm_small i hi)]
      have h := (ofFn_read (fun j => x (rho j)) ⟨i, hi⟩).trans (ofFn_read x (rho ⟨i, hi⟩)).symm
      simpa only [rho_val] using h
    · rw [perm_large i (by omega), List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      simp
  have rename_props (D : Circuit) (hDf : FanInTwo D) :
      FanInTwo (renameCircuit D) ∧ (renameCircuit D).size = D.size ∧
      ((∃ g ∈ D.gates, g.op = GateOp.not) ↔ (∃ g ∈ (renameCircuit D).gates, g.op = GateOp.not)) := by
    refine ⟨?_, by change (D.gates.map renameGate).length = D.gates.length; simp only [List.length_map], ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      simpa [renameGate] using hDf g' hg'
    · constructor
      · rintro ⟨g, hg, hop⟩
        exact ⟨renameGate g, List.mem_map_of_mem hg, hop⟩
      · rintro ⟨g, hg, hop⟩
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact ⟨g', hg', hop⟩
  have solve_nine : ∀ (a : Fin 9), a.val ≠ 0 →
      (∀ x : Fin 9 → Bool,
        let x8 := List.ofFn x ++ [!x 0]
        GateOp.or.eval (x1.map fun i => x8.getD i false) = (!x 0 || x a)) →
      ∃ x : Fin 9 → Bool,
        let x8 := List.ofFn x ++ [!x 0]
        C.eval (x8 ++ [GateOp.or.eval (x1.map fun i => x8.getD i false)]) ≠ edgeF x := by
    intro a ha0 hval
    have hfin : a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 4 ∨ a.val = 5 ∨ a.val = 6 ∨ a.val = 7 ∨ a.val = 8 := by
      omega
    rcases hfin with h | h | h | h | h | h | h | h
    · obtain ⟨x, hx⟩ := hNine a (by omega) C hCfan hCsize
      refine ⟨x, ?_⟩; dsimp only; rw [hval x]; simpa only [List.append_assoc, List.singleton_append] using hx
    · obtain ⟨x, hx⟩ := hNine a (by omega) C hCfan hCsize
      refine ⟨x, ?_⟩; dsimp only; rw [hval x]; simpa only [List.append_assoc, List.singleton_append] using hx
    · obtain ⟨x, hx⟩ := hNine a (by omega) C hCfan hCsize
      refine ⟨x, ?_⟩; dsimp only; rw [hval x]; simpa only [List.append_assoc, List.singleton_append] using hx
    · obtain ⟨x, hx⟩ := hNine a (by omega) C hCfan hCsize
      refine ⟨x, ?_⟩; dsimp only; rw [hval x]; simpa only [List.append_assoc, List.singleton_append] using hx
    · obtain ⟨hRf, hRs, _⟩ := rename_props C hCfan
      have hrho : (rho a).val = 1 := by
        have hae : a = ⟨5, by omega⟩ := Fin.ext h
        rw [hae]; rfl
      obtain ⟨x, hx⟩ := hNine (rho a) (Or.inl hrho) (renameCircuit C) hRf (by omega)
      refine ⟨fun j => x (rho j), ?_⟩
      dsimp only
      rw [hval (fun j => x (rho j)), graph_inv x]
      have hrel := run_rel C.gates
        (List.ofFn (fun j => x (rho j)) ++ [!x 0, !x 0 || x (rho a)])
        (List.ofFn x ++ [!x 0, !x 0 || x (rho a)]) (by simp) (by simp) (pref_rel x _ _) C.output
      have hrho0 : rho 0 = 0 := rfl
      rw [hrho0]
      change (C.gates.foldl stepW ((List.ofFn (fun j => x (rho j)) ++ [!x 0]) ++ [!x 0 || x (rho a)])).getD C.output false ≠ _
      rw [List.append_assoc, List.singleton_append, hrel]
      exact hx
    · obtain ⟨x, hx⟩ := hNine a (by omega) C hCfan hCsize
      refine ⟨x, ?_⟩; dsimp only; rw [hval x]; simpa only [List.append_assoc, List.singleton_append] using hx
    · obtain ⟨hRf, hRs, _⟩ := rename_props C hCfan
      have hrho : (rho a).val = 6 := by
        have hae : a = ⟨7, by omega⟩ := Fin.ext h
        rw [hae]; rfl
      obtain ⟨x, hx⟩ := hNine (rho a) (Or.inr (Or.inr (Or.inr (Or.inr hrho)))) (renameCircuit C) hRf (by omega)
      refine ⟨fun j => x (rho j), ?_⟩
      dsimp only
      rw [hval (fun j => x (rho j)), graph_inv x]
      have hrel := run_rel C.gates
        (List.ofFn (fun j => x (rho j)) ++ [!x 0, !x 0 || x (rho a)])
        (List.ofFn x ++ [!x 0, !x 0 || x (rho a)]) (by simp) (by simp) (pref_rel x _ _) C.output
      have hrho0 : rho 0 = 0 := rfl
      rw [hrho0]
      change (C.gates.foldl stepW ((List.ofFn (fun j => x (rho j)) ++ [!x 0]) ++ [!x 0 || x (rho a)])).getD C.output false ≠ _
      rw [List.append_assoc, List.singleton_append, hrel]
      exact hx
    · obtain ⟨hRf, hRs, _⟩ := rename_props C hCfan
      have hrho : (rho a).val = 2 := by
        have hae : a = ⟨8, by omega⟩ := Fin.ext h
        rw [hae]; rfl
      obtain ⟨x, hx⟩ := hNine (rho a) (Or.inr (Or.inl hrho)) (renameCircuit C) hRf (by omega)
      refine ⟨fun j => x (rho j), ?_⟩
      dsimp only
      rw [hval (fun j => x (rho j)), graph_inv x]
      have hrel := run_rel C.gates
        (List.ofFn (fun j => x (rho j)) ++ [!x 0, !x 0 || x (rho a)])
        (List.ofFn x ++ [!x 0, !x 0 || x (rho a)]) (by simp) (by simp) (pref_rel x _ _) C.output
      have hrho0 : rho 0 = 0 := rfl
      rw [hrho0]
      change (C.gates.foldl stepW ((List.ofFn (fun j => x (rho j)) ++ [!x 0]) ++ [!x 0 || x (rho a)])).getD C.output false ≠ _
      rw [List.append_assoc, List.singleton_append, hrel]
      exact hx
  have solve_canon : ∀ (a b : Fin 9),
      ((a.val < b.val ∧ a.val ≠ 5 ∧ b.val ≠ 5 ∧ b.val ≠ 7 ∧ b.val ≠ 8) ∨
       (a.val = 1 ∧ (b.val = 5 ∨ b.val = 7 ∨ b.val = 8)) ∨
       (a.val = 2 ∧ (b.val = 7 ∨ b.val = 8)) ∨
       (a.val = 6 ∧ b.val = 7)) →
      ∀ (D : Circuit), FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x a || x b]) ≠ edgeF x := by
    intro a b hcan D hDf hDs
    by_cases hhas : ∃ g ∈ D.gates, g.op = GateOp.not
    · exact hNot a b hcan D hDf hDs hhas
    · push Not at hhas
      exact hMono a b hcan D hDf hDs hhas
  have solve_pair : ∀ (a b : Fin 9), a.val < b.val →
      (∀ x : Fin 9 → Bool,
        let x8 := List.ofFn x ++ [!x 0]
        GateOp.or.eval (x1.map fun i => x8.getD i false) = (x a || x b)) →
      ∃ x : Fin 9 → Bool,
        let x8 := List.ofFn x ++ [!x 0]
        C.eval (x8 ++ [GateOp.or.eval (x1.map fun i => x8.getD i false)]) ≠ edgeF x := by
    intro a b hab hval
    by_cases hcan :
        ((a.val < b.val ∧ a.val ≠ 5 ∧ b.val ≠ 5 ∧ b.val ≠ 7 ∧ b.val ≠ 8) ∨
         (a.val = 1 ∧ (b.val = 5 ∨ b.val = 7 ∨ b.val = 8)) ∨
         (a.val = 2 ∧ (b.val = 7 ∨ b.val = 8)) ∨
         (a.val = 6 ∧ b.val = 7))
    · obtain ⟨x, hx⟩ := solve_canon a b hcan C hCfan hCsize
      refine ⟨x, ?_⟩
      dsimp only
      rw [hval x]
      simpa only [List.append_assoc, List.singleton_append] using hx
    · let a' : Fin 9 := if (rho a).val < (rho b).val then rho a else rho b
      let b' : Fin 9 := if (rho a).val < (rho b).val then rho b else rho a
      have hcan_all : ∀ u v : Fin 9, u.val < v.val →
          ¬((u.val < v.val ∧ u.val ≠ 5 ∧ v.val ≠ 5 ∧ v.val ≠ 7 ∧ v.val ≠ 8) ∨
            (u.val = 1 ∧ (v.val = 5 ∨ v.val = 7 ∨ v.val = 8)) ∨
            (u.val = 2 ∧ (v.val = 7 ∨ v.val = 8)) ∨
            (u.val = 6 ∧ v.val = 7)) →
          let ru := if (rho u).val < (rho v).val then rho u else rho v
          let rv := if (rho u).val < (rho v).val then rho v else rho u
          ((ru.val < rv.val ∧ ru.val ≠ 5 ∧ rv.val ≠ 5 ∧ rv.val ≠ 7 ∧ rv.val ≠ 8) ∨
           (ru.val = 1 ∧ (rv.val = 5 ∨ rv.val = 7 ∨ rv.val = 8)) ∨
           (ru.val = 2 ∧ (rv.val = 7 ∨ rv.val = 8)) ∨
           (ru.val = 6 ∧ rv.val = 7)) := by
        dsimp only [rho]
        decide +kernel
      have hcan' :
          ((a'.val < b'.val ∧ a'.val ≠ 5 ∧ b'.val ≠ 5 ∧ b'.val ≠ 7 ∧ b'.val ≠ 8) ∨
           (a'.val = 1 ∧ (b'.val = 5 ∨ b'.val = 7 ∨ b'.val = 8)) ∨
           (a'.val = 2 ∧ (b'.val = 7 ∨ b'.val = 8)) ∨
           (a'.val = 6 ∧ b'.val = 7)) := hcan_all a b hab hcan
      have hor_eq : ∀ x : Fin 9 → Bool, (x (rho a) || x (rho b)) = (x a' || x b') := by
        intro x
        dsimp only [a', b']
        split_ifs
        · rfl
        · exact Bool.or_comm _ _
      obtain ⟨hRf, hRs, _⟩ := rename_props C hCfan
      obtain ⟨x, hx⟩ := solve_canon a' b' hcan' (renameCircuit C) hRf (by omega)
      refine ⟨fun j => x (rho j), ?_⟩
      dsimp only
      rw [hval (fun j => x (rho j)), hor_eq x, graph_inv x]
      have hrel := run_rel C.gates
        (List.ofFn (fun j => x (rho j)) ++ [!x 0, x a' || x b'])
        (List.ofFn x ++ [!x 0, x a' || x b']) (by simp) (by simp) (pref_rel x _ _) C.output
      have hrho0 : rho 0 = 0 := rfl
      rw [hrho0]
      change (C.gates.foldl stepW ((List.ofFn (fun j => x (rho j)) ++ [!x 0]) ++ [x a' || x b'])).getD C.output false ≠ _
      rw [List.append_assoc, List.singleton_append, hrel]
      exact hx
  have hcases : x1 = [] ∨ (∃ a, x1 = [a]) ∨ (∃ a b, x1 = [a, b]) := by
    cases x1 with
    | nil => exact Or.inl rfl
    | cons a r1 =>
      cases r1 with
      | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
      | cons b r2 =>
        cases r2 with
        | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
        | cons c r3 => simp at hlen
  rcases hcases with hx1 | ⟨a, hx1⟩ | ⟨a, b, hx1⟩
  · exact elimWire10 (Sum.inl false) (fun _ h => by cases h) (fun x => by
      dsimp only; simp only [hx1, List.map_nil, eval_or, List.any_nil]; rfl)
  · by_cases ha : a < 10
    · exact elimWire10 (Sum.inr a) (fun w hw => by cases hw; exact ha) (fun x => by
        dsimp only; simp only [hx1, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil,
          id_eq, Bool.or_false]; rfl)
    · exact elimWire10 (Sum.inl false) (fun _ h => by cases h) (fun x => by
        dsimp only; simp only [hx1, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, x8_read_ge x a (by omega)]; rfl)
  · by_cases ha : a < 10
    · by_cases hb : b < 10
      · by_cases hab_eq : a = b
        · subst hab_eq
          exact elimWire10 (Sum.inr a) (fun w hw => by cases hw; exact ha) (fun x => by
            dsimp only; simp only [hx1, List.map_cons, List.map_nil, eval_or,
              List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]; rfl)
        · by_cases ha9 : a = 9
          · subst ha9
            by_cases hb0 : b = 0
            · subst hb0
              exact elimWire10 (Sum.inl true) (fun _ h => by cases h) (fun x => by
                dsimp only
                simp only [hx1, List.map_cons, List.map_nil, eval_or,
                  List.any_cons, List.any_nil, id_eq, Bool.or_false, x8_read_9 x]
                have h0 : (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := x8_read_lt x 0
                rw [h0, Bool.not_or_self]; rfl)
            · exact solve_nine ⟨b, by omega⟩ (by simp [hb0]) (fun x => by
                dsimp only
                simp only [hx1, List.map_cons, List.map_nil, eval_or,
                  List.any_cons, List.any_nil, id_eq, Bool.or_false,
                  x8_read_9 x, x8_read_lt x ⟨b, by omega⟩])
          · by_cases hb9 : b = 9
            · subst hb9
              by_cases ha0 : a = 0
              · subst ha0
                exact elimWire10 (Sum.inl true) (fun _ h => by cases h) (fun x => by
                  dsimp only
                  simp only [hx1, List.map_cons, List.map_nil, eval_or,
                    List.any_cons, List.any_nil, id_eq, Bool.or_false, x8_read_9 x]
                  have h0 : (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := x8_read_lt x 0
                  rw [h0, Bool.or_not_self]; rfl)
              · exact solve_nine ⟨a, by omega⟩ (by simp [ha0]) (fun x => by
                  dsimp only
                  simp only [hx1, List.map_cons, List.map_nil, eval_or,
                    List.any_cons, List.any_nil, id_eq, Bool.or_false,
                    x8_read_9 x, x8_read_lt x ⟨a, by omega⟩]
                  exact Bool.or_comm _ _)
            · by_cases hlt : a < b
              · exact solve_pair ⟨a, by omega⟩ ⟨b, by omega⟩ hlt (fun x => by
                  dsimp only
                  simp only [hx1, List.map_cons, List.map_nil, eval_or,
                    List.any_cons, List.any_nil, id_eq, Bool.or_false,
                    x8_read_lt x ⟨a, by omega⟩, x8_read_lt x ⟨b, by omega⟩])
              · exact solve_pair ⟨b, by omega⟩ ⟨a, by omega⟩ (show b < a by omega) (fun x => by
                  dsimp only
                  simp only [hx1, List.map_cons, List.map_nil, eval_or,
                    List.any_cons, List.any_nil, id_eq, Bool.or_false,
                    x8_read_lt x ⟨a, by omega⟩, x8_read_lt x ⟨b, by omega⟩]
                  exact Bool.or_comm _ _)
      · exact elimWire10 (Sum.inr a) (fun w hw => by cases hw; exact ha) (fun x => by
          dsimp only; simp only [hx1, List.map_cons, List.map_nil, eval_or,
            List.any_cons, List.any_nil, id_eq, Bool.or_false,
            x8_read_ge x b (by omega)]; rfl)
    · by_cases hb : b < 10
      · exact elimWire10 (Sum.inr b) (fun w hw => by cases hw; exact hb) (fun x => by
          dsimp only; simp only [hx1, List.map_cons, List.map_nil, eval_or,
            List.any_cons, List.any_nil, id_eq, Bool.or_false,
            x8_read_ge x a (by omega), Bool.false_or]; rfl)
      · exact elimWire10 (Sum.inl false) (fun _ h => by cases h) (fun x => by
          dsimp only; simp only [hx1, List.map_cons, List.map_nil, eval_or,
            List.any_cons, List.any_nil, id_eq, Bool.or_false,
            x8_read_ge x a (by omega), x8_read_ge x b (by omega)]; rfl)
