import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2978_3
    (charge : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [_x4 : DecidableRel x3]
      (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
        ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 =
        Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧
          x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →
      ∃ T : Finset (Fin (x1+x2)),
        (∀ p l, x3 p l → Fin.castAdd x2 p ∈ T ∨ Fin.natAdd x1 l ∈ T) ∧
        (PEqualNP.ReadTwo.incid x3).card + T.card ≤ x5.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [_x4 : DecidableRel x3]
      (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
        ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 =
        Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧
          x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →
      ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ),
        PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧
        (∀ x12 : Fin (x1 + x2) → Bool, PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 =
          Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧
            x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧
        x9.size ≤ x5.size ∧
        (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length,
          x12 = x1 + x2 + x14 ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧
        (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length,
          x12 = x1 + x2 + x14 ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧
        ∀ x12 < x9.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x15 : ℕ) (x16 : ℕ),
            (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15,x16] ∧
            x15 ∈ x11 ∧ x16 ∈ x10 := by
  classical

  let isEnd (c : ℕ) (e : ℕ × ℕ) : Bool := e.1 == c || e.2 == c

  let other (c : ℕ) (e : ℕ × ℕ) : ℕ := if e.1 = c then e.2 else e.1

  let assignStep (st : List (ℕ × ℕ) × List (ℕ × List ℕ)) (c : ℕ) :
      List (ℕ × ℕ) × List (ℕ × List ℕ) :=
    (st.1.filter (fun e => !isEnd c e), st.2 ++ [(c, (st.1.filter (isEnd c)).map (other c))])

  let assign (edges : List (ℕ × ℕ)) (cover : List ℕ) : List (ℕ × List ℕ) :=
    (cover.foldl
      (fun st c => (st.1.filter (fun e => !isEnd c e),
        st.2 ++ [(c, (st.1.filter (isEnd c)).map (other c))]))
      (edges, [])).2

  let blocks (edges : List (ℕ × ℕ)) (cover : List ℕ) : List (ℕ × List ℕ) :=
    (assign edges cover).filter (fun b => decide (0 < b.2.length))

  have any_congr_mem {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
        l.any p = l.any q := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.any_cons]
        rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

  have getD_ofFn {n : ℕ} (x : Fin n → Bool) (v : ℕ) (h : v < n) :
        (List.ofFn x).getD v false = x ⟨v, h⟩ := by
      simp [List.getD_eq_getElem?_getD, h]

  have assign_eq (edges : List (ℕ × ℕ)) (cover : List ℕ) :
        assign edges cover = (cover.foldl assignStep (edges, [])).2 := rfl

  have isEnd_iff (c : ℕ) (e : ℕ × ℕ) : isEnd c e = true ↔ e.1 = c ∨ e.2 = c := by
      simp [isEnd]

  have other_lt (c : ℕ) (e : ℕ × ℕ) (n : ℕ) (h1 : e.1 < n) (h2 : e.2 < n) : other c e < n := by
      unfold other; split <;> assumption

  have assign_len : ∀ (l : List ℕ) (st : List (ℕ × ℕ) × List (ℕ × List ℕ)),
        (l.foldl assignStep st).2.length = st.2.length + l.length := by
      intro l
      induction l with
      | nil => intro st; simp
      | cons c l ih =>
        intro st
        rw [List.foldl_cons, ih]
        simp [assignStep]
        omega

  have assign_mem : ∀ (l : List ℕ) (R : List (ℕ × ℕ)) (acc : List (ℕ × List ℕ)),
        ∀ b ∈ (l.foldl assignStep (R, acc)).2,
          b ∈ acc ∨ ∀ v ∈ b.2, ∃ e ∈ R, isEnd b.1 e = true ∧ v = other b.1 e := by
      intro l
      induction l with
      | nil => intro R acc b hb; exact Or.inl hb
      | cons c l ih =>
        intro R acc b hb
        rw [List.foldl_cons] at hb
        rcases ih _ _ b hb with h | h
        · simp only [assignStep, List.mem_append, List.mem_singleton] at h
          rcases h with h | rfl
          · exact Or.inl h
          · right
            intro v hv
            simp only [List.mem_map, List.mem_filter] at hv
            obtain ⟨e, ⟨he, hce⟩, rfl⟩ := hv
            exact ⟨e, he, hce, rfl⟩
        · right
          intro v hv
          obtain ⟨e, he, h1, h2⟩ := h v hv
          simp only [assignStep, List.mem_filter] at he
          exact ⟨e, he.1, h1, h2⟩

  have block_iff (W : ℕ → Bool) (c : ℕ) (R : List (ℕ × ℕ)) :
        (W c && ((R.filter (isEnd c)).map (other c)).any W) = true ↔
          ∃ e ∈ R, isEnd c e = true ∧ W e.1 = true ∧ W e.2 = true := by
      simp only [Bool.and_eq_true, List.any_map, List.any_eq_true, List.mem_filter, Function.comp]
      constructor
      · rintro ⟨hc, e, ⟨he, hce⟩, hv⟩
        refine ⟨e, he, hce, ?_⟩
        rw [isEnd_iff] at hce
        unfold other at hv
        by_cases h1 : e.1 = c
        · rw [if_pos h1] at hv
          exact ⟨by rw [h1]; exact hc, hv⟩
        · rw [if_neg h1] at hv
          rcases hce with h | h
          · exact absurd h h1
          · exact ⟨hv, by rw [h]; exact hc⟩
      · rintro ⟨e, he, hce, h1, h2⟩
        have hce' := (isEnd_iff c e).mp hce
        unfold other
        by_cases h3 : e.1 = c
        · refine ⟨by rw [← h3]; exact h1, e, ⟨he, hce⟩, ?_⟩
          rw [if_pos h3]; exact h2
        · rcases hce' with h | h
          · exact absurd h h3
          · refine ⟨by rw [← h]; exact h2, e, ⟨he, hce⟩, ?_⟩
            rw [if_neg h3]; exact h1

  have assign_any (W : ℕ → Bool) : ∀ (l : List ℕ) (R : List (ℕ × ℕ)) (acc : List (ℕ × List ℕ)),
        (∃ b ∈ (l.foldl assignStep (R, acc)).2, (W b.1 && b.2.any W) = true) ↔
          (∃ b ∈ acc, (W b.1 && b.2.any W) = true) ∨
            ∃ e ∈ R, (∃ c ∈ l, isEnd c e = true) ∧ W e.1 = true ∧ W e.2 = true := by
      intro l
      induction l with
      | nil => intro R acc; simp
      | cons c l ih =>
        intro R acc
        rw [List.foldl_cons]
        simp only [assignStep]
        rw [ih]
        have hN := block_iff W c R
        constructor
        · rintro (⟨b, hb, hF⟩ | ⟨e, he, ⟨c', hc', hce'⟩, hG⟩)
          · rw [List.mem_append, List.mem_singleton] at hb
            rcases hb with hb | rfl
            · exact Or.inl ⟨b, hb, hF⟩
            · obtain ⟨e, he, hce, hG⟩ := hN.mp hF
              exact Or.inr ⟨e, he, ⟨c, List.mem_cons_self .., hce⟩, hG⟩
          · rw [List.mem_filter] at he
            exact Or.inr ⟨e, he.1, ⟨c', List.mem_cons_of_mem _ hc', hce'⟩, hG⟩
        · rintro (⟨b, hb, hF⟩ | ⟨e, he, ⟨c', hc', hce'⟩, hG⟩)
          · exact Or.inl ⟨b, List.mem_append_left _ hb, hF⟩
          · by_cases hce : isEnd c e = true
            · exact Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
                hN.mpr ⟨e, he, hce, hG⟩⟩
            · rw [List.mem_cons] at hc'
              rcases hc' with rfl | hc'
              · exact absurd hce' hce
              · exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simpa using hce⟩, ⟨c', hc', hce'⟩, hG⟩

  have filter_split (R : List (ℕ × ℕ)) (p q : ℕ × ℕ → Bool) :
        (R.filter (fun e => p e || q e)).length =
          (R.filter p).length + ((R.filter (fun e => !p e)).filter q).length := by
      induction R with
      | nil => rfl
      | cons e R ih =>
        cases hp : p e <;> cases hq : q e <;> simp [List.filter_cons, hp, hq, ih] <;> omega

  have assign_sum : ∀ (l : List ℕ) (R : List (ℕ × ℕ)) (acc : List (ℕ × List ℕ)),
        ((l.foldl assignStep (R, acc)).2.map (fun b => b.2.length)).sum =
          (acc.map (fun b => b.2.length)).sum + (R.filter (fun e => l.any (fun c => isEnd c e))).length := by
      intro l
      induction l with
      | nil => intro R acc; simp
      | cons c l ih =>
        intro R acc
        rw [List.foldl_cons]
        simp only [assignStep]
        rw [ih]
        simp only [List.any_cons]
        rw [filter_split R (isEnd c) (fun e => l.any (fun c => isEnd c e))]
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, List.length_map]
        omega

  have sum_filter_pos (l : List (ℕ × List ℕ)) :
        ((l.filter (fun b => decide (0 < b.2.length))).map (fun b => b.2.length)).sum =
          (l.map (fun b => b.2.length)).sum := by
      induction l with
      | nil => rfl
      | cons b l ih =>
        by_cases h : 0 < b.2.length
        · simp [List.filter_cons, h, ih]
        · have h0 : b.2.length = 0 := by omega
          simp [List.filter_cons, h, ih, h0]

  have blocks_pos (edges : List (ℕ × ℕ)) (cover : List ℕ) :
        ∀ b ∈ blocks edges cover, 0 < b.2.length := by
      intro b hb
      unfold blocks at hb
      rw [List.mem_filter] at hb
      simpa using hb.2

  have blocks_ok (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
        (hE : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
        ∀ b ∈ blocks edges cover, 0 < b.2.length ∧ b.1 < n ∧ ∀ v ∈ b.2, v < n := by
      intro b hb
      have hpos := blocks_pos edges cover b hb
      have hb' : b ∈ assign edges cover := (List.mem_filter.mp hb).1
      rw [assign_eq] at hb'
      rcases assign_mem cover edges [] b hb' with h | h
      · simp at h
      · obtain ⟨v0, hv0⟩ := List.exists_mem_of_length_pos hpos
        obtain ⟨e, he, hce, _⟩ := h v0 hv0
        refine ⟨hpos, ?_, ?_⟩
        · rcases (isEnd_iff _ _).mp hce with h1 | h1
          · rw [← h1]; exact (hE e he).1
          · rw [← h1]; exact (hE e he).2
        · intro v hv
          obtain ⟨e', he', _, rfl⟩ := h v hv
          exact other_lt _ _ _ (hE e' he').1 (hE e' he').2

  have sum_blocks (edges : List (ℕ × ℕ)) (cover : List ℕ) :
        ((blocks edges cover).map (fun b => b.2.length)).sum =
          (edges.filter (fun e => cover.any (fun c => isEnd c e))).length := by
      unfold blocks
      rw [sum_filter_pos, assign_eq, assign_sum]
      simp

  have block_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
      (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
    cases lead <;> simp [blockGates]

  have gates_length_false : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ), (∀ p ∈ own, p.2 ≠ []) →
      (coverGatesB B false a own).length =
        (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
    intro own
    induction own with
    | nil => intro B a h; simp [coverGatesB]
    | cons o os ih =>
      rcases o with ⟨t, l⟩
      cases l with
      | nil => intro B a h; simp at h
      | cons v1 rest =>
        intro B a h
        have ih' := ih (B + (blockGates B a t v1 rest false).length)
          (B + (blockGates B a t v1 rest false).length - 1)
          (fun p hp => h p (List.mem_cons_of_mem _ hp))
        simp only [coverGatesB, List.length_append]
        rw [ih']
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [block_length]
        simp
        omega

  have circuit_size (n : ℕ) (own : List (ℕ × List ℕ)) (hne : own ≠ [])
        (h : ∀ p ∈ own, p.2 ≠ []) :
        (coverCircuitB n own).size + 1 =
          (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
      match own, hne, h with
      | (t, []) :: os, _, h => simp at h
      | (t, v1 :: rest) :: os, _, h =>
          have ih := gates_length_false os (n + (blockGates n 0 t v1 rest true).length)
            (n + (blockGates n 0 t v1 rest true).length - 1)
            (fun p hp => h p (List.mem_cons_of_mem _ hp))
          have hgl : (coverGatesB n true 0 ((t, v1 :: rest) :: os)).length =
              rest.length + 1 + ((os.map (fun p : ℕ × List ℕ => p.2.length)).sum + os.length) := by
            simp only [coverGatesB, List.length_append]
            rw [ih, block_length]
            simp
          have hnn : coverGatesB n true 0 ((t, v1 :: rest) :: os) ≠ [] := by
            intro h0
            have h1 := congrArg List.length h0
            rw [hgl] at h1
            simp at h1
          unfold coverCircuitB Circuit.size
          rw [if_neg hnn]
          simp only [hgl, List.map_cons, List.sum_cons, List.length_cons]
          omega

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

  have fold_app (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
        gs.foldl step w = w ++ t ∧ t.length = gs.length := by
      induction gs with
      | nil => intro w; exact ⟨[], by simp, rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨t, ht, hl⟩ := ih (step w g)
        refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_, ?_⟩
        · rw [List.foldl_cons, ht]; simp [step]
        · simp [hl]

  have getD_app_left {w t : List Bool} {i : ℕ} (h : i < w.length) :
        (w ++ t).getD i false = w.getD i false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

  have getD_app_right {w t : List Bool} {i : ℕ} :
        (w ++ t).getD (w.length + i) false = t.getD i false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        ← List.getD_eq_getElem?_getD]

  have getD_snoc' (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
        (l ++ [b]).getD i false = b := by
      subst h
      simpa using getD_app_right (w := l) (t := [b]) (i := 0)

  have fold_length (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := fold_app gs w
      rw [ht, List.length_append, hl]

  have fold_keep (gs : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      obtain ⟨t, ht, _⟩ := fold_app gs w
      rw [ht, getD_app_left h]

  let cv (w : List Bool) (v1 : ℕ) (rest : List ℕ) (k : ℕ) : Bool :=
    w.getD v1 false || (rest.take k).any (fun u => w.getD u false)

  have chain_read (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
        (hv1 : v1 < B) (k : ℕ) (hk : k ≤ rest.length) :
        (w ++ (List.range k).map (fun i => cv w v1 rest (i + 1))).getD
            ((v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0) false
          = cv w v1 rest k := by
      cases k with
      | zero =>
        simp only [List.getD_cons_zero]
        rw [getD_app_left (by omega)]
        simp [cv]
      | succ j =>
        have hj : j < rest.length := by omega
        have e1 : (v1 :: (List.range rest.length).map (fun j => B + j)).getD (j + 1) 0 = B + j := by
          simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hj]
        rw [e1, ← hw, getD_app_right]
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j < j + 1 by omega)]

  have chain (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
        (hv1 : v1 < B) (hrest : ∀ u ∈ rest, u < B) :
        ∀ k ≤ rest.length,
          ((List.range k).map (fun i => (⟨GateOp.or,
              [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩ : Gate))).foldl
            step w = w ++ (List.range k).map (fun i => cv w v1 rest (i + 1)) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
        rw [List.append_assoc]
        congr 2
        have hkr : k < rest.length := by omega
        have hrk : rest.getD k 0 = rest[k] := by
          simp [List.getD_eq_getElem?_getD, hkr]
        have hlt : rest[k] < w.length := by rw [hw]; exact hrest _ (List.getElem_mem hkr)
        simp only [List.map_cons, List.map_nil, GateOp.eval]
        rw [chain_read w B v1 rest hw hv1 k (by omega), hrk, getD_app_left hlt]
        simp only [cv, List.take_succ, List.getElem?_eq_getElem hkr, Option.toList_some,
          List.any_append, List.any_cons, List.any_nil, List.any_cons, Bool.or_false, id]
        simp [Bool.or_assoc, List.getElem?_eq_getElem hkr]

  have block_val (w : List Bool) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
        (hw : w.length = B) (ha : lead = false → a < B) (ht : t < B) (hv1 : v1 < B)
        (hrest : ∀ u ∈ rest, u < B) :
        ((blockGates B a t v1 rest lead).foldl step w).getD
            (B + (blockGates B a t v1 rest lead).length - 1) false
          = if lead then (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))
            else (w.getD a false ||
              (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))) := by
      have hc := chain w B v1 rest hw hv1 hrest rest.length le_rfl
      have hr := chain_read w B v1 rest hw hv1 rest.length le_rfl
      have hcvr : cv w v1 rest rest.length = (w.getD v1 false || rest.any (fun u => w.getD u false)) := by
        simp [cv]
      set L := (List.range rest.length).map (fun i => cv w v1 rest (i + 1)) with hL
      have hLl : L.length = rest.length := by simp [hL]
      have htW : (w ++ L).getD t false = w.getD t false := getD_app_left (by omega)
      rw [block_length]
      cases lead with
      | true =>
        simp only [blockGates, ↓reduceIte, List.foldl_append, hc, List.foldl_cons, List.foldl_nil,
          step]
        rw [getD_snoc']
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
          rw [htW, hr, hcvr]
          simp
        · simp [hLl, hw]
      | false =>
        have ha' : a < B := ha rfl
        simp only [blockGates, Bool.false_eq_true, ↓reduceIte, List.foldl_append, hc, List.foldl_cons,
          List.foldl_nil, step]
        rw [getD_snoc']
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
          rw [getD_app_left (by simp; omega), getD_app_left (by omega), getD_snoc']
          · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
            rw [htW, hr, hcvr]
            simp
          · simp [hLl, hw]
        · simp [hLl, hw]

  let targetF (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
    own.any (fun p => x.getD p.1 false && p.2.any (fun u => x.getD u false))

  have gates_nil_F (x : List Bool) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
      coverGatesB B lead a own = [] → targetF x own = false := by
    intro own
    induction own with
    | nil => intro B lead a h; rfl
    | cons o os ih =>
      rcases o with ⟨t, l⟩
      cases l with
      | nil =>
        intro B lead a h
        simp only [coverGatesB] at h
        have hh := ih B lead a h
        simp only [targetF, List.any_cons, List.any_nil, Bool.and_false, Bool.false_or] at hh ⊢
        exact hh
      | cons v1 rest =>
        intro B lead a h
        simp only [coverGatesB] at h
        cases lead <;> simp [blockGates] at h

  have main (n : ℕ) (x : List Bool) :
      ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool),
        (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) → w.length = B → n ≤ B →
        (∀ i < n, w.getD i false = x.getD i false) → (lead = false → a < B) →
        coverGatesB B lead a own ≠ [] →
        ((coverGatesB B lead a own).foldl step w).getD
            (B + (coverGatesB B lead a own).length - 1) false
          = if lead then targetF x own else (w.getD a false || targetF x own) := by
    intro own
    induction own with
    | nil => intro B lead a w hown hw hnB hwx ha hne; simp [coverGatesB] at hne
    | cons o os ih =>
      rcases o with ⟨t, l⟩
      cases l with
      | nil =>
        intro B lead a w hown hw hnB hwx ha hne
        simp only [coverGatesB] at hne ⊢
        rw [ih B lead a w (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hw hnB hwx ha hne]
        simp [targetF]
      | cons v1 rest =>
        intro B lead a w hown hw hnB hwx ha hne
        have hp := hown (t, v1 :: rest) (by simp)
        have ht : t < n := hp.1
        have hv1 : v1 < n := hp.2 v1 (by simp)
        have hrest : ∀ u ∈ rest, u < n := fun u hu => hp.2 u (by simp [hu])
        have hos : ∀ p ∈ os, p.1 < n ∧ ∀ u ∈ p.2, u < n :=
          fun p hp => hown p (List.mem_cons_of_mem _ hp)
        have hbv := block_val w B a t v1 rest lead hw ha (by omega) (by omega)
          (fun u hu => by have := hrest u hu; omega)
        have hrx : rest.any (fun u => w.getD u false) = rest.any (fun u => x.getD u false) :=
          any_congr_mem rest (fun u => w.getD u false) (fun u => x.getD u false)
            (fun u hu => hwx u (hrest u hu))
        rw [hrx, hwx t ht, hwx v1 hv1] at hbv
        set bg := blockGates B a t v1 rest lead with hbg
        have hm : 0 < bg.length := by
          rw [hbg, block_length]
          omega
        set W1 := bg.foldl step w with hW1
        have hW1l : W1.length = B + bg.length := by rw [hW1, fold_length, hw]
        have hW1x : ∀ i < n, W1.getD i false = x.getD i false := by
          intro i hi
          rw [hW1, fold_keep bg w (by omega)]
          exact hwx i hi
        have hW1a : lead = false → W1.getD a false = w.getD a false := by
          intro hl
          rw [hW1, fold_keep bg w (by have := ha hl; omega)]
        have hcons : targetF x ((t, v1 :: rest) :: os) =
            ((x.getD t false && (x.getD v1 false || rest.any (fun u => x.getD u false))) || targetF x os) :=
          rfl
        rw [hcons]
        simp only [coverGatesB]
        rw [← hbg, List.foldl_append, ← hW1, List.length_append]
        by_cases hnil : coverGatesB (B + bg.length) false (B + bg.length - 1) os = []
        · have hF := gates_nil_F x os _ false _ hnil
          rw [hnil, List.foldl_nil, List.length_nil, Nat.add_zero, hbv]
          rw [hF]
          cases lead <;> simp
        · have ih' := ih (B + bg.length) false (B + bg.length - 1) W1 hos hW1l (by omega)
            hW1x (fun _ => by omega) hnil
          have hidx : B + (bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length) - 1
              = B + bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length - 1 := by
            omega
          rw [hidx, ih', hbv]
          cases lead <;> simp [Bool.or_assoc]

  have circuit_fun (n : ℕ) (own : List (ℕ × List ℕ))
        (h : ∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) (x : Fin n → Bool) :
        ((coverCircuitB n own).eval (List.ofFn x) = true ↔
          ∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
            ∃ w ∈ p.2, (List.ofFn x).getD w false = true) := by
      have hF : (∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
            ∃ w ∈ p.2, (List.ofFn x).getD w false = true) ↔ targetF (List.ofFn x) own = true := by
        simp [targetF, List.any_eq_true]
      rw [hF]
      unfold coverCircuitB Circuit.eval
      split_ifs with hnil
      · rw [gates_nil_F _ own n true 0 hnil, wires_eq]
        simp [List.getD_eq_getElem?_getD]
      · rw [wires_eq]
        simp only
        rw [main n (List.ofFn x) own n true 0 (List.ofFn x) h (by simp) le_rfl (fun _ _ => rfl)
          (by simp) hnil]
        simp

  let Inv (p q : ℕ → Prop) (B : ℕ) (L : List Gate) (S T : Finset ℕ) : Prop :=
    (∀ (k : ℕ) (g : Gate), L[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      ∀ i ∈ g.inputs, i < B + k) ∧
    (∀ w ∈ S, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, p i ∨ i ∈ S) ∧
    (∀ w ∈ T, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, q i ∨ i ∈ T) ∧
    (∀ (k : ℕ) (g : Gate), L[k]? = some g → g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧
       (((p a ∨ a ∈ S) ∧ (q b ∨ b ∈ T)) ∨ ((q a ∨ a ∈ T) ∧ (p b ∨ b ∈ S))))

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have inv_swap {p q : ℕ → Prop} {B : ℕ} {L : List Gate} {S T : Finset ℕ}
        (h : Inv p q B L S T) : Inv q p B L T S := by
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨h1, h3, h2, ?_⟩
      intro k g hk ho
      obtain ⟨a, b, e, h⟩ := h4 k g hk ho
      exact ⟨a, b, e, h.symm⟩

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have inv_nil (p q : ℕ → Prop) (B : ℕ) : Inv p q B [] ∅ ∅ := by
      simp [Inv]

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have app_cases {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : (L1 ++ L2)[k]? = some g) :
        L1[k]? = some g ∨ ∃ k2, k = L1.length + k2 ∧ L2[k2]? = some g := by
      rw [List.getElem?_append] at h
      split at h
      · exact Or.inl h
      · exact Or.inr ⟨k - L1.length, by omega, h⟩

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have app_left {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L1[k]? = some g) :
        (L1 ++ L2)[k]? = some g := by
      have hk : k < L1.length := (List.getElem?_eq_some_iff.mp h).1
      rw [List.getElem?_append_left hk]
      exact h

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have app_right {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L2[k]? = some g) :
        (L1 ++ L2)[L1.length + k]? = some g := by
      rw [List.getElem?_append_right (by omega)]
      simpa using h

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have inv_app {p q : ℕ → Prop} {B : ℕ} {L1 L2 : List Gate} {S1 T1 S2 T2 : Finset ℕ}
        (h : Inv p q B L1 S1 T1) (h' : Inv p q (B + L1.length) L2 S2 T2) :
        Inv p q B (L1 ++ L2) (S1 ∪ S2) (T1 ∪ T2) := by
      obtain ⟨a1, a2, a3, a4⟩ := h
      obtain ⟨b1, b2, b3, b4⟩ := h'
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k g hk
        rcases app_cases hk with h | ⟨k2, rfl, h⟩
        · exact a1 k g h
        · obtain ⟨x, y, z⟩ := b1 k2 g h
          exact ⟨x, y, fun i hi => by have := z i hi; omega⟩
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨k, g, e1, e2, e3, e4⟩ := a2 w hw
          exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
        · obtain ⟨k, g, e1, e2, e3, e4⟩ := b2 w hw
          exact ⟨L1.length + k, g, app_right e1, by omega, e3,
            fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨k, g, e1, e2, e3, e4⟩ := a3 w hw
          exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
        · obtain ⟨k, g, e1, e2, e3, e4⟩ := b3 w hw
          exact ⟨L1.length + k, g, app_right e1, by omega, e3,
            fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
      · intro k g hk ho
        rcases app_cases hk with h | ⟨k2, rfl, h⟩
        · obtain ⟨a, b, e, hh⟩ := a4 k g h ho
          refine ⟨a, b, e, ?_⟩
          simp only [Finset.mem_union]
          tauto
        · obtain ⟨a, b, e, hh⟩ := b4 k2 g h ho
          refine ⟨a, b, e, ?_⟩
          simp only [Finset.mem_union]
          tauto

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have cval (B v1 m i : ℕ) (hi : i ≤ m) :
        (i = 0 ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = v1) ∨
        (0 < i ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = B + (i - 1)) := by
      cases i with
      | zero => left; simp
      | succ j =>
        right
        have hj : j < m := by omega
        simp [List.getD_eq_getElem?_getD, hj]

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have block_get {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} {g : Gate}
        (h : (blockGates B a t v1 rest lead)[k]? = some g) :
        (k < rest.length ∧ g = ⟨GateOp.or,
          [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩) ∨
        (k = rest.length ∧ g = ⟨GateOp.and,
          [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩) ∨
        (k = rest.length + 1 ∧ lead = false ∧ g = ⟨GateOp.or, [a, B + rest.length]⟩) := by
      unfold blockGates at h
      rcases app_cases h with h | ⟨k2, hk, h⟩
      · left
        have hk : k < rest.length := by
          have := (List.getElem?_eq_some_iff.mp h).1
          simpa using this
        refine ⟨hk, ?_⟩
        simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.some.injEq] at h
        exact h.symm
      · right
        simp only [List.length_map, List.length_range] at hk
        cases k2 with
        | zero =>
          left
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          exact ⟨by omega, h.symm⟩
        | succ k3 =>
          right
          cases lead with
          | true => simp at h
          | false =>
            cases k3 with
            | zero =>
              simp only [List.getElem?_cons_succ, Bool.false_eq_true, ite_false,
                List.getElem?_cons_zero, Option.some.injEq] at h
              exact ⟨by omega, rfl, h.symm⟩
            | succ k4 => simp at h

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have block_chain {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} (hk : k < rest.length) :
        (blockGates B a t v1 rest lead)[k]? = some ⟨GateOp.or,
          [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩ := by
      unfold blockGates
      apply app_left
      simp [hk]

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have rest_mem {rest : List ℕ} {k : ℕ} (hk : k < rest.length) : rest.getD k 0 ∈ rest := by
      simp [List.getD_eq_getElem?_getD, hk]

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have inv_block {p q : ℕ → Prop} {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool}
        (hp : ∀ i, p i → i < B) (hq : ∀ i, q i → i < B) (ha : lead = false → a < B)
        (ht : q t) (hv : p v1) (hr : ∀ v ∈ rest, p v) :
        Inv p q B (blockGates B a t v1 rest lead)
          ((Finset.range rest.length).image (fun j => B + j)) ∅ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k g hk
        rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
        · refine ⟨Or.inr rfl, rfl, ?_⟩
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
            · rw [e]; have := hp _ hv; omega
            · rw [e]; omega
          · have := hp _ (hr _ (rest_mem h1)); omega
        · refine ⟨Or.inl rfl, rfl, ?_⟩
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · have := hq _ ht; omega
          · rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
            · rw [e]; have := hp _ hv; omega
            · rw [e]; omega
        · refine ⟨Or.inr rfl, rfl, ?_⟩
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          have := ha h2
          rcases hi with rfl | rfl <;> omega
      · intro w hw
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        have hk : k < rest.length := Finset.mem_range.mp hk
        refine ⟨k, _, block_chain hk, rfl, rfl, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
          · rw [e]; exact Or.inl hv
          · rw [e]; right
            exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩
        · exact Or.inl (hr _ (rest_mem hk))
      · intro w hw
        simp at hw
      · intro k g hk ho
        rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
        · simp at ho
        · refine ⟨_, _, rfl, Or.inr ⟨Or.inl ht, ?_⟩⟩
          rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
          · rw [e]; exact Or.inl hv
          · rw [e]; right
            exact Finset.mem_image.mpr ⟨rest.length - 1, Finset.mem_range.mpr (by omega), rfl⟩
        · simp at ho

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
        1 ≤ (blockGates B a t v1 rest lead).length := by
      unfold blockGates
      simp
      omega

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have inv_cover (p q : ℕ → Prop) (own : List (ℕ × List ℕ)) :
        ∀ (B : ℕ) (lead : Bool) (a : ℕ), (∀ i, p i → i < B) → (∀ i, q i → i < B) →
          (lead = false → a < B) →
          (∀ o ∈ own, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v)) →
          ∃ S T, Inv p q B (coverGatesB B lead a own) S T := by
      induction own with
      | nil =>
        intro B lead a _ _ _ _
        exact ⟨∅, ∅, by simpa [coverGatesB] using inv_nil p q B⟩
      | cons o os ih =>
        intro B lead a hp hq ha ho
        obtain ⟨t, l⟩ := o
        have hos : ∀ o ∈ os, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v) :=
          fun o h => ho o (List.mem_cons_of_mem _ h)
        cases l with
        | nil =>
          simp only [coverGatesB]
          exact ih B lead a hp hq ha hos
        | cons v1 rest =>
          simp only [coverGatesB]
          have hl := block_len B a t v1 rest lead
          obtain ⟨S2, T2, h2⟩ := ih (B + (blockGates B a t v1 rest lead).length) false
            (B + (blockGates B a t v1 rest lead).length - 1)
            (fun i h => by have := hp i h; omega) (fun i h => by have := hq i h; omega)
            (fun _ => by omega) hos
          have h0 := ho (t, v1 :: rest) List.mem_cons_self
          simp only [List.mem_cons, forall_eq_or_imp] at h0
          rcases h0 with ⟨h1, h3, h4⟩ | ⟨h1, h3, h4⟩
          · exact ⟨_, _, inv_app (inv_block hp hq ha h1 h3 h4) h2⟩
          · exact ⟨_, _, inv_app (inv_swap (inv_block hq hp ha h1 h3 h4)) h2⟩

  have gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
        (coverCircuitB n own).gates = coverGatesB n true 0 own := by
      unfold coverCircuitB
      by_cases h : coverGatesB n true 0 own = [] <;> simp [coverCircuitB, h]

  have gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
        C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, hj]

  have L3245 : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
      intro x1 x2 x3 x4 hyp x6 x7
      obtain ⟨S, T, h1, h2, h3, h4⟩ := inv_cover (fun i => i < x1) (fun i => x1 ≤ i ∧ i < x4) x3 x4 true 0
        (fun i h => by show i < x1 + x2; omega) (fun i h => h.2) (fun h => by simp at h)
        (fun o ho => by
          rcases (hyp o ho).2 with h | h
          · exact Or.inr h
          · exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
      have hg : x6.gates = PEqualNP.MetaComplexity.coverGatesB x4 true 0 x3 := gates_eq x4 x3
      rw [← hg] at h1 h2 h3 h4
      have key : ∀ k g, x6.gates[k]? = some g → k < x6.gates.length ∧ x7 k = g := by
        intro k g h
        have hk : k < x6.gates.length := (List.getElem?_eq_some_iff.mp h).1
        refine ⟨hk, ?_⟩
        have := gateAt_get x6 k hk
        rw [h] at this
        exact (Option.some.inj this).symm
      refine ⟨Finset.range x1 ∪ S, Finset.Ico x1 x4 ∪ T, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · intro g hg2
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg2
        exact (h1 k g hk).1
      · intro j hj i hi
        exact (h1 j _ (gateAt_get x6 j hj)).2.2 i hi
      · intro g hg2
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg2
        exact (h1 k g hk).2.1
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact Or.inl (Finset.mem_range.mp hw)
        · right
          obtain ⟨k, g, e1, e2, e3, e4⟩ := h2 w hw
          obtain ⟨hk, rfl⟩ := key k g e1
          refine ⟨k, hk, e2, e3, fun i hi => ?_⟩
          rcases e4 i hi with h | h
          · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
          · exact Finset.mem_union_right _ h
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact Or.inl (Finset.mem_Ico.mp hw)
        · right
          obtain ⟨k, g, e1, e2, e3, e4⟩ := h3 w hw
          obtain ⟨hk, rfl⟩ := key k g e1
          refine ⟨k, hk, e2, e3, fun i hi => ?_⟩
          rcases e4 i hi with h | h
          · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr h)
          · exact Finset.mem_union_right _ h
      · intro k hk ho
        obtain ⟨a, b, e, h⟩ := h4 k _ (gateAt_get x6 k hk) ho
        refine ⟨a, b, e, ?_⟩
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
        exact h

  let orientGate (P L : Finset ℕ) (g : Gate) : Gate :=
    if g.op = GateOp.and ∧
        ¬(g.inputs.headD 0 ∈ L ∧ g.inputs.getD 1 0 ∈ P) then
      ⟨g.op, g.inputs.reverse⟩
    else g

  have orientGate_eval (P L : Finset ℕ) (g : Gate)
        (hlen : g.inputs.length = 2)
        (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
        (hcross : g.op = GateOp.and → ∃ a b, g.inputs = [a,b] ∧
          ((a ∈ L ∧ b ∈ P) ∨ (a ∈ P ∧ b ∈ L)))
        (w : List Bool) :
        (orientGate P L g).op.eval ((orientGate P L g).inputs.map (fun i => w.getD i false)) =
          g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
      rcases g with ⟨op, ins⟩
      cases op with
      | and =>
        obtain ⟨a, b, rfl, h⟩ := hcross rfl
        by_cases hab : a ∈ L ∧ b ∈ P
        · simp [orientGate, hab]
        · have hb : b ∈ L := by
            rcases h with h | h
            · exact False.elim (hab h)
            · exact h.2
          have ha : a ∈ P := by
            rcases h with h | h
            · exact False.elim (hab h)
            · exact h.1
          simp only [orientGate]
          have hc : True ∧
              ¬([a, b].headD 0 ∈ L ∧ [a, b].getD 1 0 ∈ P) :=
            ⟨trivial, by simpa using hab⟩
          rw [if_pos hc]
          simp [GateOp.eval, Bool.and_comm]
      | or =>
        simp [orientGate]
      | not => simp at hop
      | mod m => simp at hop
      | maj => simp at hop

  have orient_wires (P L : Finset ℕ) (gs : List Gate) (x : List Bool)
        (hlen : ∀ g ∈ gs, g.inputs.length = 2)
        (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
        (hcross : ∀ g ∈ gs, g.op = GateOp.and → ∃ a b, g.inputs = [a,b] ∧
          ((a ∈ L ∧ b ∈ P) ∨ (a ∈ P ∧ b ∈ L))) :
        (gs.map (orientGate P L)).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) x =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) x := by
      induction gs generalizing x with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [orientGate_eval P L g (hlen g (by simp)) (hop g (by simp))
          (hcross g (by simp)) x]
        exact ih (x ++ [g.op.eval (g.inputs.map (fun i => x.getD i false))])
          (fun g hg => hlen g (by simp [hg]))
          (fun g hg => hop g (by simp [hg]))
          (fun g hg => hcross g (by simp [hg]))

  have gateAt_orient (C : Circuit) (P L : Finset ℕ) (j : ℕ) :
        gateAt ⟨C.gates.map (orientGate P L), C.output⟩ j = orientGate P L (gateAt C j) := by
      unfold gateAt
      have hd : orientGate P L ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩ := by
        simp [orientGate]
      simpa only [hd] using
        (List.getD_map (l := C.gates) (n := j) (d := ⟨GateOp.or, []⟩)
          (orientGate P L))

  have orientGate_and (P L : Finset ℕ) (g : Gate)
        (hlen : g.inputs.length = 2)
        (hop : g.op = GateOp.and)
        (hcross : g.op = GateOp.and → ∃ a b, g.inputs = [a,b] ∧
          ((a ∈ L ∧ b ∈ P) ∨ (a ∈ P ∧ b ∈ L))) :
        ∃ a b, (orientGate P L g).inputs = [a,b] ∧ a ∈ L ∧ b ∈ P := by
      rcases g with ⟨op, ins⟩
      cases op with
      | and =>
        obtain ⟨a, b, hin, h⟩ := hcross rfl
        change ins = [a,b] at hin
        by_cases hab : a ∈ L ∧ b ∈ P
        · exact ⟨a, b, by simp [orientGate, hin, hab], hab⟩
        · have h' : a ∈ P ∧ b ∈ L := by
            rcases h with h | h
            · exact False.elim (hab h)
            · exact h
          refine ⟨b, a, ?_, h'.2, h'.1⟩
          subst ins
          simp only [orientGate]
          have hc : True ∧
              ¬([a, b].headD 0 ∈ L ∧ [a, b].getD 1 0 ∈ P) :=
            ⟨trivial, by simpa using hab⟩
          rw [if_pos hc]
          rfl
      | or => cases hop
      | not => cases hop
      | mod m => cases hop
      | maj => cases hop

  have orient_circuit (n : ℕ) (C : Circuit) (P L : Finset ℕ)
        (hAO : IsAO2 n C)
        (hcross : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and →
          ∃ a b, (gateAt C i).inputs = [a,b] ∧
            ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) :
        let D : Circuit := ⟨C.gates.map (orientGate P L), C.output⟩
        IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
          (∀ i, (gateAt D i).op = (gateAt C i).op) ∧
          (∀ i, (gateAt C i).op = GateOp.or → gateAt D i = gateAt C i) ∧
          (∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
            ∃ a b, (gateAt D i).inputs = [a,b] ∧ a ∈ L ∧ b ∈ P) := by
      dsimp only
      obtain ⟨hmono, hread, hfan⟩ := hAO
      have hshape : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
        intro g hg
        exact ⟨hmono g hg, hfan g hg⟩
      have hcross' : ∀ g ∈ C.gates, g.op = GateOp.and → ∃ a b, g.inputs = [a,b] ∧
          ((a ∈ L ∧ b ∈ P) ∨ (a ∈ P ∧ b ∈ L)) := by
        intro g hg ho
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
        have hik : i < C.gates.length := (List.getElem?_eq_some_iff.mp hi).1
        have hh : C.gates[i]? = some (gateAt C i) := by
          unfold gateAt
          simp [List.getD_eq_getElem?_getD, hik]
        rw [hi] at hh
        have heq : gateAt C i = g := (Option.some.inj hh).symm
        rw [← heq] at ho
        simpa [or_comm, heq] using hcross i hik ho
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
          have hs := hshape g0 hg0
          simp only [orientGate]
          split
          · simpa using hs.1
          · exact hs.1
        · intro j hj i hi
          rw [gateAt_orient] at hi
          have hiC : i ∈ (gateAt C j).inputs := by
            by_cases hc : (gateAt C j).op = GateOp.and ∧
                ¬((gateAt C j).inputs.headD 0 ∈ L ∧
                  (gateAt C j).inputs.getD 1 0 ∈ P)
            · simp only [orientGate, if_pos hc] at hi
              simpa using hi
            · simp only [orientGate, if_neg hc] at hi
              exact hi
          exact hread j (by simpa using hj) i hiC
        · intro g hg
          rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
          have hs := hshape g0 hg0
          simp only [orientGate]
          split
          · simpa using hs.2
          · exact hs.2
      · simp [Circuit.size]
      · funext x
        unfold circuitFun Circuit.eval
        simp only [Circuit.wires]
        rw [orient_wires P L C.gates (List.ofFn x)
          (fun g hg => (hshape g hg).2) (fun g hg => (hshape g hg).1) hcross']
      · intro i
        rw [gateAt_orient]
        unfold orientGate
        split <;> rfl
      · intro i ho
        rw [gateAt_orient]
        simp [orientGate, ho]
      · intro i hi ho
        have hoC : (gateAt C i).op = GateOp.and := by
          rw [gateAt_orient] at ho
          unfold orientGate at ho
          split at ho <;> exact ho
        rw [gateAt_orient]
        have hiC : i < C.gates.length := by simpa using hi
        have hg : gateAt C i ∈ C.gates := by
          apply List.mem_iff_getElem?.mpr
          refine ⟨i, ?_⟩
          unfold gateAt
          simp [List.getD_eq_getElem?_getD, hiC]
        exact orientGate_and P L (gateAt C i) (hshape _ hg).2 hoC
          (fun h => by simpa [or_comm] using hcross i hiC h)

  have blocks_side (p n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
        (hpn : p ≤ n) (hpoint : ∀ e ∈ edges, e.1 < p)
        (hline : ∀ e ∈ edges, p ≤ e.2 ∧ e.2 < n) :
        ∀ b ∈ blocks edges cover,
          ((p ≤ b.1 ∧ b.1 < n) ∧ ∀ v ∈ b.2, v < p) ∨
            (b.1 < p ∧ ∀ v ∈ b.2, p ≤ v ∧ v < n) := by
      intro b hb
      have hbA : b ∈ (cover.foldl assignStep (edges, [])).2 := by
        exact (List.mem_filter.mp hb).1
      have hm : ∀ v ∈ b.2, ∃ e ∈ edges, isEnd b.1 e = true ∧ v = other b.1 e := by
        rcases assign_mem cover edges [] b hbA with h | h
        · simp at h
        · exact h
      have hok := blocks_ok n edges cover
        (fun e he => ⟨by have := hpoint e he; omega, (hline e he).2⟩) b hb
      by_cases hc : b.1 < p
      · right
        refine ⟨hc, fun v hv => ?_⟩
        obtain ⟨e, he, hce, hve⟩ := hm v hv
        have hce' := (isEnd_iff b.1 e).mp hce
        have he1 : e.1 = b.1 := by
          rcases hce' with h | h
          · exact h
          · have := (hline e he).1
            omega
        rw [hve]
        simp only [other, if_pos he1]
        exact hline e he
      · left
        refine ⟨⟨by omega, hok.2.1⟩, fun v hv => ?_⟩
        obtain ⟨e, he, hce, hve⟩ := hm v hv
        have hce' := (isEnd_iff b.1 e).mp hce
        have he2 : e.2 = b.1 := by
          rcases hce' with h | h
          · have := hpoint e he
            omega
          · exact h
        have hne : e.1 ≠ b.1 := by
          intro heq
          have := hpoint e he
          omega
        rw [hve]
        simp only [other, if_neg hne]
        exact hpoint e he

  have coverB_fun (n : ℕ) (edges : List (ℕ × ℕ)) (cover : List ℕ)
        (hE : ∀ e ∈ edges, e.1 < n ∧ e.2 < n)
        (hT : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover) (x : Fin n → Bool) :
        circuitFun n (coverCircuitB n (blocks edges cover)) x =
          decide (∃ i j : Fin n,
            ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges) ∧
              x i = true ∧ x j = true) := by
      rw [show circuitFun n (coverCircuitB n (blocks edges cover)) x =
          (coverCircuitB n (blocks edges cover)).eval (List.ofFn x) from rfl]
      rw [Bool.eq_iff_iff]
      rw [circuit_fun n (blocks edges cover)
        (fun b hb => (blocks_ok n edges cover hE b hb).2) x]
      simp only [decide_eq_true_eq]
      have hA := assign_any (fun v => (List.ofFn x).getD v false) cover edges []
      rw [← assign_eq] at hA
      have hblk : (∃ b ∈ blocks edges cover,
          (List.ofFn x).getD b.1 false = true ∧
            ∃ v ∈ b.2, (List.ofFn x).getD v false = true) ↔
          ∃ b ∈ assign edges cover,
            ((List.ofFn x).getD b.1 false && b.2.any (fun v => (List.ofFn x).getD v false)) = true := by
        constructor
        · rintro ⟨b, hb, hc, v, hv, hval⟩
          refine ⟨b, (List.mem_filter.mp hb).1, ?_⟩
          simp only [Bool.and_eq_true, List.any_eq_true]
          exact ⟨hc, v, hv, hval⟩
        · rintro ⟨b, hb, hval⟩
          simp only [Bool.and_eq_true, List.any_eq_true] at hval
          obtain ⟨hc, v, hv, hval⟩ := hval
          refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hc, v, hv, hval⟩
          simpa using List.length_pos_of_mem hv
      rw [hblk, hA]
      simp only [List.not_mem_nil, false_and, exists_false, false_or]
      constructor
      · rintro ⟨e, he, _, h1, h2⟩
        refine ⟨⟨e.1, (hE e he).1⟩, ⟨e.2, (hE e he).2⟩, Or.inl (by simpa using he), ?_, ?_⟩
        · rw [← getD_ofFn x e.1 (hE e he).1]; exact h1
        · rw [← getD_ofFn x e.2 (hE e he).2]; exact h2
      · rintro ⟨i, j, hij, hi, hj⟩
        have gi : (List.ofFn x).getD i.val false = true := by
          rw [getD_ofFn x i.val i.isLt]; exact hi
        have gj : (List.ofFn x).getD j.val false = true := by
          rw [getD_ofFn x j.val j.isLt]; exact hj
        have cov : ∀ e ∈ edges, ∃ c ∈ cover, isEnd c e = true := by
          intro e he
          rcases hT e he with h | h
          · exact ⟨e.1, h, by simp [isEnd]⟩
          · exact ⟨e.2, h, by simp [isEnd]⟩
        rcases hij with h | h
        · exact ⟨_, h, cov _ h, gi, gj⟩
        · exact ⟨_, h, cov _ h, gj, gi⟩

  intro p l I inst C hno hC hfun
  obtain ⟨T, covers, budget⟩ := charge p l I C hno hC hfun
  let n := p + l
  let edges : List (ℕ × ℕ) :=
    (PEqualNP.ReadTwo.incid I).toList.map (fun e =>
      ((Fin.castAdd l e.1).val, (Fin.natAdd p e.2).val))
  let cover : List ℕ := T.toList.map Fin.val
  let own := blocks edges cover
  let C0 : Circuit := coverCircuitB n own
  have hpn : p ≤ n := by omega
  have hpoint : ∀ e ∈ edges, e.1 < p := by
    intro e he
    rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
    simpa [Fin.castAdd] using e0.1.isLt
  have hline : ∀ e ∈ edges, p ≤ e.2 ∧ e.2 < n := by
    intro e he
    rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
    exact ⟨by simp [Fin.natAdd], (Fin.natAdd p e0.2).isLt⟩
  have hE : ∀ e ∈ edges, e.1 < n ∧ e.2 < n := by
    intro e he
    exact ⟨by have := hpoint e he; omega, (hline e he).2⟩
  have hcover : ∀ e ∈ edges, e.1 ∈ cover ∨ e.2 ∈ cover := by
    intro e he
    rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
    have heI : e0 ∈ PEqualNP.ReadTwo.incid I := Finset.mem_toList.mp he0
    have hI : I e0.1 e0.2 := by
      simpa [PEqualNP.ReadTwo.incid] using heI
    rcases covers e0.1 e0.2 hI with h | h
    · left
      apply List.mem_map.mpr
      exact ⟨Fin.castAdd l e0.1, Finset.mem_toList.mpr h, rfl⟩
    · right
      apply List.mem_map.mpr
      exact ⟨Fin.natAdd p e0.2, Finset.mem_toList.mpr h, rfl⟩
  have hside : ∀ o ∈ own,
      ((p ≤ o.1 ∧ o.1 < n) ∧ ∀ v ∈ o.2, v < p) ∨
        (o.1 < p ∧ ∀ v ∈ o.2, p ≤ v ∧ v < n) :=
    blocks_side p n edges cover hpn hpoint hline
  have hown : ∀ o ∈ own, o.2 ≠ [] ∧
      ((o.1 < p ∧ ∀ v ∈ o.2, p ≤ v ∧ v < n) ∨
        p ≤ o.1 ∧ o.1 < n ∧ ∀ v ∈ o.2, v < p) := by
    intro o ho
    refine ⟨List.length_pos_iff.mp (blocks_pos edges cover o ho), ?_⟩
    rcases hside o ho with h | h
    · exact Or.inr ⟨h.1.1, h.1.2, h.2⟩
    · exact Or.inl h
  obtain ⟨P0, L0, hAO0, hpoints0, hlines0, hands0⟩ :=
    L3245 p l own hown
  let D : Circuit := ⟨C0.gates.map (orientGate P0 L0), C0.output⟩
  obtain ⟨hD, sameSize, sameFun, sameOp, sameOr, oriented⟩ :=
    orient_circuit n C0 P0 L0 hAO0 hands0
  have hlen : D.gates.length = C0.gates.length := sameSize
  refine ⟨D, P0, L0, hD, ?_, ?_, ?_, ?_, oriented⟩
  · intro x
    rw [sameFun]
    rw [coverB_fun n edges cover hE hcover x]
    congr 1
    apply propext
    have hedge_mem : ∀ a b : ℕ, (a,b) ∈ edges ↔
        ∃ q r, a = (Fin.castAdd l q).val ∧ b = (Fin.natAdd p r).val ∧ I q r := by
      intro a b
      constructor
      · intro h
        rcases List.mem_map.mp h with ⟨e, he, heq⟩
        rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        refine ⟨e.1, e.2, rfl, rfl, ?_⟩
        have he' : e ∈ PEqualNP.ReadTwo.incid I := Finset.mem_toList.mp he
        simpa [PEqualNP.ReadTwo.incid] using he'
      · rintro ⟨q, r, rfl, rfl, hI⟩
        apply List.mem_map.mpr
        refine ⟨(q,r), ?_, rfl⟩
        apply Finset.mem_toList.mpr
        simpa [PEqualNP.ReadTwo.incid, hI]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      rcases hij with h | h
      · obtain ⟨q, r, hiq, hjr, hI⟩ := (hedge_mem i.val j.val).mp h
        refine ⟨q, r, hI, ?_, ?_⟩
        · have heq : i = Fin.castAdd l q := Fin.ext hiq
          rwa [heq] at hi
        · have heq : j = Fin.natAdd p r := Fin.ext hjr
          rwa [heq] at hj
      · obtain ⟨q, r, hjq, hir, hI⟩ := (hedge_mem j.val i.val).mp h
        refine ⟨q, r, hI, ?_, ?_⟩
        · have heq : j = Fin.castAdd l q := Fin.ext hjq
          rwa [heq] at hj
        · have heq : i = Fin.natAdd p r := Fin.ext hir
          rwa [heq] at hi
    · rintro ⟨q, r, hI, hq, hr⟩
      refine ⟨Fin.castAdd l q, Fin.natAdd p r, ?_, hq, hr⟩
      left
      exact (hedge_mem _ _).mpr ⟨q, r, rfl, rfl, hI⟩
  · have hsize0 : C0.size + 1 ≤ C.size + 1 := by
      by_cases hne : own = []
      · have hz : C0.size = 0 := by
          simp [C0, own, hne, coverCircuitB, coverGatesB, Circuit.size]
        omega
      · have hpos : ∀ o ∈ own, o.2 ≠ [] := fun o ho =>
          List.length_pos_iff.mp (blocks_pos edges cover o ho)
        rw [circuit_size n own hne hpos]
        have hsum := sum_blocks edges cover
        have hfilter := List.length_filter_le (fun e => cover.any (fun c => isEnd c e)) edges
        have hblocks : own.length ≤ cover.length := by
          unfold own blocks
          have h1 := List.length_filter_le (fun b => decide (0 < b.2.length)) (assign edges cover)
          have h2 := assign_len cover (edges, [])
          rw [← assign_eq] at h2
          simp only [List.length_nil, zero_add] at h2
          omega
        have hedges : edges.length = (PEqualNP.ReadTwo.incid I).card := by
          simp [edges]
        have hcovlen : cover.length = T.card := by simp [cover]
        rw [hsum]
        omega
    have hDs : D.size = C0.size := sameSize
    omega
  · intro w hw
    rcases hpoints0 w hw with h | ⟨j, hj, hwire, hop, hinputs⟩
    · exact Or.inl h
    · have hjC : j < C0.gates.length := by simpa [C0] using hj
      have hjD : j < D.gates.length := by rwa [hlen]
      have hopC : (gateAt C0 j).op = GateOp.or := by simpa [C0] using hop
      have hinputsC : ∀ i ∈ (gateAt C0 j).inputs, i ∈ P0 := by
        simpa [C0] using hinputs
      refine Or.inr ⟨j, hjD, hwire, ?_, ?_⟩
      · rw [sameOr j hopC]
        exact hopC
      · intro i hi
        apply hinputsC i
        rwa [sameOr j hopC] at hi
  · intro w hw
    rcases hlines0 w hw with h | ⟨j, hj, hwire, hop, hinputs⟩
    · exact Or.inl h
    · have hjC : j < C0.gates.length := by simpa [C0] using hj
      have hjD : j < D.gates.length := by rwa [hlen]
      have hopC : (gateAt C0 j).op = GateOp.or := by simpa [C0] using hop
      have hinputsC : ∀ i ∈ (gateAt C0 j).inputs, i ∈ L0 := by
        simpa [C0] using hinputs
      refine Or.inr ⟨j, hjD, hwire, ?_, ?_⟩
      · rw [sameOr j hopC]
        exact hopC
      · intro i hi
        apply hinputsC i
        rwa [sameOr j hopC] at hi