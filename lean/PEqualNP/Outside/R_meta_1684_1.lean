import Mathlib
import PEqualNP.Defs

-- Split on line-degree. Degree at most 1: the merged L_meta_1500 (h1). Its soundness clause (an arc of
-- points with any lines avoiding it is rejected) is derived inline from two families of degenerate
-- rejected rows, all points with no line and the complement of line w with line w, by one invariant
-- carried gate by gate: a degree-0 wire true at x is true at both rows, a degree-1 wire true at x is
-- true at the first row or at the row of a line that is on in x. Degree at least 2: h2.
-- h1 is L_meta_1500 restated so it prints and reads back: the filter count as Fintype.card of a subtype
-- (Fintype.card_subtype) and each Finset literal membership as a list literal membership (same elements).
theorem PEqualNP.Outside.R_meta_1684_1
    (h1 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 ∧ (∀ x : Fin 26 → Bool, (∀ wa : Fin 13, Fintype.card {pa : Fin 13 // (∃ da : ℕ, da ∈ ([0, 1, 3, 9] : List ℕ) ∧ (wa.val + da) % 13 = pa.val) ∧ x (Fin.castAdd 13 pa) = true} ≤ 2) → PEqualNP.MetaComplexity.circuitFun 26 C x = true → ∃ pb wb : Fin 13, (∃ db : ℕ, db ∈ ([0, 1, 3, 9] : List ℕ) ∧ (wb.val + db) % 13 = pb.val) ∧ x (Fin.castAdd 13 pb) = true ∧ x (Fin.natAdd 13 wb) = true) ∧ (∀ pc wc : Fin 13, (∃ dc : ℕ, dc ∈ ([0, 1, 3, 9] : List ℕ) ∧ (wc.val + dc) % 13 = pc.val) → PEqualNP.MetaComplexity.circuitFun 26 C (fun k : Fin 26 => decide (k = Fin.castAdd 13 pc ∨ k = Fin.natAdd 13 wc)) = true)))
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 63 → ¬ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 → (∀ p w : Fin 13, (∃ dd : Fin 13, dd ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧ p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) → (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd : Fin 13, dd ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧ pp = w2 + dd)) ∧ (∃ dd : Fin 13, dd ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧ v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd : Fin 13, dd ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧ p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd : Fin 13, dd ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧ pp = w4 + dd)) → (∃ dd : Fin 13, dd ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧ v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd : Fin 13, dd ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧ pp = ww + dd))))) = false) → False) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  have bridge : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 → (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) → (∀ x : Fin 26 → Bool, (∀ wa : Fin 13, Fintype.card {pa : Fin 13 // (∃ da : ℕ, da ∈ ([0, 1, 3, 9] : List ℕ) ∧ (wa.val + da) % 13 = pa.val) ∧ x (Fin.castAdd 13 pa) = true} ≤ 2) → PEqualNP.MetaComplexity.circuitFun 26 C x = true → ∃ pb wb : Fin 13, (∃ db : ℕ, db ∈ ([0, 1, 3, 9] : List ℕ) ∧ (wb.val + db) % 13 = pb.val) ∧ x (Fin.castAdd 13 pb) = true ∧ x (Fin.natAdd 13 wb) = true) := by
    intro C hm hd hneg x _ hx
    by_contra hnone
    have gA : ∀ {α : Type} (l : List α) (a d : α) (j : ℕ), (l ++ [a]).getD j d =
        if j < l.length then l.getD j d else if j = l.length then a else d := by
      intro α l a d j
      simp only [List.getD_eq_getElem?_getD]
      split_ifs with h1 h2
      · rw [List.getElem?_append_left h1]
      · subst h2; simp
      · rw [List.getElem?_append_right (by omega)]
        rw [List.getElem?_eq_none (by simp; omega)]; rfl
    have onN : ∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) →
        x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 w) = true → False := by
      intro p w hpw hp hw
      obtain ⟨dd, hdd, he⟩ := hpw
      apply hnone
      have hD : ∀ e : Fin 13, e ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → e.val ∈ ([0, 1, 3, 9] : List ℕ) := by
        decide
      refine ⟨p, w, ⟨dd.val, hD dd hdd, ?_⟩, hp, hw⟩
      subst he
      exact (Fin.val_add w dd).symm
    have r0 := hneg Finset.univ (fun v hv => absurd (Finset.mem_univ v) hv)
      (Or.inr ⟨0, fun w4 h4 => absurd ⟨0, by decide, (add_zero w4).symm⟩ (h4 w4 (Finset.mem_univ w4))⟩)
    have key : ∀ w w4 : Fin 13, (∀ pp : Fin 13, (¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w + dd) →
        ¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd) →
        ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), w = w4 + dd := by
      decide +kernel
    have rW := fun w : Fin 13 => hneg (Finset.univ.filter (fun p : Fin 13 => ¬ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd))
      (fun v hv => ⟨w, fun pp hpp => (Finset.mem_filter.mp hpp).2,
        by_contra (fun hc => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩))⟩)
      (Or.inr ⟨w, fun w4 h4 => key w w4 (fun pp hp => h4 pp (Finset.mem_filter.mpr ⟨Finset.mem_univ pp, hp⟩))⟩)
    -- the invariant, carried gate by gate
    have one : ∀ g : PEqualNP.CircuitLowerBounds.Gate, (g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        ∀ (Lx L0 : List Bool) (Lw : Fin 13 → List Bool) (Ld : List ℕ),
        Lx.length = Ld.length → L0.length = Ld.length → (∀ w, (Lw w).length = Ld.length) →
        (∀ j, (Ld.getD j 0 = 0 → Lx.getD j false = true → L0.getD j false = true ∧
            ∀ w, x (Fin.natAdd 13 w) = true → (Lw w).getD j false = true) ∧
          (Ld.getD j 0 ≤ 1 → Lx.getD j false = true → L0.getD j false = true ∨
            ∃ w, x (Fin.natAdd 13 w) = true ∧ (Lw w).getD j false = true)) →
        (∀ j, ((Ld ++ [g.lineDegree Ld]).getD j 0 = 0 →
            (Lx ++ [g.op.eval (g.inputs.map fun i => Lx.getD i false)]).getD j false = true →
            (L0 ++ [g.op.eval (g.inputs.map fun i => L0.getD i false)]).getD j false = true ∧
            ∀ w, x (Fin.natAdd 13 w) = true →
              (Lw w ++ [g.op.eval (g.inputs.map fun i => (Lw w).getD i false)]).getD j false = true) ∧
          ((Ld ++ [g.lineDegree Ld]).getD j 0 ≤ 1 →
            (Lx ++ [g.op.eval (g.inputs.map fun i => Lx.getD i false)]).getD j false = true →
            (L0 ++ [g.op.eval (g.inputs.map fun i => L0.getD i false)]).getD j false = true ∨
            ∃ w, x (Fin.natAdd 13 w) = true ∧
              (Lw w ++ [g.op.eval (g.inputs.map fun i => (Lw w).getD i false)]).getD j false = true)) := by
      intro g hg Lx L0 Lw Ld e1 e2 e3 h j
      have evA : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.and l = l.all id := fun l => rfl
      have evO : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id := fun l => rfl
      simp only [gA, e1, e2, e3]
      split_ifs with hj1 hj2
      · exact h j
      · rcases g with ⟨op, ins⟩
        obtain ⟨hop, hlen⟩ := hg
        have hop' : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using hop
        match ins, hlen with
        | [], _ =>
          rcases hop' with rfl | rfl
          · exact ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ _ => Or.inl rfl⟩
          · exact ⟨fun _ hx => absurd (show PEqualNP.CircuitLowerBounds.GateOp.or.eval [] = true from hx) (by decide),
              fun _ hx => absurd (show PEqualNP.CircuitLowerBounds.GateOp.or.eval [] = true from hx) (by decide)⟩
        | [a], _ =>
          have ha := h a
          rcases hop' with rfl | rfl
          · have e : ∀ l : List ℕ, PEqualNP.CircuitLowerBounds.Gate.lineDegree ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a]⟩ l = l.getD a 0 := fun l => rfl
            simp only [e, evA, evO, List.map, List.all_cons, List.all_nil, Bool.and_true, id]
            exact ha
          · have e : ∀ l : List ℕ, PEqualNP.CircuitLowerBounds.Gate.lineDegree ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ l = max (l.getD a 0) 0 := fun l => rfl
            simp only [e, evA, evO, List.map, List.any_cons, List.any_nil, Bool.or_false, id, Nat.max_zero]
            exact ha
        | [a, b], _ =>
          have ha := h a
          have hb := h b
          rcases hop' with rfl | rfl
          · have e : ∀ l : List ℕ, PEqualNP.CircuitLowerBounds.Gate.lineDegree ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ l = l.getD a 0 + (l.getD b 0 + 0) := fun l => rfl
            simp only [e, evA, evO, List.map, List.all_cons, List.all_nil, Bool.and_true, id, Nat.add_zero,
              Bool.and_eq_true]
            constructor
            · intro hz ⟨xa, xb⟩
              obtain ⟨a0, aw⟩ := ha.1 (by omega) xa
              obtain ⟨b0, bw⟩ := hb.1 (by omega) xb
              exact ⟨⟨a0, b0⟩, fun w hw => ⟨aw w hw, bw w hw⟩⟩
            · intro hz ⟨xa, xb⟩
              rcases Nat.eq_zero_or_pos (Ld.getD a 0) with da | da
              · obtain ⟨a0, aw⟩ := ha.1 da xa
                rcases hb.2 (by omega) xb with b0 | ⟨w, hw, bw⟩
                · exact Or.inl ⟨a0, b0⟩
                · exact Or.inr ⟨w, hw, aw w hw, bw⟩
              · obtain ⟨b0, bw⟩ := hb.1 (by omega) xb
                rcases ha.2 (by omega) xa with a0 | ⟨w, hw, aw⟩
                · exact Or.inl ⟨a0, b0⟩
                · exact Or.inr ⟨w, hw, aw, bw w hw⟩
          · have e : ∀ l : List ℕ, PEqualNP.CircuitLowerBounds.Gate.lineDegree ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ l = max (l.getD a 0) (max (l.getD b 0) 0) := fun l => rfl
            simp only [e, evA, evO, List.map, List.any_cons, List.any_nil, Bool.or_false, id, Nat.max_zero,
              Bool.or_eq_true]
            constructor
            · intro hz hxab
              rcases hxab with xa | xb
              · obtain ⟨a0, aw⟩ := ha.1 (by omega) xa
                exact ⟨Or.inl a0, fun w hw => Or.inl (aw w hw)⟩
              · obtain ⟨b0, bw⟩ := hb.1 (by omega) xb
                exact ⟨Or.inr b0, fun w hw => Or.inr (bw w hw)⟩
            · intro hz hxab
              rcases hxab with xa | xb
              · rcases ha.2 (by omega) xa with a0 | ⟨w, hw, aw⟩
                · exact Or.inl (Or.inl a0)
                · exact Or.inr ⟨w, hw, Or.inl aw⟩
              · rcases hb.2 (by omega) xb with b0 | ⟨w, hw, bw⟩
                · exact Or.inl (Or.inr b0)
                · exact Or.inr ⟨w, hw, Or.inr bw⟩
        | _ :: _ :: _ :: _, hl => simp at hl
      · exact ⟨fun _ hx => absurd hx (by decide), fun _ hx => absurd hx (by decide)⟩
    have main : ∀ (u0 : Fin 26 → Bool) (uw : Fin 13 → Fin 26 → Bool),
        PEqualNP.MetaComplexity.circuitFun 26 C u0 = false →
        (∀ w, PEqualNP.MetaComplexity.circuitFun 26 C (uw w) = false) →
        (∀ p : Fin 13, x (Fin.castAdd 13 p) = true → u0 (Fin.castAdd 13 p) = true) →
        (∀ p w : Fin 13, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 w) = true → uw w (Fin.castAdd 13 p) = true) →
        (∀ w : Fin 13, uw w (Fin.natAdd 13 w) = true) → False := by
      intro u0 uw r0 rW f0 fw fl
      have ind : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
          ∀ (Lx L0 : List Bool) (Lw : Fin 13 → List Bool) (Ld : List ℕ),
          Lx.length = Ld.length → L0.length = Ld.length → (∀ w, (Lw w).length = Ld.length) →
          (∀ j, (Ld.getD j 0 = 0 → Lx.getD j false = true → L0.getD j false = true ∧
              ∀ w, x (Fin.natAdd 13 w) = true → (Lw w).getD j false = true) ∧
            (Ld.getD j 0 ≤ 1 → Lx.getD j false = true → L0.getD j false = true ∨
              ∃ w, x (Fin.natAdd 13 w) = true ∧ (Lw w).getD j false = true)) →
          (∀ j, ((gs.foldl (fun d g => d ++ [g.lineDegree d]) Ld).getD j 0 = 0 →
              (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) Lx).getD j false = true →
              (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L0).getD j false = true ∧
              ∀ w, x (Fin.natAdd 13 w) = true →
                (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (Lw w)).getD j false = true) ∧
            ((gs.foldl (fun d g => d ++ [g.lineDegree d]) Ld).getD j 0 ≤ 1 →
              (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) Lx).getD j false = true →
              (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) L0).getD j false = true ∨
              ∃ w, x (Fin.natAdd 13 w) = true ∧
                (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (Lw w)).getD j false = true)) := by
        intro gs
        induction gs with
        | nil => intro _ Lx L0 Lw Ld _ _ _ h; exact h
        | cons g gs ih =>
          intro hg Lx L0 Lw Ld e1 e2 e3 h
          exact ih (fun g' h' => hg g' (List.mem_cons_of_mem g h')) _ _ _ _ (by simp [e1]) (by simp [e2])
            (fun w => by simp [e3]) (one g (hg g (List.mem_cons.mpr (Or.inl rfl))) Lx L0 Lw Ld e1 e2 e3 h)
      have base : ∀ j, ((((List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0).getD j 0 = 0 →
            (List.ofFn x).getD j false = true → (List.ofFn u0).getD j false = true ∧
              ∀ w, x (Fin.natAdd 13 w) = true → (List.ofFn (uw w)).getD j false = true) ∧
          (((List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0).getD j 0 ≤ 1 →
            (List.ofFn x).getD j false = true → (List.ofFn u0).getD j false = true ∨
              ∃ w, x (Fin.natAdd 13 w) = true ∧ (List.ofFn (uw w)).getD j false = true)) := by
        intro j
        by_cases hj : j < 26
        · have gx : ∀ f : Fin 26 → Bool, (List.ofFn f).getD j false = f ⟨j, hj⟩ := fun f => by
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            simp only [hj, dif_pos, Option.getD_some]
          have gd : ((List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0).getD j 0 =
              if 13 ≤ j then 1 else 0 := by
            simp [List.getD_eq_getElem?_getD, hj]
          simp only [gx, gd]
          by_cases hp : 13 ≤ j
          · simp only [hp, if_true]
            have e : (Fin.natAdd 13 (⟨j - 13, by omega⟩ : Fin 13) : Fin 26) = ⟨j, hj⟩ := Fin.ext (by simp; omega)
            refine ⟨fun h => absurd h (by norm_num), fun _ hxj => Or.inr ⟨⟨j - 13, by omega⟩, ?_, ?_⟩⟩
            · rw [e]; exact hxj
            · have := fl ⟨j - 13, by omega⟩
              rw [e] at this
              exact this
          · simp only [hp, if_false]
            have e : (Fin.castAdd 13 (⟨j, by omega⟩ : Fin 13) : Fin 26) = ⟨j, hj⟩ := Fin.ext rfl
            refine ⟨fun _ hxj => ⟨?_, fun w hw => ?_⟩, fun _ hxj => Or.inl ?_⟩
            · rw [← e] at hxj ⊢; exact f0 _ hxj
            · rw [← e] at hxj ⊢; exact fw _ w hxj hw
            · rw [← e] at hxj ⊢; exact f0 _ hxj
        · have go : ∀ f : Fin 26 → Bool, (List.ofFn f).getD j false = false := fun f => by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_ofFn]; omega)]; rfl
          simp only [go]
          exact ⟨fun _ h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
      have hI := ind C.gates (fun g hg => hm g hg) (List.ofFn x) (List.ofFn u0) (fun w => List.ofFn (uw w))
        ((List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0) (by simp) (by simp) (fun w => by simp) base
      rcases (hI C.output).2 hd hx with h0 | ⟨w, _, hw⟩
      · exact absurd (show PEqualNP.MetaComplexity.circuitFun 26 C u0 = true from h0) (by rw [r0]; decide)
      · exact absurd (show PEqualNP.MetaComplexity.circuitFun 26 C (uw w) = true from hw) (by rw [rW w]; decide)
    exact main _ _ r0 rW (fun p _ => decide_eq_true (Or.inl ⟨p, Finset.mem_univ p, rfl⟩))
      (fun p w hp hw => decide_eq_true (Or.inl ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, fun h => onN p w h hp hw⟩, rfl⟩))
      (fun w => decide_eq_true (Or.inr ⟨w, rfl, fun pp hpp => (Finset.mem_filter.mp hpp).2⟩))
  rintro ⟨C, hm, hs, hpos, hneg⟩
  by_cases hd : PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1
  · refine h1 ⟨C, hm, hs, hd, bridge C hm hd hneg, ?_⟩
    intro pc wc hpc
    obtain ⟨dc, hdc, heq⟩ := hpc
    apply hpos pc wc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdc
    rcases hdc with rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, Fin.ext (by simp; omega)⟩
    · exact ⟨1, by decide, Fin.ext (by simp [Fin.val_add]; omega)⟩
    · exact ⟨3, by decide, Fin.ext (by simp [Fin.val_add]; omega)⟩
    · exact ⟨9, by decide, Fin.ext (by simp [Fin.val_add]; omega)⟩
  · have hmem : ∀ a : Fin 13, a ∈ ([0, 1, 3, 9] : List (Fin 13)) ↔ a ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      decide
    refine h2 C hm hs hd (fun p w h => hpos p w (by simp only [hmem] at h; exact h)) (fun P hA hB => ?_)
    have hn := hneg P (by simp only [hmem] at hA; exact hA) (by simp only [hmem] at hB; exact hB)
    convert hn using 2
    funext kk
    exact decide_eq_decide.mpr (by simp only [hmem])
