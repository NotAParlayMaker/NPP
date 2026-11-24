import Mathlib.Tactic
import PEqualNP.Defs

-- Set one vertex to false. A gate that becomes constant, or equal to an earlier wire, is free, and
-- the AND of what is left of the two wires is the edge function of the Petersen graph minus a vertex
-- (all such restrictions are isomorphic). If four of the eighteen gates are free, fifteen gates do
-- it (that AND included), against the first hypothesis. The second is the rest.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2375_2
    (minusVertex : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) 15)
    (freeFour : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (W : (Fin 10 → Bool) → ℕ → Bool) (p q : ℕ),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 → (∀ x i, W x i = (C.wires (List.ofFn x)).getD i false) →
      (∀ x, (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x = (W x p && W x q)) →
      (∃ x, W x p = true ∧ W x q = false) → (∃ x, W x p = false ∧ W x q = true) →
      ∃ (v : Fin 10) (J : Finset ℕ), 4 ≤ J.card ∧ ∀ j ∈ J, j < C.size ∧
        ∃ (a b : Bool), ∃ k < 10 + j, ∀ x : Fin 10 → Bool, x v = false → W x (10 + j) = (a && W x k || b)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  classical
  have wnil : ∀ (o : ℕ) (x : List Bool), PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[], o⟩ x = x := fun _ _ => rfl
  have wsnoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
        [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
    fun gs g o x => List.foldl_append
  have fnil : PEqualNP.MetaComplexity.FanInTwo ⟨[], 0⟩ := fun g hg => absurd hg List.not_mem_nil
  have fone : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (l : List ℕ),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ op = PEqualNP.CircuitLowerBounds.GateOp.not) → l.length ≤ 2 → PEqualNP.MetaComplexity.FanInTwo ⟨[⟨op, l⟩], 0⟩ := by
    intro op l h hl a ha
    obtain rfl := List.mem_singleton.1 ha
    exact ⟨h, hl⟩
  -- facts about running a list of gates
  have run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length ∧
      (∀ i < x.length, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false = x.getD i false) ∧
      ∀ (j : ℕ) (h : j < gs.length), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD (x.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < x.length + j then
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false else false) := by
    intro gs o x
    induction gs using List.reverseRecOn with
    | nil => refine ⟨by rw [wnil]; simp, fun i _ => by rw [wnil], fun j h => absurd h (Nat.not_lt_zero _)⟩
    | append_singleton gs g ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have e : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x =
          PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
            [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
        wsnoc gs g o x
      rw [e]
      generalize PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x = W at h1 h2 h3 ⊢
      generalize hval : g.op.eval (g.inputs.map fun i => W.getD i false) = val
      have old : ∀ i < W.length, (W ++ [val]).getD i false = W.getD i false := fun i hi =>
        List.getD_append _ _ _ _ hi
      refine ⟨by simp [h1]; omega, fun i hi => by rw [old i (by omega)]; exact h2 i hi, ?_⟩
      intro j hj
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · rw [old _ (by omega), h3 j hlt, List.getElem_append_left hlt]
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · rfl
      · have hj' : j = gs.length := by simp at hj; omega
        subst hj'
        rw [← h1, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero, List.getElem_concat_length]
        refine hval.symm.trans ?_
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · exact List.getD_eq_default _ _ (by omega)
  have gen : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
      (∃ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD p false = true ∧ (C.wires (List.ofFn x)).getD q false = false) →
      (∃ x : Fin 10 → Bool, (C.wires (List.ofFn x)).getD p false = false ∧ (C.wires (List.ofFn x)).getD q false = true) →
      (∀ x : Fin 10 → Bool, (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x = ((C.wires (List.ofFn x)).getD p false && (C.wires (List.ofFn x)).getD q false)) → False := by
    intro C p q hfan hsize hs1 hs2 hboth
    obtain ⟨v, J, hcard, hJ⟩ := freeFour C (fun x i => (C.wires (List.ofFn x)).getD i false) p q hfan hsize
      (fun _ _ => rfl) hboth hs1 hs2
    apply minusVertex
    let σ : Fin 10 → Fin 10 → Fin 9 := ![![0, 4, 0, 1, 6, 7, 3, 5, 2, 8], ![4, 0, 6, 1, 0, 3, 7, 8, 2, 5],
      ![0, 4, 0, 6, 1, 5, 3, 7, 8, 2], ![0, 1, 6, 0, 4, 5, 2, 8, 7, 3], ![4, 0, 1, 6, 0, 3, 5, 2, 8, 7],
      ![4, 0, 1, 2, 3, 0, 5, 6, 7, 8], ![0, 4, 3, 2, 1, 5, 0, 8, 7, 6], ![0, 1, 6, 8, 5, 4, 2, 0, 3, 7],
      ![0, 1, 2, 7, 5, 4, 6, 3, 0, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0]]
    let X : (Fin 9 → Bool) → Fin 10 → Bool := fun y i => if i = v then false else y (σ v i)
    have hX : ∀ y, X y v = false := fun y => by simp [X]
    have hrestr : ∀ y, (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) (X y) = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) y := by
      intro y
      have key : ∀ (v : Fin 10) (a : Fin 9 → Bool),
          (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) (fun i => if i = v then false else a (σ v i)) = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) a := by
        intro v a
        fin_cases v <;> simp [σ] <;> ac_rfl
      exact key v y
    let W : (Fin 9 → Bool) → ℕ → Bool := fun y i => (C.wires (List.ofFn (X y))).getD i false
    have hW0 : ∀ y (i : Fin 10), W y i = X y i := by
      intro y i
      have := (run C.gates C.output (List.ofFn (X y))).2.1 i (by simp)
      refine this.trans ?_
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn (by simp)
    have hWg : ∀ y (j : ℕ) (h : j < C.gates.length), W y (10 + j) =
        (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => if i < 10 + j then W y i else false) := by
      intro y j h
      have := (run C.gates C.output (List.ofFn (X y))).2.2 j h
      rw [List.length_ofFn] at this
      exact this
    have hWout : ∀ y i, 10 + C.gates.length ≤ i → W y i = false := by
      intro y i hi
      have := (run C.gates C.output (List.ofFn (X y))).1
      rw [List.length_ofFn] at this
      exact List.getD_eq_default _ _ (this.le.trans hi)
    -- a gate on constants and kept wires is constant or a gate on kept wires
    have hall : ∀ (A U : (Fin 9 → Bool) → ℕ → Bool) (m : ℕ) (l : List ℕ),
        (∀ i ∈ l, (∃ b, ∀ y, A y i = b) ∨ ∃ k < m, ∀ y, A y i = U y k) →
        (∀ y, (l.map (A y)).all id = false) ∨
          ∃ l' : List ℕ, l'.length ≤ l.length ∧ ∀ y, (l.map (A y)).all id = (l'.map (U y)).all id := by
      intro A U m l
      induction l with
      | nil => intro _; exact Or.inr ⟨[], by simp⟩
      | cons i l ih =>
        intro h
        rcases ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) with h0 | ⟨l', hl, he⟩
        · left; intro y; simp only [List.map_cons, List.all_cons, h0 y, Bool.and_false]
        rcases h i List.mem_cons_self with ⟨b, hb⟩ | ⟨k, hk, hb⟩
        · cases b
          · left; intro y; simp only [List.map_cons, List.all_cons, hb y, id, Bool.false_and]
          · exact Or.inr ⟨l', by simp; omega, fun y => by
              rw [List.map_cons, List.all_cons, hb y, he y]; simp⟩
        · exact Or.inr ⟨k :: l', by simpa using hl, fun y => by
            rw [List.map_cons, List.all_cons, hb y, he y, List.map_cons, List.all_cons]⟩
    have hany : ∀ (A U : (Fin 9 → Bool) → ℕ → Bool) (m : ℕ) (l : List ℕ),
        (∀ i ∈ l, (∃ b, ∀ y, A y i = b) ∨ ∃ k < m, ∀ y, A y i = U y k) →
        (∀ y, (l.map (A y)).any id = true) ∨
          ∃ l' : List ℕ, l'.length ≤ l.length ∧ ∀ y, (l.map (A y)).any id = (l'.map (U y)).any id := by
      intro A U m l
      induction l with
      | nil => intro _; exact Or.inr ⟨[], by simp⟩
      | cons i l ih =>
        intro h
        rcases ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) with h0 | ⟨l', hl, he⟩
        · left; intro y; simp only [List.map_cons, List.any_cons, h0 y, Bool.or_true]
        rcases h i List.mem_cons_self with ⟨b, hb⟩ | ⟨k, hk, hb⟩
        · cases b
          · exact Or.inr ⟨l', by simp; omega, fun y => by
              rw [List.map_cons, List.any_cons, hb y, he y]; simp⟩
          · left; intro y; simp only [List.map_cons, List.any_cons, hb y, id, Bool.true_or]
        · exact Or.inr ⟨k :: l', by simpa using hl, fun y => by
            rw [List.map_cons, List.any_cons, hb y, he y, List.map_cons, List.any_cons]⟩
    have main : ∀ k ≤ C.gates.length, ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
        PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k)).card ≤ k ∧
        ∀ i < 10 + k, (∃ b, ∀ y, W y i = b) ∨ ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
          W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨[], fnil, by simp, ?_⟩
        intro i hi
        have hw : ∀ y, W y i = X y ⟨i, by omega⟩ := fun y => hW0 y ⟨i, by omega⟩
        by_cases hv : (⟨i, by omega⟩ : Fin 10) = v
        · exact Or.inl ⟨false, fun y => by rw [hw, hv, hX]⟩
        · refine Or.inr ⟨σ v ⟨i, by omega⟩, by simp, fun y => ?_⟩
          rw [hw]
          have hl := List.getElem_ofFn (f := y) (i := (σ v ⟨i, by omega⟩ : ℕ)) (by simp)
          simp only [X, hv, ite_false, wnil]
          rw [List.getD_eq_getElem _ _ (by simp)]
          exact hl.symm
      | succ k ih =>
        intro hk
        obtain ⟨gs, hgf, hgc, hgi⟩ := ih (by omega)
        have hfilt : (J.filter (· < k + 1)).card ≤ (J.filter (· < k)).card + (if k ∈ J then 1 else 0) := by
          have hsub : J.filter (· < k + 1) ⊆ J.filter (· < k) ∪ (if k ∈ J then {k} else ∅) := by
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_union] at ha ⊢
            rcases Nat.lt_or_ge a k with h | h
            · exact Or.inl ⟨ha.1, h⟩
            · have : a = k := by omega
              subst this
              right; simp [ha.1]
          refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
          split <;> simp
        -- wire `10 + k` is constant, kept already, or one new gate away
        have keep : ((∃ b, ∀ y, W y (10 + k) = b) ∨ ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
              W y (10 + k) = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false) →
            ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
            PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k + 1)).card ≤ k + 1 ∧
            ∀ i < 10 + (k + 1), (∃ b, ∀ y, W y i = b) ∨ ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
              W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
          intro h
          refine ⟨gs, hgf, ?_, ?_⟩
          · split at hfilt <;> omega
          · intro i hi
            rcases Nat.lt_or_ge i (10 + k) with h' | h'
            · exact hgi i h'
            · have : i = 10 + k := by omega
              subst this; exact h
        by_cases hkJ : k ∈ J
        · apply keep
          obtain ⟨a, b, i, hi, hb⟩ := (hJ k hkJ).2
          have hb' : ∀ y, W y (10 + k) = (a && W y i || b) := fun y => hb (X y) (hX y)
          cases b with
          | true => exact Or.inl ⟨true, fun y => by rw [hb']; simp⟩
          | false =>
            cases a with
            | false => exact Or.inl ⟨false, fun y => by rw [hb']; simp⟩
            | true =>
              have hb'' : ∀ y, W y (10 + k) = W y i := fun y => by rw [hb']; simp
              rcases hgi i hi with ⟨c, hc⟩ | ⟨j, hj, hc⟩
              · exact Or.inl ⟨c, fun y => (hb'' y).trans (hc y)⟩
              · exact Or.inr ⟨j, hj, fun y => (hb'' y).trans (hc y)⟩
        · have hmem : C.gates[k] ∈ C.gates := List.getElem_mem _
          have hg := hfan _ hmem
          have hWk := fun y => hWg y k (by omega)
          generalize C.gates[k] = g at hg hWk
          let U : (Fin 9 → Bool) → ℕ → Bool := fun y j =>
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false
          let A : (Fin 9 → Bool) → ℕ → Bool := fun y i => if i < 10 + k then W y i else false
          have hA : ∀ i, (∃ b, ∀ y, A y i = b) ∨ ∃ j < 9 + gs.length, ∀ y, A y i = U y j := by
            intro i
            by_cases h : i < 10 + k
            · simpa [A, h, U] using hgi i h
            · exact Or.inl ⟨false, fun y => by simp [A, h]⟩
          have hWA : ∀ y, W y (10 + k) = g.op.eval (g.inputs.map (A y)) := hWk
          have hnew : (∃ b, ∀ y, W y (10 + k) = b) ∨ ∃ g' : PEqualNP.CircuitLowerBounds.Gate,
              PEqualNP.MetaComplexity.FanInTwo ⟨[g'], 0⟩ ∧ ∀ y, W y (10 + k) = g'.op.eval (g'.inputs.map (U y)) := by
            obtain ⟨op, l⟩ := g
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            obtain ⟨hop, hlen⟩ := hg
            rcases hop with rfl | rfl | rfl
            · rcases hall A U _ l (fun i _ => hA i) with h | ⟨l', h1, h3⟩
              · exact Or.inl ⟨false, fun y => (hWA y).trans (h y)⟩
              · exact Or.inr ⟨⟨.and, l'⟩, fone _ _ (Or.inl rfl) (h1.trans hlen), fun y => (hWA y).trans (h3 y)⟩
            · rcases hany A U _ l (fun i _ => hA i) with h | ⟨l', h1, h3⟩
              · exact Or.inl ⟨true, fun y => (hWA y).trans (h y)⟩
              · exact Or.inr ⟨⟨.or, l'⟩, fone _ _ (Or.inr (Or.inl rfl)) (h1.trans hlen), fun y => (hWA y).trans (h3 y)⟩
            · cases l with
              | nil => exact Or.inl ⟨true, fun y => by rw [hWA]; rfl⟩
              | cons i l =>
                rcases hA i with ⟨b, hb⟩ | ⟨j, _, hb⟩
                · exact Or.inl ⟨!b, fun y => by rw [hWA, ← hb y]; rfl⟩
                · exact Or.inr ⟨⟨.not, [j]⟩, fone _ _ (Or.inr (Or.inr rfl)) (by simp), fun y => by
                    rw [hWA]; show (!(A y i)) = !(U y j); rw [hb y]⟩
          rcases hnew with h | ⟨g', hg', hv⟩
          · exact keep (Or.inl h)
          have step : ∀ y : Fin 9 → Bool, PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g'], 0⟩ (List.ofFn y) =
              PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y) ++ [g'.op.eval (g'.inputs.map (U y))] := by
            intro y
            exact wsnoc gs g' 0 _
          have hlen : ∀ y : Fin 9 → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).length = 9 + gs.length := by
            intro y
            have := (run gs 0 (List.ofFn y)).1
            rwa [List.length_ofFn] at this
          refine ⟨gs ++ [g'], ?_, ?_, ?_⟩
          · intro a ha
            rcases List.mem_append.1 ha with h | h
            · exact hgf a h
            · exact hg' a h
          · simp only [hkJ, ite_false] at hfilt
            simp only [List.length_append, List.length_singleton]
            omega
          · intro i hi
            rcases Nat.lt_or_ge i (10 + k) with h' | h'
            · rcases hgi i h' with h | ⟨j, hj, h⟩
              · exact Or.inl h
              · refine Or.inr ⟨j, by simp; omega, fun y => ?_⟩
                rw [step, List.getD_append _ _ _ _ (by rw [hlen]; exact hj)]
                exact h y
            · have : i = 10 + k := by omega
              subst this
              refine Or.inr ⟨9 + gs.length, by simp, fun y => ?_⟩
              rw [step, List.getD_append_right _ _ _ _ (by rw [hlen]), hlen]
              simpa using hv y
    obtain ⟨gs, hgf, hgc, hgi⟩ := main C.gates.length (le_refl _)
    have hJf : J.filter (· < C.gates.length) = J := by
      apply Finset.filter_true_of_mem
      intro j hj
      exact (hJ j hj).1
    rw [hJf] at hgc
    have hsz : C.gates.length ≤ 18 := hsize
    have hok : ∀ y, (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) y = (W y p && W y q) := fun y => (hrestr y).symm.trans (hboth (X y))
    have hin : ∀ i, (∃ b, ∀ y, W y i = b) ∨ ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
        W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
      intro i
      rcases Nat.lt_or_ge i (10 + C.gates.length) with h | h
      · exact hgi _ h
      · exact Or.inl ⟨false, fun y => hWout y _ h⟩
    have e1 : W (fun _ => true) p = true ∧ W (fun _ => true) q = true := by
      have := hok (fun _ => true)
      exact Bool.and_eq_true_iff.1 (this.symm.trans (by rfl))
    have e0 : ¬ (W (fun _ => false) p = true ∧ W (fun _ => false) q = true) := by
      intro h
      have := hok (fun _ => false)
      rw [h.1, h.2] at this
      exact absurd this (by decide)
    have hlast : ∀ y : Fin 9 → Bool,
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).length = 9 + gs.length := by
      intro y
      have := (run gs 0 (List.ofFn y)).1
      rwa [List.length_ofFn] at this
    rcases hin p with ⟨b, hb⟩ | ⟨j, _, hj⟩
    · have hbt : b = true := (hb (fun _ => true)).symm.trans e1.1
      subst hbt
      rcases hin q with ⟨b', hb'⟩ | ⟨k, _, hk⟩
      · exact absurd ⟨hb (fun _ => false), (hb' (fun _ => false)).trans ((hb' (fun _ => true)).symm.trans e1.2)⟩ e0
      · refine ⟨⟨gs, k⟩, hgf, (show gs.length ≤ 15 by omega), fun y => ?_⟩
        rw [hok y, hb y, Bool.true_and]
        exact (hk y).symm
    · rcases hin q with ⟨b', hb'⟩ | ⟨k, _, hk⟩
      · have hbt : b' = true := (hb' (fun _ => true)).symm.trans e1.2
        subst hbt
        refine ⟨⟨gs, j⟩, hgf, (show gs.length ≤ 15 by omega), fun y => ?_⟩
        rw [hok y, hb' y, Bool.and_true]
        exact (hj y).symm
      · refine ⟨⟨gs ++ [⟨.and, [j, k]⟩], 9 + gs.length⟩, ?_,
          (show (gs ++ [_]).length ≤ 15 by rw [List.length_append, List.length_singleton]; omega), fun y => ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with h | h
          · exact hgf g h
          · obtain rfl := List.mem_singleton.1 h
            exact ⟨Or.inl rfl, le_refl _⟩
        · rw [hok y, hj y, hk y]
          have hw := wsnoc gs ⟨.and, [j, k]⟩ 0 (List.ofFn y)
          have : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [⟨.and, [j, k]⟩], 0⟩ (List.ofFn y)).getD (9 + gs.length) false =
              ((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false &&
                (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD k false) := by
            rw [hw, List.getD_append_right _ _ _ _ (by rw [hlast]), hlast, Nat.sub_self, List.getD_cons_zero]
            show (_ && (_ && true)) = _
            rw [Bool.and_true]
            rfl
          exact this
  intro g D p q hg hD hsize f w hs1 hs2 htrue
  by_contra hno
  refine gen ⟨g :: D.gates, 0⟩ p q ?_ ?_ hs1 hs2 ?_
  · intro a ha
    rcases List.mem_cons.1 ha with rfl | h
    · exact hg a List.mem_cons_self
    · exact hD a h
  · have : D.gates.length ≤ 17 := hsize
    show (g :: D.gates).length ≤ 18
    rw [List.length_cons]
    omega
  · intro x
    rw [Bool.eq_iff_iff, Bool.and_eq_true_iff]
    refine ⟨fun h => htrue x h, fun h => ?_⟩
    by_contra hn
    exact hno ⟨x, Bool.eq_false_iff.2 hn, h.1, h.2⟩
