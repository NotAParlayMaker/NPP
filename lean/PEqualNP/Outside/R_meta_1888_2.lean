import Mathlib.Tactic
import PEqualNP.Defs

-- Set one vertex to false. A gate that becomes constant, or equal to an earlier wire, is free. The
-- extra wire costs nothing if the vertex is 0 or 2 and one gate otherwise. If some vertex frees
-- enough gates (three for 0 and 2, four for the others), at most fifteen gates are left, and they
-- compute the edge function of the Petersen graph minus a vertex (all such restrictions are
-- isomorphic). So it is enough to bound that function, and circuits where every vertex frees few.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1888_2
    (minusVertex : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) 15)
    (fewFree : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin 10 → Fin 10) (W : (Fin 10 → Bool) → ℕ → Bool),
      (∀ x i, W x i = (C.wires (List.ofFn (x ∘ p) ++ [x 0 || x 2])).getD i false) →
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
      (∀ (v : Fin 10) (J : Finset ℕ), (∀ j ∈ J, j < C.size ∧ ∃ (a b : Bool), ∃ k < 11 + j,
        ∀ x : Fin 10 → Bool, x v = false → W x (11 + j) = (a && W x k || b)) →
        J.card ≤ if v = 0 ∨ v = 2 then 2 else 3) →
      ∃ x : Fin 10 → Bool, W x C.output ≠ (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  classical
  intro C p hfan hsize
  by_contra hne
  have hcomp : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [x 0 || x 2]) = (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x := by
    intro x
    by_contra h
    exact hne ⟨x, h⟩
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
  have opv : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
    intro a b
    cases a <;> cases b <;> rfl
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
  have main : ∀ (v : Fin 10) (J : Finset ℕ), (∀ j ∈ J, j < C.size ∧ ∃ (a b : Bool), ∃ k < 11 + j,
      ∀ x : Fin 10 → Bool, x v = false → (C.wires (List.ofFn (x ∘ p) ++ [x 0 || x 2])).getD (11 + j) false =
        (a && (C.wires (List.ofFn (x ∘ p) ++ [x 0 || x 2])).getD k false || b)) →
      ¬ J.card ≤ (if v = 0 ∨ v = 2 then 2 else 3) → False := by
    intro v J hJ hcard
    apply minusVertex
    let σ : Fin 10 → Fin 10 → Fin 9 := ![![0, 4, 0, 1, 6, 7, 3, 5, 2, 8], ![4, 0, 6, 1, 0, 3, 7, 8, 2, 5],
      ![0, 4, 0, 6, 1, 5, 3, 7, 8, 2], ![0, 1, 6, 0, 4, 5, 2, 8, 7, 3], ![4, 0, 1, 6, 0, 3, 5, 2, 8, 7],
      ![4, 0, 1, 2, 3, 0, 5, 6, 7, 8], ![0, 4, 3, 2, 1, 5, 0, 8, 7, 6], ![0, 1, 6, 8, 5, 4, 2, 0, 3, 7],
      ![0, 1, 2, 7, 5, 4, 6, 3, 0, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0]]
    let X : (Fin 9 → Bool) → Fin 10 → Bool := fun y i => if i = v then false else y (σ v i)
    let I : (Fin 9 → Bool) → List Bool := fun y => List.ofFn (X y ∘ p) ++ [X y 0 || X y 2]
    have hIl : ∀ y, (I y).length = 11 := fun y => by simp [I]
    have hX : ∀ y, X y v = false := fun y => by simp [X]
    have hrestr : ∀ y, C.eval (I y) = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) y := by
      intro y
      show C.eval (List.ofFn (X y ∘ p) ++ [X y 0 || X y 2]) = _
      rw [hcomp]
      have key : ∀ (v : Fin 10) (a : Fin 9 → Bool),
          (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) (fun i => if i = v then false else a (σ v i)) = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) a := by
        intro v a
        fin_cases v <;> simp [σ] <;> ac_rfl
      exact key v y
    let W : (Fin 9 → Bool) → ℕ → Bool := fun y i => (C.wires (I y)).getD i false
    have hW0 : ∀ y (i : Fin 10), W y i = X y (p i) := by
      intro y i
      have := (run C.gates C.output (I y)).2.1 i (by rw [hIl]; omega)
      refine this.trans ?_
      refine (List.getD_append _ _ _ _ (by simp)).trans ?_
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn (by simp)
    have hW10 : ∀ y, W y 10 = (X y 0 || X y 2) := by
      intro y
      have := (run C.gates C.output (I y)).2.1 10 (by rw [hIl]; omega)
      refine this.trans ?_
      refine (List.getD_append_right _ _ _ _ (by simp)).trans ?_
      simp
    have hWg : ∀ y (j : ℕ) (h : j < C.gates.length), W y (11 + j) =
        (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => if i < 11 + j then W y i else false) := by
      intro y j h
      have := (run C.gates C.output (I y)).2.2 j h
      rw [hIl] at this
      exact this
    have hWout : ∀ y i, 11 + C.gates.length ≤ i → W y i = false := by
      intro y i hi
      have := (run C.gates C.output (I y)).1
      rw [hIl] at this
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
    let e : ℕ := if v = 0 ∨ v = 2 then 0 else 1
    have build : ∀ k ≤ C.gates.length, ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
        PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k)).card ≤ k + e ∧
        ∀ i < 11 + k, (∃ b, ∀ y, W y i = b) ∨ ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
          W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
      intro k
      induction k with
      | zero =>
        intro _
        have base : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (c : Fin 10), c ≠ v → ∀ y : Fin 9 → Bool,
            X y c = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD (σ v c) false := by
          intro gs c hc y
          rw [(run gs 0 (List.ofFn y)).2.1 _ (by simp), List.getD_eq_getElem _ _ (by simp)]
          simp only [X, hc, ite_false]
          exact (List.getElem_ofFn (f := y) (by simp)).symm
        have base10 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ i < 10, (∃ b, ∀ y, W y i = b) ∨
            ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
              W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
          intro gs i hi
          have hw : ∀ y, W y i = X y (p ⟨i, hi⟩) := fun y => hW0 y ⟨i, hi⟩
          by_cases hv : p ⟨i, hi⟩ = v
          · exact Or.inl ⟨false, fun y => by rw [hw, hv, hX]⟩
          · exact Or.inr ⟨σ v (p ⟨i, hi⟩), by have := (σ v (p ⟨i, hi⟩)).2; omega, fun y => (hw y).trans (base gs _ hv y)⟩
        by_cases hv : v = 0 ∨ v = 2
        · refine ⟨[], fnil, by simp, ?_⟩
          intro i hi
          rcases Nat.lt_or_ge i 10 with h | h
          · exact base10 [] i h
          · have : i = 10 := by omega
            subst this
            rcases hv with h0 | h0
            · exact Or.inr ⟨σ v 2, by have := (σ v 2).2; omega, fun y => by
                rw [hW10, show X y 0 = false by simp [X, h0], Bool.false_or]
                exact base [] 2 (by rw [h0]; decide) y⟩
            · exact Or.inr ⟨σ v 0, by have := (σ v 0).2; omega, fun y => by
                rw [hW10, show X y 2 = false by simp [X, h0], Bool.or_false]
                exact base [] 0 (by rw [h0]; decide) y⟩
        · refine ⟨[⟨.or, [(σ v 0 : ℕ), (σ v 2 : ℕ)]⟩], fone _ _ (Or.inr (Or.inl rfl)) (by simp), by simp [e, hv], ?_⟩
          intro i hi
          rcases Nat.lt_or_ge i 10 with h | h
          · exact base10 _ i h
          · have : i = 10 := by omega
            subst this
            refine Or.inr ⟨9, by simp, fun y => ?_⟩
            have h0 : X y 0 = _ := base [] 0 (fun h => hv (Or.inl h.symm)) y
            have h2 : X y 2 = _ := base [] 2 (fun h => hv (Or.inr h.symm)) y
            have hs := wsnoc [] ⟨.or, [(σ v 0 : ℕ), (σ v 2 : ℕ)]⟩ 0 (List.ofFn y)
            rw [List.nil_append] at hs
            rw [hW10, hs, List.getD_append_right _ _ _ _ (by rw [wnil]; simp), h0, h2, wnil]
            rw [List.length_ofFn]
            exact (opv _ _).symm
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
        have keep : ((∃ b, ∀ y, W y (11 + k) = b) ∨ ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
              W y (11 + k) = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false) →
            ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
            PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k + 1)).card ≤ k + 1 + e ∧
            ∀ i < 11 + (k + 1), (∃ b, ∀ y, W y i = b) ∨ ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
              W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
          intro h
          refine ⟨gs, hgf, ?_, ?_⟩
          · split at hfilt <;> omega
          · intro i hi
            rcases Nat.lt_or_ge i (11 + k) with h' | h'
            · exact hgi i h'
            · have : i = 11 + k := by omega
              subst this; exact h
        by_cases hkJ : k ∈ J
        · apply keep
          obtain ⟨a, b, i, hi, hb⟩ := (hJ k hkJ).2
          have hb' : ∀ y, W y (11 + k) = (a && W y i || b) := fun y => hb (X y) (hX y)
          cases b with
          | true => exact Or.inl ⟨true, fun y => by rw [hb']; simp⟩
          | false =>
            cases a with
            | false => exact Or.inl ⟨false, fun y => by rw [hb']; simp⟩
            | true =>
              have hb'' : ∀ y, W y (11 + k) = W y i := fun y => by rw [hb']; simp
              rcases hgi i hi with ⟨c, hc⟩ | ⟨j, hj, hc⟩
              · exact Or.inl ⟨c, fun y => (hb'' y).trans (hc y)⟩
              · exact Or.inr ⟨j, hj, fun y => (hb'' y).trans (hc y)⟩
        · have hmem : C.gates[k] ∈ C.gates := List.getElem_mem _
          have hg := hfan _ hmem
          have hWk := fun y => hWg y k (by omega)
          generalize C.gates[k] = g at hg hWk
          let U : (Fin 9 → Bool) → ℕ → Bool := fun y j =>
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false
          let A : (Fin 9 → Bool) → ℕ → Bool := fun y i => if i < 11 + k then W y i else false
          have hA : ∀ i, (∃ b, ∀ y, A y i = b) ∨ ∃ j < 9 + gs.length, ∀ y, A y i = U y j := by
            intro i
            by_cases h : i < 11 + k
            · simpa [A, h, U] using hgi i h
            · exact Or.inl ⟨false, fun y => by simp [A, h]⟩
          have hWA : ∀ y, W y (11 + k) = g.op.eval (g.inputs.map (A y)) := hWk
          have hnew : (∃ b, ∀ y, W y (11 + k) = b) ∨ ∃ g' : PEqualNP.CircuitLowerBounds.Gate,
              PEqualNP.MetaComplexity.FanInTwo ⟨[g'], 0⟩ ∧ ∀ y, W y (11 + k) = g'.op.eval (g'.inputs.map (U y)) := by
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
            rcases Nat.lt_or_ge i (11 + k) with h' | h'
            · rcases hgi i h' with h | ⟨j, hj, h⟩
              · exact Or.inl h
              · refine Or.inr ⟨j, by simp; omega, fun y => ?_⟩
                rw [step, List.getD_append _ _ _ _ (by rw [hlen]; exact hj)]
                exact h y
            · have : i = 11 + k := by omega
              subst this
              refine Or.inr ⟨9 + gs.length, by simp, fun y => ?_⟩
              rw [step, List.getD_append_right _ _ _ _ (by rw [hlen]), hlen]
              simpa using hv y
    obtain ⟨gs, hgf, hgc, hgi⟩ := build C.gates.length (le_refl _)
    have hJf : J.filter (· < C.gates.length) = J := by
      apply Finset.filter_true_of_mem
      intro j hj
      exact (hJ j hj).1
    rw [hJf] at hgc
    have hsz : C.gates.length ≤ 18 := hsize
    have hce : 3 + e ≤ J.card := by
      by_cases h : v = 0 ∨ v = 2
      · rw [if_pos h] at hcard; simp only [e, if_pos h]; omega
      · rw [if_neg h] at hcard; simp only [e, if_neg h]; omega
    have hout : (∃ b, ∀ y, W y C.output = b) ∨ ∃ j < 9 + gs.length, ∀ y : Fin 9 → Bool,
        W y C.output = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
      rcases Nat.lt_or_ge C.output (11 + C.gates.length) with h | h
      · exact hgi _ h
      · exact Or.inl ⟨false, fun y => hWout y _ h⟩
    rcases hout with ⟨b, hb⟩ | ⟨j, _, hb⟩
    · exfalso
      have e1 := (hrestr (fun _ => true)).symm.trans (hb (fun _ => true))
      have e0 := (hrestr (fun _ => false)).symm.trans (hb (fun _ => false))
      simp at e1 e0
      exact absurd (e1.symm.trans e0) (by simp)
    · refine ⟨⟨gs, j⟩, hgf, ?_, fun y => ?_⟩
      · show gs.length ≤ 15
        omega
      · rw [← hrestr y]
        exact (hb y).symm
  have few : ∀ (v : Fin 10) (J : Finset ℕ), (∀ j ∈ J, j < C.size ∧ ∃ (a b : Bool), ∃ k < 11 + j,
      ∀ x : Fin 10 → Bool, x v = false → (C.wires (List.ofFn (x ∘ p) ++ [x 0 || x 2])).getD (11 + j) false =
        (a && (C.wires (List.ofFn (x ∘ p) ++ [x 0 || x 2])).getD k false || b)) →
      J.card ≤ if v = 0 ∨ v = 2 then 2 else 3 := by
    intro v J hJ
    by_contra hcard
    refine main v J hJ hcard
  obtain ⟨x, hx⟩ := fewFree C p _ (fun _ _ => rfl) hfan hsize few
  exact hx (hcomp x)
