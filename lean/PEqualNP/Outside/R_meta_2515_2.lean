import Mathlib.Tactic
import PEqualNP.Defs

-- Set one of the three vertices 4, 6, 7 of degree two to false. A gate that becomes constant, or
-- equal to an earlier wire, is free, and what is left computes the edge function of the Petersen
-- graph minus the ends of an edge, which needs thirteen gates (first hypothesis; it is L-meta-2036).
-- So if three gates are free the circuit has sixteen gates. The second hypothesis is the rest.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2515_2
    (cofactor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12)
    (freeThree : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 ≤ (3 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) →
      ∃ (v : Fin 9) (J : Finset ℕ), (v = 4 ∨ v = 6 ∨ v = 7) ∧ 3 ≤ J.card ∧ ∀ j ∈ J, j < x1.size ∧
        ∃ (a b : Bool), ∃ k < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
          (x1.wires (List.ofFn x)).getD (9 + j) false = (a && (x1.wires (List.ofFn x)).getD k false || b)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 ≤ (3 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
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
  intro C hfan hnot hw9 hcomp
  by_contra hsize
  have hsz0 : C.size ≤ 15 := by omega
  obtain ⟨v, J, hv, hcard, hJ⟩ := freeThree C hfan hnot hw9 hcomp hsz0
  apply cofactor
  let σ : Fin 9 → Fin 9 → Fin 8 := ![0, 0, 0, 0, ![0, 1, 2, 3, 0, 4, 5, 6, 7], 0, ![1, 0, 4, 7, 5, 2, 0, 6, 3],
    ![1, 2, 3, 7, 5, 0, 6, 0, 4], 0]
  let X : (Fin 8 → Bool) → Fin 9 → Bool := fun y i => if i = v then false else y (σ v i)
  have hX : ∀ y, X y v = false := fun y => by simp [X]
  have hrestr : ∀ y, C.eval (List.ofFn (X y)) = (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) y := by
    intro y
    refine (congrFun hcomp (X y)).trans ?_
    have key : ∀ a : Fin 8 → Bool, (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) (fun i => if i = v then false else a (σ v i)) = (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) a := by
      intro a
      rcases hv with rfl | rfl | rfl <;> simp [σ] <;> ac_rfl
    exact key y
  let W : (Fin 8 → Bool) → ℕ → Bool := fun y i => (C.wires (List.ofFn (X y))).getD i false
  have hW0 : ∀ y (i : Fin 9), W y i = X y i := by
    intro y i
    have := (run C.gates C.output (List.ofFn (X y))).2.1 i (by simp)
    refine this.trans ?_
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn (by simp)
  have hWg : ∀ y (j : ℕ) (h : j < C.gates.length), W y (9 + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => if i < 9 + j then W y i else false) := by
    intro y j h
    have := (run C.gates C.output (List.ofFn (X y))).2.2 j h
    rw [List.length_ofFn] at this
    exact this
  have hWout : ∀ y i, 9 + C.gates.length ≤ i → W y i = false := by
    intro y i hi
    have := (run C.gates C.output (List.ofFn (X y))).1
    rw [List.length_ofFn] at this
    exact List.getD_eq_default _ _ (this.le.trans hi)
  -- a gate on constants and kept wires is constant or a gate on kept wires
  have hall : ∀ (A U : (Fin 8 → Bool) → ℕ → Bool) (m : ℕ) (l : List ℕ),
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
  have hany : ∀ (A U : (Fin 8 → Bool) → ℕ → Bool) (m : ℕ) (l : List ℕ),
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
      ∀ i < 9 + k, (∃ b, ∀ y, W y i = b) ∨ ∃ j < 8 + gs.length, ∀ y : Fin 8 → Bool,
        W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fnil, by simp, ?_⟩
      intro i hi
      have hw : ∀ y, W y i = X y ⟨i, by omega⟩ := fun y => hW0 y ⟨i, by omega⟩
      by_cases hv : (⟨i, by omega⟩ : Fin 9) = v
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
      -- wire `9 + k` is constant, kept already, or one new gate away
      have keep : ((∃ b, ∀ y, W y (9 + k) = b) ∨ ∃ j < 8 + gs.length, ∀ y : Fin 8 → Bool,
            W y (9 + k) = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false) →
          ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
          PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k + 1)).card ≤ k + 1 ∧
          ∀ i < 9 + (k + 1), (∃ b, ∀ y, W y i = b) ∨ ∃ j < 8 + gs.length, ∀ y : Fin 8 → Bool,
            W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
        intro h
        refine ⟨gs, hgf, ?_, ?_⟩
        · split at hfilt <;> omega
        · intro i hi
          rcases Nat.lt_or_ge i (9 + k) with h' | h'
          · exact hgi i h'
          · have : i = 9 + k := by omega
            subst this; exact h
      by_cases hkJ : k ∈ J
      · apply keep
        obtain ⟨a, b, i, hi, hb⟩ := (hJ k hkJ).2
        have hb' : ∀ y, W y (9 + k) = (a && W y i || b) := fun y => hb (X y) (hX y)
        cases b with
        | true => exact Or.inl ⟨true, fun y => by rw [hb']; simp⟩
        | false =>
          cases a with
          | false => exact Or.inl ⟨false, fun y => by rw [hb']; simp⟩
          | true =>
            have hb'' : ∀ y, W y (9 + k) = W y i := fun y => by rw [hb']; simp
            rcases hgi i hi with ⟨c, hc⟩ | ⟨j, hj, hc⟩
            · exact Or.inl ⟨c, fun y => (hb'' y).trans (hc y)⟩
            · exact Or.inr ⟨j, hj, fun y => (hb'' y).trans (hc y)⟩
      · have hmem : C.gates[k] ∈ C.gates := List.getElem_mem _
        have hg := hfan _ hmem
        have hWk := fun y => hWg y k (by omega)
        generalize C.gates[k] = g at hg hWk
        let U : (Fin 8 → Bool) → ℕ → Bool := fun y j =>
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false
        let A : (Fin 8 → Bool) → ℕ → Bool := fun y i => if i < 9 + k then W y i else false
        have hA : ∀ i, (∃ b, ∀ y, A y i = b) ∨ ∃ j < 8 + gs.length, ∀ y, A y i = U y j := by
          intro i
          by_cases h : i < 9 + k
          · simpa [A, h, U] using hgi i h
          · exact Or.inl ⟨false, fun y => by simp [A, h]⟩
        have hWA : ∀ y, W y (9 + k) = g.op.eval (g.inputs.map (A y)) := hWk
        have hnew : (∃ b, ∀ y, W y (9 + k) = b) ∨ ∃ g' : PEqualNP.CircuitLowerBounds.Gate,
            PEqualNP.MetaComplexity.FanInTwo ⟨[g'], 0⟩ ∧ ∀ y, W y (9 + k) = g'.op.eval (g'.inputs.map (U y)) := by
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
        have step : ∀ y : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g'], 0⟩ (List.ofFn y) =
            PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y) ++ [g'.op.eval (g'.inputs.map (U y))] := by
          intro y
          exact wsnoc gs g' 0 _
        have hlen : ∀ y : Fin 8 → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).length = 8 + gs.length := by
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
          rcases Nat.lt_or_ge i (9 + k) with h' | h'
          · rcases hgi i h' with h | ⟨j, hj, h⟩
            · exact Or.inl h
            · refine Or.inr ⟨j, by simp; omega, fun y => ?_⟩
              rw [step, List.getD_append _ _ _ _ (by rw [hlen]; exact hj)]
              exact h y
          · have : i = 9 + k := by omega
            subst this
            refine Or.inr ⟨8 + gs.length, by simp, fun y => ?_⟩
            rw [step, List.getD_append_right _ _ _ _ (by rw [hlen]), hlen]
            simpa using hv y
  obtain ⟨gs, hgf, hgc, hgi⟩ := main C.gates.length (le_refl _)
  have hJf : J.filter (· < C.gates.length) = J := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact (hJ j hj).1
  rw [hJf] at hgc
  have hsz : C.gates.length ≤ 15 := hsz0
  have hout : (∃ b, ∀ y, W y C.output = b) ∨ ∃ j < 8 + gs.length, ∀ y : Fin 8 → Bool,
      W y C.output = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
    rcases Nat.lt_or_ge C.output (9 + C.gates.length) with h | h
    · exact hgi _ h
    · exact Or.inl ⟨false, fun y => hWout y _ h⟩
  rcases hout with ⟨b, hb⟩ | ⟨j, _, hb⟩
  · exfalso
    have e1 := (hrestr (fun _ => true)).symm.trans (hb (fun _ => true))
    have e0 := (hrestr (fun _ => false)).symm.trans (hb (fun _ => false))
    simp at e1 e0
    exact absurd (e1.symm.trans e0) (by simp)
  · refine ⟨⟨gs, j⟩, hgf, ?_, fun y => ?_⟩
    · show gs.length ≤ 12
      omega
    · rw [← hrestr y]
      exact (hb y).symm
