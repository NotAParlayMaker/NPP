import Mathlib.Tactic
import PEqualNP.Defs

-- Set one vertex to false. A gate that becomes constant, or equal to an earlier wire, is free, and
-- the AND of what is left of the two wires is the edge function of the Heawood graph minus that
-- vertex. If four gates are free, at most 22 gates do it (that AND included), against the first
-- hypothesis. The second is the rest: with at most 25 gates some vertex frees four gates.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2708_1
    (minusVertex : ∀ (E : List (ℕ × ℕ)) (f : (Fin 14 → Bool) → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin 14),
      E = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] →
      (∀ x, f x ↔ ∃ a b : Fin 14, (a.1, b.1) ∈ E ∧ x a = true ∧ x b = true) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool, x v = false → (C.eval (List.ofFn x) = true ↔ f x)) → 23 ≤ C.size)
    (freeFour : ∀ (E : List (ℕ × ℕ)) (f : (Fin 14 → Bool) → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (W : (Fin 14 → Bool) → ℕ → Bool) (p q : ℕ),
      E = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] →
      (∀ x, f x ↔ ∃ a b : Fin 14, (a.1, b.1) ∈ E ∧ x a = true ∧ x b = true) →
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 25 → (∀ x i, W x i = (C.wires (List.ofFn x)).getD i false) →
      (∀ x, f x ↔ W x p = true ∧ W x q = true) →
      (∃ x, W x p = false ∧ W x q = true) → (∃ x, W x q = false ∧ W x p = true) →
      ∃ (v : Fin 14) (J : Finset ℕ), 4 ≤ J.card ∧ ∀ j ∈ J, j < C.size ∧
        ∃ (a b : Bool), ∃ k < 14 + j, ∀ x : Fin 14 → Bool, x v = false → W x (14 + j) = (a && W x k || b)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size := by
  classical
  have wnil : ∀ (o : ℕ) (x : List Bool), PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[], o⟩ x = x := fun _ _ => rfl
  have wsnoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
        [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
    fun gs g o x => List.foldl_append
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
  have gen : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : ℕ), PEqualNP.MetaComplexity.Monotone2 C →
      p < 14 + C.size → q < 14 + C.size →
      ∀ (E : List (ℕ × ℕ)), E = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] →
      ∀ f : (Fin 14 → Bool) → Prop, (∀ x, f x ↔ ∃ a b : Fin 14, (a.1, b.1) ∈ E ∧ x a = true ∧ x b = true) →
      ∀ V : ℕ → (Fin 14 → Bool) → Bool, V = (fun i x => (C.wires (List.ofFn x)).getD i false) →
      (∀ x, f x → V p x = true ∧ V q x = true) → (∀ x, ¬ f x → V p x = false ∨ V q x = false) →
      (∃ x, ¬ f x ∧ V p x = false ∧ V q x = true) → (∃ x, ¬ f x ∧ V q x = false ∧ V p x = true) → 26 ≤ C.size := by
    intro C p q hmono hp hq E hE f hf V hV htrue hfalse hs1 hs2
    by_contra hsize
    subst hV
    have hboth : ∀ x, f x ↔ (C.wires (List.ofFn x)).getD p false = true ∧ (C.wires (List.ofFn x)).getD q false = true := by
      intro x
      refine ⟨htrue x, fun h => ?_⟩
      by_contra hn
      rcases hfalse x hn with h' | h'
      · exact absurd (h'.symm.trans h.1) Bool.noConfusion
      · exact absurd (h'.symm.trans h.2) Bool.noConfusion
    obtain ⟨v, J, hcard, hJ⟩ := freeFour E f C (fun x i => (C.wires (List.ofFn x)).getD i false) p q hE hf hmono
      (by omega) (fun _ _ => rfl) hboth (hs1.imp fun _ h => h.2) (hs2.imp fun _ h => h.2)
    let S := {y : Fin 14 → Bool // y v = false}
    let W : S → ℕ → Bool := fun y i => (C.wires (List.ofFn y.1)).getD i false
    have hW0 : ∀ (y : S) (i : Fin 14), W y i = y.1 i := by
      intro y i
      have := (run C.gates C.output (List.ofFn y.1)).2.1 i (by simp)
      refine this.trans ?_
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn (by simp)
    have hWg : ∀ (y : S) (j : ℕ) (h : j < C.gates.length), W y (14 + j) =
        (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => if i < 14 + j then W y i else false) := by
      intro y j h
      have := (run C.gates C.output (List.ofFn y.1)).2.2 j h
      rw [List.length_ofFn] at this
      exact this
    have hWout : ∀ (y : S) i, 14 + C.gates.length ≤ i → W y i = false := by
      intro y i hi
      have := (run C.gates C.output (List.ofFn y.1)).1
      rw [List.length_ofFn] at this
      exact List.getD_eq_default _ _ (this.le.trans hi)
    have hall : ∀ (A U : {y : Fin 14 → Bool // y v = false} → ℕ → Bool) (m : ℕ) (l : List ℕ),
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
    have hany : ∀ (A U : {y : Fin 14 → Bool // y v = false} → ℕ → Bool) (m : ℕ) (l : List ℕ),
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
        PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k)).card ≤ k ∧
        ∀ i < 14 + k, (∃ b, ∀ y, W y i = b) ∨ ∃ j < 14 + gs.length, ∀ y : S,
          W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨[], (fun g hg => absurd hg List.not_mem_nil), by simp, ?_⟩
        intro i hi
        refine Or.inr ⟨i, by simpa using hi, fun y => ?_⟩
        rw [wnil]
        refine (hW0 y ⟨i, hi⟩).trans ?_
        rw [List.getD_eq_getElem _ _ (by simpa using hi)]
        exact (List.getElem_ofFn (f := y.1) (by simpa using hi)).symm
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
        -- wire `14 + k` is constant, kept already, or one new gate away
        have keep : ((∃ b, ∀ y, W y (14 + k) = b) ∨ ∃ j < 14 + gs.length, ∀ y : S,
              W y (14 + k) = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false) →
            ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
            PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k + 1)).card ≤ k + 1 ∧
            ∀ i < 14 + (k + 1), (∃ b, ∀ y, W y i = b) ∨ ∃ j < 14 + gs.length, ∀ y : S,
              W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false := by
          intro h
          refine ⟨gs, hgf, ?_, ?_⟩
          · split at hfilt <;> omega
          · intro i hi
            rcases Nat.lt_or_ge i (14 + k) with h' | h'
            · exact hgi i h'
            · have : i = 14 + k := by omega
              subst this; exact h
        by_cases hkJ : k ∈ J
        · apply keep
          obtain ⟨a, b, i, hi, hb⟩ := (hJ k hkJ).2
          have hb' : ∀ y : S, W y (14 + k) = (a && W y i || b) := fun y => hb y.1 y.2
          cases b with
          | true => exact Or.inl ⟨true, fun y => by rw [hb']; simp⟩
          | false =>
            cases a with
            | false => exact Or.inl ⟨false, fun y => by rw [hb']; simp⟩
            | true =>
              have hb'' : ∀ y, W y (14 + k) = W y i := fun y => by rw [hb']; simp
              rcases hgi i hi with ⟨c, hc⟩ | ⟨j, hj, hc⟩
              · exact Or.inl ⟨c, fun y => (hb'' y).trans (hc y)⟩
              · exact Or.inr ⟨j, hj, fun y => (hb'' y).trans (hc y)⟩
        · have hmem : C.gates[k] ∈ C.gates := List.getElem_mem _
          have hg := hmono _ hmem
          have hWk := fun y => hWg y k (by omega)
          generalize C.gates[k] = g at hg hWk
          let U : S → ℕ → Bool := fun y j =>
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false
          let A : S → ℕ → Bool := fun y i => if i < 14 + k then W y i else false
          have hA : ∀ i, (∃ b, ∀ y, A y i = b) ∨ ∃ j < 14 + gs.length, ∀ y, A y i = U y j := by
            intro i
            by_cases h : i < 14 + k
            · simpa [A, h, U] using hgi i h
            · exact Or.inl ⟨false, fun y => by simp [A, h]⟩
          have hWA : ∀ y, W y (14 + k) = g.op.eval (g.inputs.map (A y)) := hWk
          have hnew : (∃ b, ∀ y, W y (14 + k) = b) ∨ ∃ g' : PEqualNP.CircuitLowerBounds.Gate,
              PEqualNP.MetaComplexity.Monotone2 ⟨[g'], 0⟩ ∧ ∀ y, W y (14 + k) = g'.op.eval (g'.inputs.map (U y)) := by
            obtain ⟨op, l⟩ := g
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            obtain ⟨hop, hlen⟩ := hg
            rcases hop with rfl | rfl
            · rcases hall A U _ l (fun i _ => hA i) with h | ⟨l', h1, h3⟩
              · exact Or.inl ⟨false, fun y => (hWA y).trans (h y)⟩
              · exact Or.inr ⟨⟨.and, l'⟩, (fun g hg => by obtain rfl := List.mem_singleton.1 hg; exact ⟨Or.inl rfl, h1.trans hlen⟩), fun y => (hWA y).trans (h3 y)⟩
            · rcases hany A U _ l (fun i _ => hA i) with h | ⟨l', h1, h3⟩
              · exact Or.inl ⟨true, fun y => (hWA y).trans (h y)⟩
              · exact Or.inr ⟨⟨.or, l'⟩, (fun g hg => by obtain rfl := List.mem_singleton.1 hg; exact ⟨Or.inr rfl, h1.trans hlen⟩), fun y => (hWA y).trans (h3 y)⟩
          rcases hnew with h | ⟨g', hg', hv⟩
          · exact keep (Or.inl h)
          have step : ∀ y : S, PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g'], 0⟩ (List.ofFn y.1) =
              PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1) ++ [g'.op.eval (g'.inputs.map (U y))] := by
            intro y
            exact wsnoc gs g' 0 _
          have hlen : ∀ y : S, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).length = 14 + gs.length := by
            intro y
            have := (run gs 0 (List.ofFn y.1)).1
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
            rcases Nat.lt_or_ge i (14 + k) with h' | h'
            · rcases hgi i h' with h | ⟨j, hj, h⟩
              · exact Or.inl h
              · refine Or.inr ⟨j, by simp; omega, fun y => ?_⟩
                rw [step, List.getD_append _ _ _ _ (by rw [hlen]; exact hj)]
                exact h y
            · have : i = 14 + k := by omega
              subst this
              refine Or.inr ⟨14 + gs.length, by simp, fun y => ?_⟩
              rw [step, List.getD_append_right _ _ _ _ (by rw [hlen]), hlen]
              simpa using hv y
    obtain ⟨gs, hgf, hgc, hgi⟩ := main C.gates.length (le_refl _)
    have hJf : J.filter (· < C.gates.length) = J := by
      apply Finset.filter_true_of_mem
      intro j hj
      exact (hJ j hj).1
    rw [hJf] at hgc
    have hsz : C.gates.length ≤ 25 := by
      have : C.size = C.gates.length := rfl
      omega
    have hok : ∀ y : S, f y.1 ↔ W y p = true ∧ W y q = true := fun y => hboth y.1
    -- an input with an edge, and one without
    let y0 : S := ⟨fun _ => false, rfl⟩
    have hc : ∃ c d : Fin 14, (c.1, d.1) ∈ E ∧ v ≠ c ∧ v ≠ d := by
      rw [hE]
      clear * -
      revert v
      decide
    obtain ⟨c, d, hcd, hc1, hc2⟩ := hc
    let y1 : S := ⟨fun i => decide (i = c ∨ i = d), decide_eq_false (not_or.2 ⟨hc1, hc2⟩)⟩
    have e1 : f y1.1 := (hf _).2 ⟨c, d, hcd, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
    have e0 : ¬ f y0.1 := by
      intro h
      obtain ⟨a, _, _, ha, _⟩ := (hf _).1 h
      exact absurd ha Bool.noConfusion
    -- a circuit on the kept gates is impossible
    have hno : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 22 →
        (∀ y : S, D.eval (List.ofFn y.1) = true ↔ f y.1) → False := by
      intro D hD hDs hDf
      have := minusVertex E f D v hE hf hD (fun x hx => hDf ⟨x, hx⟩)
      omega
    have hlast : ∀ y : Fin 14 → Bool,
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).length = 14 + gs.length := by
      intro y
      have := (run gs 0 (List.ofFn y)).1
      rwa [List.length_ofFn] at this
    rcases hgi p hp with ⟨b, hb⟩ | ⟨j, _, hj⟩
    · cases b with
      | false => exact absurd ((hb y1).symm.trans ((hok y1).1 e1).1) Bool.noConfusion
      | true =>
        rcases hgi q hq with ⟨b', hb'⟩ | ⟨k, _, hk⟩
        · exact e0 ((hok y0).2 ⟨hb y0, (hb' y0).trans ((hb' y1).symm.trans ((hok y1).1 e1).2)⟩)
        · refine hno ⟨gs, k⟩ hgf (show gs.length ≤ 22 by omega) (fun y => ?_)
          rw [hok y]
          exact ⟨fun h => ⟨hb y, (hk y).trans h⟩, fun h => (hk y).symm.trans h.2⟩
    · rcases hgi q hq with ⟨b', hb'⟩ | ⟨k, _, hk⟩
      · cases b' with
        | false => exact absurd ((hb' y1).symm.trans ((hok y1).1 e1).2) Bool.noConfusion
        | true =>
          refine hno ⟨gs, j⟩ hgf (show gs.length ≤ 22 by omega) (fun y => ?_)
          rw [hok y]
          exact ⟨fun h => ⟨(hj y).trans h, hb' y⟩, fun h => (hj y).symm.trans h.1⟩
      · refine hno ⟨gs ++ [⟨.and, [j, k]⟩], 14 + gs.length⟩ ?_
          (show (gs ++ [_]).length ≤ 22 by rw [List.length_append, List.length_singleton]; omega) (fun y => ?_)
        · intro g hg
          rcases List.mem_append.1 hg with h | h
          · exact hgf g h
          · obtain rfl := List.mem_singleton.1 h
            exact ⟨Or.inl rfl, le_refl _⟩
        · rw [hok y, hj y, hk y]
          have hw := wsnoc gs ⟨.and, [j, k]⟩ 0 (List.ofFn y.1)
          have : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [⟨.and, [j, k]⟩], 0⟩ (List.ofFn y.1)).getD (14 + gs.length) false =
              ((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false &&
                (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD k false) := by
            rw [hw, List.getD_append_right _ _ _ _ (by rw [hlast]), hlast, Nat.sub_self, List.getD_cons_zero]
            show (_ && (_ && true)) = _
            rw [Bool.and_true]
            rfl
          exact (Bool.eq_iff_iff.1 this).trans Bool.and_eq_true_iff
  intro C p q h1 h2 h3 E f V h4 h5 h6 h7
  exact gen C p q h1 h2 h3 _ rfl _ (fun _ => Iff.rfl) _ rfl h4 h5 h6 h7
