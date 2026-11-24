import Mathlib.Tactic
import Mathlib.Order.Preorder.Finite
import PEqualNP.Defs

-- Set vertex 0 or vertex 7 to false. A gate that becomes constant, or equal to an earlier wire, is
-- free. The deleted edge disappears, so what is left computes the edge function of the Heawood
-- graph minus that vertex. If two gates are free, at most 22 gates do it, against the first
-- hypothesis. The second is the rest: some end of the deleted edge always frees two gates.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2276_1
    (minusVertex : ∀ (E : List (ℕ × ℕ)) (f : (Fin 14 → Bool) → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin 14),
      E = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] →
      (∀ x, f x ↔ ∃ a b : Fin 14, (a.1, b.1) ∈ E ∧ x a = true ∧ x b = true) →
      v = 0 ∨ v = 7 → PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool, x v = false → (C.eval (List.ofFn x) = true ↔ f x)) → 23 ≤ C.size)
    (freeTwo : ∀ (E : List (ℕ × ℕ)) (f : (Fin 14 → Bool) → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (W : (Fin 14 → Bool) → ℕ → Bool),
      E = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] →
      (∀ x, f x ↔ ∃ a b : Fin 14, (a.1, b.1) ∈ E ∧ x a = true ∧ x b = true) →
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 24 → (∀ x i, W x i = (C.wires (List.ofFn x)).getD i false) →
      (∀ x : Fin 14 → Bool, x 0 = false ∨ x 7 = false → (W x C.output = true ↔ f x)) →
      W (fun i => decide (i = 0 ∨ i = 7)) C.output = false →
      ∃ (v : Fin 14) (J : Finset ℕ), (v = 0 ∨ v = 7) ∧ 2 ≤ J.card ∧ ∀ j ∈ J, j < C.size ∧
        ∃ (a b : Bool), ∃ k < 14 + j, ∀ x : Fin 14 → Bool, x v = false → W x (14 + j) = (a && W x k || b)) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → x6 (0 : Fin (14 : ℕ)) = Bool.false ∨ x6 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x6) = Bool.true ↔ x2 x6)) → x4.eval (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = (0 : Fin (14 : ℕ)) ∨ x7 = (7 : Fin (14 : ℕ)))) = Bool.false → (25 : ℕ) ≤ x4.size := by
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
  have gen : ∀ (E : List (ℕ × ℕ)), E = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] →
      ∀ f : (Fin 14 → Bool) → Prop, (∀ x, f x ↔ ∃ a b : Fin 14, (a.1, b.1) ∈ E ∧ x a = true ∧ x b = true) →
      ∀ R : (Fin 14 → Bool) → Prop, (∀ x, R x ↔ ((f x ∧ ∀ c, x c = true → ¬ f (Function.update x c false)) ∨
        ¬ f x ∧ ∀ c, x c = false → f (Function.update x c true))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x, R x → x 0 = false ∨ x 7 = false → (C.eval (List.ofFn x) = true ↔ f x)) →
      C.eval (List.ofFn fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = false → 25 ≤ C.size := by
    intro E hE f hf R hR C hmono hrows h07
    by_contra hsize
    -- the circuit is monotone
    have mono : ∀ x z : Fin 14 → Bool, x ≤ z → C.eval (List.ofFn x) = true → C.eval (List.ofFn z) = true := by
      intro x z hxz
      have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
          ∀ i, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false = true →
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false = true := by
        intro gs
        induction gs using List.reverseRecOn with
        | nil =>
          intro _ i h
          rw [wnil] at h ⊢
          rcases Nat.lt_or_ge i 14 with hi | hi
          · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn] at h ⊢
            have := hxz ⟨i, hi⟩
            rw [h] at this
            exact le_antisymm (Bool.le_true _) this
          · rw [List.getD_eq_default _ _ (by simpa using hi)] at h
            exact absurd h (by simp)
        | append_singleton gs g ih =>
          intro hg i h
          have ih' := ih (fun a ha => hg a (List.mem_append_left _ ha))
          have hgop := hg g (List.mem_append_right _ List.mem_cons_self)
          have l1 := (run gs 0 (List.ofFn x)).1
          have l2 := (run gs 0 (List.ofFn z)).1
          rw [List.length_ofFn] at l1 l2
          rw [wsnoc] at h ⊢
          rcases Nat.lt_trichotomy i (14 + gs.length) with hi | hi | hi
          · rw [List.getD_append _ _ _ _ (by omega)] at h ⊢
            exact ih' i h
          · rw [List.getD_append_right _ _ _ _ (by omega), show i - (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).length = 0 by omega] at h
            rw [List.getD_append_right _ _ _ _ (by omega), show i - (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).length = 0 by omega]
            rw [List.getD_cons_zero] at h ⊢
            obtain ⟨op, l⟩ := g
            rcases hgop with hop | hop
            · subst hop
              have h' : (l.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false).all id = true := h
              show (l.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false).all id = true
              simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, id] at h' ⊢
              exact fun a ha => ih' a (h' a ha)
            · subst hop
              have h' : (l.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false).any id = true := h
              show (l.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false).any id = true
              simp only [List.any_eq_true, List.mem_map, id] at h' ⊢
              obtain ⟨b, ⟨a, ha, hab⟩, hb⟩ := h'
              exact ⟨_, ⟨a, ha, rfl⟩, ih' a (hab.trans hb)⟩
          · rw [List.getD_eq_default _ _ (by rw [List.length_append, l1]; simp; omega)] at h
            exact absurd h (by simp)
      exact key C.gates (fun g hg => (hmono g hg).1) C.output
    have hright : ∀ x : Fin 14 → Bool, x 0 = false ∨ x 7 = false → (C.eval (List.ofFn x) = true ↔ f x) := by
      intro x hx
      constructor
      · intro hC
        by_contra hfx
        obtain ⟨m, hxm, hm⟩ := (Set.toFinite {z : Fin 14 → Bool | ¬ f z}).exists_le_maximal hfx
        have hmf : ¬ f m := hm.prop
        have hm07 : m 0 = false ∨ m 7 = false := by
          by_contra h
          rw [not_or, Bool.not_eq_false, Bool.not_eq_false] at h
          exact hmf ((hf m).2 ⟨0, 7, by rw [hE]; exact List.mem_cons_self, h.1, h.2⟩)
        have hRm : R m := by
          refine (hR m).2 (Or.inr ⟨hmf, fun c hc => ?_⟩)
          by_contra hn
          have h1 : m ≤ Function.update m c true := by
            intro i
            by_cases hi : i = c
            · subst hi; rw [hc]; exact Bool.false_le _
            · rw [Function.update_of_ne hi]
          have h2 := hm.le_of_ge hn h1 c
          rw [Function.update_self, hc] at h2
          exact absurd (le_antisymm h2 (Bool.false_le _)) Bool.noConfusion
        exact hmf ((hrows m hRm hm07).1 (mono x m hxm hC))
      · intro hfx
        obtain ⟨m, hxm, hm⟩ := (Set.toFinite {z : Fin 14 → Bool | f z}).exists_le_minimal hfx
        have hmf : f m := hm.prop
        have hm07 : m 0 = false ∨ m 7 = false := by
          rcases hx with h | h
          · left; have := hxm 0; rw [h] at this; exact le_antisymm this (Bool.false_le _)
          · right; have := hxm 7; rw [h] at this; exact le_antisymm this (Bool.false_le _)
        have hRm : R m := by
          refine (hR m).2 (Or.inl ⟨hmf, fun c hc hn => ?_⟩)
          have h1 : Function.update m c false ≤ m := by
            intro i
            by_cases hi : i = c
            · subst hi; rw [Function.update_self]; exact Bool.false_le _
            · rw [Function.update_of_ne hi]
          have h2 := hm.le_of_le hn h1 c
          rw [Function.update_self, hc] at h2
          exact absurd (le_antisymm h2 (Bool.false_le _)) Bool.noConfusion
        exact mono m x hxm ((hrows m hRm hm07).2 hmf)
    obtain ⟨v, J, hv, hcard, hJ⟩ := freeTwo E f C (fun x i => (C.wires (List.ofFn x)).getD i false) hE hf hmono
      (by omega) (fun _ _ => rfl) hright h07
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
    have hsz : C.gates.length ≤ 24 := by
      have : C.size = C.gates.length := rfl
      omega
    have hout : (∃ b, ∀ y, W y C.output = b) ∨ ∃ j < 14 + gs.length, ∀ y : S,
        W y C.output = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false := by
      rcases Nat.lt_or_ge C.output (14 + C.gates.length) with h | h
      · exact hgi _ h
      · exact Or.inl ⟨false, fun y => hWout y _ h⟩
    have hok : ∀ y : S, W y C.output = true ↔ f y.1 := fun y =>
      hright y.1 (hv.imp (fun h => by rw [← h]; exact y.2) (fun h => by rw [← h]; exact y.2))
    rcases hout with ⟨b, hb⟩ | ⟨j, _, hb⟩
    · let y0 : S := ⟨fun _ => false, rfl⟩
      have hv1 : v ≠ 1 ∧ v ≠ 9 := by rcases hv with rfl | rfl <;> decide
      let y1 : S := ⟨fun i => decide (i = 1 ∨ i = 9), by simp [hv1]⟩
      have e1 : f y1.1 := (hf _).2 ⟨1, 9, by rw [hE]; decide, by simp [y1], by simp [y1]⟩
      have e0 : f y0.1 := (hok y0).1 ((hb y0).trans ((hb y1).symm.trans ((hok y1).2 e1)))
      obtain ⟨a, _, _, ha, _⟩ := (hf _).1 e0
      exact absurd ha (by simp [y0])
    · have h23 := minusVertex E f ⟨gs, j⟩ v hE hf hv hgf (fun x hx => by
        rw [← hok ⟨x, hx⟩, hb ⟨x, hx⟩]
        rfl)
      have : (PEqualNP.CircuitLowerBounds.Circuit.mk gs j).size = gs.length := rfl
      omega
  intro E f R C h1 h2 h3
  exact gen _ rfl _ (fun _ => Iff.rfl) _ (fun _ => Iff.rfl) C h1 h2 h3
