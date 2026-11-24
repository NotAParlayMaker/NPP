import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2658_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C' ∧
        PEqualNP.TopForm.TopForm G C' ∧
        C'.size ≤ C.size ∧
        (PEqualNP.TopForm.junk G C' = ∅ →
          ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
            G.edgeFinset.card + K.card ≤ C'.size + 1))
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = {g} →
      ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
        G.edgeFinset.card + K.card ≤ C.size + 1)
    (h3 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      (∀ i ∈ PEqualNP.TopForm.junk G C, ∀ j ∈ PEqualNP.TopForm.junk G C,
        ¬ PEqualNP.EdgeOwnership.InCone n C i j) →
      ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
        G.edgeFinset.card + K.card ≤ C.size + 1)
    (h4 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      (∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C,
        PEqualNP.EdgeOwnership.InCone n C i j) →
      ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
        G.edgeFinset.card + K.card ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧ x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 → x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true := by
  intro n G C hEx hNoC4 hMonoC hFunC
  classical
  have hNo4G : PEqualNP.TopForm.NoFourCycle G := by
    change ∀ a b : Fin n, a ≠ b → (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1
    intro a b hab
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    rw [Finset.mem_filter] at hw1 hw2
    by_contra hw12
    exact hNoC4 a w1 b w2
      (G.ne_of_adj hw1.2.1) hab (G.ne_of_adj hw2.2.1)
      (G.ne_of_adj hw1.2.2).symm hw12 (G.ne_of_adj hw2.2.2)
      hw1.2.1 hw1.2.2.symm hw2.2.2 hw2.2.1.symm
  have hGne : G.edgeFinset.Nonempty := by
    obtain ⟨u0, v0, huv0⟩ := hEx
    exact ⟨s(u0, v0), SimpleGraph.mem_edgeFinset.mpr huv0⟩
  let stepW : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wiresFrom : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool :=
    fun gs w => gs.foldl stepW w
  have wiresFrom_append : ∀ (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
    intro gs1 gs2 w; dsimp only [wiresFrom]; exact List.foldl_append
  have wiresFrom_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by dsimp only [wiresFrom]; simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (stepW w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      change wiresFrom gs (stepW w g) = _
      rw [ht]; dsimp only [stepW]; simp
  have length_wiresFrom : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
    rw [ht]; simp [hl]
  have getD_wiresFrom : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
    intro gs w i h
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
    rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have getD_snoc : ∀ (u : List Bool) (b : Bool), (u ++ [b]).getD u.length false = b := by
    intro u b; simp [List.getD_eq_getElem?_getD]
  have getD_ge : ∀ (u : List Bool) (i : ℕ), u.length ≤ i → u.getD i false = false := by
    intro u i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    rfl
  have wiresFrom_snoc_val : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) (x : Fin n → Bool) (t : ℕ),
      (wiresFrom (gs ++ [g]) (List.ofFn x)).getD t false =
        if t = n + gs.length then
          g.op.eval (g.inputs.map fun i => (wiresFrom gs (List.ofFn x)).getD i false)
        else (wiresFrom gs (List.ofFn x)).getD t false := by
    intro gs g x t
    rw [wiresFrom_append]
    set u := wiresFrom gs (List.ofFn x) with hu
    have lu : u.length = n + gs.length := by rw [hu, length_wiresFrom, List.length_ofFn]
    change (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]).getD t false = _
    by_cases ht : t = n + gs.length
    · rw [if_pos ht, ht, ← lu, getD_snoc]
    · rw [if_neg ht]
      by_cases hlt : t < n + gs.length
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
      · rw [getD_ge _ _ (by simp [lu]; omega), getD_ge _ _ (by omega)]
  let Fan2 : PEqualNP.CircuitLowerBounds.Gate → Prop :=
    fun g => (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2
  let RB : List PEqualNP.CircuitLowerBounds.Gate → Prop :=
    fun gs => ∀ j < gs.length,
      ∀ i ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, i < n + j
  let Rep : List PEqualNP.CircuitLowerBounds.Gate → ((Fin n → Bool) → Bool) → Prop :=
    fun gs f => (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
      (∃ j : ℕ, j < n + gs.length ∧
        ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD j false = f x)
  let Ext : List PEqualNP.CircuitLowerBounds.Gate → List PEqualNP.CircuitLowerBounds.Gate → Prop :=
    fun gs gs' => gs' = gs ∨
      ∃ h : PEqualNP.CircuitLowerBounds.Gate,
        gs' = gs ++ [h] ∧ Fan2 h ∧ ∀ i ∈ h.inputs, i < n + gs.length
  have rep_congr : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (f g : (Fin n → Bool) → Bool),
      (∀ x, f x = g x) → Rep gs f → Rep gs g := by
    intro gs f g h hf
    have heq : f = g := funext h
    rw [← heq]
    exact hf
  have rep_ext : ∀ (gs gs' : List PEqualNP.CircuitLowerBounds.Gate),
      Ext gs gs' → ∀ (f : (Fin n → Bool) → Bool), Rep gs f → Rep gs' f := by
    intro gs gs' he f hf
    rcases he with rfl | ⟨k, rfl, _⟩
    · exact hf
    · rcases hf with hc | ⟨j, hj, hv⟩
      · exact Or.inl hc
      · refine Or.inr ⟨j, by simp; omega, fun x => ?_⟩
        rw [wiresFrom_snoc_val, if_neg (by omega)]
        exact hv x
  have rep_and : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (f g : (Fin n → Bool) → Bool),
      Rep gs f → Rep gs g → ∃ gs', Ext gs gs' ∧ Rep gs' (fun x => f x && g x) := by
    intro gs f g hf hg
    rcases hf with ⟨c1, h1'⟩ | ⟨j, hj, hjv⟩
    · cases c1 with
      | false =>
        exact ⟨gs, Or.inl rfl, Or.inl ⟨false, fun x => by dsimp only; rw [h1' x]; rfl⟩⟩
      | true =>
        exact ⟨gs, Or.inl rfl, rep_congr gs g (fun x => f x && g x)
          (fun x => by rw [h1' x]; rfl) hg⟩
    · rcases hg with ⟨c2, h2'⟩ | ⟨k, hk, hkv⟩
      · cases c2 with
        | false =>
          exact ⟨gs, Or.inl rfl, Or.inl ⟨false, fun x => by dsimp only; rw [h2' x, Bool.and_false]⟩⟩
        | true =>
          exact ⟨gs, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
            dsimp only; rw [hjv x, h2' x, Bool.and_true]⟩⟩
      · refine ⟨gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [j, k]⟩],
          Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, by
            intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> assumption⟩,
          Or.inr ⟨n + gs.length, by simp, fun x => ?_⟩⟩
        rw [wiresFrom_snoc_val, if_pos rfl]
        change ((wiresFrom gs (List.ofFn x)).getD j false &&
          ((wiresFrom gs (List.ofFn x)).getD k false && true)) = (f x && g x)
        rw [Bool.and_true, hjv x, hkv x]
  have rep_or : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (f g : (Fin n → Bool) → Bool),
      Rep gs f → Rep gs g → ∃ gs', Ext gs gs' ∧ Rep gs' (fun x => f x || g x) := by
    intro gs f g hf hg
    rcases hf with ⟨c1, h1'⟩ | ⟨j, hj, hjv⟩
    · cases c1 with
      | true =>
        exact ⟨gs, Or.inl rfl, Or.inl ⟨true, fun x => by dsimp only; rw [h1' x]; rfl⟩⟩
      | false =>
        exact ⟨gs, Or.inl rfl, rep_congr gs g (fun x => f x || g x)
          (fun x => by rw [h1' x]; rfl) hg⟩
    · rcases hg with ⟨c2, h2'⟩ | ⟨k, hk, hkv⟩
      · cases c2 with
        | true =>
          exact ⟨gs, Or.inl rfl, Or.inl ⟨true, fun x => by dsimp only; rw [h2' x, Bool.or_true]⟩⟩
        | false =>
          exact ⟨gs, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
            dsimp only; rw [hjv x, h2' x, Bool.or_false]⟩⟩
      · refine ⟨gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [j, k]⟩],
          Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, by
            intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> assumption⟩,
          Or.inr ⟨n + gs.length, by simp, fun x => ?_⟩⟩
        rw [wiresFrom_snoc_val, if_pos rfl]
        change ((wiresFrom gs (List.ofFn x)).getD j false ||
          ((wiresFrom gs (List.ofFn x)).getD k false || false)) = (f x || g x)
        rw [Bool.or_false, hjv x, hkv x]
  have gate_rep : ∀ (old new : List PEqualNP.CircuitLowerBounds.Gate)
      (op : PEqualNP.CircuitLowerBounds.GateOp) (l : List ℕ),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      l.length ≤ 2 →
      (∀ t : ℕ, Rep new (fun x => (wiresFrom old (List.ofFn x)).getD t false)) →
      ∃ new', Ext new new' ∧
        Rep new' (fun x => op.eval (l.map fun i => (wiresFrom old (List.ofFn x)).getD i false)) := by
    intro old new op l hop hlen hrep
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
    · rcases hop with rfl | rfl
      · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun _ => rfl⟩⟩
      · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun _ => rfl⟩⟩
    · rcases hop with rfl | rfl
      · exact ⟨new, Or.inl rfl, rep_congr new
          (fun x => (wiresFrom old (List.ofFn x)).getD a false)
          (fun x => PEqualNP.CircuitLowerBounds.GateOp.and.eval
            ([a].map fun i => (wiresFrom old (List.ofFn x)).getD i false))
          (fun x => by
            change (wiresFrom old (List.ofFn x)).getD a false =
              ((wiresFrom old (List.ofFn x)).getD a false && true)
            rw [Bool.and_true]) (hrep a)⟩
      · exact ⟨new, Or.inl rfl, rep_congr new
          (fun x => (wiresFrom old (List.ofFn x)).getD a false)
          (fun x => PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([a].map fun i => (wiresFrom old (List.ofFn x)).getD i false))
          (fun x => by
            change (wiresFrom old (List.ofFn x)).getD a false =
              ((wiresFrom old (List.ofFn x)).getD a false || false)
            rw [Bool.or_false]) (hrep a)⟩
    · rcases hop with rfl | rfl
      · obtain ⟨new', he, hr⟩ := rep_and new
          (fun x => (wiresFrom old (List.ofFn x)).getD a false)
          (fun x => (wiresFrom old (List.ofFn x)).getD b false) (hrep a) (hrep b)
        refine ⟨new', he, rep_congr new' _ _ (fun x => ?_) hr⟩
        change ((wiresFrom old (List.ofFn x)).getD a false &&
          (wiresFrom old (List.ofFn x)).getD b false) =
          ((wiresFrom old (List.ofFn x)).getD a false &&
            ((wiresFrom old (List.ofFn x)).getD b false && true))
        rw [Bool.and_true]
      · obtain ⟨new', he, hr⟩ := rep_or new
          (fun x => (wiresFrom old (List.ofFn x)).getD a false)
          (fun x => (wiresFrom old (List.ofFn x)).getD b false) (hrep a) (hrep b)
        refine ⟨new', he, rep_congr new' _ _ (fun x => ?_) hr⟩
        change ((wiresFrom old (List.ofFn x)).getD a false ||
          (wiresFrom old (List.ofFn x)).getD b false) =
          ((wiresFrom old (List.ofFn x)).getD a false ||
            ((wiresFrom old (List.ofFn x)).getD b false || false))
        rw [Bool.or_false]
    · simp only [List.length_cons] at hlen; omega
  have rb_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (h : PEqualNP.CircuitLowerBounds.Gate),
      RB gs → (∀ i ∈ h.inputs, i < n + gs.length) → RB (gs ++ [h]) := by
    intro gs h hrb hh j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have e : (gs ++ [h]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
          gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [e] at hi
      exact hrb j hlt i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have e : (gs ++ [h]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = h := by
        simp [List.getD_eq_getElem?_getD]
      rw [e] at hi
      exact hh i hi
  let Inv : List PEqualNP.CircuitLowerBounds.Gate → Prop :=
    fun old => ∃ new : List PEqualNP.CircuitLowerBounds.Gate,
      (∀ g ∈ new, Fan2 g) ∧ RB new ∧ new.length ≤ old.length ∧
      ∀ t : ℕ, Rep new (fun x => (wiresFrom old (List.ofFn x)).getD t false)
  have inv_nil : Inv [] := by
    refine ⟨[], fun _ hg => False.elim (List.not_mem_nil hg),
      fun _ hj => absurd hj (Nat.not_lt_zero _), le_rfl, ?_⟩
    intro t
    by_cases ht : t < n
    · exact Or.inr ⟨t, by simpa using ht, fun x => rfl⟩
    · refine Or.inl ⟨false, fun x => ?_⟩
      change (List.ofFn x).getD t false = false
      exact getD_ge _ _ (by simp; omega)
  have inv_step : ∀ (old : List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate),
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      g.inputs.length ≤ 2 → Inv old → Inv (old ++ [g]) := by
    intro old g hop hlen hinv
    obtain ⟨new, hfan, hrb, hl, hrep⟩ := hinv
    obtain ⟨new', he, hr⟩ := gate_rep old new g.op g.inputs hop hlen hrep
    refine ⟨new', ?_, ?_, ?_, ?_⟩
    · rcases he with rfl | ⟨k, rfl, hk, _⟩
      · exact hfan
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hfan q hq
        · rw [List.mem_singleton] at hq; rw [hq]; exact hk
    · rcases he with rfl | ⟨k, rfl, _, hkb⟩
      · exact hrb
      · exact rb_snoc new k hrb hkb
    · rcases he with rfl | ⟨k, rfl, _⟩ <;> simp <;> omega
    · intro t
      by_cases ht : t = n + old.length
      · exact rep_congr new' _ _ (fun x => by
          rw [wiresFrom_snoc_val, if_pos ht]) hr
      · exact rep_congr new' _ _ (fun x => by
          rw [wiresFrom_snoc_val, if_neg ht])
          (rep_ext new new' he _ (hrep t))
  have hgC : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hMonoC g hgm
    have h1' := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1'
    exact ⟨h1', h.2⟩
  have hInvC : Inv C.gates := by
    have hall : ∀ (post pre : List PEqualNP.CircuitLowerBounds.Gate),
        pre ++ post = C.gates → Inv pre → Inv C.gates := by
      intro post
      induction post with
      | nil =>
        intro pre h hinv
        rw [List.append_nil] at h; rw [← h]; exact hinv
      | cons g post ih =>
        intro pre h hinv
        have hmem : g ∈ C.gates := by rw [← h]; simp
        exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
          (inv_step pre g (hgC g hmem).1 (hgC g hmem).2 hinv)
    exact hall C.gates [] (List.nil_append _) inv_nil
  obtain ⟨new0, hfan0, hrb0, hlen0, hrep0⟩ := hInvC
  have hgf : ∀ x : Fin n → Bool,
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = C.eval (List.ofFn x) := by
    intro x
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = C.eval (List.ofFn x)
    have hemp : decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) = false := by simp
    rw [hemp, Bool.false_or, Bool.eq_iff_iff, decide_eq_true_iff, hFunC x]
  have hAO2Ex : ∃ C0 : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C0 ∧
      PEqualNP.MetaComplexity.circuitFun n C0 =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      C0.size ≤ C.size := by
    rcases hrep0 C.output with ⟨c, hc⟩ | ⟨j0, _, hj0⟩
    · have hc' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = c := hc
      have hcf : c = false := by
        have h0 := hFunC (fun _ => false)
        rw [hc'] at h0
        cases c with
        | false => rfl
        | true =>
          obtain ⟨u, _, _, hu, _⟩ := h0.mp rfl
          cases hu
      subst hcf
      refine ⟨⟨[], n⟩,
        And.intro (fun _ hg => False.elim (List.not_mem_nil hg))
          (And.intro (fun _ hj => absurd hj (Nat.not_lt_zero _))
            (fun _ hg => False.elim (List.not_mem_nil hg))),
        ?_, Nat.zero_le _⟩
      funext x
      rw [hgf x, hc' x]
      show (List.ofFn x).getD n false = false
      simp
    · refine ⟨⟨new0, j0⟩,
        And.intro (fun g hg => (hfan0 g hg).1)
          (And.intro hrb0 (fun g hg => (hfan0 g hg).2)),
        ?_, hlen0⟩
      funext x
      rw [hgf x]
      exact hj0 x
  obtain ⟨C0, hAO2C0, hFunC0, hSizeC0⟩ := hAO2Ex
  obtain ⟨C', hLeast, hTF, hSize', hZero⟩ := h1 n G C0 hNo4G hGne hAO2C0 hFunC0
  have hCoverEx : ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
      G.edgeFinset.card + K.card ≤ C'.size + 1 := by
    by_cases hj0 : (PEqualNP.TopForm.junk G C').card = 0
    · exact hZero (Finset.card_eq_zero.mp hj0)
    · by_cases hj1 : (PEqualNP.TopForm.junk G C').card = 1
      · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hj1
        exact h2 n G C' g hNo4G hGne hLeast hTF hg
      · have hj2 : 2 ≤ (PEqualNP.TopForm.junk G C').card := by omega
        by_cases hnest : ∃ i ∈ PEqualNP.TopForm.junk G C',
            ∃ j ∈ PEqualNP.TopForm.junk G C', PEqualNP.EdgeOwnership.InCone n C' i j
        · exact h4 n G C' hNo4G hGne hLeast hTF hj2 hnest
        · refine h3 n G C' hNo4G hGne hLeast hTF hj2 ?_
          intro i hi j hj hic
          exact hnest ⟨i, hi, j, hj, hic⟩
  obtain ⟨K, hCovK, hBoundK⟩ := hCoverEx
  let BldJF : ((Fin n → Bool) → Bool) → ℕ → Prop :=
    fun F s => ∀ m, n ≤ m →
      ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
        (∀ g ∈ gs,
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        gs.length ≤ s ∧ out < m + gs.length ∧
        (∀ j (hj : j < gs.length),
          (gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ v : List Bool, v.length = m →
            (wiresFrom gs v).getD (m + j) false = true →
            ∃ a b : Fin n, G.Adj a b ∧ v.getD a.val false = true ∧ v.getD b.val false = true) ∧
        ∀ v : List Bool, v.length = m →
          (wiresFrom gs v).getD out false = F (fun i => v.getD i false)
  have bldJF_mono : ∀ (F : (Fin n → Bool) → Bool) (s s' : ℕ),
      BldJF F s → s ≤ s' → BldJF F s' := by
    intro F s s' h hs m hm
    obtain ⟨gs, out, hok, hlen, hout, hand, hev⟩ := h m hm
    exact ⟨gs, out, hok, le_trans hlen hs, hout, hand, hev⟩
  have bldJF_congr : ∀ (F H : (Fin n → Bool) → Bool) (s : ℕ),
      BldJF F s → (∀ x, F x = H x) → BldJF H s := by
    intro F H s h he m hm
    obtain ⟨gs, out, hok, hlen, hout, hand, hev⟩ := h m hm
    exact ⟨gs, out, hok, hlen, hout, hand, fun v hv => by rw [hev v hv, he]⟩
  have bldJF_var : ∀ i : Fin n, BldJF (fun x => x i) 0 := by
    intro i m hm
    refine ⟨[], i.val, fun _ hg => False.elim (List.not_mem_nil hg), le_rfl,
      by simp; have := i.isLt; omega, fun _ hj => absurd hj (Nat.not_lt_zero _), ?_⟩
    intro v _; dsimp only [wiresFrom]; simp
  have bldJF_or : ∀ (F1 F2 : (Fin n → Bool) → Bool) (s1 s2 : ℕ),
      BldJF F1 s1 → BldJF F2 s2 → BldJF (fun x => F1 x || F2 x) (s1 + s2 + 1) := by
    intro F1 F2 s1 s2 hb1 hb2 m hm
    obtain ⟨gs1, o1, hok1, hlen1, ho1, hand1, hev1⟩ := hb1 m hm
    obtain ⟨gs2, o2, hok2, hlen2, ho2, hand2, hev2⟩ := hb2 (m + gs1.length) (by omega)
    let out := m + gs1.length + gs2.length
    let g := PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [o1, o2]
    refine ⟨(gs1 ++ gs2) ++ [g], out, ?_, by simp; omega, by dsimp only [out]; simp; omega, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq12 | hqg
      · rcases List.mem_append.mp hq12 with hq1 | hq2
        · exact hok1 q hq1
        · exact hok2 q hq2
      · rw [List.mem_singleton] at hqg; subst hqg
        exact ⟨Or.inr rfl, le_rfl⟩
    · intro j hj hop v hv hval
      have hj' := hj
      simp only [List.length_append, List.length_singleton] at hj'
      by_cases hlt12 : j < (gs1 ++ gs2).length
      · rw [List.getElem_append_left hlt12] at hop
        by_cases hlt1 : j < gs1.length
        · rw [List.getElem_append_left hlt1] at hop
          rw [List.append_assoc, wiresFrom_append,
            getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hv]; omega)] at hval
          exact hand1 j hlt1 hop v hv hval
        · have hk : j - gs1.length < gs2.length := by rw [List.length_append] at hlt12; omega
          rw [List.getElem_append_right (Nat.le_of_not_lt hlt1)] at hop
          rw [wiresFrom_append,
            getD_wiresFrom _ _ _ (by
              rw [length_wiresFrom, List.length_append, hv]
              rw [List.length_append] at hlt12; omega),
            wiresFrom_append] at hval
          set u1 := wiresFrom gs1 v with hu1
          have lu1 : u1.length = m + gs1.length := by rw [hu1, length_wiresFrom, hv]
          have heq : m + j = (m + gs1.length) + (j - gs1.length) := by omega
          rw [heq] at hval
          obtain ⟨a, b, hab, ha, hb⟩ := hand2 (j - gs1.length) hk hop u1 lu1 hval
          rw [hu1, getD_wiresFrom _ _ _ (by rw [hv]; have := a.isLt; omega)] at ha
          rw [hu1, getD_wiresFrom _ _ _ (by rw [hv]; have := b.isLt; omega)] at hb
          exact ⟨a, b, hab, ha, hb⟩
      · have hjlast : j = (gs1 ++ gs2).length := by rw [List.length_append] at hlt12 ⊢; omega
        subst hjlast
        dsimp only [g] at hop
        simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
          List.getElem_cons_zero] at hop
        cases hop
    · intro v hv
      rw [wiresFrom_append, wiresFrom_append]
      set u1 := wiresFrom gs1 v with hu1
      have lu1 : u1.length = m + gs1.length := by rw [hu1, length_wiresFrom, hv]
      set u2 := wiresFrom gs2 u1 with hu2
      have lu2 : u2.length = out := by rw [hu2, length_wiresFrom, lu1]
      change (u2 ++ [(u2.getD o1 false || (u2.getD o2 false || false))]).getD out false = _
      rw [← lu2, getD_snoc, Bool.or_false]
      have e1 : u2.getD o1 false = F1 (fun i => v.getD i false) := by
        rw [hu2, getD_wiresFrom _ _ _ (by omega), hu1, hev1 v hv]
      have e2 : u2.getD o2 false = F2 (fun i => v.getD i false) := by
        rw [hu2, hev2 u1 lu1]
        congr 1; funext i
        rw [hu1, getD_wiresFrom _ _ _ (by have := i.isLt; omega)]
      rw [e1, e2]
  have bldJF_anyFinset : ∀ (S : Finset (Fin n)), S.Nonempty →
      BldJF (fun x => decide (∃ b ∈ S, x b = true)) (S.card - 1) := by
    intro S hS
    have hlist : ∀ (vs : List (Fin n)) (v0 : Fin n),
        BldJF (fun x => (v0 :: vs).any fun j => x j) vs.length := by
      intro vs
      induction vs with
      | nil =>
        intro v0
        exact bldJF_congr (fun x => x v0) (fun x => [v0].any fun j => x j) 0
          (bldJF_var v0) (by intro x; simp)
      | cons v1 vs ih =>
        intro v0
        exact bldJF_congr
          (fun x => x v0 || ((v1 :: vs).any fun j => x j))
          (fun x => (v0 :: v1 :: vs).any fun j => x j) (v1 :: vs).length
          (bldJF_mono
            (fun x => x v0 || ((v1 :: vs).any fun j => x j))
            (0 + vs.length + 1) (v1 :: vs).length
            (bldJF_or (fun x => x v0) (fun x => (v1 :: vs).any fun j => x j)
              0 vs.length (bldJF_var v0) (ih v1)) (by simp))
          (by intro x; simp)
    obtain ⟨v0, vs, hl⟩ : ∃ v0 vs, S.toList = v0 :: vs := by
      cases h : S.toList with
      | nil => simp at h; exact absurd h hS.ne_empty
      | cons v0 vs => exact ⟨v0, vs, rfl⟩
    have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
    refine bldJF_congr (fun x => (v0 :: vs).any fun j => x j)
      (fun x => decide (∃ b ∈ S, x b = true)) (S.card - 1)
      (bldJF_mono (fun x => (v0 :: vs).any fun j => x j)
        vs.length (S.card - 1) (hlist vs v0) (by omega)) ?_
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
    simp
  have bldJF_star : ∀ (t : Fin n) (S : Finset (Fin n)), S.Nonempty →
      (∀ b ∈ S, G.Adj t b) →
      BldJF (fun x => x t && decide (∃ b ∈ S, x b = true)) S.card := by
    intro t S hS hadj m hm
    obtain ⟨gsS, oS, hokS, hlenS, hoS, handS, hevS⟩ := bldJF_anyFinset S hS m hm
    have hpos : 1 ≤ S.card := hS.card_pos
    let out := m + gsS.length
    let g := PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [t.val, oS]
    refine ⟨gsS ++ [g], out, ?_, by simp; omega, by dsimp only [out]; simp, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with hqS | hqg
      · exact hokS q hqS
      · rw [List.mem_singleton] at hqg; subst hqg
        exact ⟨Or.inl rfl, le_rfl⟩
    · intro j hj hop v hv hval
      have hj' := hj
      simp only [List.length_append, List.length_singleton] at hj'
      by_cases hlt : j < gsS.length
      · rw [List.getElem_append_left hlt] at hop
        rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hv]; omega)] at hval
        exact handS j hlt hop v hv hval
      · have hjlast : j = gsS.length := by omega
        subst hjlast
        rw [wiresFrom_append] at hval
        set u := wiresFrom gsS v with hu
        have lu : u.length = m + gsS.length := by rw [hu, length_wiresFrom, hv]
        change (u ++ [(u.getD t.val false && (u.getD oS false && true))]).getD (m + gsS.length) false =
          true at hval
        rw [← lu, getD_snoc, Bool.and_true, Bool.and_eq_true] at hval
        have ht : v.getD t.val false = true := by
          have := hval.1
          rwa [hu, getD_wiresFrom _ _ _ (by rw [hv]; have := t.isLt; omega)] at this
        have ho : decide (∃ b ∈ S, v.getD b.val false = true) = true := by
          have hev' : (wiresFrom gsS v).getD oS false =
              decide (∃ b ∈ S, v.getD b.val false = true) := hevS v hv
          rw [← hev', ← hu]
          exact hval.2
        obtain ⟨b, hb, hvb⟩ := decide_eq_true_iff.mp ho
        exact ⟨t, b, hadj b hb, ht, hvb⟩
    · intro v hv
      rw [wiresFrom_append]
      set u := wiresFrom gsS v with hu
      have lu : u.length = out := by rw [hu, length_wiresFrom, hv]
      change (u ++ [(u.getD t.val false && (u.getD oS false && true))]).getD out false = _
      rw [← lu, getD_snoc, Bool.and_true]
      have et : u.getD t.val false = v.getD t.val false := by
        rw [hu, getD_wiresFrom _ _ _ (by rw [hv]; have := t.isLt; omega)]
      rw [et, hu, hevS v hv]
  have bldJF_edges : ∀ (T : Finset (Fin n)) (E0 : Finset (Sym2 (Fin n))),
      E0 ⊆ G.edgeFinset → E0.Nonempty → (∀ e ∈ E0, ∃ t ∈ T, t ∈ e) →
      BldJF (fun x => decide (∃ e ∈ E0, ∀ v ∈ e, x v = true)) (E0.card + T.card - 1) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro E0 _ hE0 hc
      obtain ⟨e, he⟩ := hE0
      obtain ⟨t, ht, _⟩ := hc e he
      simp at ht
    | @insert t T0 htT ih =>
      intro E0 hsub hE0 hc
      set E1 := E0.filter (fun e => t ∈ e) with hE1
      set E2 := E0.filter (fun e => t ∉ e) with hE2
      have hsplit : E1.card + E2.card = E0.card := Finset.card_filter_add_card_filter_not _
      have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
      have hsub1 : E1 ⊆ G.edgeFinset := Finset.Subset.trans (Finset.filter_subset _ _) hsub
      have hsub2 : E2 ⊆ G.edgeFinset := Finset.Subset.trans (Finset.filter_subset _ _) hsub
      have hc2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
        intro e he
        rw [hE2, Finset.mem_filter] at he
        obtain ⟨t', ht', hte⟩ := hc e he.1
        rcases Finset.mem_insert.mp ht' with rfl | h0
        · exact absurd hte he.2
        · exact ⟨t', h0, hte⟩
      set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
      have hSc : S.card ≤ E1.card := by
        refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
        · intro v hv
          rw [Finset.mem_coe, hS, Finset.mem_filter] at hv
          exact Finset.mem_coe.mpr hv.2
        · intro a _ b _ hab
          exact Sym2.congr_right.mp hab
      have hadjS : ∀ b ∈ S, G.Adj t b := by
        intro b hb
        rw [hS, Finset.mem_filter] at hb
        exact SimpleGraph.mem_edgeFinset.mp (hsub1 hb.2)
      have hstar : E1.Nonempty →
          BldJF (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true)) E1.card := by
        intro h1'
        have hSne : S.Nonempty := by
          obtain ⟨e, he⟩ := h1'
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp he'.2
          exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hb]; exact he⟩⟩
        refine bldJF_congr
          (fun x => x t && decide (∃ b ∈ S, x b = true))
          (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true)) E1.card
          (bldJF_mono (fun x => x t && decide (∃ b ∈ S, x b = true))
            S.card E1.card (bldJF_star t S hSne hadjS) hSc) ?_
        intro x
        rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨ht, b, hb, hxb⟩
          refine ⟨s(t, b), (Finset.mem_filter.mp hb).2, ?_⟩
          intro u hu
          rcases Sym2.mem_iff.mp hu with rfl | rfl <;> assumption
        · rintro ⟨e, he, hall⟩
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp he'.2
          subst hb
          exact ⟨hall t (Sym2.mem_mk_left _ _), b,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩,
            hall b (Sym2.mem_mk_right _ _)⟩
      have key : ∀ x : Fin n → Bool,
          decide (∃ e ∈ E0, ∀ v ∈ e, x v = true) =
          (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) ||
            decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
        intro x
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
        constructor
        · rintro ⟨e, he, h⟩
          by_cases hte : t ∈ e
          · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
          · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
        · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
      let FE : Finset (Sym2 (Fin n)) → (Fin n → Bool) → Bool :=
        fun X x => decide (∃ e ∈ X, ∀ v ∈ e, x v = true)
      rw [hcard]
      by_cases he1 : E1.Nonempty
      · by_cases he2 : E2.Nonempty
        · have hp2 := he2.card_pos
          refine bldJF_congr (fun x => FE E1 x || FE E2 x) (FE E0) (E0.card + (T0.card + 1) - 1)
            (bldJF_mono (fun x => FE E1 x || FE E2 x)
              (E1.card + (E2.card + T0.card - 1) + 1) (E0.card + (T0.card + 1) - 1)
              (bldJF_or (FE E1) (FE E2) E1.card (E2.card + T0.card - 1)
                (hstar he1) (ih E2 hsub2 he2 hc2)) (by omega)) ?_
          intro x; exact (key x).symm
        · rw [Finset.not_nonempty_iff_eq_empty] at he2
          refine bldJF_congr (FE E1) (FE E0) (E0.card + (T0.card + 1) - 1)
            (bldJF_mono (FE E1) E1.card (E0.card + (T0.card + 1) - 1) (hstar he1) (by omega)) ?_
          intro x; dsimp only [FE]; rw [key, he2]; simp
      · rw [Finset.not_nonempty_iff_eq_empty] at he1
        have he2 : E2.Nonempty := by
          by_contra he2
          rw [Finset.not_nonempty_iff_eq_empty] at he2
          have := hE0.card_pos
          rw [he1, he2] at hsplit; simp at hsplit; omega
        refine bldJF_congr (FE E2) (FE E0) (E0.card + (T0.card + 1) - 1)
          (bldJF_mono (FE E2) (E2.card + T0.card - 1) (E0.card + (T0.card + 1) - 1)
            (ih E2 hsub2 he2 hc2) (by omega)) ?_
        intro x; dsimp only [FE]; rw [key, he1]; simp
  have hCovE : ∀ e ∈ G.edgeFinset, ∃ t ∈ K, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hCovK he with ha | hb
    · exact ⟨a, ha, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, hb, Sym2.mem_mk_right _ _⟩
  obtain ⟨gs, out, hok, hlen, _, hand, hev⟩ :=
    bldJF_edges K G.edgeFinset Finset.Subset.rfl hGne hCovE n le_rfl
  have hEpos : 1 ≤ G.edgeFinset.card := hGne.card_pos
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, out⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · delta PEqualNP.MetaComplexity.Monotone2
    intro g hg
    refine ⟨?_, (hok g hg).2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact (hok g hg).1
  · intro x
    have e := hev (List.ofFn x) (List.length_ofFn)
    have hfun : (fun i : Fin n => (List.ofFn x).getD i false) = x := by
      funext i; simp [List.getD_eq_getElem?_getD]
    rw [hfun] at e
    change (wiresFrom gs (List.ofFn x)).getD out false = true ↔ _
    rw [e, decide_eq_true_iff]
    constructor
    · rintro ⟨e0, he0, hall⟩
      revert he0 hall
      refine Sym2.ind (fun a b => ?_) e0
      intro he0 hall
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he0
      exact ⟨a, b, he0, hall a (Sym2.mem_mk_left _ _), hall b (Sym2.mem_mk_right _ _)⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      refine ⟨s(a, b), SimpleGraph.mem_edgeFinset.mpr hab, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
  · change gs.length ≤ C.gates.length
    have h1s : C'.size = C'.gates.length := rfl
    have h2s : C0.size = C0.gates.length := rfl
    have h3s : C.size = C.gates.length := rfl
    omega
  · intro j g hg hop x hval
    have hj : j < gs.length := by
      by_contra hge
      have hnone : D.gates[j]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hge)
      rw [hnone] at hg
      cases hg
    have hgj : gs[j] = g := by
      have hsome : D.gates[j]? = some gs[j] := List.getElem?_eq_getElem hj
      rw [hsome] at hg
      injection hg with heq
    obtain ⟨a, b, hab, ha, hb⟩ :=
      hand j hj (by rw [hgj]; exact hop) (List.ofFn x) (List.length_ofFn) hval
    have hax : (List.ofFn x).getD a.val false = x a := by simp [List.getD_eq_getElem?_getD]
    have hbx : (List.ofFn x).getD b.val false = x b := by simp [List.getD_eq_getElem?_getD]
    rw [hax] at ha
    rw [hbx] at hb
    exact ⟨a, b, hab, ha, hb⟩
