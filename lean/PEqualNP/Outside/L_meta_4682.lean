import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4682

open PEqualNP.CircuitLowerBounds

private def collapse_wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private lemma collapse_wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    collapse_wiresFrom (gs₁ ++ gs₂) w = collapse_wiresFrom gs₂ (collapse_wiresFrom gs₁ w) := by
  simp [collapse_wiresFrom, List.foldl_append]

private lemma collapse_wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, collapse_wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [collapse_wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : collapse_wiresFrom (g :: gs) w = collapse_wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

private lemma collapse_length_wiresFrom (gs : List Gate) (w : List Bool) :
    (collapse_wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := collapse_wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

private lemma collapse_getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (collapse_wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := collapse_wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

private lemma collapse_getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (collapse_wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (collapse_wiresFrom gs w).getD i false else false := by
  have hlen : (collapse_wiresFrom (gs.take k) w).length = w.length + k := by
    rw [collapse_length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, collapse_wiresFrom_append]
    exact (collapse_getD_wiresFrom_lt (gs.drop k) (collapse_wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

private lemma collapse_getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

private lemma collapse_getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (collapse_wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (collapse_wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (collapse_wiresFrom (gs.take k) w).length = w.length + k := by
    rw [collapse_length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : collapse_wiresFrom gs w =
      collapse_wiresFrom (gs.drop (k + 1))
        (collapse_wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (collapse_wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, collapse_wiresFrom_append]
    rfl
  rw [heq, collapse_getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, collapse_getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [collapse_getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

open PEqualNP.MetaComplexity PEqualNP.AndCount

private abbrev CollSide (n k : ℕ) := Finset (Fin n) × Finset (Fin k)

private def collVal {n k : ℕ} (U : Finset (Fin n)) (v : Fin k → Bool)
    (s : CollSide n k) : Bool := decide ((∃ x ∈ s.1, x ∈ U) ∨ ∃ i ∈ s.2, v i = true)

private def collCollect {n k : ℕ} (L : List ℕ) (s : ℕ → CollSide n k) : CollSide n k :=
  ⟨L.toFinset.biUnion (fun j => (s j).1), L.toFinset.biUnion (fun j => (s j).2)⟩

private lemma collCollect_true {n k : ℕ} (U : Finset (Fin n)) (v : Fin k → Bool)
    (L : List ℕ) (s : ℕ → CollSide n k) :
    collVal U v (collCollect L s) = true ↔ ∃ j ∈ L, collVal U v (s j) = true := by
  classical
  simp only [collVal, collCollect, decide_eq_true_eq, Finset.mem_biUnion, List.mem_toFinset]
  aesop

private def collOrig {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (w : ℕ) : Bool :=
  (collapse_wiresFrom C.gates (List.ofFn (fun i : Fin n => decide (i ∈ U)))).getD w false

private lemma coll_gate {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (j : ℕ)
    (h : j < C.gates.length) :
    collOrig C U (n+j) = C.gates[j].op.eval (C.gates[j].inputs.map
      (fun i => if i < n+j then collOrig C U i else false)) := by
  simpa only [collOrig,List.length_ofFn] using collapse_getD_wiresFrom_gate C.gates
    (List.ofFn (fun i : Fin n => decide (i ∈ U))) j h

private def collV {n k : ℕ} (C : Circuit) (ord : Fin k → ℕ) (U : Finset (Fin n))
    (j : Fin k) : Bool := collOrig C U (n+ord j)

private lemma coll_prior {n k w : ℕ} (C : Circuit) (ord : Fin k → ℕ)
    (ih : ∀ i < w, ∃ s : CollSide n k, (∀ j ∈ s.2, n + ord j ≤ i) ∧
      ∀ U : Finset (Fin n), collVal U (collV C ord U) s = collOrig C U i) :
    ∃ f : ℕ → CollSide n k, (∀ i j, j ∈ (f i).2 → n + ord j < w) ∧
      ∀ i (U : Finset (Fin n)), collVal U (collV C ord U) (f i) =
        if i < w then collOrig C U i else false := by
  classical
  let f (i : ℕ) : CollSide n k := if hi : i < w then (ih i hi).choose else (∅,∅)
  refine ⟨f, ?_, ?_⟩
  · intro i j hj
    by_cases hi : i < w
    · simp only [f,dite_eq_left hi] at hj
      exact Nat.lt_of_le_of_lt ((ih i hi).choose_spec.1 _ hj) hi
    · simp [f,hi] at hj
  · intro i U
    by_cases hi : i < w
    · simpa only [f,dite_eq_left hi,ite_eq_left hi] using (ih i hi).choose_spec.2 U
    · simp [f, hi, collVal]

private lemma coll_wires {n k : ℕ} (C : Circuit) (hm : Monotone2 C) (ord : Fin k → ℕ)
    (allAnd : ∀ (j : ℕ) (hj : j < C.gates.length), C.gates[j].op = GateOp.and →
      ∃ i, ord i = j) (w : ℕ) :
    ∃ s : CollSide n k, (∀ j ∈ s.2, n + ord j ≤ w) ∧
      ∀ U : Finset (Fin n), collVal U (collV C ord U) s = collOrig C U w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hinput : w < n
    · let p : Fin n := ⟨w,hinput⟩
      refine ⟨({p},∅), by simp, ?_⟩
      intro U
      unfold collOrig
      rw [collapse_getD_wiresFrom_lt _ _ _ (by simpa using hinput)]
      rw [List.getD_eq_getElem _ _ (by simpa using hinput), List.getElem_ofFn]
      simp [collVal,p]
    let j := w-n
    have hw : n + j = w := by dsimp [j]; omega
    by_cases hj : j < C.gates.length
    · obtain h | h := (hm C.gates[j] (List.getElem_mem hj)).1
      · obtain ⟨z,hz⟩ := allAnd j hj h
        exact ⟨(∅,{z}), by simp [hz,hw], fun U => by simp [collVal,collV,hz,hw]⟩
      · obtain ⟨f,hf,he⟩ := coll_prior C ord ih
        refine ⟨collCollect C.gates[j].inputs f, ?_, ?_⟩
        · intro z hz
          obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
          exact Nat.le_of_lt (hf i z hi)
        · intro U
          rw [← hw, coll_gate C U j hj, show C.gates[j].op = GateOp.or from h]
          apply Bool.eq_iff_iff.mpr
          rw [collCollect_true]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
          simp_rw [he, hw]
    · refine ⟨(∅,∅), by simp, ?_⟩
      intro U
      unfold collOrig
      rw [List.getD_eq_default _ _ (by simp only [collapse_length_wiresFrom, List.length_ofFn]; omega)]
      simp [collVal]

private lemma coll_sides {n k : ℕ} (C : Circuit) (hm : Monotone2 C) (ord : Fin k ↪o ℕ)
    (allAnd : ∀ j (hj : j < C.gates.length), C.gates[j].op = GateOp.and →
      ∃ i, ord i = j)
    (ok : ∀ i, ∃ h : ord i < C.gates.length, C.gates[ord i].op = GateOp.and)
    (i : Fin k) :
    ∃ l r : CollSide n k,
      (∀ z ∈ l.2, z < i) ∧ (∀ z ∈ r.2, z < i) ∧
      ∀ U : Finset (Fin n), U.Nonempty →
        (collVal U (collV C ord U) l && collVal U (collV C ord U) r) = collV C ord U i := by
  classical
  obtain ⟨h,hop⟩ := ok i
  let g := C.gates[ord i]
  have hlen := (hm g (List.getElem_mem h)).2
  obtain ⟨f, hf, he⟩ := coll_prior (w := n + ord i) C ord
    (fun w _ => coll_wires C hm ord allAnd w)
  have ltj (a : ℕ) (z : Fin k) (hz : z ∈ (f a).2) : z < i :=
    ord.lt_iff_lt.mp (Nat.lt_of_add_lt_add_left (hf _ _ hz))
  have gate (U : Finset (Fin n)) :
      collV C ord U i = (g.inputs.map fun j => collVal U (collV C ord U) (f j)).all id := by
    rw [collV, coll_gate C U (ord i) h, hop]
    simp only [GateOp.eval, he, g]
  cases hL : g.inputs with
  | nil =>
    refine ⟨(Finset.univ,∅), (Finset.univ,∅), by simp, by simp, ?_⟩
    intro U hu
    rw [gate,hL]
    simpa [collVal] using (show ∃ x, x ∈ U from hu)
  | cons a L =>
    cases L with
    | nil =>
      refine ⟨f a, f a, ltj a, ltj a, ?_⟩
      intro U _
      simp [gate, hL]
    | cons b L =>
      have hem : L = [] := by rw [hL] at hlen; simpa using hlen
      subst L
      refine ⟨f a, f b, ltj a, ltj b, ?_⟩
      intro U _
      simp [gate, hL]

private lemma coll_empty_gate {n : ℕ} (D : AndCountCircuit n) (d : ℕ) :
    ∀ i, D.gateValFuel ∅ d i = false := by
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    simp [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue, ih]

private lemma coll_realize {n k : ℕ} (val : Finset (Fin n) → Fin k → Bool)
    (l r : Fin k → CollSide n k) (o : CollSide n k)
    (hl : ∀ i z, z ∈ (l i).2 → z < i) (hr : ∀ i z, z ∈ (r i).2 → z < i)
    (hv : ∀ i (U : Finset (Fin n)), U.Nonempty →
      (collVal U (val U) (l i) && collVal U (val U) (r i)) = val U i) :
    ∃ D : AndCountCircuit n, D.size = k ∧ D.WellFormed ∧ D.eval ∅ = false ∧
      ∀ U : Finset (Fin n), U.Nonempty → D.eval U = collVal U (val U) o := by
  classical
  let D : AndCountCircuit n := ⟨k,fun i => (l i).1,fun i => (l i).2,
    fun i => (r i).1,fun i => (r i).2,o.1,o.2⟩
  refine ⟨D, rfl, fun i => ⟨hl i,hr i⟩, ?_, ?_⟩
  · simp [AndCountCircuit.eval, AndCountCircuit.gateVal, coll_empty_gate]
  intro U hU
  have fuel (d : ℕ) : ∀ i : Fin k, i.val < d → D.gateValFuel U d i = val U i := by
    induction d with
    | zero => intro i; omega
    | succ d ih =>
      intro i hd
      have eqSide (s : CollSide n k) (hs : ∀ z ∈ s.2, z < i) :
          AndCountCircuit.sideTrue U s.1 s.2 i (D.gateValFuel U d) = collVal U (val U) s := by
        unfold AndCountCircuit.sideTrue collVal
        congr 1
        apply propext
        apply or_congr_right
        constructor
        · rintro ⟨j,hj,hji,hval⟩
          exact ⟨j,hj,(ih j (by have := hji; change j.val < i.val at this; omega)).symm.trans hval⟩
        · rintro ⟨j,hj,hval⟩
          have hji := hs j hj
          exact ⟨j,hj,hji,(ih j (by change j.val < i.val at hji; omega)).trans hval⟩
      change (AndCountCircuit.sideTrue U (l i).1 (l i).2 i (D.gateValFuel U d) &&
        AndCountCircuit.sideTrue U (r i).1 (r i).2 i (D.gateValFuel U d)) = _
      rw [eqSide _ (hl i), eqSide _ (hr i), hv _ _ hU]
  have gate (i : Fin k) : D.gateVal U i = val U i := fuel k i i.isLt
  simp only [AndCountCircuit.eval, gate, collVal, D]


lemma mono_fold : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ w w' : List Bool, w.length = w'.length →
    (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (collapse_wiresFrom gs w).getD i false = true →
      (collapse_wiresFrom gs w').getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ w w' _ h; simpa [collapse_wiresFrom] using h
  | cons g gs ih =>
    intro hg w w' hl h
    have hstep : ∀ v, collapse_wiresFrom (g :: gs) v =
        collapse_wiresFrom gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) :=
      fun v => rfl
    rw [hstep, hstep]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hl])
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
      rcases hg g (List.mem_cons_self ..) with ho | ho <;> rw [ho] <;> simp only [GateOp.eval]
      · intro H
        rw [List.all_eq_true] at H ⊢
        intro b hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
        exact h a (H _ (List.mem_map_of_mem ha))
      · intro H
        rw [List.any_eq_true] at H ⊢
        obtain ⟨b, hb, hbt⟩ := H
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
        exact ⟨_, List.mem_map_of_mem ha, h a hbt⟩
    intro j hj
    rcases lt_trichotomy j w.length with hj1 | hj1 | hj1
    · rw [List.getD_append _ _ _ _ hj1] at hj
      rw [List.getD_append _ _ _ _ (hl ▸ hj1)]
      exact h j hj
    · subst hj1
      rw [collapse_getD_snoc_eq] at hj
      rw [hl, collapse_getD_snoc_eq]
      exact hv hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
      exact absurd hj (by simp)

lemma empty_input (n : ℕ) : ∀ i, (List.ofFn (fun x : Fin n => decide (x ∈ (∅ : Finset (Fin n))))).getD i false = false := by
  intro i
  rcases lt_or_ge i n with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]; simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

lemma main_aux {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (hf : ∃ S : Finset (Fin n), circuitFun n C (fun x => decide (x ∈ S)) = false) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.size ≤ Nat.card {x : Fin C.gates.length // (C.gates.get x).op = GateOp.and} ∧
      ∀ U : Finset (Fin n), D.eval U = circuitFun n C (fun x => decide (x ∈ U)) := by
  classical
  let T := (Finset.range C.gates.length).filter
    (fun j => ∃ h : j < C.gates.length, C.gates[j].op = GateOp.and)
  let ord := T.orderEmbOfFin rfl
  have memOrd (i : Fin T.card) : ord i ∈ T := T.orderEmbOfFin_mem rfl i
  have allAnd (j : ℕ) (hj : j < C.gates.length) (ha : C.gates[j].op = GateOp.and) :
      ∃ i, ord i = j := by
    have hT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, ha⟩
    change j ∈ Set.range (T.orderEmbOfFin rfl)
    rwa [Finset.range_orderEmbOfFin]
  have ok (i : Fin T.card) : ∃ h : ord i < C.gates.length, C.gates[ord i].op = GateOp.and :=
    (Finset.mem_filter.mp (memOrd i)).2
  choose l r hl hr hex using coll_sides (n := n) C hm ord allAnd ok
  obtain ⟨o, _, ho⟩ := coll_wires (n := n) C hm ord allAnd C.output
  obtain ⟨D, hsize, hw, hempty, hval⟩ := coll_realize (collV C ord) l r o hl hr hex
  refine ⟨D, hw, ?_, ?_⟩
  · rw [hsize, ← Nat.card_eq_finsetCard]
    apply Nat.card_le_card_of_injective (fun j : T =>
      (⟨⟨j.1, (Finset.mem_filter.mp j.2).2.1⟩, (Finset.mem_filter.mp j.2).2.2⟩ :
        {x : Fin C.gates.length // (C.gates.get x).op = GateOp.and}))
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun z => z.1.1) hab
    simpa using this
  · intro U
    by_cases hn : U.Nonempty
    · rw [hval U hn, ho]
      rfl
    · have hU : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst hU
      rw [hempty]
      obtain ⟨S, hS⟩ := hf
      cases hc : circuitFun n C (fun x => decide (x ∈ (∅ : Finset (Fin n))))
      · rfl
      · exfalso
        have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
          intro g hg
          rcases (hm g hg).1 with h | h
          · exact Or.inl h
          · exact Or.inr h
        have := mono_fold C.gates hops
          (List.ofFn (fun x : Fin n => decide (x ∈ (∅ : Finset (Fin n)))))
          (List.ofFn (fun x : Fin n => decide (x ∈ S))) (by simp)
          (fun i hi => by rw [empty_input] at hi; exact absurd hi (by simp)) C.output hc
        have h2 : circuitFun n C (fun x => decide (x ∈ S)) = true := this
        rw [hS] at h2
        exact Bool.noConfusion h2

end PEqualNP.Outside.L_meta_4682

theorem PEqualNP.Outside.L_meta_4682 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : Finset (Fin (27 : ℕ))), (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x1 fun (x4 : Fin (27 : ℕ)) => Decidable.decide (x4 ∈ x3)) = Bool.false) → ∃ (x4 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)), x4.WellFormed ∧ x4.size ≤ Nat.card { x5 : Fin x1.gates.length // (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and } ∧ ∀ (x5 : Finset (Fin (27 : ℕ))), x4.eval x5 = PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x1 fun (x6 : Fin (27 : ℕ)) => Decidable.decide (x6 ∈ x5) := by
  intro C hm hf
  exact PEqualNP.Outside.L_meta_4682.main_aux C hm hf
