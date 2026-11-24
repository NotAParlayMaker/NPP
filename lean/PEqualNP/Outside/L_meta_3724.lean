import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3724

open PEqualNP.CircuitLowerBounds

def stepO (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def sub (σ : ℕ → ℕ) (gg : Gate) : Gate := { op := gg.op, inputs := gg.inputs.map σ }

lemma foldl_len (L : List Gate) (a : List Bool) :
    (L.foldl stepO a).length = a.length + L.length := by
  induction L generalizing a with
  | nil => simp
  | cons g L ih => simp [List.foldl_cons, ih, stepO]; omega

lemma foldl_prefix (L : List Gate) (a : List Bool) (i : ℕ) (hi : i < a.length) :
    (L.foldl stepO a).getD i false = a.getD i false := by
  induction L generalizing a with
  | nil => rfl
  | cons g L ih =>
    rw [List.foldl_cons, ih _ (by simp [stepO]; omega)]
    simp [stepO, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (a : List Bool) (i : ℕ) (h : a.length ≤ i) : a.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma app_mono (a b : List Bool) (va vb : Bool) (hl : a.length = b.length)
    (h : ∀ k, a.getD k false = true → b.getD k false = true) (hv : va = true → vb = true) :
    ∀ k, (a ++ [va]).getD k false = true → (b ++ [vb]).getD k false = true := by
  intro k hk
  rcases Nat.lt_trichotomy k a.length with hlt | heq | hgt
  · have h1 : (a ++ [va]).getD k false = a.getD k false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    have h2 : (b ++ [vb]).getD k false = b.getD k false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hlt)]
    rw [h1] at hk; rw [h2]; exact h k hk
  · subst heq
    have h1 : (a ++ [va]).getD a.length false = va := by simp [List.getD_eq_getElem?_getD]
    have h2 : (b ++ [vb]).getD a.length false = vb := by
      simp [List.getD_eq_getElem?_getD, hl]
    rw [h1] at hk; rw [h2]; exact hv hk
  · rw [getD_ge _ _ (by simp; omega)] at hk; exact absurd hk (by simp)

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (p q : ℕ → Bool) (h : ∀ i ∈ ins, p i = true → q i = true)
    (hp : op.eval (ins.map p) = true) : op.eval (ins.map q) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hp ⊢
    rintro _ ⟨i, hi, rfl⟩
    exact h i hi (hp _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hp ⊢
    obtain ⟨_, ⟨i, hi, rfl⟩, hpi⟩ := hp
    exact ⟨_, ⟨i, hi, rfl⟩, h i hi hpi⟩

lemma mono_run (L : List Gate) (hops : ∀ g ∈ L, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → (∀ k, a.getD k false = true → b.getD k false = true) →
    ∀ k, (L.foldl stepO a).getD k false = true → (L.foldl stepO b).getD k false = true := by
  induction L with
  | nil => intro a b _ h; exact h
  | cons g L ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
    · simp [stepO, hl]
    · exact app_mono a b _ _ hl h
        (eval_mono g.op (hops g (List.mem_cons_self ..)) g.inputs _ _ (fun i _ => h i))

lemma map_ops (L : List Gate) (σ : ℕ → ℕ) (hops : ∀ g ∈ L, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ g ∈ L.map (sub σ), g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  exact hops g0 hg0

/-- Old wires below new wires, where the old value at `n + w` forces the old value at `w2`. -/
lemma cmp_up (gs : List Gate) (x : List Bool) (n w w2 : ℕ) (hx : x.length = n)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (hw2 : w2 < n + w)
    (H : (gs.foldl stepO x).getD (n + w) false = true → (gs.foldl stepO x).getD w2 false = true) :
    ∀ L R : List Gate, L ++ R = gs → ∀ k, (L.foldl stepO x).getD k false = true →
      ((L.map (sub fun i => if i = n + w then w2 else i)).foldl stepO x).getD k false = true := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro R _ k hk; exact hk
  | append_singleton L' g ih =>
    intro R hLR
    have hLR' : L' ++ g :: R = gs := by simpa using hLR
    have hg : g ∈ gs := by rw [← hLR']; simp
    rw [List.map_append, List.foldl_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    have hlA := foldl_len L' x
    have hlB := foldl_len (L'.map (sub fun i => if i = n + w then w2 else i)) x
    simp only [List.length_map] at hlB
    have hfull : gs.foldl stepO x = (g :: R).foldl stepO (L'.foldl stepO x) := by
      rw [← hLR', List.foldl_append]
    apply app_mono _ _ _ _ (by rw [hlA, hlB]) (ih (g :: R) hLR')
    simp only [sub, List.map_map]
    apply eval_mono g.op (hops g hg)
    intro i _ hi
    simp only [Function.comp]
    by_cases hiw : i = n + w
    · subst hiw
      simp only [ite_true]
      have hlt : n + w < (L'.foldl stepO x).length := by
        by_contra hc; rw [getD_ge _ _ (by omega)] at hi; exact absurd hi (by simp)
      rw [← foldl_prefix (g :: R) _ _ hlt, ← hfull] at hi
      have h2 := H hi
      rw [hfull, foldl_prefix (g :: R) _ _ (by omega)] at h2
      exact ih (g :: R) hLR' w2 h2
    · simp only [hiw, ite_false]
      exact ih (g :: R) hLR' i hi

/-- New wires below old wires, where the old value at `w2` forces the old value at `n + w`. -/
lemma cmp_down (gs : List Gate) (x : List Bool) (n w w2 : ℕ) (hx : x.length = n)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hRB : ∀ L' g R, L' ++ g :: R = gs → ∀ i ∈ g.inputs, i < n + L'.length)
    (H : (gs.foldl stepO x).getD w2 false = true → (gs.foldl stepO x).getD (n + w) false = true) :
    ∀ L R : List Gate, L ++ R = gs → ∀ k,
      ((L.map (sub fun i => if i = n + w then w2 else i)).foldl stepO x).getD k false = true →
      (L.foldl stepO x).getD k false = true := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro R _ k hk; exact hk
  | append_singleton L' g ih =>
    intro R hLR
    have hLR' : L' ++ g :: R = gs := by simpa using hLR
    have hg : g ∈ gs := by rw [← hLR']; simp
    rw [List.map_append, List.foldl_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    have hlA := foldl_len L' x
    have hlB := foldl_len (L'.map (sub fun i => if i = n + w then w2 else i)) x
    simp only [List.length_map] at hlB
    have hfull : gs.foldl stepO x = (g :: R).foldl stepO (L'.foldl stepO x) := by
      rw [← hLR', List.foldl_append]
    apply app_mono _ _ _ _ (by rw [hlA, hlB]) (ih (g :: R) hLR')
    have hsub : (sub (fun i => if i = n + w then w2 else i) g).op = g.op := rfl
    rw [hsub]
    simp only [sub, List.map_map]
    apply eval_mono g.op (hops g hg)
    intro i hmem hi
    simp only [Function.comp] at hi
    by_cases hiw : i = n + w
    · subst hiw
      simp only [ite_true] at hi
      have h1 := ih (g :: R) hLR' w2 hi
      have hlt : w2 < (L'.foldl stepO x).length := by
        by_contra hc; rw [getD_ge _ _ (by omega)] at h1; exact absurd h1 (by simp)
      rw [← foldl_prefix (g :: R) _ _ hlt, ← hfull] at h1
      have h2 := H h1
      have hlt2 : n + w < (L'.foldl stepO x).length := by
        have := hRB L' g R hLR' _ hmem; rw [hlA, hx]; exact this
      rw [hfull, foldl_prefix (g :: R) _ _ hlt2] at h2
      exact h2
    · simp only [hiw, ite_false] at hi
      exact ih (g :: R) hLR' i hi

lemma ofFn_mono {n : ℕ} (x y : Fin n → Bool) (h : ∀ z, x z = true → y z = true) :
    ∀ k, (List.ofFn x).getD k false = true → (List.ofFn y).getD k false = true := by
  intro k hk
  by_cases hkn : k < n
  · simp [List.getD_eq_getElem?_getD, hkn] at hk ⊢
    exact h _ hk
  · rw [getD_ge _ _ (by simp; omega)] at hk; exact absurd hk (by simp)

end PEqualNP.Outside.L_meta_3724

theorem PEqualNP.Outside.L_meta_3724.main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (w w2 : ℕ),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  w < C.gates.length → w2 < n + w →
  (∀ u v : Fin n, G.Adj u v →
    (C.wires (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD (n + w) false = true →
    (C.wires (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD w2 false = true) →
  (∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) → (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) →
    (C.wires (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD w2 false = true →
    (C.wires (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD (n + w) false = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + w then w2 else i) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := if C.output = n + w then w2 else C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C w w2 hAO hF hw hw2 hK hM
  have hops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := hAO.1
  have hRB : ∀ L' g R, L' ++ g :: R = C.gates → ∀ i ∈ g.inputs, i < n + L'.length := by
    intro L' g R h i hi
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C L'.length = g := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [← h]; simp [List.getD_eq_getElem?_getD]
    exact hAO.2.1 L'.length (by rw [← h]; simp) i (by rw [hgat]; exact hi)
  have hold : ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C y
      = (C.gates.foldl PEqualNP.Outside.L_meta_3724.stepO (List.ofFn y)).getD C.output false :=
    fun y => rfl
  have hwires : ∀ y : List Bool, C.wires y = C.gates.foldl PEqualNP.Outside.L_meta_3724.stepO y :=
    fun y => rfl
  -- monotonicity of the new circuit
  have hmono : ∀ y1 y2 : Fin n → Bool, (∀ z, y1 z = true → y2 z = true) →
      ((C.gates.map (PEqualNP.Outside.L_meta_3724.sub (fun i => if i = n + w then w2 else i))).foldl
          PEqualNP.Outside.L_meta_3724.stepO (List.ofFn y1)).getD
          (if C.output = n + w then w2 else C.output) false = true →
      ((C.gates.map (PEqualNP.Outside.L_meta_3724.sub (fun i => if i = n + w then w2 else i))).foldl
          PEqualNP.Outside.L_meta_3724.stepO (List.ofFn y2)).getD
          (if C.output = n + w then w2 else C.output) false = true := by
    intro y1 y2 h
    exact PEqualNP.Outside.L_meta_3724.mono_run _
      (PEqualNP.Outside.L_meta_3724.map_ops _ _ hops) _ _ (by simp)
      (PEqualNP.Outside.L_meta_3724.ofFn_mono y1 y2 h) _
  -- comparison at a single input
  have hup : ∀ y : Fin n → Bool,
      ((C.wires (List.ofFn y)).getD (n + w) false = true → (C.wires (List.ofFn y)).getD w2 false = true) →
      (C.gates.foldl PEqualNP.Outside.L_meta_3724.stepO (List.ofFn y)).getD C.output false = true →
      ((C.gates.map (PEqualNP.Outside.L_meta_3724.sub (fun i => if i = n + w then w2 else i))).foldl
          PEqualNP.Outside.L_meta_3724.stepO (List.ofFn y)).getD
          (if C.output = n + w then w2 else C.output) false = true := by
    intro y H ho
    simp only [hwires] at H
    have cmp := PEqualNP.Outside.L_meta_3724.cmp_up C.gates (List.ofFn y) n w w2 (by simp) hops hw2 H
      C.gates [] (by simp)
    by_cases hc : C.output = n + w
    · rw [if_pos hc]; rw [hc] at ho; exact cmp w2 (H ho)
    · rw [if_neg hc]; exact cmp _ ho
  have hdown : ∀ y : Fin n → Bool,
      ((C.wires (List.ofFn y)).getD w2 false = true → (C.wires (List.ofFn y)).getD (n + w) false = true) →
      ((C.gates.map (PEqualNP.Outside.L_meta_3724.sub (fun i => if i = n + w then w2 else i))).foldl
          PEqualNP.Outside.L_meta_3724.stepO (List.ofFn y)).getD
          (if C.output = n + w then w2 else C.output) false = true →
      (C.gates.foldl PEqualNP.Outside.L_meta_3724.stepO (List.ofFn y)).getD C.output false = true := by
    intro y H ho
    simp only [hwires] at H
    have cmp := PEqualNP.Outside.L_meta_3724.cmp_down C.gates (List.ofFn y) n w w2 (by simp) hops hRB H
      C.gates [] (by simp)
    by_cases hc : C.output = n + w
    · rw [if_pos hc] at ho; rw [hc]; exact H (cmp w2 ho)
    · rw [if_neg hc] at ho; exact cmp _ ho
  have hgf : ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true ↔
      ∃ u v, G.Adj u v ∧ y u = true ∧ y v = true := by
    intro y; simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  funext x
  change ((C.gates.map (PEqualNP.Outside.L_meta_3724.sub (fun i => if i = n + w then w2 else i))).foldl
          PEqualNP.Outside.L_meta_3724.stepO (List.ofFn x)).getD
          (if C.output = n + w then w2 else C.output) false = _
  cases hnx : ((C.gates.map (PEqualNP.Outside.L_meta_3724.sub (fun i => if i = n + w then w2 else i))).foldl
          PEqualNP.Outside.L_meta_3724.stepO (List.ofFn x)).getD
          (if C.output = n + w then w2 else C.output) false <;>
    cases hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
  · rfl
  · -- new false, F true: contradiction via an edge below x
    exfalso
    obtain ⟨u, v, huv, hu, hv⟩ := (hgf x).1 hx
    have hoe : (C.gates.foldl PEqualNP.Outside.L_meta_3724.stepO
        (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD C.output false = true := by
      rw [← hold, hF]; exact (hgf _).2 ⟨u, v, huv, by simp, by simp⟩
    have hne := hup _ (hK u v huv) hoe
    have := hmono _ x (by
      intro z hz
      simp only [decide_eq_true_eq] at hz
      rcases hz with rfl | rfl
      · exact hu
      · exact hv) hne
    rw [hnx] at this; exact absurd this (by simp)
  · -- new true, F false: contradiction via a maximal independent set above x
    exfalso
    have hind : ∀ a b : Fin n, G.Adj a b → x a = true → x b = true → False := by
      intro a b hab ha hb
      have := (hgf x).2 ⟨a, b, hab, ha, hb⟩
      rw [hx] at this; exact absurd this (by simp)
    let S : Finset (Fin n) := Finset.univ.filter (fun z => x z = true)
    let Fm : Finset (Finset (Fin n)) := (Finset.univ : Finset (Finset (Fin n))).filter
      (fun M => S ⊆ M ∧ ∀ a ∈ M, ∀ b ∈ M, ¬ G.Adj a b)
    have hS : S ∈ Fm := by
      simp only [Fm, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨le_refl _, ?_⟩
      intro a ha b hb hab
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hind a b hab ha hb
    obtain ⟨M, hMm, hMmax⟩ := Finset.exists_max_image Fm Finset.card ⟨S, hS⟩
    simp only [Fm, Finset.mem_filter, Finset.mem_univ, true_and] at hMm
    obtain ⟨hSM, hMind⟩ := hMm
    have hMdom : ∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v := by
      intro v hv
      by_contra hc
      push_neg at hc
      have hins : insert v M ∈ Fm := by
        simp only [Fm, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hSM.trans (Finset.subset_insert _ _), ?_⟩
        intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact G.irrefl hab
        · exact hc b hb hab.symm
        · exact hc a ha hab
        · exact hMind a ha b hb hab
      have := hMmax _ hins
      rw [Finset.card_insert_of_notMem hv] at this
      omega
    have hxm : ∀ z, x z = true → decide (z ∈ M) = true := by
      intro z hz
      simp only [decide_eq_true_eq]
      exact hSM (by simp [S, hz])
    have hnm := hmono x _ hxm hnx
    have hom := hdown _ (hM M hMind hMdom) hnm
    rw [← hold, hF] at hom
    obtain ⟨a, b, hab, ha, hb⟩ := (hgf _).1 hom
    simp only [decide_eq_true_eq] at ha hb
    exact hMind a ha b hb hab
  · rfl

theorem PEqualNP.Outside.L_meta_3724 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (w w2 : ℕ),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  w < C.gates.length → w2 < n + w →
  (∀ u v : Fin n, G.Adj u v →
    (C.wires (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD (n + w) false = true →
    (C.wires (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD w2 false = true) →
  (∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) → (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) →
    (C.wires (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD w2 false = true →
    (C.wires (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD (n + w) false = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + w then w2 else i) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := if C.output = n + w then w2 else C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ :=
  PEqualNP.Outside.L_meta_3724.main
