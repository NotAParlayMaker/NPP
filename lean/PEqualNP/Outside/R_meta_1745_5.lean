import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first two children are the standard cover construction and the input incidence bound.
-- The last child is the strict-below-bound residual, narrowed by the proved reader constraints.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1745_5
  (buildFromCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A T : Finset (Fin n))
      (f : (Fin n → Bool) → Bool),
    (∃ u w, G.Adj u w) →
    (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
    (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) →
    ∃ s, s + 1 ≤ A.card + G.edgeSet.ncard + T.card ∧ HasCircuitSize n f s)
  (inputBudget : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
    (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
    (∑ i : Fin n, (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i.val).length) ≤ C.size + 1)
  (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit),
    let R := fun v : Fin n => C.gates.filter (fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    (∀ u w, G.Adj u w → u ∉ A) → (∃ u w, G.Adj u w) →
    (∀ x, circuitFun n C x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) →
    IsMinimalCircuit n C →
    (∀ v ∉ A, (R v).length ≤ 3 ∧ ((R v).length = 3 → ∀ g ∈ R v, g.op = .or)) →
    (∀ T : Finset (Fin n), (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
      C.size + 1 < A.card + G.edgeSet.ncard + T.card) →
    (G.IsBipartite → (Aᶜ.filter (fun v => 3 ≤ (R v).length)).card <
      (Aᶜ.filter (fun v => (R v).length = 1)).card) →
    (∀ v ∉ A, ∀ w ∉ A, v ≠ w → ∀ g : Gate, R v = [g] → w.val ∈ g.inputs → g.op = .not) →
    ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s) :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (C : Circuit),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    (∀ u w, G.Adj u w → u ∉ A) →
    (∃ u w, G.Adj u w) →
    (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A,
      let readers := C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
      readers.length ≤ 3 ∧ (readers.length = 3 → ∀ g ∈ readers, g.op = GateOp.or)) →
    ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) s := by
  classical
  -- Wire evaluation and effective inputs.
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have evalWires (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
      circuitFun n C x = (wiresFrom C.gates (List.ofFn x)).getD C.output false := rfl
  have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : wiresFrom (g :: gs) w
          = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp
  have getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
    rw [ht, List.getD_append _ _ _ _ h]
  have getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
      (L ++ [S]).getD j d = L.getD j d := by
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  let effectiveInputs (g : Gate) : List ℕ :=
    g.inputs.take (bif g.op.eval [false] then 1 else 2)
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evalNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have effective_eval (g : Gate) (ok : FanInTwo ⟨[g],0⟩) (f : ℕ → Bool) :
      g.op.eval (g.inputs.map f) = g.op.eval ((effectiveInputs g).map f) := by
    obtain ⟨hop, hlen⟩ := ok g (by simp)
    rcases hop with hand | hor | hnot
    · simp [effectiveInputs, hand, evalAnd, List.take_of_length_le hlen]
    · simp [effectiveInputs, hor, evalOr, List.take_of_length_le hlen]
    · change g.op = GateOp.not at hnot
      cases h : g.inputs <;> simp [effectiveInputs, hnot, evalNot, h]
  let readers (gs : List Gate) (wire : ℕ) : ℕ :=
    (gs.filter fun g => (effectiveInputs g).contains wire).length
  have agree_except (gs : List Gate) (a : ℕ)
      (fan : ∀ g ∈ gs, FanInTwo ⟨[g],0⟩)
      (unread : ∀ g ∈ gs, a ∉ effectiveInputs g) (x y : List Bool)
      (len : x.length = y.length) (off : ∀ i, i ≠ a → x.getD i false = y.getD i false) :
      ∀ i, i ≠ a → (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
    induction gs generalizing x y with
    | nil => exact off
    | cons g gs ih =>
      have same : (effectiveInputs g).map (fun i => x.getD i false) =
          (effectiveInputs g).map (fun i => y.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact off i (fun eq => unread g (by simp) (eq ▸ hi))
      have eqGate : g.op.eval (g.inputs.map (fun i => x.getD i false)) =
          g.op.eval (g.inputs.map (fun i => y.getD i false)) := by
        simp only [effective_eval g (fan g (by simp)), same]
      simp only [wiresFrom, List.foldl_cons] at ih ⊢
      rw [eqGate]
      apply ih (fun g hg => fan g (by simp [hg])) (fun g hg => unread g (by simp [hg]))
      · simp [len]
      · intro i hia
        by_cases h : i = x.length
        · subst i
          simp [len]
        · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by simpa [← len] using h)]
          exact off i hia
  let Represents {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :=
    ∀ x, circuitFun n C x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ v w, G.Adj v w ∧ x v = true ∧ x w = true
  let Cover {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) :=
    ∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T
  let BelowEveryCover {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :=
    ∀ T : Finset (Fin n), Cover G T → C.size + 1 < A.card + G.edgeSet.ncard + T.card
  have positive_of_change {n : ℕ} {C : Circuit} (fan : FanInTwo C) (a : Fin n)
      (out : C.output ≠ a.val) (x y : Fin n → Bool)
      (off : ∀ i, i ≠ a → x i = y i) (diff : circuitFun n C x ≠ circuitFun n C y) :
      1 ≤ readers C.gates a.val := by
    by_contra! zero
    have none : ∀ g ∈ C.gates, a.val ∉ effectiveInputs g := by
      intro g hg h
      have : 0 < readers C.gates a.val :=
        List.length_filter_pos_iff.mpr ⟨g,hg,List.contains_iff_mem.mpr h⟩
      omega
    have equal := agree_except C.gates a.val (fun g hg h hh => by
      have eq : h = g := by simpa using hh
      exact eq.symm ▸ fan g hg) none (List.ofFn x) (List.ofFn y)
      (by simp) (by
        intro i hi
        by_cases hn : i < n
        · simp [List.getD_eq_getElem?_getD, hn, off ⟨i, hn⟩ (fun eq => hi (congrArg Fin.val eq))]
        · simp [List.getD_eq_getElem?_getD, hn]) C.output out
    change circuitFun n C x = circuitFun n C y at equal
    exact diff equal
  have singleton_reads {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
      {A : Finset (Fin n)} (rep : Represents C G A)
      (isolated : ∀ u w, G.Adj u w → u ∉ A) (edge : ∃ u w, G.Adj u w)
      (fan : FanInTwo C) (a : Fin n) (ha : a ∈ A) : 1 ≤ readers C.gates a.val := by
    classical
    obtain ⟨u,w,huw⟩ := edge
    have out : C.output ≠ a.val := by
      intro eq
      let x : Fin n → Bool := fun i => decide (i ∉ A)
      have ht := (rep x).mpr (Or.inr ⟨u,w,huw, by simp [x, isolated u w huw],
        by simp [x, isolated w u huw.symm]⟩)
      simp only [evalWires, eq] at ht
      rw [getD_wiresFrom _ _ _ (by simp)] at ht
      simp [x, ha] at ht
    let x : Fin n → Bool := fun i => decide (i = a)
    let y : Fin n → Bool := fun _ => false
    apply positive_of_change fan a out x y (by intro i hi; simp [x,y,hi])
    intro equal
    have hx := (rep x).mpr (Or.inl ⟨a, ha, by simp [x]⟩)
    have hy := (rep y).mp (equal ▸ hx)
    simp [y] at hy
  -- Count primary reads, then compare the two sides of a bipartition.
  have below_cover_budget {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
      {A : Finset (Fin n)} (least : IsMinimalCircuit n C) (rep : Represents C G A)
      (isolated : ∀ u w, G.Adj u w → u ∉ A) (edge : ∃ u w, G.Adj u w)
      (cheap : BelowEveryCover C G A) (T : Finset (Fin n)) (cover : Cover G T) :
      ∑ v ∈ Aᶜ, readers C.gates v.val < G.edgeSet.ncard + T.card := by
    obtain ⟨u,w,huw⟩ := edge
    have yes := (rep (fun _ => true)).mpr (Or.inr ⟨u,w,huw,rfl,rfl⟩)
    have no : circuitFun n C (fun _ => false) ≠ true := by simpa using (rep (fun _ => false)).mp
    have hbudget : (∑ i : Fin n, readers C.gates i.val) ≤ C.size + 1 :=
      inputBudget n C least ⟨_, _, fun eq => no (eq ▸ yes)⟩
    have hA := Finset.sum_le_sum (singleton_reads rep isolated ⟨u,w,huw⟩ least.1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hA
    have hsplit := A.sum_compl_add_sum (fun v => readers C.gates v.val)
    have hcheap := cheap T cover
    omega
  have degree_sum {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
      (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
      (isolated : ∀ u w, G.Adj u w → u ∉ A) :
      2 * G.edgeSet.ncard = 3 * Aᶜ.card := by
    classical
    have hA : ∀ v ∈ A, G.degree v = 0 := by
      intro v hv
      apply (G.degree_eq_zero v).mpr
      intro w hw
      exact isolated v w hw hv
    have hOrd : ∀ v ∈ Aᶜ, G.degree v = 3 := by
      intro v hv
      simpa only [SimpleGraph.ncard_neighborSet] using deg v (Finset.mem_compl.mp hv)
    have hs := A.sum_compl_add_sum (fun v => G.degree v)
    rw [Finset.sum_congr rfl hOrd, Finset.sum_congr rfl hA] at hs
    have h := G.sum_degrees_eq_twice_card_edges
    simp only [← SimpleGraph.card_edgeSet, Set.fintypeCard_eq_ncard] at h
    simp at hs
    omega
  have small_bipartite_cover {n : ℕ} {G : SimpleGraph (Fin n)}
      {A : Finset (Fin n)} (bip : G.IsBipartite) (isolated : ∀ u w, G.Adj u w → u ∉ A) :
      ∃ T : Finset (Fin n), Cover G T ∧ 2 * T.card ≤ Aᶜ.card := by
    classical
    obtain ⟨s, t, parts⟩ := bip.exists_isBipartiteWith
    let L := Aᶜ.filter (· ∈ s)
    let R := Aᶜ.filter (· ∉ s)
    have sizes : L.card + R.card = Aᶜ.card := Finset.card_filter_add_card_filter_not ..
    have covers : Cover G L ∧ Cover G R := by
      constructor <;> intro v w vw
      all_goals
        have vA := isolated v w vw
        have wA := isolated w v vw.symm
        rcases parts.mem_of_adj vw with ⟨vs, wt⟩ | ⟨vt, ws⟩
        all_goals simp only [L, R, Finset.mem_filter, Finset.mem_compl]
        all_goals grind [Set.disjoint_left.mp parts.disjoint]
    by_cases h : L.card ≤ R.card
    · exact ⟨L, covers.1, by omega⟩
    · exact ⟨R, covers.2, by omega⟩
  have bipartite_budget {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
      (least : IsMinimalCircuit n C) (rep : Represents C G A)
      (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
      (isolated : ∀ u w, G.Adj u w → u ∉ A) (edge : ∃ u w, G.Adj u w)
      (cheap : BelowEveryCover C G A) (bip : G.IsBipartite) :
      (∑ v ∈ Aᶜ, readers C.gates v.val) < 2 * Aᶜ.card := by
    obtain ⟨T, cover, small⟩ := small_bipartite_cover bip isolated
    have h := below_cover_budget least rep isolated edge cheap T cover
    have he := degree_sum deg isolated
    omega
  have ordinary_reads {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
      (least : IsMinimalCircuit n C) (rep : Represents C G A)
      (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
      (isolated : ∀ u w, G.Adj u w → u ∉ A) (v : Fin n) (hv : v ∉ A) : 1 ≤ readers C.gates v.val := by
    classical
    have nv : (G.neighborSet v).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [deg v hv]; decide)
    obtain ⟨w, hvw⟩ := nv
    change G.Adj v w at hvw
    have hw := isolated w v hvw.symm
    let single (a : Fin n) : Fin n → Bool := fun i => decide (i = a)
    have off_single (a : Fin n) (ha : a ∉ A) : circuitFun n C (single a) ≠ true := by
      intro h
      rcases (rep _).mp h with ⟨u,hu,ht⟩ | ⟨u,z,uz,ht,hz⟩
      · have : u = a := by simpa [single] using ht
        exact ha (this ▸ hu)
      · have eu : u = a := by simpa [single] using ht
        have ez : z = a := by simpa [single] using hz
        exact uz.ne (eu.trans ez.symm)
    have out : C.output ≠ v.val := by
      intro eq
      apply off_single v hv
      simp only [evalWires, eq]
      rw [getD_wiresFrom _ _ _ (by simp)]
      simp [single]
    let both : Fin n → Bool := fun i => decide (i = v ∨ i = w)
    have yes := (rep both).mpr (Or.inr ⟨v,w,hvw,by simp [both],by simp [both]⟩)
    exact positive_of_change least.1 v out both (single w)
      (by intro i hi; simp [both,single,hi]) (fun eq => off_single w hw (eq ▸ yes))
  have more_single_than_heavy {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
      (least : IsMinimalCircuit n C) (rep : Represents C G A)
      (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
      (isolated : ∀ u w, G.Adj u w → u ∉ A) (edge : ∃ u w, G.Adj u w)
      (cheap : BelowEveryCover C G A) (bip : G.IsBipartite) :
      (Aᶜ.filter (fun v => 3 ≤ readers C.gates v.val)).card <
        (Aᶜ.filter (fun v => readers C.gates v.val = 1)).card := by
    let r (v : Fin n) := readers C.gates v.val
    have localCount (v : Fin n) (hv : v ∈ Aᶜ) :
        2 + (if 3 ≤ r v then 1 else 0) ≤ r v + (if r v = 1 then 1 else 0) := by
      have h := ordinary_reads least rep deg isolated v (Finset.mem_compl.mp hv)
      dsimp [r]
      split <;> split <;> omega
    have total := Finset.sum_le_sum localCount
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole,
      Nat.cast_id] at total
    have h := bipartite_budget least rep deg isolated edge cheap bip
    dsimp [r] at total
    omega
  -- Distinguish two assignments on which a putative single gate is masked.
  let absorbOp (b : Bool) : GateOp := if b then .or else .and
  have absorbs (b : Bool) (g : Gate) (f : ℕ → Bool) (w : ℕ)
      (op : g.op = absorbOp b) (mem : w ∈ g.inputs) (fixed : f w = b) :
      g.op.eval (g.inputs.map f) = b := by
    cases b
    · change g.op = GateOp.and at op
      simp only [op, evalAnd, List.all_eq_false, List.mem_map]
      exact ⟨false, ⟨w, mem, fixed⟩, by decide⟩
    · change g.op = GateOp.or at op
      simp only [op, evalOr, List.any_eq_true, List.mem_map]
      exact ⟨true, ⟨w, mem, fixed⟩, rfl⟩
  have masked_wires (gs : List Gate) (v w : ℕ) (b : Bool)
      (fan : ∀ g ∈ gs, FanInTwo ⟨[g], 0⟩)
      (mask : ∀ g ∈ gs, v ∈ effectiveInputs g → g.op = absorbOp b ∧ w ∈ g.inputs)
      (x y : List Bool) (hw : w < x.length) (len : x.length = y.length)
      (fx : x.getD w false = b) (fy : y.getD w false = b)
      (off : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
      ∀ i, i ≠ v → (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
    induction gs generalizing x y with
    | nil => exact off
    | cons g gs ih =>
      have eqGate : g.op.eval (g.inputs.map (fun i => x.getD i false)) =
          g.op.eval (g.inputs.map (fun i => y.getD i false)) := by
        by_cases hit : v ∈ effectiveInputs g
        · obtain ⟨op,mem⟩ := mask g (by simp) hit
          exact (absorbs b g _ w op mem fx).trans (absorbs b g _ w op mem fy).symm
        · rw [effective_eval g (fan g (by simp)), effective_eval g (fan g (by simp))]
          congr 1
          exact List.map_congr_left fun i hi => off i (fun eq => hit (eq ▸ hi))
      simp only [wiresFrom, List.foldl_cons] at ih ⊢
      rw [eqGate]
      apply ih (fun a ha => fan a (by simp [ha])) (fun a ha => mask a (by simp [ha]))
      · simp; omega
      · simp [len]
      · rwa [List.getD_append _ _ _ _ hw]
      · rwa [List.getD_append _ _ _ _ (len ▸ hw)]
      · intro i hi
        by_cases h : i = x.length
        · subst i; simp [len]
        · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by simpa [← len] using h)]
          exact off i hi
  have escape_square {n : ℕ} {G : SimpleGraph (Fin n)} {v w : Fin n}
      (distinct : v ≠ w) (deg : (G.neighborSet v).ncard = 3)
      (girth : ∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) :
      ∃ z, G.Adj v z ∧ ¬ G.Adj w z := by
    by_contra! h
    obtain ⟨s,t,hs,ht,hst⟩ := (Set.one_lt_ncard_iff (G.neighborSet v).toFinite).mp (show 1 < (G.neighborSet v).ncard by omega)
    change G.Adj v s at hs
    change G.Adj v t at ht
    have ws := h s hs
    have wt := h t ht
    let p : G.Walk v v := .cons hs (.cons ws.symm (.cons wt (.cons ht.symm .nil)))
    have cycle : p.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · simp [p, SimpleGraph.Walk.cons_isPath_iff, distinct.symm,
          hs.ne.symm, ht.ne.symm, ws.ne.symm, wt.ne, hst]
      · simp [p]
    have bad := girth v p cycle
    simp [p] at bad
  have test_pair {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
      {v w : Fin n} (distinct : v ≠ w) (wA : w ∉ A)
      (deg : (G.neighborSet v).ncard = 3) (isolated : ∀ i j, G.Adj i j → i ∉ A)
      (girth : ∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length)
      {C : Circuit} (rep : Represents C G A) (b : Bool) :
      ∃ x y : Fin n → Bool, x w = b ∧ y w = b ∧ (∀ i, i ≠ v → x i = y i) ∧
        circuitFun n C x = true ∧ circuitFun n C y ≠ true := by
    classical
    obtain ⟨z, vz, extra⟩ : ∃ z, G.Adj v z ∧
        (if b then ¬ G.Adj w z else z ≠ w) := by
      cases b with
      | false => simpa using Set.exists_ne_of_one_lt_ncard (show 1 < (G.neighborSet v).ncard by omega) w
      | true => simpa using escape_square distinct deg girth
    have zA := isolated z v vz.symm
    let y : Fin n → Bool := fun i => decide (i = z ∨ (b = true ∧ i = w))
    let x : Fin n → Bool := fun i => decide (i = v) || y i
    have yw : y w = b := by
      cases b with
      | false =>
        have hzw : z ≠ w := extra
        simp [y, hzw.symm]
      | true => simp [y]
    refine ⟨x,y,?_,yw,?_,?_,?_⟩
    · simpa [x, distinct.symm] using yw
    · intro i hi; simp [x,hi]
    · apply (rep x).mpr
      exact Or.inr ⟨v,z,vz,by simp [x],by simp [x,y]⟩
    · intro h
      have hbad := (rep y).mp h
      simp only [y, decide_eq_true_eq] at hbad
      rcases hbad with ⟨a,ha,hh⟩ | ⟨i,j,ij,hi,hj⟩
      · rcases hh with hz | ⟨_, hw⟩
        · exact zA (hz ▸ ha)
        · exact wA (hw ▸ ha)
      · rcases hi with iz | ⟨hi, iw⟩ <;> rcases hj with jz | ⟨hj, jw⟩
        · exact ij.ne (iz.trans jz.symm)
        · have nwz : ¬ G.Adj w z := by simpa [hj] using extra
          exact nwz (by simpa only [iz, jw] using ij.symm)
        · have nwz : ¬ G.Adj w z := by simpa [hi] using extra
          exact nwz (by simpa only [iw, jz] using ij)
        · exact ij.ne (iw.trans jw.symm)
  have single_reader_excludes_primary_pair {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
      {C : Circuit} (fan : FanInTwo C) (rep : Represents C G A)
      (isolated : ∀ i j, G.Adj i j → i ∉ A)
      (girth : ∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length)
      (v w : Fin n) (distinct : v ≠ w) (vA : v ∉ A) (wA : w ∉ A)
      (deg : (G.neighborSet v).ncard = 3) (g : Gate)
      (sole : C.gates.filter (fun h => (effectiveInputs h).contains v.val) = [g])
      (partner : w.val ∈ g.inputs) : g.op ≠ .and ∧ g.op ≠ .or := by
    have out : C.output ≠ v.val := by
      intro eq
      let y : Fin n → Bool := fun i => decide (i = v)
      have on : circuitFun n C y = true := by
        simp only [evalWires, eq]
        rw [getD_wiresFrom _ _ _ (by simp)]
        simp [y]
      have off := (rep y).mp on
      simp [y] at off
      exact vA off
    have impossible (b : Bool) (op : g.op = absorbOp b) : False := by
      obtain ⟨x,y,hx,hy,off,yes,no⟩ := test_pair distinct wA deg isolated girth rep b
      have hmask (h : Gate) (hh : h ∈ C.gates) (reads : v.val ∈ effectiveInputs h) :
          h.op = absorbOp b ∧ w.val ∈ h.inputs := by
        have hh' : h ∈ C.gates.filter (fun k => (effectiveInputs k).contains v.val) :=
          List.mem_filter.mpr ⟨hh,List.contains_iff_mem.mpr reads⟩
        rw [sole, List.mem_singleton] at hh'
        exact hh' ▸ ⟨op,partner⟩
      have eq := masked_wires C.gates v.val w.val b
        (fun h hh k hk => by
          have e : k = h := by simpa using hk
          exact e.symm ▸ fan h hh) hmask (List.ofFn x) (List.ofFn y)
        (by simp) (by simp) (by simpa using hx) (by simpa using hy)
        (by
          intro i hi
          by_cases bound : i < n
          · simp [List.getD_eq_getElem?_getD, bound,
              off ⟨i,bound⟩ (fun e => hi (congrArg Fin.val e))]
          · simp [List.getD_eq_getElem?_getD,bound]) C.output out
      change circuitFun n C x = circuitFun n C y at eq
      exact no (eq ▸ yes)
    exact ⟨impossible false, impossible true⟩
  -- Apply the two restrictions to the cheap case and the cover construction elsewhere.
  intro n G A f C hdeg hgirth hfree hedge hsem hfan hfun hmin hread
  by_cases cheap : ∀ T : Finset (Fin n), (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
      C.size + 1 < A.card + G.edgeSet.ncard + T.card
  · have least : IsMinimalCircuit n C := by
      refine ⟨hfan, ?_⟩
      intro D hD e
      exact hmin _ ⟨D, hD, le_rfl, fun x => congrFun (e.trans hfun) x⟩
    have rep : Represents C G A := by
      intro x
      rw [hfun]
      exact hsem x
    rw [← hfun]
    apply residual n G A C hdeg hgirth hfree hedge rep least hread cheap
    · exact more_single_than_heavy least rep hdeg hfree hedge cheap
    · intro v hv w hw ne g sole partner
      have ex := single_reader_excludes_primary_pair hfan rep hfree hgirth
        v w ne hv hw (hdeg v hv) g sole partner
      change C.gates.filter (fun h => (effectiveInputs h).contains v.val) = [g] at sole
      have inside : g ∈ C.gates := by
        have h : g ∈ C.gates.filter (fun h => (effectiveInputs h).contains v.val) := by
          rw [sole]
          simp
        exact (List.mem_filter.mp h).1
      rcases (hfan g inside).1 with op | op | op
      · exact (ex.1 op).elim
      · exact (ex.2 op).elim
      · exact op
  push Not at cheap
  obtain ⟨T, hcover, hbudget⟩ := cheap
  obtain ⟨i, j, hij⟩ := hedge
  have pick : ∃ v w, v ∈ T ∧ G.Adj v w := by
    rcases hcover i j hij with hi | hj
    · exact ⟨i, j, hi, hij⟩
    · exact ⟨j, i, hj, hij.symm⟩
  obtain ⟨v, w, hvT, hvw⟩ := pick
  have hvA := hfree v w hvw
  have hwA := hfree w v hvw.symm
  have alive : ∃ z, G.Adj w z ∧ z ≠ v := by
    by_contra! h
    have sub : G.neighborSet w ⊆ {v} := fun z hz => h z hz
    have := Set.ncard_le_ncard sub
    simp [hdeg w hwA] at this
  obtain ⟨z, hwz, hz⟩ := alive
  have edge' : (G.deleteIncidenceSet v).Adj w z :=
    SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hwz, hvw.ne.symm, hz⟩
  have cover' : ∀ i j, (G.deleteIncidenceSet v).Adj i j → i ∈ T.erase v ∨ j ∈ T.erase v := by
    intro i j h
    obtain ⟨hij, hi, hj⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
    simpa [Finset.mem_erase, hi, hj] using hcover i j hij
  have sem' : ∀ x : Fin n → Bool, f (Function.update x v false) = true ↔
      (∃ a ∈ A, x a = true) ∨
        ∃ i j, (G.deleteIncidenceSet v).Adj i j ∧ x i = true ∧ x j = true := by
    intro x
    rw [hsem]
    have upd (i : Fin n) : Function.update x v false i = true ↔ i ≠ v ∧ x i = true := by
      by_cases h : i = v <;> simp [h]
    simp only [upd, SimpleGraph.deleteIncidenceSet_adj]
    grind
  obtain ⟨s, hs, hsize⟩ := buildFromCover n (G.deleteIncidenceSet v) A (T.erase v) _
    ⟨w, z, edge'⟩ cover' sem'
  refine ⟨v, hvA, s, ?_, hsize⟩
  have removed := G.card_edgeFinset_deleteIncidenceSet v
  have enough := G.degree_le_card_edgeFinset v
  simp only [← SimpleGraph.card_edgeSet, Set.fintypeCard_eq_ncard,
    ← SimpleGraph.ncard_neighborSet] at removed enough
  rw [hdeg v hvA] at removed enough
  rw [removed, Finset.card_erase_of_mem hvT] at hs
  have pos := Finset.card_pos.mpr ⟨v, hvT⟩
  omega
