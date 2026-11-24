import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Slot counting against a cover circuit, with Aᶜ \ I as the cover of an
-- independent set I, gives the density bound. The 4-gate escape is left open.
theorem PEqualNP.Outside.R_meta_1973_2
    (hcover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A T : Finset (Fin n)),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) →
      HasCircuitSize n (PEqualNP.MetaComplexity.NestedCover.graphFun G A)
        (A.card + G.edgeFinset.card + T.card - 1))
    (hinternal : ∀ (n : ℕ) (C : Circuit),
      FanInTwo C →
      (∀ s : ℕ, HasCircuitSize n (circuitFun n C) s → C.size ≤ s) →
      ∀ i : ℕ, i < C.size → n + i ∈ C.output :: C.gates.flatMap Gate.inputs)
    (hescape : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    let f := PEqualNP.MetaComplexity.NestedCover.graphFun G A
    let r := fun v : Fin n => C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A, 2 ≤ (r v).length ∧ (r v).length ≤ 3 ∧
      ((r v).length = 3 → ∀ g ∈ r v, g.op = GateOp.or)) →
    (∀ I : Finset (Fin n), I ⊆ Aᶜ → (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      Aᶜ.card + 2 * I.card ≤ 2 * (Aᶜ.filter fun v => (r v).length = 2).card) →
    ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       (2 : ℕ) ≤ x16.length ∧ x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length = (2 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro n G A f C degree girth noMarked edge fSpec fan computes minimal readBounds _
  classical
  let graphTarget := PEqualNP.MetaComplexity.NestedCover.graphFun G A
  let readers (v : Fin n) : List Gate := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  let slots : List ℕ := C.output :: C.gates.flatMap Gate.inputs
  have sameTarget : graphTarget = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) || decide (∃ u v, G.Adj u v ∧
      x u = true ∧ x v = true)) = true ↔ f x = true
    rw [fSpec x]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have computesGraph : circuitFun n C = graphTarget := computes.trans sameTarget.symm
  have leastGraph (s : ℕ) (h : HasCircuitSize n graphTarget s) : C.size ≤ s :=
    minimal s (sameTarget ▸ h)
  have gateSlotBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g tail ih =>
      have hg := h g List.mem_cons_self
      have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have countBound (xs : List ℕ) (S : Finset ℕ) : ∑ i ∈ S, xs.count i ≤ xs.length := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
      by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega
  have filteredSlots (v : ℕ) (gs : List Gate) :
      (gs.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v).length ≤
        (gs.flatMap Gate.inputs).count v := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons, List.count_append, List.filter_cons]
      split
      next h =>
        have hm : v ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.mp h)
        have := List.count_pos_iff.mpr hm
        simp only [List.length_cons]
        omega
      next => omega
  have getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (h : i < w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    have h' : i < (w ++ [b]).length := by
      simp [List.length_append, List.length_cons]; omega
    rw [List.getD_eq_getElem (l := w ++ [b]) (n := i) false h']
    rw [List.getD_eq_getElem (l := w) (n := i) false h]
    exact List.getElem_append_left h
  have getD_snoc_eq (w : List Bool) (b : Bool) (i : ℕ) (h : i = w.length) :
      (w ++ [b]).getD i false = b := by
    subst h
    rw [List.getD_append_right w [b] false w.length (Nat.le_refl _)]
    simp
  have getD_snoc_gt (w : List Bool) (b : Bool) (i : ℕ) (h : w.length + 1 ≤ i) :
      (w ++ [b]).getD i false = false := by
    have : (w ++ [b]).length ≤ i := by
      simp [List.length_append, List.length_cons]; omega
    exact List.getD_eq_default _ _ this
  have ofFn_getD_lt {m : ℕ} (f : Fin m → Bool) (i : ℕ) (hi : i < m) :
      (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
    have hi' : i < (List.ofFn f).length := by simpa [List.length_ofFn] using hi
    rw [List.getD_eq_getElem (l := List.ofFn f) (n := i) false hi']
    exact List.getElem_ofFn (f := f) hi'
  have wiresFrom_agree (gs : List Gate) (a : ℕ) :
      ∀ w₁ w₂ : List Bool, w₁.length = w₂.length →
        (∀ i : ℕ, i ≠ a → w₁.getD i false = w₂.getD i false) →
        (∀ g ∈ gs, a ∉ g.inputs) →
        let W1 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w₁
        let W2 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w₂
        W1.length = W2.length ∧ ∀ i : ℕ, i ≠ a → W1.getD i false = W2.getD i false := by
    induction gs with
    | nil =>
      intro w₁ w₂ hlen hag _
      exact ⟨hlen, hag⟩
    | cons g gs ih =>
      intro w₁ w₂ hlen hag hread
      have hmap : (g.inputs.map fun i => w₁.getD i false) =
          (g.inputs.map fun i => w₂.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact hag i (fun h => hread g List.mem_cons_self (h ▸ hi))
      have hlen' : (w₁ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)]).length =
          (w₂ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)]).length := by
        simp [hlen]
      have hag' : ∀ i : ℕ, i ≠ a →
          (w₁ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)]).getD i false =
            (w₂ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)]).getD i false := by
        intro i hi
        by_cases hlt : i < w₁.length
        · have hlt2 : i < w₂.length := by omega
          rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ hlt2]
          exact hag i hi
        · rcases Nat.lt_trichotomy i w₁.length with h | h | h
          · exact (hlt h).elim
          · have hw : i = w₂.length := by omega
            rw [getD_snoc_eq _ _ _ h, getD_snoc_eq _ _ _ hw, hmap]
          · have hge1 : w₁.length + 1 ≤ i := by omega
            have hge2 : w₂.length + 1 ≤ i := by omega
            rw [getD_snoc_gt _ _ _ hge1, getD_snoc_gt _ _ _ hge2]
      exact ih _ _ hlen' hag' (fun g' hg' => hread g' (List.mem_cons_of_mem _ hg'))
  have essentialA (a : Fin n) (ha : a ∈ A) : 1 ≤ slots.count (a : ℕ) := by
    apply List.count_pos_iff.mpr
    by_contra hn
    have hout : C.output ≠ (a : ℕ) := fun he => hn (by simp [slots, he])
    have noRead : ∀ g ∈ C.gates, (a : ℕ) ∉ g.inputs := by
      intro g hg hi
      exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hi⟩))
    let z : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i = a)
    have hoff : ∀ i : ℕ, i ≠ (a : ℕ) →
        (List.ofFn z).getD i false = (List.ofFn y).getD i false := by
      intro i hi
      by_cases hlt : i < n
      · rw [ofFn_getD_lt z i hlt, ofFn_getD_lt y i hlt]
        simp [z, y]
        exact fun hia => hi (congrArg Fin.val hia)
      · rw [List.getD_eq_default _ _ (by simp [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by simp [List.length_ofFn]; omega)]
    have ev := (wiresFrom_agree C.gates (a : ℕ) (List.ofFn z) (List.ofFn y)
      (by simp [List.length_ofFn]) hoff noRead).2 C.output hout
    have hne : circuitFun n C z ≠ circuitFun n C y := by
      rw [computes]
      have hz : f z ≠ true := by
        simp [fSpec, z]
      have hy : f y = true := (fSpec y).mpr (Or.inl ⟨a, ha, by simp [y]⟩)
      exact fun eq => hz (eq.trans hy)
    exact hne (by
      change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn z)).getD C.output false =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn y)).getD C.output false
      exact ev)
  have allocation : ∀ I : Finset (Fin n), I ⊆ Aᶜ →
      (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      Aᶜ.card + 2 * I.card ≤ 2 * (Aᶜ.filter fun v => (readers v).length = 2).card := by
    intro I hIsub hind
    let k := (Aᶜ.filter fun v => (readers v).length = 2).card
    have isCover : ∀ u v : Fin n, G.Adj u v → u ∈ Aᶜ \ I ∨ v ∈ Aᶜ \ I := by
      intro u v adj
      have huA : u ∉ A := noMarked u v adj
      have hvA : v ∉ A := noMarked v u adj.symm
      have hu : u ∈ Aᶜ := Finset.mem_compl.mpr huA
      have hv : v ∈ Aᶜ := Finset.mem_compl.mpr hvA
      by_cases huI : u ∈ I
      · have hvI : v ∉ I := fun h => (hind u huI v h) adj
        exact Or.inr (Finset.mem_sdiff.mpr ⟨hv, hvI⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨hu, huI⟩)
    have ub0 := hcover n G A (Aᶜ \ I) edge isCover
    have ub : C.size ≤ A.card + G.edgeFinset.card + (Aᶜ \ I).card - 1 :=
      leastGraph _ ub0
    have sdiff_card : (Aᶜ \ I).card = Aᶜ.card - I.card :=
      Finset.card_sdiff_of_subset hIsub
    have marked (a : Fin n) (ha : a ∈ A) : 1 ≤ slots.count (a : ℕ) := essentialA a ha
    have unmarked (a : Fin n) (ha : a ∈ Aᶜ) :
        (readers a).length ≤ slots.count (a : ℕ) := by
      have h := filteredSlots (a : ℕ) C.gates
      have hle : (C.gates.flatMap Gate.inputs).count (a : ℕ) ≤ slots.count (a : ℕ) := by
        simp only [slots, List.count_cons, beq_iff_eq]
        split <;> omega
      exact (le_trans h hle)
    have r23 (a : Fin n) (ha : a ∈ Aᶜ) :
        (readers a).length = 2 ∨ (readers a).length = 3 := by
      have h := readBounds a (Finset.mem_compl.mp ha)
      dsimp at h
      have h12 : 2 ≤ (readers a).length ∧ (readers a).length ≤ 3 := by
        simpa [readers] using And.intro h.1 h.2.1
      omega
    have internal (i : ℕ) (hi : i ∈ Finset.range C.gates.length) :
        1 ≤ slots.count (n + i) :=
      List.count_pos_iff.mpr
        (hinternal n C fan (by simpa [computes] using minimal) i
          (by simpa [show C.size = C.gates.length from rfl] using Finset.mem_range.mp hi))
    have lowerA := Finset.sum_le_sum marked
    have lowerB' := Finset.sum_le_sum unmarked
    have lowerI := Finset.sum_le_sum internal
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at lowerA lowerI
    have sumr : ∑ v ∈ Aᶜ, (readers v).length = 3 * Aᶜ.card - k := by
      have hite : ∀ v ∈ Aᶜ, (readers v).length =
          if (readers v).length = 2 then 2 else 3 := by
        intro v hv
        rcases r23 v hv with h | h <;> simp [h]
      have hk_le : k ≤ Aᶜ.card := Finset.card_filter_le _ _
      have hcard : (Aᶜ.filter fun v => ¬ (readers v).length = 2).card = Aᶜ.card - k := by
        unfold k
        rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      calc
        ∑ v ∈ Aᶜ, (readers v).length
            = ∑ v ∈ Aᶜ, if (readers v).length = 2 then 2 else 3 :=
              Finset.sum_congr rfl hite
        _ = (∑ v ∈ Aᶜ.filter fun v => (readers v).length = 2, 2)
            + ∑ v ∈ Aᶜ.filter fun v => ¬ (readers v).length = 2, 3 :=
              Finset.sum_ite (fun _ => 2) (fun _ => 3)
        _ = 2 * k + 3 * (Aᶜ.card - k) := by
            simp [Finset.sum_const, smul_eq_mul, k, hcard, Nat.mul_comm]
        _ = 3 * Aᶜ.card - k := by
            omega
    have lowerB : 3 * Aᶜ.card - k ≤ ∑ v ∈ Aᶜ, slots.count (v : ℕ) := by
      have := lowerB'
      have hk_le : k ≤ Aᶜ.card := Finset.card_filter_le _ _
      omega
    have inSum := A.sum_add_sum_compl (fun a => slots.count (a : ℕ))
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => slots.count i)] at inSum
    have countAll := countBound slots (Finset.range (n + C.gates.length))
    change ∑ i ∈ Finset.range (n + C.gates.length), slots.count i ≤ slots.length at countAll
    rw [Finset.sum_range_add] at countAll
    have glen := gateSlotBound C.gates (fun g hg => (fan g hg).2)
    have slotLen : slots.length ≤ 1 + 2 * C.gates.length := by
      have : slots.length = (C.gates.flatMap Gate.inputs).length + 1 := by
        simp [slots, List.length_cons, Nat.add_comm]
      omega
    have dA (a : Fin n) (ha : a ∈ A) : G.degree a = 0 := by
      apply (G.degree_eq_zero a).mpr
      exact fun j h => noMarked a j h ha
    have dB (a : Fin n) (ha : a ∈ Aᶜ) : G.degree a = 3 := by
      rw [← G.ncard_neighborSet]
      exact degree a (Finset.mem_compl.mp ha)
    have degreeSum := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at degreeSum
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degreeSum
    have degEq : 2 * G.edgeFinset.card = 3 * Aᶜ.card := by
      have := degreeSum
      omega
    obtain ⟨i0, j0, hij⟩ := edge
    have hp : 0 < Aᶜ.card :=
      Finset.card_pos.mpr ⟨i0, Finset.mem_compl.mpr (noMarked i0 j0 hij)⟩
    have Icard : I.card ≤ Aᶜ.card := Finset.card_le_card hIsub
    have hk_le : k ≤ Aᶜ.card := Finset.card_filter_le _ _
    have Tpos : 0 < (Aᶜ \ I).card :=
      Finset.card_pos.mpr ⟨
        (if i0 ∈ I then j0 else i0),
        by
          by_cases hiI : i0 ∈ I
          · have hjI : j0 ∉ I := fun h => (hind i0 hiI j0 h) hij
            have hjA : j0 ∈ Aᶜ := Finset.mem_compl.mpr (noMarked j0 i0 hij.symm)
            simp [hiI, Finset.mem_sdiff, hjA, hjI]
          · have hiA : i0 ∈ Aᶜ := Finset.mem_compl.mpr (noMarked i0 j0 hij)
            simp [hiI, Finset.mem_sdiff, hiA]⟩
    have hsz : C.size = C.gates.length := rfl
    have ub' : C.gates.length ≤ A.card + G.edgeFinset.card + (Aᶜ.card - I.card) - 1 := by
      rw [sdiff_card] at ub
      simpa [hsz] using ub
    have slotLower :
        A.card + (3 * Aᶜ.card - k) + C.gates.length ≤ slots.length := by
      have hA := lowerA
      have hB := lowerB
      have hI := lowerI
      have hS := inSum
      have hC := countAll
      omega
    have sizeLower : A.card + 3 * Aᶜ.card - k - 1 ≤ C.gates.length := by
      have h1 := slotLower
      have h2 := slotLen
      omega
    have step : 2 * Aᶜ.card + I.card ≤ G.edgeFinset.card + k := by
      have h1 := sizeLower
      have h2 := ub'
      omega
    have doubled : 4 * Aᶜ.card + 2 * I.card ≤ 2 * G.edgeFinset.card + 2 * k := by
      have := step
      omega
    rw [degEq] at doubled
    omega
  have result := hescape n G A C degree girth noMarked edge fan computesGraph leastGraph
    readBounds allocation
  change ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
    HasCircuitSize n (fun x => graphTarget (Function.update x v false)) s at result
  rwa [sameTarget] at result
