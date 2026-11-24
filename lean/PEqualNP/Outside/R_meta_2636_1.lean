import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Strip the isolated OR inputs. On the remaining cubic graph, deleting a
-- cover vertex removes three edges and one vertex from the cover circuit.
-- Only a least circuit strictly smaller than every cover circuit can escape
-- this argument. A vertex with enough readers already gives the desired cut.
-- If every edge had an endpoint with at least three readers, those endpoints
-- would form a cover whose construction costs at most the least circuit.
-- Hence some edge has at most two readers at each end.
--
-- Padding follows from PadOr.pad_or by moving the chosen input to the last
-- position and back. The cover and reader bounds are L105 and L_meta_1743.
theorem PEqualNP.Outside.R_meta_2636_1
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let readers (z : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains z.val
      G.IsRegularOfDegree 3 →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
      (∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T →
        C.size + 1 < G.edgeFinset.card + T.card) →
      (∀ z : Fin n, (readers z).length ≤ 3 ∧
        ((readers z).length = 3 → ∀ g ∈ readers z, g.op = .or)) →
      (∃ u v : Fin n, G.Adj u v ∧ (readers u).length ≤ 2 ∧ (readers v).length ≤ 2) →
      ∃ (z : Fin n) (t : ℕ), t + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => graphFun G ∅ (Function.update x z false)) t)
    (padding : ∀ (n s : ℕ) (a : Fin (n + 1)) (g : (Fin n → Bool) → Bool),
      (∃ x y, g x ≠ g y) →
      (HasCircuitSize (n + 1) (fun x => x a || g (fun i => x (a.succAbove i))) (s + 1) ↔
        HasCircuitSize n g s))
    (coverUpper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (T : Finset (Fin n)), (∃ i j, G.Adj i j) →
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
      HasCircuitSize n (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
        (G.edgeFinset.card + T.card - 1))
    (readerCut : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (z : Fin n),
      FanInTwo C → circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∃ x y, f (Function.update x z false) ≠ f (Function.update y z false)) →
      (let readers := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains z.val
       4 ≤ readers.length ∨ readers.length = 3 ∧ ∃ g ∈ readers, g.op ≠ .or) →
      ∃ t, t + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x z false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → (∀ (x9 : Fin x1 → Bool), x4 x9 = Bool.true ↔ (∃ x10 ∈ x3, x9 x10 = Bool.true) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x10 → ∃ x12 ∉ x3, ∃ (x13 : ℕ), x13 + (4 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x14 : Fin x1 → Bool) => x4 (Function.update x14 x12 Bool.false)) x13 := by
  classical
  have spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (x : Fin n → Bool) : graphFun G A x = true ↔
        (∃ a ∈ A, x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
    change (decide _ || decide _) = true ↔ _
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  have survives {n : ℕ} (G : SimpleGraph (Fin n)) (edge : ∃ i j, G.Adj i j)
      (degree : ∀ i j, G.Adj i j → (G.neighborSet i).ncard = 3) (z : Fin n) :
      ∃ i j, G.Adj i j ∧ i ≠ z ∧ j ≠ z := by
    obtain ⟨u, v, uv⟩ := edge
    obtain ⟨w, hw, t, hwt⟩ : ∃ w, w ≠ z ∧ ∃ t, G.Adj w t := by
      by_cases huz : u = z
      · exact ⟨v, fun hvz => uv.ne (huz.trans hvz.symm), u, uv.symm⟩
      · exact ⟨u, huz, v, uv⟩
    by_contra none
    have sub : G.neighborSet w ⊆ {z} := by
      intro j hj
      apply Set.mem_singleton_iff.mpr
      by_contra hjz
      exact none ⟨w, j, hj, hw, hjz⟩
    have h := Set.ncard_le_ncard sub
    simp [degree w t hwt] at h
  have varies {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (z : Fin n) (away : ∃ i j, G.Adj i j ∧ i ≠ z ∧ j ≠ z) :
      ∃ x y, graphFun G A (Function.update x z false) ≠
        graphFun G A (Function.update y z false) := by
    obtain ⟨i, j, hij, hi, hj⟩ := away
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    have on := (spec G A (Function.update (fun _ => true) z false)).2
      (Or.inr ⟨i, j, hij, by simp [hi], by simp [hj]⟩)
    rw [on]
    intro h
    rcases (spec G A _).1 h with ⟨a, _, ha⟩ | ⟨p, _, _, hp, _⟩
    · simp at ha
    · simp at hp
  -- Count wire uses, including the output, as in L_meta_1975.
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

  have wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    induction gs₁ generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

  have wiresFrom_length (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [wiresFrom]
    | cons g gs ih =>
      rw [wiresFrom_cons, ih]
      simp
      omega

  have getD_snoc_lt {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    simp [List.getD, List.getElem?_append_left hi]

  have getD_snoc_eq {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    subst hi
    simp [List.getD]

  let OkGate (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  have wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
      (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
      (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
      (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
      (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
      ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
    induction gs generalizing w₁ w₂ with
    | nil => exact ⟨hlen, hagree⟩
    | cons g gs ih =>
      rw [wiresFrom_cons, wiresFrom_cons]
      have hmap : (g.inputs.map fun i => w₁.getD i false) =
          (g.inputs.map fun i => w₂.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact hagree i (hread g List.mem_cons_self i hi)
      rw [hmap]
      apply ih
      · simp [hlen]
      · intro b hb; simp; have := hB b hb; omega
      · intro i hi
        by_cases hlt : i < w₁.length
        · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
          exact hagree i hi
        · by_cases heq : i = w₁.length
          · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]
      · intro g' hg'
        exact hread g' (List.mem_cons_of_mem _ hg')

  have ofFn_getD_lt {α : Type} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
      (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

  let substWire (k a i : ℕ) : ℕ :=
    if i < k then i else if i = k then a else i - 1

  let substGate (k a : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (substWire k a)⟩

  have substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
    ⟨h.1, by simp [substGate]; exact h.2⟩

  let deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
    ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
      substWire (m + j) a C.output⟩

  have deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
      (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
    intro g hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact hok g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))

  have deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
      (deleteGate m C j a).gates.length = C.gates.length - 1 := by
    simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
    omega

  have deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
      (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
      (x : List Bool) (hx : x.length = m) :
      ∀ i < m + C.gates.length, i ≠ m + j →
        ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
          (C.wires x).getD i false := by
    have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
      have h1 := List.take_append_drop j C.gates
      have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [h2] at h1
      simpa only [List.append_assoc, List.singleton_append] using h1.symm
    show ∀ i < m + C.gates.length, i ≠ m + j →
        (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
            (substWire (m + j) 0 i) false =
          (wiresFrom C.gates x).getD i false
    set w₂ := wiresFrom (C.gates.take j) x with hw₂
    set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
    have hw₂_len : w₂.length = m + j := by
      rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
    have hw₁_len : w₁.length = m + j + 1 := by
      rw [hw₁, wiresFrom_length, hw₂_len]; simp
    have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
      rw [List.getElem_drop]
      exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
    have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
        w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
        (∀ g ∈ gs, (m + j) ∉ g.inputs) →
        (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
        ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
          (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
            (wiresFrom gs w₁').getD i false := by
      intro gs
      induction gs with
      | nil =>
        intro w₁' w₂' _ _ _ hag i hi hne
        exact hag i hi hne
      | cons g rest ih =>
        intro w₁' w₂' hlen' hk' hnod hag'
        rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
        have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
            (g.inputs.map fun i => w₁'.getD i false) := by
          simp only [substGate, List.map_map]
          apply List.map_congr_left
          intro i hi
          simp only [Function.comp_apply]
          have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
          by_cases hlt : i < w₁'.length
          · exact hag' i hlt hne
          · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
              unfold substWire; split_ifs <;> omega
            rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
        rw [hmap]
        apply ih _ _ (by simp [hlen']) (by simp; omega)
          (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
        intro i hi hne
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < w₁'.length
        · have hsublt : substWire (m + j) 0 i < w₂'.length := by
            unfold substWire; split_ifs <;> omega
          rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
          exact hag' i hlt hne
        · have hieq : i = w₁'.length := by omega
          have hsubeq : substWire (m + j) 0 i = w₂'.length := by
            unfold substWire; split_ifs <;> omega
          rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
    intro i hi hne
    rw [wiresFrom_append, ← hw₂]
    conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
    have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
      rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
    apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
    intro u hu hune
    have hlt : u < m + j := by omega
    simp only [substWire, hlt, ↓reduceIte]
    rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

  have deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
      (j : ℕ) (hj : j < C.gates.length)
      (hout : C.output ≠ m + j)
      (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
      HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
    refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
      by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
    intro x
    show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
      (C.wires (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < m + C.gates.length
    · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
    · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
        rw [deleteGate_len m C j 0 hj]
        unfold substWire
        split_ifs <;> omega
      have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
          m + (deleteGate m C j 0).gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

  let slots (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

  have gateSlotBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g tail ih =>
      have hg := h g List.mem_cons_self
      have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

  have countBound (xs : List ℕ) (S : Finset ℕ) :
      ∑ i ∈ S, xs.count i ≤ xs.length := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
      by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

  let reads (v : ℕ) (g : Gate) :=
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v

  have filteredSlots (v : ℕ) (gs : List Gate) :
      (gs.filter (reads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons, List.count_append, List.filter_cons]
      split
      next h =>
        have hm : v ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.mp h)
        have hp := List.count_pos_iff.mpr hm
        simp only [List.length_cons]
        omega
      next => omega

  have essentialSlot {n : ℕ} (C : Circuit) (a : Fin n)
      (dep : ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
      (a : ℕ) ∈ slots C := by
    obtain ⟨x, y, hagree, hne⟩ := dep
    by_contra hn
    have hout : C.output ≠ (a : ℕ) := by
      intro he
      exact hn (by simp [slots, he])
    have noRead : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({↑a} : Set ℕ) := by
      intro g hg i hi hia
      have hi' : i = (a : ℕ) := hia
      exact hn (by apply List.mem_cons_of_mem; exact List.mem_flatMap.mpr ⟨g,hg,hi' ▸ hi⟩)
    apply hne
    apply (wiresFrom_agree C.gates ({↑a} : Set ℕ) (List.ofFn x) (List.ofFn y)
      (by simp) (by simp) ?_ noRead).2 C.output hout
    intro i hi
    by_cases h : i < n
    · rw [ofFn_getD_lt _ _ _ h, ofFn_getD_lt _ _ _ h]
      exact hagree _ (fun he => hi (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have internalSlot {n : ℕ} (C : Circuit) (hC : FanInTwo C)
      (hmin : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
      (i : ℕ) (hi : i < C.gates.length) : n+i ∈ slots C := by
    by_contra hn
    have hout : C.output ≠ n+i := fun e => hn (by simp [slots,e])
    have hno : ∀ j, (hj : j < C.gates.length) → i < j → n+i ∉ C.gates[j].inputs := by
      intro j hj _ hm
      exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,List.getElem_mem hj,hm⟩))
    have bad := hmin _ (deleteDeadGate C hC i hi hout hno)
    change C.gates.length ≤ C.gates.length - 1 at bad
    omega
  have pureDrop {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (regular : G.IsRegularOfDegree 3)
      (girth : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
      (edge : ∃ u v, G.Adj u v) (s : ℕ) (hs : HasCircuitSize n (graphFun G ∅) s) :
      ∃ (z : Fin n) (t : ℕ), t + 4 ≤ s ∧
        HasCircuitSize n (fun x => graphFun G ∅ (Function.update x z false)) t := by
    have existsSize : ∃ k, HasCircuitSize n (graphFun G ∅) k := ⟨s, hs⟩
    obtain ⟨C, fan, size, computes⟩ := Nat.find_spec existsSize
    have eqF : circuitFun n C = graphFun G ∅ := funext computes
    have least (k : ℕ) (hk : HasCircuitSize n (graphFun G ∅) k) : C.size ≤ k :=
      size.trans (Nat.find_min' existsSize hk)
    have bound := least s hs
    have away := survives G edge (fun i _ _ => (G.ncard_neighborSet i).trans (regular i))
    by_cases within : ∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧
        G.edgeFinset.card + T.card ≤ C.size + 1
    · obtain ⟨T, cover, budget⟩ := within
      obtain ⟨u, v, uv⟩ := edge
      obtain ⟨z, hz⟩ : T.Nonempty := by
        rcases cover u v uv with hu | hv
        · exact ⟨u, hu⟩
        · exact ⟨v, hv⟩
      let K := G.deleteIncidenceSet z
      obtain ⟨i, j, ij, iz, jz⟩ := away z
      have ijK : K.Adj i j := SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ij, iz, jz⟩
      have pos : 0 < K.edgeFinset.card := Finset.card_pos.mpr ⟨s(i,j), by simpa using ijK⟩
      have ec : K.edgeFinset.card = G.edgeFinset.card - 3 := by
        simpa only [K, regular z] using G.card_edgeFinset_deleteIncidenceSet z
      have tc := Finset.card_erase_add_one hz
      refine ⟨z, K.edgeFinset.card + (T.erase z).card - 1, by omega, ?_⟩
      have coversK (a b : Fin n) (h : K.Adj a b) :
          a ∈ T.erase z ∨ b ∈ T.erase z := by
        obtain ⟨ab, az, bz⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
        exact (cover a b ab).imp (fun ha => Finset.mem_erase.mpr ⟨az, ha⟩)
          (fun hb => Finset.mem_erase.mpr ⟨bz, hb⟩)
      have eqK : (fun x => graphFun G ∅ (Function.update x z false)) =
          fun x => decide (∃ a b, K.Adj a b ∧ x a = true ∧ x b = true) := by
        funext x
        have off (a : Fin n) : Function.update x z false a = true ↔ a ≠ z ∧ x a = true := by
          by_cases h : a = z <;> simp [h]
        rw [Bool.eq_iff_iff, spec, decide_eq_true_eq]
        simp only [Finset.notMem_empty, false_and, exists_false, false_or, off, K,
          SimpleGraph.deleteIncidenceSet_adj]
        constructor
        · rintro ⟨a, b, ab, ⟨az, xa⟩, bz, xb⟩
          exact ⟨a, b, ⟨ab, az, bz⟩, xa, xb⟩
        · rintro ⟨a, b, ⟨ab, az, bz⟩, xa, xb⟩
          exact ⟨a, b, ab, ⟨az, xa⟩, bz, xb⟩
      rw [eqK]
      exact coverUpper n K (T.erase z) ⟨i, j, ijK⟩ coversK
    · have cheap (T : Finset (Fin n)) (hT : CoverPromise.IsVertexCover G T) :
          C.size + 1 < G.edgeFinset.card + T.card :=
        Nat.lt_of_not_ge (fun h => within ⟨T, hT, h⟩)
      let readers (z : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains z.val
      by_cases many : ∃ z : Fin n, 4 ≤ (readers z).length ∨
          (readers z).length = 3 ∧ ∃ g ∈ readers z, g.op ≠ .or
      · obtain ⟨z, hz⟩ := many
        obtain ⟨t, ht, hc⟩ := readerCut n _ C z fan eqF least (varies G ∅ z (away z)) hz
        exact ⟨z, t, ht.trans bound, hc⟩
      · have minimal : IsMinimalCircuit n C := ⟨fan, fun D hD eqD =>
            least D.size ⟨D, hD, le_rfl, congrFun (eqD.trans eqF)⟩⟩
        have sparse (z : Fin n) : (readers z).length ≤ 3 ∧
            ((readers z).length = 3 → ∀ g ∈ readers z, g.op = .or) := by
          constructor
          · by_contra! h
            exact many ⟨z, Or.inl h⟩
          · intro h g hg
            by_contra hop
            exact many ⟨z, Or.inr ⟨h, g, hg, hop⟩⟩
        have adjacentPair : ∃ u v : Fin n, G.Adj u v ∧
            (readers u).length ≤ 2 ∧ (readers v).length ≤ 2 := by
          let T := Finset.univ.filter fun u : Fin n => 3 ≤ (readers u).length
          have memT (u : Fin n) : u ∈ T ↔ 3 ≤ (readers u).length := by simp [T]
          by_contra noPair
          have cover : CoverPromise.IsVertexCover G T := by
            intro u v uv
            by_cases hu : u ∈ T
            · exact Or.inl hu
            right
            by_contra hv
            have hru := mt (memT u).2 hu
            have hrv := mt (memT v).2 hv
            exact noPair ⟨u, v, uv, by omega, by omega⟩
          have cap : G.edgeFinset.card ≤ T.card * 3 := by
            have includes : G.edgeFinset ⊆ T.biUnion (fun v => G.incidenceFinset v) := by
              intro e
              refine Sym2.ind (fun u v => ?_) e
              intro huv
              have uv : G.Adj u v := by simpa using huv
              rcases cover u v uv with hu | hv
              · exact Finset.mem_biUnion.mpr ⟨u, hu,
                  G.mem_incidenceFinset.mpr ((G.mem_incidenceSet u v).2 uv)⟩
              · exact Finset.mem_biUnion.mpr ⟨v, hv, by
                  rw [Sym2.eq_swap]
                  exact G.mem_incidenceFinset.mpr ((G.mem_incidenceSet v u).2 uv.symm)⟩
            exact (Finset.card_le_card includes).trans
              (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ =>
                (G.card_incidenceFinset_eq_degree v).le.trans (regular v).le))
          let cnt (j : ℕ) := (slots C).count j
          have high (v : Fin n) (hv : v ∈ T) : 3 ≤ cnt v.val := by
            have h1 := (memT v).1 hv
            have h2 := filteredSlots v.val C.gates
            change (C.gates.filter (reads v.val)).length ≥ 3 at h1
            simp only [cnt, slots, List.count_cons]
            omega
          have low (v : Fin n) (_ : v ∈ Tᶜ) : 1 ≤ cnt v.val := by
            apply List.count_pos_iff.mpr
            apply essentialSlot C v
            have hpos : 0 < (G.neighborFinset v).card := by
              rw [G.card_neighborFinset_eq_degree, regular v]
              decide
            obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
            have vw : G.Adj v w := by simpa using hw
            let x (i : Fin n) := decide (i = w)
            let y (i : Fin n) := decide (i = v ∨ i = w)
            refine ⟨x, y, fun i hi => by simp [x, y, hi], ?_⟩
            rw [eqF]
            have on := (spec G ∅ y).2 (Or.inr ⟨v, w, vw, by simp [y], by simp [y]⟩)
            rw [on]
            intro hon
            rcases (spec G ∅ x).1 hon with ⟨_, h, _⟩ | ⟨p, q, pq, hp, hq⟩
            · exact Finset.notMem_empty _ h
            · have pw : p = w := of_decide_eq_true hp
              have qw : q = w := of_decide_eq_true hq
              exact pq.ne (pw.trans qw.symm)
          have internal (j : ℕ) (hj : j ∈ Finset.range C.gates.length) : 1 ≤ cnt (n+j) :=
            List.count_pos_iff.mpr (internalSlot C fan (fun k hk => least k (eqF ▸ hk)) j
              (Finset.mem_range.mp hj))
          have hiSum := Finset.sum_le_sum high
          have loSum := Finset.sum_le_sum low
          have gateSum := Finset.sum_le_sum internal
          simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at hiSum loSum gateSum
          have inSum := T.sum_add_sum_compl (fun v => cnt (v : ℕ))
          rw [Fin.sum_univ_eq_sum_range] at inSum
          have allCounts := countBound (slots C) (Finset.range (n+C.gates.length))
          change ∑ i ∈ Finset.range (n+C.gates.length), cnt i ≤ (slots C).length at allCounts
          rw [Finset.sum_range_add] at allCounts
          have countLimit := gateSlotBound C.gates (fun g h => (fan g h).2)
          simp only [slots, List.length_cons] at allCounts
          have card := Finset.card_add_card_compl T
          simp only [Fintype.card_fin] at card
          have handshake := G.sum_degrees_eq_twice_card_edges
          simp only [regular.degree_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul] at handshake
          have strict := cheap T cover
          change C.gates.length + 1 < _ at strict
          omega
        obtain ⟨z, t, ht, hc⟩ :=
          residual n G C regular girth minimal eqF cheap sparse adjacentPair
        exact ⟨z, t, ht.trans bound, hc⟩
  intro n
  induction n with
  | zero =>
    intro G A f _ _ _ edge
    obtain ⟨v, _, _⟩ := edge
    exact Fin.elim0 v
  | succ n ih =>
    intro G A f degree girth marked edge truth s hs
    by_cases markedExists : A.Nonempty
    · obtain ⟨a, ha⟩ := markedExists
      let K := G.comap a.succAbove
      let B := Finset.univ.filter fun i : Fin n => a.succAbove i ∈ A
      have memB (i : Fin n) : i ∈ B ↔ a.succAbove i ∈ A := by simp [B]
      have avoid (u v : Fin (n+1)) (uv : G.Adj u v) : u ≠ a :=
        fun e => marked u v uv (e ▸ ha)
      have degreeK (i : Fin n) (hi : i ∉ B) : (K.neighborSet i).ncard = 3 := by
        have sub : G.neighborSet (a.succAbove i) ⊆ Set.range a.succAbove :=
          fun j hj => Fin.exists_succAbove_eq (avoid j _ (G.adj_symm hj))
        have h := Set.ncard_preimage_of_injective_subset_range Fin.succAbove_right_injective sub
        exact h.trans (degree _ (fun hm => hi ((memB i).2 hm)))
      let inc : K →g G := SimpleGraph.Hom.comap a.succAbove G
      have girthK (i : Fin n) (w : K.Walk i i) (hw : w.IsCycle) : 7 ≤ w.length := by
        have h := girth _ (w.map inc) (hw.map (f := inc) Fin.succAbove_right_injective)
        simpa using h
      have markedK (i j : Fin n) (ij : K.Adj i j) : i ∉ B :=
        fun hi => marked _ _ ij ((memB i).1 hi)
      obtain ⟨u, v, uv⟩ := edge
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (avoid u v uv)
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (avoid v _ uv.symm)
      have edgeK : ∃ i j, K.Adj i j := ⟨i, j, uv⟩
      let g := graphFun K B
      have fpad : f = fun x => x a || g (fun k => x (a.succAbove k)) := by
        funext x
        rw [Bool.eq_iff_iff, truth, Bool.or_eq_true, spec K B]
        constructor
        · rintro (⟨b, hb, xb⟩ | ⟨p, q, pq, xp, xq⟩)
          · rcases Fin.eq_self_or_eq_succAbove a b with rfl | ⟨k, rfl⟩
            · exact Or.inl xb
            · exact Or.inr (Or.inl ⟨k, (memB k).2 hb, xb⟩)
          · obtain ⟨p', rfl⟩ := Fin.exists_succAbove_eq (avoid p q pq)
            obtain ⟨q', rfl⟩ := Fin.exists_succAbove_eq (avoid q _ pq.symm)
            exact Or.inr (Or.inr ⟨p', q', pq, xp, xq⟩)
        · rintro (xa | ⟨k, hk, xk⟩ | ⟨p, q, pq, xp, xq⟩)
          · exact Or.inl ⟨a, ha, xa⟩
          · exact Or.inl ⟨_, (memB k).1 hk, xk⟩
          · exact Or.inr ⟨_, _, pq, xp, xq⟩
      have nc : ∃ x y, g x ≠ g y := by
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        have on := (spec K B (fun _ => true)).2 (Or.inr ⟨i, j, uv, rfl, rfl⟩)
        change graphFun K B _ ≠ graphFun K B _
        rw [on]
        intro h
        rcases (spec K B _).1 h with ⟨_, _, impossible⟩ | ⟨_, _, _, impossible, _⟩ <;> cases impossible
      have relaxed : HasCircuitSize (n+1) f ((s-1)+1) := by
        obtain ⟨D, fan, hsize, eval⟩ := hs
        exact ⟨D, fan, by omega, eval⟩
      rw [fpad] at relaxed
      have smaller := (padding n (s-1) a g nc).1 relaxed
      obtain ⟨z, hz, t, saved, circuit⟩ :=
        ih K B g degreeK girthK markedK edgeK (spec K B) (s-1) smaller
      have away := survives K edgeK (fun p q hpq => degreeK p (markedK p q hpq)) z
      have restored := (padding n t a (fun x => g (Function.update x z false))
        (varies K B z away)).2 circuit
      refine ⟨a.succAbove z, fun h => hz ((memB z).2 h), t+1, by omega, ?_⟩
      have rest (x : Fin (n+1) → Bool) :
          (fun i => Function.update x (a.succAbove z) false (a.succAbove i)) =
            Function.update (fun i => x (a.succAbove i)) z false := by
        funext i
        by_cases h : i = z
        · subst i
          simp
        · simp [Function.update_of_ne h, Function.update_of_ne (Fin.succAbove_right_injective.ne h)]
      simpa only [fpad, Function.update_of_ne (Fin.succAbove_ne a z).symm, rest] using restored
    · have empty := Finset.not_nonempty_iff_eq_empty.mp markedExists
      subst A
      have eqF : f = graphFun G ∅ := by
        funext x
        exact Bool.eq_iff_iff.mpr ((truth x).trans (spec G ∅ x).symm)
      subst f
      have regular : G.IsRegularOfDegree 3 := fun i =>
        (G.ncard_neighborSet i).symm.trans (degree i (by simp))
      obtain ⟨z, t, ht, hc⟩ := pureDrop G regular girth edge s hs
      exact ⟨z, by simp, t, ht, hc⟩
