import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The bipartite side is proved inside this theorem, using effective-wire counting
-- and the star-cover circuit after deleting one covered cubic vertex.
-- The gate-deletion argument follows accepted L-meta-1975 and L-meta-522.
-- The star builder follows L-meta-1975, which credits L-meta-173.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2631_761
    (bipartite : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      G.Colorable 2 →
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = graphFun G A →
      (∀ s, HasCircuitSize n (graphFun G A) s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) →
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
        HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) s)
    (nonbipartite : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let r (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      ¬G.Colorable 2 →
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (r v).length ∧ (r v).length ≤ 3 ∧
        ((r v).length = 3 → ∀ g ∈ r v, g.op = .or)) →
      (∃ v ∉ A, (r v).length = 2 ∧ ∃ g ∈ r v, g.op = .and) →
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  let M_wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have M_wiresFrom_nil (w : List Bool) : M_wiresFrom [] w = w := rfl

  have M_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      M_wiresFrom (g :: gs) w =
        M_wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have M_wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
      M_wiresFrom (gs₁ ++ gs₂) w = M_wiresFrom gs₂ (M_wiresFrom gs₁ w) := by
    induction gs₁ generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.cons_append, M_wiresFrom_cons, ih]

  have M_wiresFrom_length (gs : List Gate) (w : List Bool) :
      (M_wiresFrom gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [M_wiresFrom]
    | cons g gs ih =>
      rw [M_wiresFrom_cons, ih]
      simp
      omega

  have M_getD_snoc_lt {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    simp [List.getD, List.getElem?_append_left hi]

  have M_getD_snoc_eq {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    subst hi
    simp [List.getD]

  let M_OkGate (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  have M_wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
      (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
      (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
      (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
      (M_wiresFrom gs w₁).length = (M_wiresFrom gs w₂).length ∧
      ∀ i ∉ B, (M_wiresFrom gs w₁).getD i false = (M_wiresFrom gs w₂).getD i false := by
    induction gs generalizing w₁ w₂ with
    | nil => exact ⟨hlen, hagree⟩
    | cons g gs ih =>
      rw [M_wiresFrom_cons, M_wiresFrom_cons]
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
        · rw [M_getD_snoc_lt _ _ _ _ hlt, M_getD_snoc_lt _ _ _ _ (by omega)]
          exact hagree i hi
        · by_cases heq : i = w₁.length
          · rw [M_getD_snoc_eq _ _ _ _ heq, M_getD_snoc_eq _ _ _ _ (by omega)]
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]
      · intro g' hg'
        exact hread g' (List.mem_cons_of_mem _ hg')

  have M_ofFn_getD_lt {α : Type} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
      (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

  let M_substWire (k a i : ℕ) : ℕ :=
    if i < k then i else if i = k then a else i - 1

  let M_substGate (k a : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (M_substWire k a)⟩

  have M_substGate_ok (k a : ℕ) (g : Gate) (h : M_OkGate g) : M_OkGate (M_substGate k a g) :=
    ⟨h.1, by simp [M_substGate]; exact h.2⟩

  let M_deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
    ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (M_substGate (m + j) a),
      M_substWire (m + j) a C.output⟩

  have M_deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
      (hok : ∀ g ∈ C.gates, M_OkGate g) : ∀ g ∈ (M_deleteGate m C j a).gates, M_OkGate g := by
    intro g hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact hok g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      exact M_substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))

  have M_deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
      (M_deleteGate m C j a).gates.length = C.gates.length - 1 := by
    simp only [M_deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
    omega

  have M_deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
      (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
      (x : List Bool) (hx : x.length = m) :
      ∀ i < m + C.gates.length, i ≠ m + j →
        ((M_deleteGate m C j 0).wires x).getD (M_substWire (m + j) 0 i) false =
          (C.wires x).getD i false := by
    have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
      have h1 := List.take_append_drop j C.gates
      have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [h2] at h1
      simpa only [List.append_assoc, List.singleton_append] using h1.symm
    show ∀ i < m + C.gates.length, i ≠ m + j →
        (M_wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (M_substGate (m + j) 0)) x).getD
            (M_substWire (m + j) 0 i) false =
          (M_wiresFrom C.gates x).getD i false
    set w₂ := M_wiresFrom (C.gates.take j) x with hw₂
    set w₁ := M_wiresFrom [C.gates[j]] w₂ with hw₁
    have hw₂_len : w₂.length = m + j := by
      rw [hw₂, M_wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
    have hw₁_len : w₁.length = m + j + 1 := by
      rw [hw₁, M_wiresFrom_length, hw₂_len]; simp
    have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
      rw [List.getElem_drop]
      exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
    have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
        w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
        (∀ g ∈ gs, (m + j) ∉ g.inputs) →
        (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (M_substWire (m + j) 0 i) false = w₁'.getD i false) →
        ∀ i < (M_wiresFrom gs w₁').length, i ≠ m + j →
          (M_wiresFrom (gs.map (M_substGate (m + j) 0)) w₂').getD (M_substWire (m + j) 0 i) false =
            (M_wiresFrom gs w₁').getD i false := by
      intro gs
      induction gs with
      | nil =>
        intro w₁' w₂' _ _ _ hag i hi hne
        exact hag i hi hne
      | cons g rest ih =>
        intro w₁' w₂' hlen' hk' hnod hag'
        rw [List.map_cons, M_wiresFrom_cons, M_wiresFrom_cons]
        have hmap : ((M_substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
            (g.inputs.map fun i => w₁'.getD i false) := by
          simp only [M_substGate, List.map_map]
          apply List.map_congr_left
          intro i hi
          simp only [Function.comp_apply]
          have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
          by_cases hlt : i < w₁'.length
          · exact hag' i hlt hne
          · have hge : w₂'.length ≤ M_substWire (m + j) 0 i := by
              unfold M_substWire; split_ifs <;> omega
            rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
        rw [hmap]
        apply ih _ _ (by simp [hlen']) (by simp; omega)
          (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
        intro i hi hne
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < w₁'.length
        · have hsublt : M_substWire (m + j) 0 i < w₂'.length := by
            unfold M_substWire; split_ifs <;> omega
          rw [M_getD_snoc_lt _ _ _ _ hsublt, M_getD_snoc_lt _ _ _ _ hlt]
          exact hag' i hlt hne
        · have hieq : i = w₁'.length := by omega
          have hsubeq : M_substWire (m + j) 0 i = w₂'.length := by
            unfold M_substWire; split_ifs <;> omega
          rw [M_getD_snoc_eq _ _ _ _ hsubeq, M_getD_snoc_eq _ _ _ _ hieq]
    intro i hi hne
    rw [M_wiresFrom_append, ← hw₂]
    conv_rhs => rw [hsplit, M_wiresFrom_append, M_wiresFrom_append, ← hw₂, ← hw₁]
    have hlen_rhs : (M_wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
      rw [M_wiresFrom_length, hw₁_len, List.length_drop]; omega
    apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
    intro u hu hune
    have hlt : u < m + j := by omega
    simp only [M_substWire, hlt, ↓reduceIte]
    rw [hw₁, M_wiresFrom_cons, M_wiresFrom_nil, M_getD_snoc_lt _ _ _ _ (by omega)]

  have M_deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, M_OkGate g)
      (j : ℕ) (hj : j < C.gates.length)
      (hout : C.output ≠ m + j)
      (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
      HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
    refine ⟨M_deleteGate m C j 0, M_deleteGate_ok m C j 0 hok,
      by show (M_deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [M_deleteGate_len m C j 0 hj], ?_⟩
    intro x
    show ((M_deleteGate m C j 0).wires (List.ofFn x)).getD (M_substWire (m + j) 0 C.output) false =
      (C.wires (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < m + C.gates.length
    · exact M_deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
    · have hge1 : (M_deleteGate m C j 0).gates.length + m ≤ M_substWire (m + j) 0 C.output := by
        rw [M_deleteGate_len m C j 0 hj]
        unfold M_substWire
        split_ifs <;> omega
      have h1 : ((M_deleteGate m C j 0).wires (List.ofFn x)).length =
          m + (M_deleteGate m C j 0).gates.length := by
        show (M_wiresFrom _ _).length = _; rw [M_wiresFrom_length]; simp
      have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
        show (M_wiresFrom _ _).length = _; rw [M_wiresFrom_length]; simp
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]


  -- Count the input M_slots of all gates, with one additional slot for the output.

  let M_slots (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

  have M_gateSlotBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g tail ih =>
      have hg := h g List.mem_cons_self
      have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

  have M_countBound (xs : List ℕ) (S : Finset ℕ) :
      ∑ i ∈ S, xs.count i ≤ xs.length := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
      by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

  let M_reads (v : ℕ) (g : Gate) :=
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v

  have M_filteredSlots (v : ℕ) (gs : List Gate) :
      (gs.filter (M_reads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
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

  have M_essentialSlot {n : ℕ} (C : Circuit) (a : Fin n)
      (dep : ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
      (a : ℕ) ∈ M_slots C := by
    obtain ⟨x, y, hagree, hne⟩ := dep
    by_contra hn
    have hout : C.output ≠ (a : ℕ) := by
      intro he
      exact hn (by simp [M_slots, he])
    have noRead : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({↑a} : Set ℕ) := by
      intro g hg i hi hia
      have hi' : i = (a : ℕ) := hia
      exact hn (by apply List.mem_cons_of_mem; exact List.mem_flatMap.mpr ⟨g,hg,hi' ▸ hi⟩)
    apply hne
    apply (M_wiresFrom_agree C.gates ({↑a} : Set ℕ) (List.ofFn x) (List.ofFn y)
      (by simp) (by simp) ?_ noRead).2 C.output hout
    intro i hi
    by_cases h : i < n
    · rw [M_ofFn_getD_lt _ _ _ h, M_ofFn_getD_lt _ _ _ h]
      exact hagree _ (fun he => hi (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have M_internalSlot {n : ℕ} (C : Circuit) (hC : FanInTwo C)
      (hmin : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
      (i : ℕ) (hi : i < C.gates.length) : n+i ∈ M_slots C := by
    by_contra hn
    have hout : C.output ≠ n+i := fun e => hn (by simp [M_slots,e])
    have hno : ∀ j, (hj : j < C.gates.length) → i < j → n+i ∉ C.gates[j].inputs := by
      intro j hj _ hm
      exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,List.getElem_mem hj,hm⟩))
    have bad := hmin _ (M_deleteDeadGate C hC i hi hout hno)
    change C.gates.length ≤ C.gates.length - 1 at bad
    omega

  let M_eff (g : Gate) : List ℕ := g.inputs.take (bif g.op.eval [false] then 1 else 2)

  let M_trimGate (g : Gate) : Gate := ⟨g.op, M_eff g⟩

  let M_trim (C : Circuit) : Circuit := ⟨C.gates.map M_trimGate, C.output⟩

  have M_trimGate_eval (g : Gate) (hg : M_OkGate g) (w : List Bool) :
      (M_trimGate g).op.eval ((M_trimGate g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
    rcases g with ⟨op,inputs⟩
    rcases hg with ⟨hop,hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · change ((inputs.take 2).map fun i => w.getD i false).all id =
        (inputs.map fun i => w.getD i false).all id
      rw [List.take_of_length_le hlen]
    · change ((inputs.take 2).map fun i => w.getD i false).any id =
        (inputs.map fun i => w.getD i false).any id
      rw [List.take_of_length_le hlen]
    · cases inputs <;> rfl

  have M_trim_wires (gs : List Gate) (hg : ∀ g ∈ gs, M_OkGate g) (w : List Bool) :
      M_wiresFrom (gs.map M_trimGate) w = M_wiresFrom gs w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.map_cons, M_wiresFrom_cons, M_wiresFrom_cons, M_trimGate_eval g (hg g List.mem_cons_self)]
      exact ih (fun g h => hg g (List.mem_cons_of_mem _ h)) _

  have M_trim_fan (C : Circuit) (hc : FanInTwo C) : FanInTwo (M_trim C) := by
    intro g hg
    change g ∈ C.gates.map M_trimGate at hg
    obtain ⟨g0,hg0,heq⟩ := List.mem_map.mp hg
    subst g
    refine ⟨(hc g0 hg0).1, ?_⟩
    change (M_eff g0).length ≤ 2
    exact (by simp only [M_eff, List.length_take]; omega : (M_eff g0).length ≤ g0.inputs.length).trans (hc g0 hg0).2

  have M_trim_fun (n : ℕ) (C : Circuit) (hc : FanInTwo C) :
      circuitFun n (M_trim C) = circuitFun n C := by
    funext x
    change (M_wiresFrom (C.gates.map M_trimGate) (List.ofFn x)).getD C.output false = _
    rw [M_trim_wires _ hc]
    rfl

  have M_eff_internal (n : ℕ) (C : Circuit) (hc : FanInTwo C)
      (hmin : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
      (i : ℕ) (hi : i < C.gates.length) :
      n+i ∈ C.output :: C.gates.flatMap M_eff := by
    have hm : ∀ s, HasCircuitSize n (circuitFun n (M_trim C)) s → (M_trim C).size ≤ s := by
      intro s hs
      rw [M_trim_fun n C hc] at hs
      change (M_trim C).gates.length ≤ s
      have h : C.gates.length ≤ s := hmin s hs
      simpa [M_trim] using h
    have h := M_internalSlot (M_trim C) (M_trim_fan C hc) hm i (by simpa [M_trim] using hi)
    simpa [M_slots, M_trim, List.flatMap_map, Function.comp_def, M_trimGate] using h

  have M_eff_slot_bound (gs : List Gate) :
      (gs.flatMap M_eff).length + (gs.filter fun g => decide (g.op = .not)).length ≤ 2*gs.length := by
    classical
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have h : (M_eff g).length + (if g.op = .not then 1 else 0) ≤ 2 := by
        by_cases hn : g.op = .not
        · have he : (M_eff g).length ≤ 1 := by
            unfold M_eff
            rw [hn]
            exact List.length_take_le 1 _
          simp only [hn, ite_true]
          omega
        · have he : (M_eff g).length ≤ 2 := by
            unfold M_eff
            cases g.op.eval [false]
            · exact List.length_take_le 2 _
            · exact (List.length_take_le 1 _).trans (by decide)
          simp only [hn, ite_false, add_zero]
          exact he
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.filter_cons]
      by_cases hn : g.op = .not
      · simp [hn] at h ih ⊢
        omega
      · simp [hn] at h ih ⊢
        omega

  have M_eff_filtered (v : ℕ) (gs : List Gate) :
      (gs.filter fun g => (M_eff g).contains v).length ≤ (gs.flatMap M_eff).count v := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons, List.count_append, List.filter_cons]
      split
      next h =>
        have hp := List.count_pos_iff.mpr (List.contains_iff_mem.mp h)
        simp only [List.length_cons]
        omega
      next => omega

  -- No liveness hypothesis remains: least size implies each effective internal wire is used.

  have M_minimal_wiring_bound (n : ℕ) (C : Circuit) (hc : FanInTwo C)
      (hmin : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s) :
      (∑ v : Fin n, (C.gates.filter fun g => (M_eff g).contains v.val).length) +
        (C.gates.filter fun g => decide (g.op = .not)).length ≤ C.size+1 := by
    classical
    let xs := C.output :: C.gates.flatMap M_eff
    have hi (v : Fin n) : (C.gates.filter fun g => (M_eff g).contains v.val).length ≤ xs.count v.val := by
      have h := M_eff_filtered v.val C.gates
      simp only [xs, List.count_cons]
      omega
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hi v)
    have hgate (i : ℕ) (hi : i ∈ Finset.range C.gates.length) : 1 ≤ xs.count (n+i) :=
      List.count_pos_iff.mpr (M_eff_internal n C hc hmin i (Finset.mem_range.mp hi))
    have hg := Finset.sum_le_sum hgate
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at hg
    have hall := M_countBound xs (Finset.range (n+C.gates.length))
    rw [Finset.sum_range_add] at hall
    have heq : (∑ v : Fin n, xs.count v.val) = ∑ i ∈ Finset.range n, xs.count i :=
      Fin.sum_univ_eq_sum_range (fun i => xs.count i) n
    rw [heq] at hsum
    have capacity := M_eff_slot_bound C.gates
    simp only [xs, List.length_cons] at hall
    change _ ≤ C.gates.length+1
    dsimp only [xs] at hsum hg
    omega



  -- The marked inputs contribute one required effective slot each.

  have M_marked_wiring_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit) (hc : FanInTwo C)
      (hf : circuitFun n C = NestedCover.graphFun G A)
      (hmin : ∀ s, HasCircuitSize n (NestedCover.graphFun G A) s → C.size ≤ s) :
      A.card + (∑ v ∈ Aᶜ, (C.gates.filter fun g => (M_eff g).contains v.val).length) +
        (C.gates.filter fun g => decide (g.op = .not)).length ≤ C.size+1 := by
    classical
    let xs := C.output :: C.gates.flatMap M_eff
    have hi (v : Fin n) : (C.gates.filter fun g => (M_eff g).contains v.val).length ≤ xs.count v.val := by
      have h := M_eff_filtered v.val C.gates
      simp only [xs, List.count_cons]
      omega
    have marked (a : Fin n) (ha : a ∈ A) : 1 ≤ xs.count a.val := by
      apply List.count_pos_iff.mpr
      have hs : a.val ∈ M_slots (M_trim C) := by
        apply M_essentialSlot
        let z : Fin n → Bool := fun _ => false
        let y : Fin n → Bool := fun i => decide (i = a)
        refine ⟨z, y, fun i hi => by simp [z,y,hi], ?_⟩
        rw [M_trim_fun n C hc, hf]
        have hz : NestedCover.graphFun G A z = false := by
          change (decide (∃ a ∈ A, z a = true) ||
            decide (∃ u v, G.Adj u v ∧ z u = true ∧ z v = true)) = false
          simp [z]
        have hy : NestedCover.graphFun G A y = true := by
          change (decide (∃ a ∈ A, y a = true) ||
            decide (∃ u v, G.Adj u v ∧ y u = true ∧ y v = true)) = true
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inl ⟨a,ha,by simp [y]⟩
        rw [hz,hy]
        decide
      simpa [M_slots, M_trim, List.flatMap_map, Function.comp_def, M_trimGate, xs] using hs
    have hA := Finset.sum_le_sum marked
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hA
    have hB := Finset.sum_le_sum (s := Aᶜ) (fun v _ => hi v)
    have hsum := A.sum_add_sum_compl (fun v => xs.count v.val)
    have heq : (∑ v : Fin n, xs.count v.val) = ∑ i ∈ Finset.range n, xs.count i :=
      Fin.sum_univ_eq_sum_range (fun i => xs.count i) n
    rw [heq] at hsum
    have hgate (i : ℕ) (hi : i ∈ Finset.range C.gates.length) : 1 ≤ xs.count (n+i) :=
      List.count_pos_iff.mpr (M_eff_internal n C hc (by
        intro s hs
        apply hmin s
        rw [← hf]
        exact hs) i (Finset.mem_range.mp hi))
    have hg := Finset.sum_le_sum hgate
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at hg
    have hall := M_countBound xs (Finset.range (n+C.gates.length))
    rw [Finset.sum_range_add] at hall
    have capacity := M_eff_slot_bound C.gates
    simp only [xs, List.length_cons] at hall
    change _ ≤ C.gates.length+1
    dsimp only [xs] at hA hB hsum hg
    omega

  let B_wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have B_wires_eq (C : Circuit) (x : List Bool) : C.wires x = B_wiresFrom C.gates x := rfl

  have B_wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
      B_wiresFrom (gs ++ gs') w = B_wiresFrom gs' (B_wiresFrom gs w) := by
    simp [B_wiresFrom, List.foldl_append]

  have B_wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, B_wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [B_wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : B_wiresFrom (g :: gs) w
          = B_wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp

  have B_length_wiresFrom (gs : List Gate) (w : List Bool) :
      (B_wiresFrom gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := B_wiresFrom_prefix gs w
    rw [ht]; simp [hl]

  have B_getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (B_wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := B_wiresFrom_prefix gs w
    rw [ht, List.getD_append _ _ _ _ h]

  let B_Ok (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  have B_getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
    simp

  have B_getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
      (List.ofFn x).getD (i : ℕ) false = x i := by simp

  let B_Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
    ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, B_Ok g) ∧ gs.length ≤ s ∧
      out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
        (B_wiresFrom gs w).getD out false = F (fun i => w.getD i false)

  have B_bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : B_Bld n F s) (hs : s ≤ s') :
      B_Bld n F s' := by
    intro m hm
    obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
    exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

  have B_bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : B_Bld n F s)
      (e : ∀ x, F x = H x) : B_Bld n H s := by
    intro m hm
    obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
    exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

  have B_bld_var {n : ℕ} (i : Fin n) : B_Bld n (fun x => x i) 0 := by
    intro m hm
    refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
    intro w _
    simp [B_wiresFrom]

  have B_bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
      {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : B_Bld n F s1) (h2 : B_Bld n H s2) :
      B_Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
    intro m hm
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
    obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
    refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | hg
      · exact ok1 g hg
      · exact ok2 g hg
      · subst hg; rcases hop with h | h <;> simp [B_Ok, h]
    · simp; omega
    · simp; omega
    · intro w hw
      rw [B_wiresFrom_append, B_wiresFrom_append]
      set v := B_wiresFrom gs1 w with hv
      have lv : v.length = m + gs1.length := by rw [hv, B_length_wiresFrom, hw]
      set u := B_wiresFrom gs2 v with hu
      have lu : u.length = m + gs1.length + gs2.length := by rw [hu, B_length_wiresFrom, lv]
      have step : B_wiresFrom [⟨op, [o1, o2]⟩] u
          = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
      rw [step, ← lu, B_getD_snoc_eq]
      simp only [List.map_cons, List.map_nil, hc]
      have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
        rw [hu, B_getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
      have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
        rw [hu, ev2 v lv]
        congr 1
        funext i
        rw [hv, B_getD_wiresFrom _ _ _ (by have := i.2; omega)]
      rw [e1, e2]

  have B_bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : B_Bld n F s1)
      (h2 : B_Bld n H s2) : B_Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
    B_bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; cases a <;> cases b <;> rfl) h1 h2

  have B_bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : B_Bld n F s1)
      (h2 : B_Bld n H s2) : B_Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
    B_bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; cases a <;> cases b <;> rfl) h1 h2

  have B_bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : B_Bld n F s) :
      HasCircuitSize n F s := by
    obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
    refine ⟨⟨gs, out⟩, ok, len, ?_⟩
    intro x
    have e := ev (List.ofFn x) (by simp)
    change (B_wiresFrom gs (List.ofFn x)).getD out false = F x
    rw [e]
    congr 1
    funext i
    exact B_getD_ofFn x i

  have B_bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
      B_Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
    induction vs with
    | nil =>
      intro v
      exact B_bld_congr (n := n) (F := fun x => x v)
        (H := fun x => (v :: []).any fun j => x j) (s := 0)
        (B_bld_var v) (by intro x; simp)
    | cons w ws ih =>
      intro v
      have h := B_bld_or (n := n) (F := fun x => x v)
        (H := fun x => (w :: ws).any fun j => x j) (s1 := 0) (s2 := ws.length)
        (B_bld_var v) (ih w)
      refine B_bld_congr (n := n) (F := fun x => x v || (w :: ws).any fun j => x j)
        (H := fun x => (v :: w :: ws).any fun j => x j) (s := (w :: ws).length)
        (B_bld_mono (n := n) (F := fun x => x v || (w :: ws).any fun j => x j)
          (s := 0 + ws.length + 1) (s' := (w :: ws).length) h (by simp)) ?_
      intro x
      simp

  have B_bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
      B_Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
    obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
      cases h : S.toList with
      | nil => simp at h; exact absurd h hS.ne_empty
      | cons v vs => exact ⟨v, vs, rfl⟩
    have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
    refine B_bld_congr (n := n) (F := fun x => (v :: vs).any fun j => x j)
      (H := fun x => decide (∃ v ∈ S, x v = true)) (s := S.card - 1)
      (B_bld_mono (n := n) (F := fun x => (v :: vs).any fun j => x j)
        (s := vs.length) (s' := S.card - 1) (B_bld_anyList vs v) (by omega)) ?_
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
    simp

  have B_bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
      (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
      B_Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
    induction T using Finset.induction_on with
    | empty =>
      intro E hE hc
      obtain ⟨e, he⟩ := hE
      obtain ⟨t, ht, _⟩ := hc e he
      simp at ht
    | @insert t T0 htT ih =>
      intro E hE hc
      set E1 := E.filter (fun e => t ∈ e) with hE1
      set E2 := E.filter (fun e => t ∉ e) with hE2
      have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
      have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
      have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
        intro e he
        rw [hE2, Finset.mem_filter] at he
        obtain ⟨t', ht', hte⟩ := hc e he.1
        rcases Finset.mem_insert.1 ht' with h | h
        · subst h; exact absurd hte he.2
        · exact ⟨t', h, hte⟩

      set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
      have hSc : S.card ≤ E1.card := by
        refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
        · intro v hv
          simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
          exact hv
        · intro a _ b _ hab
          exact Sym2.congr_right.1 hab
      have star : E1.Nonempty → B_Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
          E1.card := by
        intro h1
        have hSne : S.Nonempty := by
          obtain ⟨e, he⟩ := h1
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
          exact ⟨b, by simp [hS, ← hb, he]⟩
        have h := B_bld_and (n := n) (F := fun x => x t)
          (H := fun x => decide (∃ v ∈ S, x v = true)) (s1 := 0) (s2 := S.card - 1)
          (B_bld_var t) (B_bld_anyFinset S hSne)
        have hpos := hSne.card_pos
        refine B_bld_congr (n := n) (F := fun x => x t && decide (∃ v ∈ S, x v = true))
          (H := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true)) (s := E1.card)
          (B_bld_mono (n := n) (F := fun x => x t && decide (∃ v ∈ S, x v = true))
            (s := 0 + (S.card - 1) + 1) (s' := E1.card) h (by omega)) ?_
        intro x
        rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨ht, v, hv, hxv⟩
          refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
          intro u hu
          rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
        · rintro ⟨e, he, hall⟩
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
          subst hb
          exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
            hall b (Sym2.mem_mk_right _ _)⟩
      have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
          = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
        intro x
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
        constructor
        · rintro ⟨e, he, h⟩
          by_cases hte : t ∈ e
          · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
          · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
        · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
      rw [hcard]
      by_cases h1 : E1.Nonempty
      · by_cases h2 : E2.Nonempty
        · have h := B_bld_or (n := n)
            (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
            (H := fun x => decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
            (s1 := E1.card) (s2 := E2.card + T0.card - 1) (star h1) (ih E2 h2 c2)
          have hp := h2.card_pos
          refine B_bld_congr (n := n)
            (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) ||
              decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
            (H := fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true))
            (s := E.card + (T0.card + 1) - 1)
            (B_bld_mono (n := n)
              (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) ||
                decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
              (s := E1.card + (E2.card + T0.card - 1) + 1)
              (s' := E.card + (T0.card + 1) - 1) h (by omega)) ?_
          intro x
          rw [key]
        · rw [Finset.not_nonempty_iff_eq_empty] at h2
          refine B_bld_congr (n := n)
            (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
            (H := fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true))
            (s := E.card + (T0.card + 1) - 1)
            (B_bld_mono (n := n) (F := fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
              (s := E1.card) (s' := E.card + (T0.card + 1) - 1)
              (star h1) (by omega)) ?_
          intro x
          rw [key, h2]
          simp
      · rw [Finset.not_nonempty_iff_eq_empty] at h1
        have h2 : E2.Nonempty := by
          by_contra h2
          rw [Finset.not_nonempty_iff_eq_empty] at h2
          have := hE.card_pos
          rw [h1, h2] at hsplit
          simp at hsplit
          omega
        refine B_bld_congr (n := n)
          (F := fun x => decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
          (H := fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true))
          (s := E.card + (T0.card + 1) - 1)
          (B_bld_mono (n := n) (F := fun x => decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
            (s := E2.card + T0.card - 1) (s' := E.card + (T0.card + 1) - 1)
            (ih E2 h2 c2) (by omega)) ?_
        intro x
        rw [key, h1]
        simp

  have B_edgeBuilder : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → B_Bld n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
    intro n G _ T hE hc
    obtain ⟨i0, j0, h0⟩ := hE
    have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
    have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases hc a b he with h | h
      · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
      · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
    refine B_bld_congr (n := n)
      (F := fun x => decide (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true))
      (H := fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
      (s := G.edgeFinset.card + T.card - 1) (B_bld_edges n T G.edgeFinset hne cov) ?_
    intro x
    rw [decide_eq_decide]
    constructor
    · rintro ⟨e, he, h⟩
      revert he h
      refine Sym2.ind (fun a b => ?_) e
      intro he h
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨s(i, j), by simpa using hij, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

  have C_markedCoverUpper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n))
      (hT : G.IsVertexCover (T : Set (Fin n))) (hE : ∃ a b, G.Adj a b) :
      HasCircuitSize n (graphFun G A) (A.card + G.edgeFinset.card + T.card - 1) := by
    classical
    have b := B_edgeBuilder n G T hE (fun a b h => hT h)
    obtain ⟨a,b',hab⟩ := hE
    have epos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(a,b'),by simpa using hab⟩
    apply B_bld_hasCircuitSize (n := n) (F := graphFun G A)
      (s := A.card + G.edgeFinset.card + T.card - 1)
    by_cases ha : A.Nonempty
    · have ap := ha.card_pos
      have h := B_bld_or (n := n) (F := fun x => decide (∃ v ∈ A, x v = true))
        (H := fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
        (s1 := A.card - 1) (s2 := G.edgeFinset.card + T.card - 1) (B_bld_anyFinset A ha) b
      apply B_bld_congr (n := n)
        (F := fun x => decide (∃ v ∈ A, x v = true) ||
          decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
        (H := graphFun G A) (s := A.card + G.edgeFinset.card + T.card - 1)
        (B_bld_mono (n := n)
          (F := fun x => decide (∃ v ∈ A, x v = true) ||
            decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
          (s := (A.card - 1) + (G.edgeFinset.card + T.card - 1) + 1)
          (s' := A.card + G.edgeFinset.card + T.card - 1) h (by omega))
      intro x
      rfl
    · have he := Finset.not_nonempty_iff_eq_empty.mp ha
      apply B_bld_congr (n := n)
        (F := fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
        (H := graphFun G A) (s := A.card + G.edgeFinset.card + T.card - 1)
        (B_bld_mono (n := n)
          (F := fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
          (s := G.edgeFinset.card + T.card - 1)
          (s' := A.card + G.edgeFinset.card + T.card - 1) b (by simp [he]))
      intro x
      change decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) =
        (decide (∃ a ∈ A, x a = true) || decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
      simp [he]


  have C_erase_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) (v : Fin n)
      (hT : G.IsVertexCover (T : Set (Fin n))) :
      (G.deleteIncidenceSet v).IsVertexCover ((T.erase v : Finset (Fin n)) : Set (Fin n)) := by
    intro a b hab
    rw [SimpleGraph.deleteIncidenceSet_adj] at hab
    rcases hT hab.1 with ha | hb
    · left
      simp only [Finset.mem_coe, Finset.mem_erase]
      exact ⟨hab.2.1,ha⟩
    · right
      simp only [Finset.mem_coe, Finset.mem_erase]
      exact ⟨hab.2.2,hb⟩

  have C_restrict_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (v : Fin n) (hv : v ∉ A)
      (x : Fin n → Bool) :
      graphFun G A (Function.update x v false) = graphFun (G.deleteIncidenceSet v) A x := by
    change (decide (∃ a ∈ A, Function.update x v false a = true) ||
        decide (∃ a b, G.Adj a b ∧ Function.update x v false a = true ∧
          Function.update x v false b = true)) =
      (decide (∃ a ∈ A, x a = true) ||
        decide (∃ a b, (G.deleteIncidenceSet v).Adj a b ∧ x a = true ∧ x b = true))
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨a,ha,hx⟩ | ⟨a,b,hab,ha,hb⟩)
      · left
        have hav : a ≠ v := by intro h; subst a; exact hv ha
        exact ⟨a,ha,by simpa [Function.update_of_ne hav] using hx⟩
      · right
        have hav : a ≠ v := by intro h; subst a; simp at ha
        have hbv : b ≠ v := by intro h; subst b; simp at hb
        exact ⟨a,b,by simpa only [SimpleGraph.deleteIncidenceSet_adj] using
          (show G.Adj a b ∧ a ≠ v ∧ b ≠ v from ⟨hab,hav,hbv⟩),
          by simpa [Function.update_of_ne hav] using ha,
          by simpa [Function.update_of_ne hbv] using hb⟩
    · rintro (⟨a,ha,hx⟩ | ⟨a,b,hab,ha,hb⟩)
      · left
        have hav : a ≠ v := by intro h; subst a; exact hv ha
        exact ⟨a,ha,by simpa [Function.update_of_ne hav] using hx⟩
      · right
        rw [SimpleGraph.deleteIncidenceSet_adj] at hab
        exact ⟨a,b,hab.1,by simpa [Function.update_of_ne hab.2.1] using ha,
          by simpa [Function.update_of_ne hab.2.2] using hb⟩

  -- This isolates the remaining circuit lower bound: the ordinary star-cover
  -- upper bound already gives a four-gate saving at every covered cubic vertex
  -- whenever the original circuit reaches that upper bound.

  have C_saving_at_cover_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)) (v : Fin n) (s : ℕ)
      (hT : G.IsVertexCover (T : Set (Fin n))) (hvt : v ∈ T) (hva : v ∉ A)
      (hdeg : 3 ≤ G.degree v)
      (hne : ∃ a b, (G.deleteIncidenceSet v).Adj a b)
      (hsize : A.card + G.edgeFinset.card + T.card ≤ s + 1) :
      ∃ t, t + 4 ≤ s ∧ HasCircuitSize n
        (fun x => graphFun G A (Function.update x v false)) t := by
    obtain ⟨D,hfan,hbound,hfun⟩ :=
      C_markedCoverUpper (G.deleteIncidenceSet v) A (T.erase v) (C_erase_cover G T v hT) hne
    have hcard := G.card_edgeFinset_deleteIncidenceSet v
    have hle := G.degree_le_card_edgeFinset v
    have hTcard := Finset.card_erase_add_one hvt
    obtain ⟨a,b,hab⟩ := hne
    have hpositive : 0 < (G.deleteIncidenceSet v).edgeFinset.card :=
      Finset.card_pos.mpr ⟨s(a,b),by simpa using hab⟩
    refine ⟨D.size, by omega, D, hfan, le_rfl, ?_⟩
    intro x
    have hf := hfun x
    exact hf.trans (C_restrict_false G A v hva x).symm

  have C_edge_survives {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
      (hdeg : ∀ u ∉ A, 2 ≤ G.degree u)
      (hA : ∀ a b, G.Adj a b → a ∉ A)
      (hne : ∃ a b, G.Adj a b) (v : Fin n) :
      ∃ a b, (G.deleteIncidenceSet v).Adj a b := by
    obtain ⟨a,b,hab⟩ := hne
    obtain ⟨u,hu,hua⟩ : ∃ u : Fin n, u ≠ v ∧ u ∉ A := by
      by_cases hav : a = v
      · refine ⟨b, ?_, hA b a hab.symm⟩
        intro hbv
        exact hab.ne (hav.trans hbv.symm)
      · exact ⟨a,hav,hA a b hab⟩
    have hneighbor : ∃ w, G.Adj u w ∧ w ≠ v := by
      by_contra h
      have hsub : G.neighborFinset u ⊆ {v} := by
        intro w hw
        simp only [Finset.mem_singleton]
        by_contra hwv
        exact h ⟨w,by simpa using hw,hwv⟩
      have hc := Finset.card_le_card hsub
      have hd := hdeg u hua
      simp only [Finset.card_singleton, G.card_neighborFinset_eq_degree] at hc
      omega
    obtain ⟨w,huw,hw⟩ := hneighbor
    exact ⟨u,w,by simpa only [SimpleGraph.deleteIncidenceSet_adj] using
      (show G.Adj u w ∧ u ≠ v ∧ w ≠ v from ⟨huw,hu,hw⟩)⟩

  have C_cubic_cover_bound_suffices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)) (s : ℕ)
      (hT : G.IsVertexCover (T : Set (Fin n)))
      (hdeg : ∀ u ∉ A, (G.neighborSet u).ncard = 3)
      (hA : ∀ a b, G.Adj a b → a ∉ A)
      (hne : ∃ a b, G.Adj a b)
      (hsize : A.card + G.edgeFinset.card + T.card ≤ s + 1) :
      ∃ v ∉ A, ∃ t, t + 4 ≤ s ∧ HasCircuitSize n
        (fun x => graphFun G A (Function.update x v false)) t := by
    obtain ⟨a,b,hab⟩ := hne
    obtain ⟨v,hvt,hva⟩ : ∃ v : Fin n, v ∈ T ∧ v ∉ A := by
      rcases hT hab with ha | hb
      · exact ⟨a,ha,hA a b hab⟩
      · exact ⟨b,hb,hA b a hab.symm⟩
    have hdeg' : ∀ u ∉ A, G.degree u = 3 := by
      intro u hu
      simpa only [G.ncard_neighborSet] using hdeg u hu
    refine ⟨v,hva,?_⟩
    exact C_saving_at_cover_bound G A T v s hT hvt hva (by rw [hdeg' v hva])
      (C_edge_survives G A (fun u hu => by rw [hdeg' u hu]; omega)
        hA ⟨a,b,hab⟩ v) hsize

  have F_small_bipartite_cover {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (hcol : G.Colorable 2) (hA : ∀ a b, G.Adj a b → a ∉ A) :
      ∃ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) ∧ 2*T.card ≤ Aᶜ.card := by
    classical
    obtain ⟨col⟩ := hcol
    have hc : ∀ u v, G.Adj u v → col u ≠ col v := fun u v h => col.valid h
    have getCover (i : Fin 2)
        (small : (Aᶜ.filter fun v => col v = i).card ≤ (Aᶜ.filter fun v => col v ≠ i).card) :
        ∃ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) ∧ 2*T.card ≤ Aᶜ.card := by
      refine ⟨Aᶜ.filter fun v => col v = i, ?_, ?_⟩
      · intro a b hab
        by_cases ha : col a = i
        · exact Or.inl (by simpa using And.intro (hA a b hab) ha)
        · have hb : col b = i := by
            have h := hc a b hab
            have two : ∀ x y z : Fin 2, x ≠ y → x ≠ z → y = z := by decide
            exact two _ _ _ h ha
          exact Or.inr (by simpa using And.intro (hA b a hab.symm) hb)
      · have hcard : (Aᶜ.filter fun v => col v = i).card +
            (Aᶜ.filter fun v => col v ≠ i).card = Aᶜ.card := by
          simpa only [ne_eq] using Finset.card_filter_add_card_filter_not (s := Aᶜ) (fun v => col v = i)
        omega
    by_cases h : (Aᶜ.filter fun v => col v = 0).card ≤ (Aᶜ.filter fun v => col v ≠ 0).card
    · exact getCover 0 h
    · apply getCover 1
      have h1 : (Aᶜ.filter fun v => col v = 1) = (Aᶜ.filter fun v => col v ≠ 0) := by
        apply Finset.filter_congr
        intro v _
        have hh : ∀ x : Fin 2, x = 1 ↔ x ≠ 0 := by decide
        exact hh _
      have h0 : (Aᶜ.filter fun v => col v ≠ 1) = (Aᶜ.filter fun v => col v = 0) := by
        apply Finset.filter_congr
        intro v _
        have hh : ∀ x : Fin 2, x ≠ 1 ↔ x = 0 := by decide
        exact hh _
      rw [h1,h0]
      omega

  -- Every bipartite cubic instance of the assignment follows from the wiring bound.
  -- The AND-reader and girth hypotheses are not needed for this entire class.

  have F_bipartite_drop {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit)
      (hcol : G.Colorable 2)
      (hdeg : ∀ u ∉ A, (G.neighborSet u).ncard = 3)
      (hA : ∀ a b, G.Adj a b → a ∉ A)
      (hne : ∃ a b, G.Adj a b)
      (hc : FanInTwo C)
      (hf : circuitFun n C = graphFun G A)
      (hmin : ∀ s, HasCircuitSize n (graphFun G A) s → C.size ≤ s)
      (hread : ∀ v ∉ A, 2 ≤ (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) :
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n
        (fun x => graphFun G A (Function.update x v false)) s := by
    classical
    obtain ⟨T,hT,htsmall⟩ := F_small_bipartite_cover G A hcol hA
    have hb := M_marked_wiring_bound n G A C hc hf hmin
    have hr := Finset.sum_le_sum (s := Aᶜ) (fun v hv => hread v (Finset.mem_compl.mp hv))
    simp only [Finset.sum_const, smul_eq_mul] at hr
    have hr' : 2*Aᶜ.card ≤ (∑ v ∈ Aᶜ, (C.gates.filter fun g => (M_eff g).contains v.val).length) := by
      simpa only [M_eff, Nat.mul_comm] using hr
    have dA (a : Fin n) (ha : a ∈ A) : G.degree a = 0 := by
      apply (G.degree_eq_zero a).mpr
      exact fun j h => hA a j h ha
    have dB (a : Fin n) (ha : a ∈ Aᶜ) : G.degree a = 3 := by
      rw [← G.ncard_neighborSet]
      exact hdeg a (Finset.mem_compl.mp ha)
    have hs := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at hs
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at hs
    exact C_cubic_cover_bound_suffices G A T C.size hT hdeg hA hne (by omega)

  intro n G _ A C
  dsimp only
  intro hdeg hgirth hA hedge hfan hcomp hmin hread hand
  by_cases hcol : G.Colorable 2
  · exact F_bipartite_drop G A C hcol hdeg hA hedge hfan hcomp hmin
      (fun v hv => (hread v hv).1)
  · exact nonbipartite n G A C hcol hdeg hgirth hA hedge hfan hcomp hmin hread hand
