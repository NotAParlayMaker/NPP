import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

-- Use the restriction machinery of L-meta-314 and the cover circuit of L-meta-1975
-- to isolate the sparse case below the cover bound.
theorem PEqualNP.Outside.R_meta_4051_1
    (classify : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (V : Finset (Fin n)) (s : ℕ),
      V.Nonempty →
      (∀ v ∈ V, ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false)) →
      HasCircuitSize n f s →
      (∃ v ∈ V, ∃ t, t + 4 ≤ s ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) t) ∨
      (∃ C : Circuit, IsMinimalCircuit n C ∧ circuitFun n C = f ∧ C.size ≤ s ∧
        (∀ j < C.gates.length, n + j ∈ C.output :: C.gates.flatMap Gate.inputs) ∧
        ∀ v ∈ V, let readers := C.gates.filter (fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
        readers.length ≤ 3 ∧ (readers.length = 3 → ∀ g ∈ readers, g.op = .or)))
    (starCircuit : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
      (∃ i j, G.Adj i j) →
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
      HasCircuitSize n (graphFun G ∅) (G.edgeFinset.card + T.card - 1))
    (fewReaders : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∃ i j, G.Adj i j) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
      (∀ v : Fin n, (G.neighborSet v).ncard = 3 →
        let readers := C.gates.filter (fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
        readers.length ≤ 3 ∧ (readers.length = 3 → ∀ g ∈ readers, g.op = .or)) →
      (∃ v : Fin n, (G.neighborSet v).ncard = 3 ∧
        (C.gates.filter (fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length ≤ 2) →
      (∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + 1 < G.edgeFinset.card + T.card) →
      ∃ v : Fin n, (G.neighborSet v).ncard = 3 ∧ ∃ t, t + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 : Fin x1 → Bool), x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x8 → ∃ (x10 : Fin x1), (x2.neighborSet x10).ncard = (3 : ℕ) ∧ ∃ (x11 : ℕ), x11 + (4 : ℕ) ≤ x8 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update x12 x10 Bool.false)) x11 := by
  classical
  intro n G f degree girth edge computes s size
  let _ : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  let V := Finset.univ.filter (fun v : Fin n => (G.neighborSet v).ncard = 3)
  have memV (v : Fin n) : v ∈ V ↔ (G.neighborSet v).ncard = 3 := by
    simp [V]
  have active {i j : Fin n} (h : G.Adj i j) : (G.neighborSet i).ncard = 3 := by
    rcases degree i with hzero | hthree
    · have hmem : j ∈ G.neighborSet i := h
      rw [(Set.ncard_eq_zero (Set.toFinite _)).mp hzero] at hmem
      simp at hmem
    · exact hthree
  have nonempty : V.Nonempty := by
    obtain ⟨i, j, hij⟩ := edge
    exact ⟨i, (memV i).mpr (active hij)⟩
  have keptEdge (v : Fin n) (hv : v ∈ V) :
      ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v := by
    have first : ∃ i, G.Adj v i := by
      by_contra! none
      have empty : G.neighborSet v = ∅ := Set.eq_empty_iff_forall_notMem.mpr none
      simpa [empty] using (memV v).mp hv
    obtain ⟨i, hvi⟩ := first
    have second : ∃ j, G.Adj i j ∧ j ≠ v := by
      by_contra! sole
      have subset : G.neighborSet i ⊆ {v} :=
        fun j hj => Set.mem_singleton_iff.mpr (sole j hj)
      have bound := Set.ncard_le_ncard subset
      rw [active hvi.symm, Set.ncard_singleton] at bound
      omega
    obtain ⟨j, hij, hjv⟩ := second
    exact ⟨i, j, hij, hvi.ne.symm, hjv⟩
  have varies (v : Fin n) (hv : v ∈ V) :
      ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false) := by
    obtain ⟨i, j, hij, hiv, hjv⟩ := keptEdge v hv
    let x : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun _ => true
    have zero : f (Function.update x v false) = false := by
      cases h : f (Function.update x v false) with
      | false => rfl
      | true =>
        obtain ⟨a, _, _, ha, _⟩ := (computes _).mp h
        by_cases hav : a = v <;> simp [x, Function.update, hav] at ha
    have one : f (Function.update y v false) = true :=
      (computes _).mpr ⟨i, j, hij, by simp [y, Function.update_of_ne hiv],
        by simp [y, Function.update_of_ne hjv]⟩
    exact ⟨x, y, by simp [zero, one]⟩
  rcases classify n f V s nonempty varies size with ⟨v, hv, t, ht, hsize⟩ |
    ⟨C, minimal, computesC, within, live, readers⟩
  · exact ⟨v, (memV v).mp hv, t, ht, hsize⟩
  have graphSpec (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (x : Fin n → Bool) :
      graphFun K ∅ x = true ↔ ∃ i j, K.Adj i j ∧ x i = true ∧ x j = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ i j, K.Adj i j ∧ x i = true ∧ x j = true)) = true ↔ _
    simp
  have computesGraph : circuitFun n C = graphFun G ∅ := by
    rw [computesC]
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [computes, graphSpec]
  have shape (v : Fin n) (hv : (G.neighborSet v).ncard = 3) :=
    readers v ((memV v).mpr hv)
  have save : ∃ v : Fin n, (G.neighborSet v).ncard = 3 ∧ ∃ t, t + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) t := by
    by_cases bench : ∃ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
        G.edgeFinset.card + T.card ≤ C.size + 1
    · obtain ⟨T, cover, budget⟩ := bench
      obtain ⟨i, j, hij⟩ := edge
      obtain ⟨v, hv, vT⟩ : ∃ v ∈ V, v ∈ T := by
        rcases cover i j hij with hi | hj
        · exact ⟨i, (memV i).mpr (active hij), hi⟩
        · exact ⟨j, (memV j).mpr (active hij.symm), hj⟩
      let H := G.deleteIncidenceSet v
      let T' := T.erase v
      obtain ⟨a, b, hab, hav, hbv⟩ := keptEdge v hv
      have edgeH : H.Adj a b := SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab, hav, hbv⟩
      have coverH (a b : Fin n) (h : H.Adj a b) : a ∈ T' ∨ b ∈ T' := by
        obtain ⟨orig, ha, hb⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
        exact (cover a b orig).imp
          (fun h => Finset.mem_erase.mpr ⟨ha, h⟩) (fun h => Finset.mem_erase.mpr ⟨hb, h⟩)
      have edgesH : H.edgeFinset.card = G.edgeFinset.card - 3 := by
        have deg : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans ((memV v).mp hv)
        exact (G.card_edgeFinset_deleteIncidenceSet v).trans (by rw [deg])
      have posH : 0 < H.edgeFinset.card :=
        Finset.card_pos.mpr ⟨s(a, b), SimpleGraph.mem_edgeFinset.mpr edgeH⟩
      have coverCard : T'.card = T.card - 1 := Finset.card_erase_of_mem vT
      have coverPos : 0 < T.card := Finset.card_pos.mpr ⟨v, vT⟩
      let t := H.edgeFinset.card + T'.card - 1
      have cut := starCircuit n H T' ⟨a, b, edgeH⟩ coverH
      have cutEq : graphFun H ∅ =
          fun x => circuitFun n C (Function.update x v false) := by
        funext x
        apply Bool.eq_iff_iff.mpr
        rw [computesC, computes, graphSpec]
        constructor
        · rintro ⟨i, j, h, hi, hj⟩
          obtain ⟨orig, hiv, hjv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
          exact ⟨i, j, orig, by simpa [Function.update_of_ne hiv] using hi,
            by simpa [Function.update_of_ne hjv] using hj⟩
        · rintro ⟨i, j, h, hi, hj⟩
          have hiv : i ≠ v := by rintro rfl; simp at hi
          have hjv : j ≠ v := by rintro rfl; simp at hj
          exact ⟨i, j, SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h, hiv, hjv⟩,
            by simpa [Function.update_of_ne hiv] using hi,
            by simpa [Function.update_of_ne hjv] using hj⟩
      rw [cutEq] at cut
      exact ⟨v, (memV v).mp hv, t, by dsimp [t]; omega, cut⟩
    · apply fewReaders n G C degree girth edge minimal computesGraph shape
      · -- Three readers at every active input require more slots than the cover circuit allows.
        by_contra noFew
        have vpos : 0 < V.card := Finset.card_pos.mpr nonempty
        obtain ⟨v, vV⟩ := nonempty
        let T := V.erase v
        have cover (i j : Fin n) (h : G.Adj i j) : i ∈ T ∨ j ∈ T := by
          by_cases hi : i = v
          · exact Or.inr (Finset.mem_erase.mpr ⟨by simpa [hi] using h.ne.symm,
              (memV j).mpr (active h.symm)⟩)
          · exact Or.inl (Finset.mem_erase.mpr ⟨hi, (memV i).mpr (active h)⟩)
        have trust := starCircuit n G T edge cover
        have bound : C.size ≤ G.edgeFinset.card + T.card - 1 := by
          obtain ⟨D, fan, dsize, compute⟩ := trust
          exact (minimal.2 D fan ((funext compute).trans computesGraph.symm)).trans dsize
        have tcard : T.card = V.card - 1 := Finset.card_erase_of_mem vV
        have degreeIn (i : Fin n) (hi : i ∈ V) : G.degree i = 3 :=
          (G.ncard_neighborSet i).symm.trans ((memV i).mp hi)
        have degreeOut (i : Fin n) (hi : i ∈ Vᶜ) : G.degree i = 0 := by
          apply (G.degree_eq_zero i).mpr
          exact fun _ h => (Finset.mem_compl.mp hi) ((memV i).mpr (active h))
        have degSum := G.sum_degrees_eq_twice_card_edges
        rw [← V.sum_add_sum_compl, Finset.sum_congr rfl degreeIn,
          Finset.sum_congr rfl degreeOut] at degSum
        simp only [Finset.sum_const, smul_eq_mul, mul_zero, add_zero] at degSum
        let reads (v : ℕ) (g : Gate) :=
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
        have countReaders (v : ℕ) (gs : List Gate) :
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
        have slotCount (gs : List Gate) (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
            (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
          induction gs with
          | nil => simp
          | cons g gs ih =>
            have hg := fan g List.mem_cons_self
            have ht := ih (fun g hg => fan g (List.mem_cons_of_mem _ hg))
            simp only [List.flatMap_cons, List.length_append, List.length_cons]
            omega
        have occurrences (xs : List ℕ) (S : Finset ℕ) :
            ∑ i ∈ S, xs.count i ≤ xs.length := by
          induction xs with
          | nil => simp
          | cons a xs ih =>
            simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
            by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega
        let slots := C.output :: C.gates.flatMap Gate.inputs
        have inputsUsed (a : Fin n) (ha : a ∈ V) : 3 ≤ slots.count a.val := by
          have h : ¬ (C.gates.filter (reads a.val)).length ≤ 2 :=
            fun h => noFew ⟨a, (memV a).mp ha, h⟩
          have ht := countReaders a.val C.gates
          change 3 ≤ (C.output :: C.gates.flatMap Gate.inputs).count a.val
          simp only [List.count_cons]
          omega
        have internalsUsed (j : ℕ) (hj : j ∈ Finset.range C.gates.length) :
            1 ≤ slots.count (n+j) :=
          List.count_pos_iff.mpr (live j (Finset.mem_range.mp hj))
        have lowInput := Finset.sum_le_sum inputsUsed
        have lowInternal := Finset.sum_le_sum internalsUsed
        simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at lowInput lowInternal
        let wires := V.image Fin.val
        let gates := (Finset.range C.gates.length).image (fun j => n + j)
        have disj : Disjoint wires gates := by
          apply Finset.disjoint_left.mpr
          intro k hk hg
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hg
          omega
        have total := occurrences slots (wires ∪ gates)
        rw [Finset.sum_union disj] at total
        rw [Finset.sum_image (fun a _ b _ eq => Fin.val_injective eq),
          Finset.sum_image (fun a _ b _ eq => Nat.add_left_cancel eq)] at total
        have lengths := slotCount C.gates (fun g hg => (minimal.1 g hg).2)
        have slen : slots.length = (C.gates.flatMap Gate.inputs).length + 1 := rfl
        change C.gates.length ≤ _ at bound
        omega
      · intro T cover
        exact Nat.lt_of_not_ge (fun budget => bench ⟨T, cover, budget⟩)
  obtain ⟨v, hv, t, ht, cut⟩ := save
  exact ⟨v, hv, t, ht.trans within, by simpa [computesC] using cut⟩
