import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SyntacticMultilinear PEqualNP.CrossAnd PEqualNP.GenericRejection in
theorem PEqualNP.Outside.R_meta_2984_512
    (fewCross : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      (200 : ℕ) ≤ q → N = q ^ (2 : ℕ) + q + (1 : ℕ) →
      (∀ l : Fin N, (S l).card = q + (1 : ℕ)) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l) →
      IsAO2 (N + N) C → C.output < N + N + C.size →
      RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = Bool.false) →
      (1 : ℕ) ≤ crossCount (N + N) (Finset.univ.filter fun u : Fin (N + N) => N ≤ u.val) C →
      crossCount (N + N) (Finset.univ.filter fun u : Fin (N + N) => N ≤ u.val) C ≤ q →
      (100 : ℕ) * crossCount (N + N) (Finset.univ.filter fun u : Fin (N + N) => N ≤ u.val) C < N * q →
      N * q ≤ (100 : ℕ) * C.size)
    (manyCross : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      (200 : ℕ) ≤ q → N = q ^ (2 : ℕ) + q + (1 : ℕ) →
      (∀ l : Fin N, (S l).card = q + (1 : ℕ)) →
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ S l ∧ p2 ∈ S l) →
      IsAO2 (N + N) C → C.output < N + N + C.size →
      RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = Bool.false) →
      q < crossCount (N + N) (Finset.univ.filter fun u : Fin (N + N) => N ≤ u.val) C →
      (100 : ℕ) * crossCount (N + N) (Finset.univ.filter fun u : Fin (N + N) => N ≤ u.val) C < N * q →
      N * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q N S C hq hN hcard huniq hAO hout hright hsound
  let M : Finset (Fin (N + N)) := Finset.univ.filter fun u : Fin (N + N) => N ≤ u.val
  let cc := crossCount (N + N) M C
  by_cases hbig : N * q ≤ 100 * cc
  · have hcc_le : cc ≤ C.size := by
      unfold cc crossCount Circuit.size
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  by_cases hzero : cc = 0
  · have hNoCross : ∀ j < C.gates.length, ¬ IsCrossAnd (N + N) M C j := by
      intro j hj hcr
      have hmem : j ∈ (Finset.range C.gates.length).filter (fun k => IsCrossAnd (N + N) M C k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hcr⟩
      have hpos : 0 < cc := Finset.card_pos.mpr ⟨j, hmem⟩
      omega
    have hSuppLen : ∀ (gs : List Gate) (acc : List (Finset (Fin (N + N)))),
        (gs.foldl supportStep acc).length = acc.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro acc; simp
      | cons g rest ih =>
        intro acc
        simp only [List.foldl_cons, ih, supportStep, List.length_append, List.length_cons, List.length_nil]
        omega
    have hSuppPrefix : ∀ (gs : List Gate) (acc : List (Finset (Fin (N + N)))) (w : ℕ),
        w < acc.length → (gs.foldl supportStep acc).getD w ∅ = acc.getD w ∅ := by
      intro gs
      induction gs with
      | nil => intro acc w _; rfl
      | cons g rest ih =>
        intro acc w hw
        simp only [List.foldl_cons]
        have hlen : w < (supportStep acc g).length := by
          simp only [supportStep, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [ih (supportStep acc g) w hlen]
        simp only [supportStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
    have hSuppInput : ∀ (w : ℕ) (hw : w < N + N),
        support (N + N) C w = {⟨w, hw⟩} := by
      intro w hw
      unfold support supports
      have hlen : w < (List.ofFn fun i : Fin (N + N) => ({i} : Finset (Fin (N + N)))).length := by
        simp [hw]
      rw [hSuppPrefix C.gates _ w hlen]
      simp [List.getD_eq_getElem?_getD, hw]
    have hSuppGate : ∀ (j : ℕ) (hj : j < C.gates.length) (a b : ℕ),
        (gateAt C j).inputs = [a, b] →
        support (N + N) C (N + N + j) = support (N + N) C a ∪ support (N + N) C b := by
      intro j hj a b hab
      have halt : a < N + N + j := hAO.2.1 j hj a (by rw [hab]; simp)
      have hblt : b < N + N + j := hAO.2.1 j hj b (by rw [hab]; simp)
      have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
        have h1 : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
        have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
        calc C.gates = C.gates.take j ++ C.gates.drop j := h1.symm
          _ = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by rw [h2]
          _ = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by simp
      set base := List.ofFn (fun i : Fin (N + N) => ({i} : Finset (Fin (N + N))))
      set acc := (C.gates.take j).foldl supportStep base
      have haccLen : acc.length = N + N + j := by
        rw [hSuppLen, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have hgate : gateAt C j = C.gates[j] := by
        unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
      have haccAt : ∀ u < N + N + j, support (N + N) C u = acc.getD u ∅ := by
        intro u hu
        unfold support supports
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hu2 : u < (supportStep acc C.gates[j]).length := by
          simp only [supportStep, List.length_append, List.length_cons, List.length_nil]
          omega
        rw [hSuppPrefix (C.gates.drop (j + 1)) _ u hu2]
        simp only [supportStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < acc.length)]
      conv_lhs => unfold support supports
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hjlt : N + N + j < (supportStep acc C.gates[j]).length := by
        simp only [supportStep, List.length_append, List.length_cons, List.length_nil, haccLen]
        omega
      rw [hSuppPrefix (C.gates.drop (j + 1)) _ (N + N + j) hjlt]
      simp only [supportStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [← hgate, hab]
      simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
      rw [haccAt a halt, haccAt b hblt]
      simp [List.getD_eq_getElem?_getD]
    have hSuppNe : ∀ w < N + N + C.gates.length, (support (N + N) C w).Nonempty := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hlt : w < N + N
        · rw [hSuppInput w hlt]
          exact Finset.singleton_nonempty _
        · let j := w - (N + N)
          have hj : j < C.gates.length := by omega
          have hwj : w = N + N + j := by omega
          have hjmem : gateAt C j ∈ C.gates := by
            unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
          rcases List.length_eq_two.mp (hAO.2.2 (gateAt C j) hjmem) with ⟨a, b, hab⟩
          have halt : a < w := by
            have := hAO.2.1 j hj a (by rw [hab]; simp); omega
          rw [hwj, hSuppGate j hj a b hab]
          exact (ih a halt (by omega)).mono Finset.subset_union_left
    have hAndSplit : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < N + N + j ∧ b < N + N + j ∧
          ((support (N + N) C a ∩ M = ∅ ∧ support (N + N) C b ⊆ M) ∨
           (support (N + N) C a ⊆ M ∧ support (N + N) C b ∩ M = ∅)) := by
      intro j hj hjop
      have hjmem : gateAt C j ∈ C.gates := by
        unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
      have hjlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hjmem
      rcases List.length_eq_two.mp hjlen with ⟨a, b, hab⟩
      have halt : a < N + N + j := hAO.2.1 j hj a (by rw [hab]; simp)
      have hblt : b < N + N + j := hAO.2.1 j hj b (by rw [hab]; simp)
      have hnc := hNoCross j hj
      have hop0 : operandSupport (N + N) C j ((gateAt C j).inputs.getD 0 0) = support (N + N) C a := by
        rw [hab]; simp [operandSupport, halt]
      have hop1 : operandSupport (N + N) C j ((gateAt C j).inputs.getD 1 0) = support (N + N) C b := by
        rw [hab]; simp [operandSupport, hblt]
      have ha_ne : (support (N + N) C a).Nonempty := hSuppNe a (by omega)
      have hb_ne : (support (N + N) C b).Nonempty := hSuppNe b (by omega)
      have hnotBothM : ¬ ((support (N + N) C a ∩ M).Nonempty ∧ (support (N + N) C b ∩ M).Nonempty) := by
        intro h
        apply hnc
        exact ⟨hjop, hjlen, Or.inl (by rwa [hop0, hop1])⟩
      have hnotBothP : ¬ ((support (N + N) C a \ M).Nonempty ∧ (support (N + N) C b \ M).Nonempty) := by
        intro h
        apply hnc
        exact ⟨hjop, hjlen, Or.inr (by rwa [hop0, hop1])⟩
      refine ⟨a, b, hab, halt, hblt, ?_⟩
      by_cases haM : (support (N + N) C a ∩ M).Nonempty
      · have hbM0 : support (N + N) C b ∩ M = ∅ := by
          by_contra hne
          exact hnotBothM ⟨haM, Finset.nonempty_iff_ne_empty.mpr hne⟩
        have hbP : (support (N + N) C b \ M).Nonempty := by
          obtain ⟨u, hu⟩ := hb_ne
          refine ⟨u, Finset.mem_sdiff.mpr ⟨hu, ?_⟩⟩
          intro huM
          exact Finset.notMem_empty u (hbM0 ▸ Finset.mem_inter.mpr ⟨hu, huM⟩)
        have haP0 : support (N + N) C a \ M = ∅ := by
          by_contra hne
          exact hnotBothP ⟨Finset.nonempty_iff_ne_empty.mpr hne, hbP⟩
        exact Or.inr ⟨Finset.sdiff_eq_empty_iff_subset.mp haP0, hbM0⟩
      · have haM0 : support (N + N) C a ∩ M = ∅ := Finset.not_nonempty_iff_eq_empty.mp haM
        have haP : (support (N + N) C a \ M).Nonempty := by
          obtain ⟨u, hu⟩ := ha_ne
          refine ⟨u, Finset.mem_sdiff.mpr ⟨hu, ?_⟩⟩
          intro huM
          exact Finset.notMem_empty u (haM0 ▸ Finset.mem_inter.mpr ⟨hu, huM⟩)
        have hbP0 : support (N + N) C b \ M = ∅ := by
          by_contra hne
          exact hnotBothP ⟨haP, Finset.nonempty_iff_ne_empty.mpr hne⟩
        exact Or.inl ⟨haM0, Finset.sdiff_eq_empty_iff_subset.mp hbP0⟩
    have hAndMixed : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        (support (N + N) C (N + N + j) ∩ M).Nonempty ∧ (support (N + N) C (N + N + j) \ M).Nonempty := by
      intro j hj hjop
      obtain ⟨a, b, hab, halt, hblt, hsp⟩ := hAndSplit j hj hjop
      rw [hSuppGate j hj a b hab]
      rcases hsp with ⟨ha0, hbM⟩ | ⟨haM, hb0⟩
      · obtain ⟨u, hu⟩ := hSuppNe a (by omega)
        obtain ⟨v, hv⟩ := hSuppNe b (by omega)
        refine ⟨⟨v, Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hv, hbM hv⟩⟩,
                ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hu, fun huM =>
                  Finset.notMem_empty u (ha0 ▸ Finset.mem_inter.mpr ⟨hu, huM⟩)⟩⟩⟩
      · obtain ⟨u, hu⟩ := hSuppNe a (by omega)
        obtain ⟨v, hv⟩ := hSuppNe b (by omega)
        refine ⟨⟨u, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hu, haM hu⟩⟩,
                ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hv, fun hvM =>
                  Finset.notMem_empty v (hb0 ▸ Finset.mem_inter.mpr ⟨hv, hvM⟩)⟩⟩⟩
    have hWiresLen : ∀ (gs : List Gate) (xs : List Bool),
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length =
          xs.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro xs; simp
      | cons g rest ih =>
        intro xs
        simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
        omega
    have hWiresPrefix : ∀ (gs : List Gate) (xs : List Bool) (w : ℕ),
        w < xs.length →
          (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) xs).getD w false =
            xs.getD w false := by
      intro gs
      induction gs with
      | nil => intro xs w _; rfl
      | cons g rest ih =>
        intro xs w hw
        simp only [List.foldl_cons]
        have hlen : w < (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]).length := by
          simp; omega
        rw [ih _ w hlen]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
    have hWireInput : ∀ (w : ℕ) (hw : w < N + N) (x : List Bool),
        x.length = N + N → (C.wires x).getD w false = x.getD w false := by
      intro w hw x hx
      unfold Circuit.wires
      exact hWiresPrefix C.gates x w (by omega)
    have hWireGate : ∀ (j : ℕ) (hj : j < C.gates.length) (x : List Bool),
        x.length = N + N →
        (C.wires x).getD (N + N + j) false =
          (gateAt C j).op.eval ((gateAt C j).inputs.map fun u => (C.wires x).getD u false) := by
      intro j hj x hx
      unfold Circuit.wires
      have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
        have h1 : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
        have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
        calc C.gates = C.gates.take j ++ C.gates.drop j := h1.symm
          _ = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by rw [h2]
          _ = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by simp
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set acc := (C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      have haccLen : acc.length = N + N + j := by
        rw [hWiresLen, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have hjlt : N + N + j < (acc ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => acc.getD i false)]).length := by
        simp [haccLen]
      rw [hWiresPrefix (C.gates.drop (j + 1)) _ (N + N + j) hjlt]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      have hgate : gateAt C j = C.gates[j] := by
        unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
      rw [hgate]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hult : u < N + N + j := hAO.2.1 j hj u (by rwa [hgate])
      have huacc : u < acc.length := by omega
      symm
      change ((C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD u false) =
        acc.getD u false
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hu2 : u < (acc ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => acc.getD i false)]).length := by
        simp; omega
      rw [hWiresPrefix (C.gates.drop (j + 1)) _ u hu2]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left huacc]
    have hPureEval : ∀ w < N + N + C.gates.length,
        (support (N + N) C w ∩ M = ∅ ∨ support (N + N) C w ⊆ M) →
        ∀ x : List Bool, x.length = N + N →
          ((C.wires x).getD w false = true ↔ ∃ u ∈ support (N + N) C w, x.getD u.val false = true) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hpure x hx
        by_cases hlt : w < N + N
        · rw [hWireInput w hlt x hx, hSuppInput w hlt]
          simp
        · let j := w - (N + N)
          have hj : j < C.gates.length := by omega
          have hwj : w = N + N + j := by omega
          have hjmem : gateAt C j ∈ C.gates := by
            unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
          have hjor : (gateAt C j).op = GateOp.or := by
            rcases hAO.1 (gateAt C j) hjmem with hop | hop
            · obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hAndMixed j hj hop
              rw [← hwj] at hu hv
              rcases hpure with h0 | hsub
              · exact False.elim (Finset.notMem_empty u (h0 ▸ hu))
              · exact False.elim ((Finset.mem_sdiff.mp hv).2 (hsub (Finset.mem_sdiff.mp hv).1))
            · exact hop
          rcases List.length_eq_two.mp (hAO.2.2 (gateAt C j) hjmem) with ⟨a, b, hab⟩
          have halt : a < w := by have := hAO.2.1 j hj a (by rw [hab]; simp); omega
          have hblt : b < w := by have := hAO.2.1 j hj b (by rw [hab]; simp); omega
          have hsw : support (N + N) C w = support (N + N) C a ∪ support (N + N) C b := by
            rw [hwj]; exact hSuppGate j hj a b hab
          have hpure_a : support (N + N) C a ∩ M = ∅ ∨ support (N + N) C a ⊆ M := by
            rcases hpure with h0 | hsub
            · left
              rw [Finset.eq_empty_iff_forall_notMem]
              intro u hu
              have : u ∈ support (N + N) C w ∩ M :=
                Finset.mem_inter.mpr ⟨hsw ▸ Finset.mem_union_left _ (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hu).2⟩
              exact Finset.notMem_empty u (h0 ▸ this)
            · right
              exact Finset.subset_union_left.trans (hsw ▸ hsub)
          have hpure_b : support (N + N) C b ∩ M = ∅ ∨ support (N + N) C b ⊆ M := by
            rcases hpure with h0 | hsub
            · left
              rw [Finset.eq_empty_iff_forall_notMem]
              intro u hu
              have : u ∈ support (N + N) C w ∩ M :=
                Finset.mem_inter.mpr ⟨hsw ▸ Finset.mem_union_right _ (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hu).2⟩
              exact Finset.notMem_empty u (h0 ▸ this)
            · right
              exact Finset.subset_union_right.trans (hsw ▸ hsub)
          rw [hwj, hWireGate j hj x hx, hjor, hab]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
            Bool.or_false, Bool.or_eq_true]
          rw [ih a halt (by omega) hpure_a x hx, ih b hblt (by omega) hpure_b x hx, ← hwj, hsw]
          constructor
          · rintro (⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩)
            · exact ⟨u, Finset.mem_union_left _ hu, hxu⟩
            · exact ⟨u, Finset.mem_union_right _ hu, hxu⟩
          · rintro ⟨u, hu, hxu⟩
            rcases Finset.mem_union.mp hu with hua | hub
            · exact Or.inl ⟨u, hua, hxu⟩
            · exact Or.inr ⟨u, hub, hxu⟩
    have hDecomp : ∀ w < N + N + C.gates.length,
        ∃ (IW : Finset (Fin (N + N))) (TW : Finset ℕ),
          (∀ j ∈ TW, j < C.gates.length ∧ (gateAt C j).op = GateOp.and) ∧
          ∀ x : List Bool, x.length = N + N →
            ((C.wires x).getD w false = true ↔
              (∃ u ∈ IW, x.getD u.val false = true) ∨
              (∃ j ∈ TW, (C.wires x).getD (N + N + j) false = true)) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hlt : w < N + N
        · refine ⟨{⟨w, hlt⟩}, ∅, by simp, fun x hx => ?_⟩
          rw [hWireInput w hlt x hx]
          simp
        · let j := w - (N + N)
          have hj : j < C.gates.length := by omega
          have hwj : w = N + N + j := by omega
          have hjmem : gateAt C j ∈ C.gates := by
            unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
          rcases hAO.1 (gateAt C j) hjmem with hop | hop
          · refine ⟨∅, {j}, by simp [hj, hop], fun x _ => ?_⟩
            rw [hwj]; simp
          · rcases List.length_eq_two.mp (hAO.2.2 (gateAt C j) hjmem) with ⟨a, b, hab⟩
            have halt : a < w := by have := hAO.2.1 j hj a (by rw [hab]; simp); omega
            have hblt : b < w := by have := hAO.2.1 j hj b (by rw [hab]; simp); omega
            obtain ⟨Ia, Ta, hTa, hEa⟩ := ih a halt (by omega)
            obtain ⟨Ib, Tb, hTb, hEb⟩ := ih b hblt (by omega)
            refine ⟨Ia ∪ Ib, Ta ∪ Tb, ?_, fun x hx => ?_⟩
            · intro k hk
              rcases Finset.mem_union.mp hk with hka | hkb
              · exact hTa k hka
              · exact hTb k hkb
            · rw [hwj, hWireGate j hj x hx, hop, hab]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.or_eq_true]
              rw [hEa x hx, hEb x hx]
              constructor
              · rintro ((⟨u, hu, hxu⟩ | ⟨k, hk, hxk⟩) | (⟨u, hu, hxu⟩ | ⟨k, hk, hxk⟩))
                · exact Or.inl ⟨u, Finset.mem_union_left _ hu, hxu⟩
                · exact Or.inr ⟨k, Finset.mem_union_left _ hk, hxk⟩
                · exact Or.inl ⟨u, Finset.mem_union_right _ hu, hxu⟩
                · exact Or.inr ⟨k, Finset.mem_union_right _ hk, hxk⟩
              · rintro (⟨u, hu, hxu⟩ | ⟨k, hk, hxk⟩)
                · rcases Finset.mem_union.mp hu with hua | hub
                  · exact Or.inl (Or.inl ⟨u, hua, hxu⟩)
                  · exact Or.inr (Or.inl ⟨u, hub, hxu⟩)
                · rcases Finset.mem_union.mp hk with hka | hkb
                  · exact Or.inl (Or.inr ⟨k, hka, hxk⟩)
                  · exact Or.inr (Or.inr ⟨k, hkb, hxk⟩)
    have hIncLen : ∀ (X Y : Finset (Fin N)), (incidenceInput X Y).length = N + N := by
      intro X Y; unfold incidenceInput; simp
    have hIncAtP : ∀ (X Y : Finset (Fin N)) (p : Fin N),
        (incidenceInput X Y).getD p.val false = decide (p ∈ X) := by
      intro X Y p
      unfold incidenceInput
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, p.isLt]
    have hIncAtL : ∀ (X Y : Finset (Fin N)) (l : Fin N),
        (incidenceInput X Y).getD (N + l.val) false = decide (l ∈ Y) := by
      intro X Y l
      unfold incidenceInput
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp)]
      simp [l.isLt]
    obtain ⟨Iout, Tout, hTout, hEout⟩ := hDecomp C.output (by change C.output < N + N + C.size; exact hout)
    have hIoutEmpty : Iout = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      by_cases hult : u.val < N
      · let p : Fin N := ⟨u.val, hult⟩
        have hfalse : IsFalseInput S {p} (∅ : Finset (Fin N)) := by intro l hl; exact False.elim (Finset.notMem_empty l hl)
        have h0 : C.eval (incidenceInput {p} (∅ : Finset (Fin N))) = false := hsound {p} ∅ (by simp) hfalse
        have h1 : C.eval (incidenceInput {p} (∅ : Finset (Fin N))) = true := by
          unfold Circuit.eval
          rw [hEout _ (hIncLen {p} ∅)]
          refine Or.inl ⟨u, hu, ?_⟩
          have : (incidenceInput {p} (∅ : Finset (Fin N))).getD p.val false = true := by rw [hIncAtP]; simp
          exact this
        rw [h0] at h1; cases h1
      · let l : Fin N := ⟨u.val - N, by omega⟩
        have hfalse : IsFalseInput S (∅ : Finset (Fin N)) {l} := by intro l' _; simp
        have h0 : C.eval (incidenceInput (∅ : Finset (Fin N)) {l}) = false := hsound ∅ {l} (by simp; omega) hfalse
        have h1 : C.eval (incidenceInput (∅ : Finset (Fin N)) {l}) = true := by
          unfold Circuit.eval
          rw [hEout _ (hIncLen ∅ {l})]
          refine Or.inl ⟨u, hu, ?_⟩
          have heq : u.val = N + l.val := by dsimp [l]; omega
          rw [heq, hIncAtL]; simp
        rw [h0] at h1; cases h1
    let pWire (j : ℕ) : ℕ :=
      if support (N + N) C ((gateAt C j).inputs.getD 0 0) ∩ M = ∅
      then (gateAt C j).inputs.getD 0 0
      else (gateAt C j).inputs.getD 1 0
    let lWire (j : ℕ) : ℕ :=
      if support (N + N) C ((gateAt C j).inputs.getD 0 0) ∩ M = ∅
      then (gateAt C j).inputs.getD 1 0
      else (gateAt C j).inputs.getD 0 0
    have hPLW : ∀ j ∈ Tout,
        pWire j < N + N + j ∧ lWire j < N + N + j ∧
        support (N + N) C (pWire j) ∩ M = ∅ ∧ support (N + N) C (lWire j) ⊆ M ∧
        (∀ x : List Bool, x.length = N + N →
          ((C.wires x).getD (N + N + j) false = true ↔
            (∃ u ∈ support (N + N) C (pWire j), x.getD u.val false = true) ∧
            (∃ v ∈ support (N + N) C (lWire j), x.getD v.val false = true))) ∧
        (∀ u ∈ support (N + N) C (pWire j), ∀ v ∈ support (N + N) C (lWire j),
          ∃ (p l : Fin N), u.val = p.val ∧ v.val = N + l.val ∧ p ∈ S l) := by
      intro j hjT
      obtain ⟨hj, hjop⟩ := hTout j hjT
      obtain ⟨a, b, hab, halt, hblt, hsp⟩ := hAndSplit j hj hjop
      have h0 : (gateAt C j).inputs.getD 0 0 = a := by rw [hab]; rfl
      have h1 : (gateAt C j).inputs.getD 1 0 = b := by rw [hab]; rfl
      have hne_a : (support (N + N) C a).Nonempty := hSuppNe a (by omega)
      have hIncOfEval : ∀ (pW lW : ℕ),
          support (N + N) C pW ∩ M = ∅ → support (N + N) C lW ⊆ M →
          (∀ x : List Bool, x.length = N + N →
            ((C.wires x).getD (N + N + j) false = true ↔
              (∃ u ∈ support (N + N) C pW, x.getD u.val false = true) ∧
              (∃ v ∈ support (N + N) C lW, x.getD v.val false = true))) →
          ∀ u ∈ support (N + N) C pW, ∀ v ∈ support (N + N) C lW,
            ∃ (p l : Fin N), u.val = p.val ∧ v.val = N + l.val ∧ p ∈ S l := by
        intro pW lW hp0 hlM hev u hu v hv
        have hu_lt : u.val < N := by
          by_contra hge
          have huM : u ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
          exact Finset.notMem_empty u (hp0 ▸ Finset.mem_inter.mpr ⟨hu, huM⟩)
        have hv_ge : N ≤ v.val := (Finset.mem_filter.mp (hlM hv)).2
        let p : Fin N := ⟨u.val, hu_lt⟩
        let l : Fin N := ⟨v.val - N, by omega⟩
        refine ⟨p, l, rfl, by dsimp [l]; omega, ?_⟩
        by_contra hnotin
        have hfalse : IsFalseInput S {p} {l} := by
          intro l' hl'
          rw [Finset.mem_singleton.mp hl', Finset.disjoint_singleton_right]
          exact hnotin
        have h0' : C.eval (incidenceInput {p} {l}) = false := hsound {p} {l} (by simp; omega) hfalse
        have h1' : C.eval (incidenceInput {p} {l}) = true := by
          unfold Circuit.eval
          rw [hEout _ (hIncLen {p} {l})]
          refine Or.inr ⟨j, hjT, ?_⟩
          rw [hev _ (hIncLen {p} {l})]
          refine ⟨⟨u, hu, ?_⟩, ⟨v, hv, ?_⟩⟩
          · change (incidenceInput {p} {l}).getD p.val false = true
            rw [hIncAtP]; simp
          · have hveq : v.val = N + l.val := by dsimp [l]; omega
            rw [hveq, hIncAtL]; simp
        rw [h0'] at h1'; cases h1'
      rcases hsp with ⟨ha0, hbM⟩ | ⟨haM, hb0⟩
      · have hpweq : pWire j = a := by dsimp only [pWire]; rw [h0, if_pos ha0]
        have hlweq : lWire j = b := by dsimp only [lWire]; rw [h0, h1, if_pos ha0]
        have hev : ∀ x : List Bool, x.length = N + N →
            ((C.wires x).getD (N + N + j) false = true ↔
              (∃ u ∈ support (N + N) C a, x.getD u.val false = true) ∧
              (∃ v ∈ support (N + N) C b, x.getD v.val false = true)) := by
          intro x hx
          rw [hWireGate j hj x hx, hjop, hab]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, Bool.and_eq_true]
          rw [hPureEval a (by omega) (Or.inl ha0) x hx, hPureEval b (by omega) (Or.inr hbM) x hx]
        rw [hpweq, hlweq]
        exact ⟨halt, hblt, ha0, hbM, hev, hIncOfEval a b ha0 hbM hev⟩
      · have hne_inter : support (N + N) C a ∩ M ≠ ∅ := by
          obtain ⟨u, hu⟩ := hne_a
          exact Finset.nonempty_iff_ne_empty.mp ⟨u, Finset.mem_inter.mpr ⟨hu, haM hu⟩⟩
        have hpweq : pWire j = b := by dsimp only [pWire]; rw [h0, h1, if_neg hne_inter]
        have hlweq : lWire j = a := by dsimp only [lWire]; rw [h0, if_neg hne_inter]
        have hev : ∀ x : List Bool, x.length = N + N →
            ((C.wires x).getD (N + N + j) false = true ↔
              (∃ u ∈ support (N + N) C b, x.getD u.val false = true) ∧
              (∃ v ∈ support (N + N) C a, x.getD v.val false = true)) := by
          intro x hx
          rw [hWireGate j hj x hx, hjop, hab]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, Bool.and_eq_true]
          rw [hPureEval a (by omega) (Or.inr haM) x hx, hPureEval b (by omega) (Or.inl hb0) x hx, and_comm]
        rw [hpweq, hlweq]
        exact ⟨hblt, halt, hb0, haM, hev, hIncOfEval b a hb0 haM hev⟩
    have hStar : ∀ j ∈ Tout, (support (N + N) C (pWire j)).card = 1 ∨ (support (N + N) C (lWire j)).card = 1 := by
      intro j hjT
      obtain ⟨hplt, hllt, _, _, _, hinc⟩ := hPLW j hjT
      have hj := (hTout j hjT).1
      have hpne := hSuppNe (pWire j) (by omega)
      have hlne := hSuppNe (lWire j) (by omega)
      by_contra hnot
      push_neg at hnot
      have hp2 : 1 < (support (N + N) C (pWire j)).card := by
        have := Finset.card_pos.mpr hpne; omega
      have hl2 : 1 < (support (N + N) C (lWire j)).card := by
        have := Finset.card_pos.mpr hlne; omega
      obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp hp2
      obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp hl2
      obtain ⟨p1, l1, hp1, hl1, h11⟩ := hinc u1 hu1 v1 hv1
      obtain ⟨p1', l2, hp1', hl2', h12⟩ := hinc u1 hu1 v2 hv2
      obtain ⟨p2, l1', hp2', hl1', h21⟩ := hinc u2 hu2 v1 hv1
      obtain ⟨p2', l2', hp2'', hl2'', h22⟩ := hinc u2 hu2 v2 hv2
      have ep1 : p1 = p1' := Fin.ext (by omega)
      have ep2 : p2 = p2' := Fin.ext (by omega)
      have el1 : l1 = l1' := Fin.ext (by omega)
      have el2 : l2 = l2' := Fin.ext (by omega)
      subst ep1; subst ep2; subst el1; subst el2
      have hpne' : p1 ≠ p2 := fun h => hu12 (Fin.ext (by rw [hp1, hp2', h]))
      have hlne' : l1 ≠ l2 := fun h => hv12 (Fin.ext (by rw [hl1, hl2', h]))
      obtain ⟨l0, _, hl0u⟩ := huniq p1 p2 hpne'
      exact hlne' ((hl0u l1 ⟨h11, h21⟩).trans (hl0u l2 ⟨h12, h22⟩).symm)
    have hRed : ∀ (w : ℕ), ∃ r : ℕ,
        (w < N + N + C.gates.length → r ≤ w ∧ support (N + N) C r = support (N + N) C w ∧
          ((support (N + N) C w).card = 1 → r < N + N) ∧
          (2 ≤ (support (N + N) C w).card → r = w)) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases hw : w < N + N + C.gates.length
        · by_cases h1 : (support (N + N) C w).card = 1
          · by_cases hlt : w < N + N
            · exact ⟨w, fun _ => ⟨le_rfl, rfl, fun _ => hlt, fun h2 => by omega⟩⟩
            · let j := w - (N + N)
              have hj : j < C.gates.length := by omega
              have hwj : w = N + N + j := by omega
              have hjmem : gateAt C j ∈ C.gates := by
                unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
              rcases List.length_eq_two.mp (hAO.2.2 (gateAt C j) hjmem) with ⟨a, b, hab⟩
              have halt : a < w := by have := hAO.2.1 j hj a (by rw [hab]; simp); omega
              have hsw : support (N + N) C w = support (N + N) C a ∪ support (N + N) C b := by
                rw [hwj]; exact hSuppGate j hj a b hab
              have hsa_eq : support (N + N) C a = support (N + N) C w := by
                have hsub : support (N + N) C a ⊆ support (N + N) C w := hsw ▸ Finset.subset_union_left
                have hne := hSuppNe a (by omega)
                have hcle : (support (N + N) C a).card ≤ (support (N + N) C w).card := Finset.card_le_card hsub
                have hcpos := Finset.card_pos.mpr hne
                exact Finset.eq_of_subset_of_card_le hsub (by omega)
              obtain ⟨r, hr⟩ := ih a halt
              obtain ⟨hrle, hrsupp, hrlt, _⟩ := hr (by omega)
              exact ⟨r, fun _ => ⟨by omega, hrsupp.trans hsa_eq, fun _ => hrlt (by rw [hsa_eq]; exact h1), fun h2 => by omega⟩⟩
          · exact ⟨w, fun _ => ⟨le_rfl, rfl, fun h => by omega, fun _ => rfl⟩⟩
        · exact ⟨w, fun h => False.elim (hw h)⟩
    let red (w : ℕ) : ℕ := (hRed w).choose
    have hRedSpec : ∀ w < N + N + C.gates.length,
        red w ≤ w ∧ support (N + N) C (red w) = support (N + N) C w ∧
        ((support (N + N) C w).card = 1 → red w < N + N) ∧
        (2 ≤ (support (N + N) C w).card → red w = w) :=
      fun w hw => (hRed w).choose_spec hw
    have hFanCount : ∀ (W : Finset ℕ),
        (∀ w ∈ W, w < N + N + C.gates.length) →
        (W.biUnion (support (N + N) C)).card ≤ W.card +
          ((Finset.range C.gates.length).filter fun k =>
            2 ≤ (support (N + N) C (N + N + k)).card ∧
            support (N + N) C (N + N + k) ⊆ W.biUnion (support (N + N) C)).card := by
      intro W hW
      let F := W.biUnion (support (N + N) C)
      let U := (Finset.range C.gates.length).filter fun k =>
        2 ≤ (support (N + N) C (N + N + k)).card ∧ support (N + N) C (N + N + k) ⊆ F
      let children (w : ℕ) : Finset ℕ :=
        if N + N ≤ w then
          {red ((gateAt C (w - (N + N))).inputs.getD 0 0),
           red ((gateAt C (w - (N + N))).inputs.getD 1 0)}
        else ∅
      let step (X : Finset ℕ) : Finset ℕ := X ∪ X.biUnion children
      let B := N + N + C.gates.length
      have hStepSub : ∀ X : Finset ℕ, X ⊆ Finset.range B → step X ⊆ Finset.range B := by
        intro X hX z hz
        rcases Finset.mem_union.mp hz with hzx | hzc
        · exact hX hzx
        · obtain ⟨w, hwX, hzw⟩ := Finset.mem_biUnion.mp hzc
          have hwB : w < B := Finset.mem_range.mp (hX hwX)
          dsimp only [children] at hzw
          split_ifs at hzw with hge
          · let k := w - (N + N)
            have hk : k < C.gates.length := by omega
            have hkmem : gateAt C k ∈ C.gates := by
              unfold gateAt; simp [List.getD_eq_getElem?_getD, hk]
            rcases List.length_eq_two.mp (hAO.2.2 (gateAt C k) hkmem) with ⟨a, b, hab⟩
            have h0 : (gateAt C k).inputs.getD 0 0 = a := by rw [hab]; rfl
            have h1 : (gateAt C k).inputs.getD 1 0 = b := by rw [hab]; rfl
            have halt : a < N + N + k := hAO.2.1 k hk a (by rw [hab]; simp)
            have hblt : b < N + N + k := hAO.2.1 k hk b (by rw [hab]; simp)
            rw [Finset.mem_insert, Finset.mem_singleton] at hzw
            rcases hzw with rfl | rfl
            · rw [h0]; have := (hRedSpec a (by omega)).1; exact Finset.mem_range.mpr (by omega)
            · rw [h1]; have := (hRedSpec b (by omega)).1; exact Finset.mem_range.mpr (by omega)
          · exact False.elim (Finset.notMem_empty z hzw)
      have hStepInv : ∀ X : Finset ℕ,
          (∀ w ∈ X, w < B ∧ support (N + N) C w ⊆ F ∧ (N + N ≤ w → 2 ≤ (support (N + N) C w).card)) →
          ∀ w ∈ step X, w < B ∧ support (N + N) C w ⊆ F ∧ (N + N ≤ w → 2 ≤ (support (N + N) C w).card) := by
        intro X hX z hz
        rcases Finset.mem_union.mp hz with hzx | hzc
        · exact hX z hzx
        · obtain ⟨w, hwX, hzw⟩ := Finset.mem_biUnion.mp hzc
          obtain ⟨hwB, hwF, _⟩ := hX w hwX
          dsimp only [children] at hzw
          split_ifs at hzw with hge
          · let k := w - (N + N)
            have hk : k < C.gates.length := by omega
            have hwk : w = N + N + k := by omega
            have hkmem : gateAt C k ∈ C.gates := by
              unfold gateAt; simp [List.getD_eq_getElem?_getD, hk]
            rcases List.length_eq_two.mp (hAO.2.2 (gateAt C k) hkmem) with ⟨a, b, hab⟩
            have h0 : (gateAt C k).inputs.getD 0 0 = a := by rw [hab]; rfl
            have h1 : (gateAt C k).inputs.getD 1 0 = b := by rw [hab]; rfl
            have halt : a < N + N + k := hAO.2.1 k hk a (by rw [hab]; simp)
            have hblt : b < N + N + k := hAO.2.1 k hk b (by rw [hab]; simp)
            have hsw : support (N + N) C w = support (N + N) C a ∪ support (N + N) C b := by
              rw [hwk]; exact hSuppGate k hk a b hab
            rw [Finset.mem_insert, Finset.mem_singleton] at hzw
            rcases hzw with rfl | rfl
            · rw [h0]
              obtain ⟨hrle, hrsupp, hrlt, _⟩ := hRedSpec a (by omega)
              refine ⟨by omega, hrsupp ▸ Finset.subset_union_left.trans (hsw ▸ hwF), fun hge' => ?_⟩
              have hne := hSuppNe a (by omega)
              have hcpos := Finset.card_pos.mpr hne
              by_contra hlt2
              rw [hrsupp] at hlt2
              have hc1 : (support (N + N) C a).card = 1 := by omega
              have := hrlt hc1
              omega
            · rw [h1]
              obtain ⟨hrle, hrsupp, hrlt, _⟩ := hRedSpec b (by omega)
              refine ⟨by omega, hrsupp ▸ Finset.subset_union_right.trans (hsw ▸ hwF), fun hge' => ?_⟩
              have hne := hSuppNe b (by omega)
              have hcpos := Finset.card_pos.mpr hne
              by_contra hlt2
              rw [hrsupp] at hlt2
              have hc1 : (support (N + N) C b).card = 1 := by omega
              have := hrlt hc1
              omega
          · exact False.elim (Finset.notMem_empty z hzw)
      let X0 := W.image red
      have hX0 : ∀ w ∈ X0, w < B ∧ support (N + N) C w ⊆ F ∧ (N + N ≤ w → 2 ≤ (support (N + N) C w).card) := by
        intro w hw
        obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.mp hw
        have hw0B : w0 < B := hW w0 hw0
        obtain ⟨hrle, hrsupp, hrlt, _⟩ := hRedSpec w0 hw0B
        refine ⟨by omega, hrsupp ▸ Finset.subset_biUnion_of_mem (support (N + N) C) hw0, fun hge' => ?_⟩
        have hcpos := Finset.card_pos.mpr (hSuppNe w0 hw0B)
        by_contra hlt2
        rw [hrsupp] at hlt2
        have hc1 : (support (N + N) C w0).card = 1 := by omega
        have := hrlt hc1
        omega
      let seq (t : ℕ) : Finset ℕ := step^[t] X0
      have hSeqInv : ∀ t w, w ∈ seq t → w < B ∧ support (N + N) C w ⊆ F ∧ (N + N ≤ w → 2 ≤ (support (N + N) C w).card) := by
        intro t
        induction t with
        | zero => exact hX0
        | succ t ih =>
          intro w hw
          have : seq (t + 1) = step (seq t) := Function.iterate_succ_apply' step t X0
          rw [this] at hw
          exact hStepInv (seq t) ih w hw
      have hFix : ∃ t, step (seq t) = seq t := by
        by_contra hno
        push_neg at hno
        have hInc : ∀ t, (seq t).card + 1 ≤ (seq (t + 1)).card := by
          intro t
          have hsub : seq t ⊆ seq (t + 1) := by
            have : seq (t + 1) = step (seq t) := Function.iterate_succ_apply' step t X0
            rw [this]; exact Finset.subset_union_left
          have hssub : seq t ⊂ seq (t + 1) := by
            rw [Finset.ssubset_iff_subset_ne]
            exact ⟨hsub, fun heq => hno t (by rw [← Function.iterate_succ_apply' step t X0, heq])⟩
          exact Finset.card_lt_card hssub
        have hGrow : ∀ t, t ≤ (seq t).card := by
          intro t
          induction t with
          | zero => omega
          | succ t ih => have := hInc t; omega
        have hBound : (seq (B + 1)).card ≤ B := by
          have hsub : seq (B + 1) ⊆ Finset.range B := fun w hw => Finset.mem_range.mpr (hSeqInv (B + 1) w hw).1
          exact (Finset.card_le_card hsub).trans (by simp)
        have := hGrow (B + 1)
        omega
      obtain ⟨t0, ht0⟩ := hFix
      let Reach := seq t0
      have hX0Sub : X0 ⊆ Reach := by
        suffices h : ∀ t, X0 ⊆ seq t from h t0
        intro t
        induction t with
        | zero => exact Finset.Subset.refl _
        | succ t ih =>
          have : seq (t + 1) = step (seq t) := Function.iterate_succ_apply' step t X0
          rw [this]; exact ih.trans Finset.subset_union_left
      have hReachStep : ∀ w ∈ Reach, children w ⊆ Reach := by
        intro w hw z hz
        have : z ∈ step Reach := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw, hz⟩)
        rwa [ht0] at this
      have hReachCover : ∀ w ∈ Reach, ∀ u ∈ support (N + N) C w, u.val ∈ Reach := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw u hu
          have hwB := (hSeqInv t0 w hw).1
          by_cases hlt : w < N + N
          · rw [hSuppInput w hlt] at hu
            have hueq : u = ⟨w, hlt⟩ := Finset.mem_singleton.mp hu
            rw [hueq]; exact hw
          · let k := w - (N + N)
            have hk : k < C.gates.length := by omega
            have hwk : w = N + N + k := by omega
            have hkmem : gateAt C k ∈ C.gates := by
              unfold gateAt; simp [List.getD_eq_getElem?_getD, hk]
            rcases List.length_eq_two.mp (hAO.2.2 (gateAt C k) hkmem) with ⟨a, b, hab⟩
            have h0 : (gateAt C k).inputs.getD 0 0 = a := by rw [hab]; rfl
            have h1 : (gateAt C k).inputs.getD 1 0 = b := by rw [hab]; rfl
            have halt : a < w := by have := hAO.2.1 k hk a (by rw [hab]; simp); omega
            have hblt : b < w := by have := hAO.2.1 k hk b (by rw [hab]; simp); omega
            have hsw : support (N + N) C w = support (N + N) C a ∪ support (N + N) C b := by
              rw [hwk]; exact hSuppGate k hk a b hab
            have hra : red a ∈ Reach := by
              apply hReachStep w hw
              dsimp only [children]
              rw [if_pos (by omega), h0]
              exact Finset.mem_insert_self _ _
            have hrb : red b ∈ Reach := by
              apply hReachStep w hw
              dsimp only [children]
              rw [if_pos (by omega), h1]
              exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            rw [hsw, Finset.mem_union] at hu
            rcases hu with hua | hub
            · obtain ⟨hrle, hrsupp, _, _⟩ := hRedSpec a (by omega)
              exact ih (red a) (by omega) hra u (hrsupp.symm ▸ hua)
            · obtain ⟨hrle, hrsupp, _, _⟩ := hRedSpec b (by omega)
              exact ih (red b) (by omega) hrb u (hrsupp.symm ▸ hub)
      let ReachIn := Reach.filter fun w => w < N + N
      let ReachG := Reach.filter fun w => N + N ≤ w
      have hPart : Reach.card = ReachIn.card + ReachG.card := by
        have h1 : ReachIn ∪ ReachG = Reach := by
          ext w; simp only [ReachIn, ReachG, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h; by_cases hlt : w < N + N
            · exact Or.inl ⟨h, hlt⟩
            · exact Or.inr ⟨h, by omega⟩
        have hdisj : Disjoint ReachIn ReachG := by
          rw [Finset.disjoint_left]
          intro w h1 h2
          have := (Finset.mem_filter.mp h1).2
          have := (Finset.mem_filter.mp h2).2
          omega
        rw [← h1, Finset.card_union_of_disjoint hdisj]
      have hReachSub : Reach ⊆ X0 ∪ ReachG.biUnion children := by
        suffices h : ∀ t, seq t ⊆ X0 ∪ (seq t).biUnion children by
          have h1 := h t0
          intro z hz
          rcases Finset.mem_union.mp (h1 hz) with hz0 | hzc
          · exact Finset.mem_union_left _ hz0
          · obtain ⟨w, hwR, hzw⟩ := Finset.mem_biUnion.mp hzc
            dsimp only [children] at hzw
            split_ifs at hzw with hge
            · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hwR, hge⟩, by
                dsimp only [children]; rw [if_pos hge]; exact hzw⟩)
            · exact False.elim (Finset.notMem_empty z hzw)
        intro t
        induction t with
        | zero => exact Finset.subset_union_left
        | succ t ih =>
          have hst : seq (t + 1) = step (seq t) := Function.iterate_succ_apply' step t X0
          rw [hst]
          intro z hz
          rcases Finset.mem_union.mp hz with hzt | hzc
          · rcases Finset.mem_union.mp (ih hzt) with hz0 | hzc'
            · exact Finset.mem_union_left _ hz0
            · obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.mp hzc'
              exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, Finset.mem_union_left _ hw, hzw⟩)
          · obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.mp hzc
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, Finset.mem_union_left _ hw, hzw⟩)
      have hReachCard : Reach.card ≤ X0.card + 2 * ReachG.card := by
        calc Reach.card ≤ (X0 ∪ ReachG.biUnion children).card := Finset.card_le_card hReachSub
          _ ≤ X0.card + (ReachG.biUnion children).card := Finset.card_union_le _ _
          _ ≤ X0.card + ∑ w ∈ ReachG, (children w).card := by
              have := Finset.card_biUnion_le (s := ReachG) (t := children)
              omega
          _ ≤ X0.card + ∑ _w ∈ ReachG, 2 := by
              have hle : ∑ w ∈ ReachG, (children w).card ≤ ∑ _w ∈ ReachG, 2 := by
                apply Finset.sum_le_sum
                intro w _
                dsimp only [children]
                split_ifs
                · exact Finset.card_le_two
                · simp
              omega
          _ = X0.card + 2 * ReachG.card := by simp [Nat.mul_comm]
      have hX0Card : X0.card ≤ W.card := Finset.card_image_le
      have hReachG_U : ReachG.card ≤ U.card := by
        have hsub : ReachG.image (fun w => w - (N + N)) ⊆ U := by
          intro k hk
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
          obtain ⟨hwR, hge⟩ := Finset.mem_filter.mp hw
          obtain ⟨hwB, hwF, hw2⟩ := hSeqInv t0 w hwR
          have hwk : N + N + (w - (N + N)) = w := by omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hwk.symm ▸ hw2 hge, hwk.symm ▸ hwF⟩
        have hinj : Set.InjOn (fun w => w - (N + N)) (ReachG : Set ℕ) := by
          intro w1 hw1 w2 hw2 heq
          have h1 := (Finset.mem_filter.mp hw1).2
          have h2 := (Finset.mem_filter.mp hw2).2
          dsimp only at heq
          omega
        calc ReachG.card = (ReachG.image (fun w => w - (N + N))).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ U.card := Finset.card_le_card hsub
      have hF_In : F.card ≤ ReachIn.card := by
        have hsub : F.image Fin.val ⊆ ReachIn := by
          intro v hv
          obtain ⟨u, huF, rfl⟩ := Finset.mem_image.mp hv
          obtain ⟨w, hwW, huw⟩ := Finset.mem_biUnion.mp huF
          have hrw : red w ∈ Reach := hX0Sub (Finset.mem_image_of_mem red hwW)
          have hrsupp := (hRedSpec w (hW w hwW)).2.1
          exact Finset.mem_filter.mpr ⟨hReachCover (red w) hrw u (hrsupp.symm ▸ huw), u.isLt⟩
        calc F.card = (F.image Fin.val).card := (Finset.card_image_of_injective F Fin.val_injective).symm
          _ ≤ ReachIn.card := Finset.card_le_card hsub
      change F.card ≤ W.card + U.card
      omega
    let TP := Tout.filter fun j => (support (N + N) C (pWire j)).card = 1
    let TL := Tout.filter fun j => (support (N + N) C (pWire j)).card ≠ 1
    let AP (p : Fin N) : Finset ℕ := TP.filter fun j => Fin.castAdd N p ∈ support (N + N) C (pWire j)
    let AL (l : Fin N) : Finset ℕ := TL.filter fun j => Fin.natAdd N l ∈ support (N + N) C (lWire j)
    let UP (p : Fin N) : Finset ℕ := (Finset.range C.gates.length).filter fun k =>
      2 ≤ (support (N + N) C (N + N + k)).card ∧
      support (N + N) C (N + N + k) ⊆ M ∧
      ∀ v ∈ support (N + N) C (N + N + k), ∃ l : Fin N, v.val = N + l.val ∧ p ∈ S l
    let UL (l : Fin N) : Finset ℕ := (Finset.range C.gates.length).filter fun k =>
      2 ≤ (support (N + N) C (N + N + k)).card ∧
      support (N + N) C (N + N + k) ∩ M = ∅ ∧
      ∀ u ∈ support (N + N) C (N + N + k), ∃ p : Fin N, u.val = p.val ∧ p ∈ S l
    let EP (p : Fin N) : Finset (Fin (N + N)) := ((AP p).image lWire).biUnion (support (N + N) C)
    let EL (l : Fin N) : Finset (Fin (N + N)) := ((AL l).image pWire).biUnion (support (N + N) C)
    have hEP_le : ∀ p : Fin N, (EP p).card ≤ (AP p).card + (UP p).card := by
      intro p
      have hW : ∀ w ∈ (AP p).image lWire, w < N + N + C.gates.length := by
        intro w hw
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
        have h1 := (hTout j hjT).1
        have h2 := (hPLW j hjT).2.1
        omega
      have hfc := hFanCount ((AP p).image lWire) hW
      have hsub : ((Finset.range C.gates.length).filter fun k =>
          2 ≤ (support (N + N) C (N + N + k)).card ∧
          support (N + N) C (N + N + k) ⊆ EP p) ⊆ UP p := by
        intro k hk
        obtain ⟨hkr, hk2, hksub⟩ := Finset.mem_filter.mp hk
        refine Finset.mem_filter.mpr ⟨hkr, hk2, ?_, ?_⟩
        · intro v hv
          obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp (hksub hv)
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
          have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
          exact (hPLW j hjT).2.2.2.1 hvw
        · intro v hv
          obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp (hksub hv)
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
          have hjP := (Finset.mem_filter.mp hj).2
          have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
          obtain ⟨p', l, hp', hl', hpl⟩ := (hPLW j hjT).2.2.2.2.2 (Fin.castAdd N p) hjP v hvw
          have hpeq : p = p' := Fin.ext (by simpa using hp')
          subst hpeq
          exact ⟨l, hl', hpl⟩
      have hcard1 : ((AP p).image lWire).card ≤ (AP p).card := Finset.card_image_le
      have hcard2 := Finset.card_le_card hsub
      dsimp only [EP] at hcard2 ⊢
      omega
    have hEL_le : ∀ l : Fin N, (EL l).card ≤ (AL l).card + (UL l).card := by
      intro l
      have hW : ∀ w ∈ (AL l).image pWire, w < N + N + C.gates.length := by
        intro w hw
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
        have h1 := (hTout j hjT).1
        have h2 := (hPLW j hjT).1
        omega
      have hfc := hFanCount ((AL l).image pWire) hW
      have hsub : ((Finset.range C.gates.length).filter fun k =>
          2 ≤ (support (N + N) C (N + N + k)).card ∧
          support (N + N) C (N + N + k) ⊆ EL l) ⊆ UL l := by
        intro k hk
        obtain ⟨hkr, hk2, hksub⟩ := Finset.mem_filter.mp hk
        refine Finset.mem_filter.mpr ⟨hkr, hk2, ?_, ?_⟩
        · rw [Finset.eq_empty_iff_forall_notMem]
          intro u hu
          obtain ⟨hu1, huM⟩ := Finset.mem_inter.mp hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.mp (hksub hu1)
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
          have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
          exact Finset.notMem_empty u ((hPLW j hjT).2.2.1 ▸ Finset.mem_inter.mpr ⟨huw, huM⟩)
        · intro u hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.mp (hksub hu)
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
          have hjL := (Finset.mem_filter.mp hj).2
          have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
          obtain ⟨p, l', hp', hl', hpl⟩ := (hPLW j hjT).2.2.2.2.2 u huw (Fin.natAdd N l) hjL
          have hleq : l = l' := Fin.ext (by
            simp only [Fin.val_natAdd] at hl'
            omega)
          subst hleq
          exact ⟨p, hp', hpl⟩
      have hcard1 : ((AL l).image pWire).card ≤ (AL l).card := Finset.card_image_le
      have hcard2 := Finset.card_le_card hsub
      dsimp only [EL] at hcard2 ⊢
      omega
    have hDisjAP : ∀ p1 p2 : Fin N, p1 ≠ p2 → Disjoint (AP p1) (AP p2) := by
      intro p1 p2 hne
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have hc1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hj1).1).2
      have hm1 := (Finset.mem_filter.mp hj1).2
      have hm2 := (Finset.mem_filter.mp hj2).2
      have heq := Finset.card_le_one.mp (by omega : (support (N + N) C (pWire j)).card ≤ 1) _ hm1 _ hm2
      exact hne (Fin.ext (by simpa using congrArg Fin.val heq))
    have hDisjAL : ∀ l1 l2 : Fin N, l1 ≠ l2 → Disjoint (AL l1) (AL l2) := by
      intro l1 l2 hne
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have hjTL := (Finset.mem_filter.mp hj1).1
      have hjT := (Finset.mem_filter.mp hjTL).1
      have hne1 := (Finset.mem_filter.mp hjTL).2
      have hc1 : (support (N + N) C (lWire j)).card = 1 := (hStar j hjT).resolve_left hne1
      have hm1 := (Finset.mem_filter.mp hj1).2
      have hm2 := (Finset.mem_filter.mp hj2).2
      have heq := Finset.card_le_one.mp (by omega : (support (N + N) C (lWire j)).card ≤ 1) _ hm1 _ hm2
      have hval := congrArg Fin.val heq
      simp only [Fin.val_natAdd] at hval
      exact hne (Fin.ext (by omega))
    have hDisjUP : ∀ p1 p2 : Fin N, p1 ≠ p2 → Disjoint (UP p1) (UP p2) := by
      intro p1 p2 hne
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      obtain ⟨_, hk2c, _, h1⟩ := Finset.mem_filter.mp hk1
      obtain ⟨_, _, _, h2⟩ := Finset.mem_filter.mp hk2
      obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp (by omega : 1 < (support (N + N) C (N + N + k)).card)
      obtain ⟨l1, hl1, hp1l1⟩ := h1 v1 hv1
      obtain ⟨l2, hl2, hp1l2⟩ := h1 v2 hv2
      obtain ⟨l1', hl1', hp2l1⟩ := h2 v1 hv1
      obtain ⟨l2', hl2', hp2l2⟩ := h2 v2 hv2
      have e1 : l1 = l1' := Fin.ext (by omega)
      have e2 : l2 = l2' := Fin.ext (by omega)
      subst e1; subst e2
      have hlne : l1 ≠ l2 := fun h => hv12 (Fin.ext (by rw [hl1, hl2, h]))
      obtain ⟨l0, _, hl0u⟩ := huniq p1 p2 hne
      exact hlne ((hl0u l1 ⟨hp1l1, hp2l1⟩).trans (hl0u l2 ⟨hp1l2, hp2l2⟩).symm)
    have hDisjUL : ∀ l1 l2 : Fin N, l1 ≠ l2 → Disjoint (UL l1) (UL l2) := by
      intro l1 l2 hne
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      obtain ⟨_, hk2c, _, h1⟩ := Finset.mem_filter.mp hk1
      obtain ⟨_, _, _, h2⟩ := Finset.mem_filter.mp hk2
      obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp (by omega : 1 < (support (N + N) C (N + N + k)).card)
      obtain ⟨p1, hp1, hp1l1⟩ := h1 u1 hu1
      obtain ⟨p2, hp2, hp2l1⟩ := h1 u2 hu2
      obtain ⟨p1', hp1', hp1l2⟩ := h2 u1 hu1
      obtain ⟨p2', hp2', hp2l2⟩ := h2 u2 hu2
      have e1 : p1 = p1' := Fin.ext (by omega)
      have e2 : p2 = p2' := Fin.ext (by omega)
      subst e1; subst e2
      have hpne : p1 ≠ p2 := fun h => hu12 (Fin.ext (by rw [hp1, hp2, h]))
      obtain ⟨l0, _, hl0u⟩ := huniq p1 p2 hpne
      exact hne ((hl0u l1 ⟨hp1l1, hp2l1⟩).trans (hl0u l2 ⟨hp1l2, hp2l2⟩).symm)
    let GP := Finset.univ.biUnion AP
    let GLines := Finset.univ.biUnion AL
    let GUP := Finset.univ.biUnion UP
    let GUL := Finset.univ.biUnion UL
    have hSumAP : GP.card = ∑ p : Fin N, (AP p).card :=
      Finset.card_biUnion (fun p1 _ p2 _ hne => hDisjAP p1 p2 hne)
    have hSumAL : GLines.card = ∑ l : Fin N, (AL l).card :=
      Finset.card_biUnion (fun l1 _ l2 _ hne => hDisjAL l1 l2 hne)
    have hSumUP : GUP.card = ∑ p : Fin N, (UP p).card :=
      Finset.card_biUnion (fun p1 _ p2 _ hne => hDisjUP p1 p2 hne)
    have hSumUL : GUL.card = ∑ l : Fin N, (UL l).card :=
      Finset.card_biUnion (fun l1 _ l2 _ hne => hDisjUL l1 l2 hne)
    have hDisj_GP_GL : Disjoint GP GLines := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h1
      obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp h2
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2 (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hDisj_GUP_GUL : Disjoint GUP GUL := by
      rw [Finset.disjoint_left]
      intro k h1 h2
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h1
      obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp h2
      have hklt := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      obtain ⟨u, hu⟩ := hSuppNe (N + N + k) (by omega)
      have huM := (Finset.mem_filter.mp hp).2.2.1 hu
      have hu0 := (Finset.mem_filter.mp hl).2.2.1
      exact Finset.notMem_empty u (hu0 ▸ Finset.mem_inter.mpr ⟨hu, huM⟩)
    have hDisj_A_U : Disjoint (GP ∪ GLines) (GUP ∪ GUL) := by
      rw [Finset.disjoint_left]
      intro j hA hU
      have hjAnd : j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
        rcases Finset.mem_union.mp hA with h1 | h2
        · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h1
          exact hTout j (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp h2
          exact hTout j (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1
      obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hAndMixed j hjAnd.1 hjAnd.2
      rcases Finset.mem_union.mp hU with h1 | h2
      · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h1
        have hsub := (Finset.mem_filter.mp hp).2.2.1
        exact (Finset.mem_sdiff.mp hv).2 (hsub (Finset.mem_sdiff.mp hv).1)
      · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp h2
        have h0 := (Finset.mem_filter.mp hl).2.2.1
        exact Finset.notMem_empty u (h0 ▸ hu)
    have hTotalGates : GP.card + GLines.card + GUP.card + GUL.card ≤ C.gates.length := by
      have hsub : (GP ∪ GLines) ∪ (GUP ∪ GUL) ⊆ Finset.range C.gates.length := by
        intro j hj
        rcases Finset.mem_union.mp hj with hA | hU
        · rcases Finset.mem_union.mp hA with h1 | h2
          · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h1
            exact Finset.mem_range.mpr (hTout j (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
          · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp h2
            exact Finset.mem_range.mpr (hTout j (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1).1
        · rcases Finset.mem_union.mp hU with h1 | h2
          · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h1
            exact (Finset.mem_filter.mp hp).1
          · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp h2
            exact (Finset.mem_filter.mp hl).1
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hDisj_A_U, Finset.card_union_of_disjoint hDisj_GP_GL,
          Finset.card_union_of_disjoint hDisj_GUP_GUL, Finset.card_range] at hc
      omega
    let IncPairs : Finset (Fin N × Fin N) := Finset.univ.filter fun e => e.1 ∈ S e.2
    have hIncCount : IncPairs.card = N * (q + 1) := by
      have h1 : IncPairs = Finset.univ.biUnion fun l : Fin N => (S l).image fun p => (p, l) := by
        ext ⟨p, l⟩
        simp [IncPairs]
      rw [h1, Finset.card_biUnion]
      · simp only [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h : Function.Injective fun p : Fin N => (p, _)),
          hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      · intro l1 _ l2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro e he1 he2
        obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp he1
        obtain ⟨p2, _, heq⟩ := Finset.mem_image.mp he2
        exact hne (congrArg Prod.snd heq).symm
    let fP (p : Fin N) (v : Fin (N + N)) : Finset (Fin N × Fin N) :=
      if h : N ≤ v.val then {(p, ⟨v.val - N, by omega⟩)} else ∅
    let fL (l : Fin N) (u : Fin (N + N)) : Finset (Fin N × Fin N) :=
      if h : u.val < N then {(⟨u.val, h⟩, l)} else ∅
    let CovP : Finset (Fin N × Fin N) := Finset.univ.biUnion fun p : Fin N => (EP p).biUnion (fP p)
    let CovL : Finset (Fin N × Fin N) := Finset.univ.biUnion fun l : Fin N => (EL l).biUnion (fL l)
    have hCov : IncPairs ⊆ CovP ∪ CovL := by
      intro ⟨p, l⟩ hpl
      have hpSl : p ∈ S l := (Finset.mem_filter.mp hpl).2
      have heval : C.eval (incidenceInput {p} {l}) = true := hright l p hpSl
      unfold Circuit.eval at heval
      rw [hEout _ (hIncLen {p} {l}), hIoutEmpty] at heval
      simp only [Finset.notMem_empty, false_and, exists_false, false_or] at heval
      obtain ⟨j, hjT, hjval⟩ := heval
      obtain ⟨_, _, hp0, hlM, hevj, _⟩ := hPLW j hjT
      obtain ⟨⟨u, hu, hxu⟩, ⟨v, hv, hxv⟩⟩ := (hevj _ (hIncLen {p} {l})).mp hjval
      have hu_lt : u.val < N := by
        by_contra hge
        exact Finset.notMem_empty u (hp0 ▸ Finset.mem_inter.mpr ⟨hu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
      have hv_ge : N ≤ v.val := (Finset.mem_filter.mp (hlM hv)).2
      have hup : u = Fin.castAdd N p := by
        have : (incidenceInput {p} {l}).getD (⟨u.val, hu_lt⟩ : Fin N).val false = true := hxu
        rw [hIncAtP] at this
        simp only [decide_eq_true_eq, Finset.mem_singleton] at this
        exact Fin.ext (by simpa using congrArg Fin.val this)
      have hvl : v = Fin.natAdd N l := by
        let l' : Fin N := ⟨v.val - N, by omega⟩
        have hveq : v.val = N + l'.val := by dsimp [l']; omega
        rw [hveq, hIncAtL] at hxv
        simp only [decide_eq_true_eq, Finset.mem_singleton] at hxv
        exact Fin.ext (by rw [hveq, hxv]; simp; omega)
      subst hup; subst hvl
      by_cases h1 : (support (N + N) C (pWire j)).card = 1
      · apply Finset.mem_union_left
        refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨Fin.natAdd N l, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨lWire j, Finset.mem_image_of_mem lWire
            (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hjT, h1⟩, hu⟩), hv⟩
        · dsimp only [fP]
          simp only [Fin.val_natAdd, le_add_iff_nonneg_right, zero_le, ↓reduceDIte, Finset.mem_singleton]
          exact Prod.ext rfl (Fin.ext (by simp))
      · apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨Fin.castAdd N p, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨pWire j, Finset.mem_image_of_mem pWire
            (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hjT, h1⟩, hv⟩), hu⟩
        · dsimp only [fL]
          simp only [Fin.val_castAdd, p.isLt, ↓reduceDIte, Finset.mem_singleton]
    have hCovP_card : CovP.card ≤ ∑ p : Fin N, (EP p).card := by
      have h1 : CovP.card ≤ ∑ p : Fin N, ((EP p).biUnion (fP p)).card :=
        Finset.card_biUnion_le (s := Finset.univ) (t := fun p : Fin N => (EP p).biUnion (fP p))
      have h2 : ∑ p : Fin N, ((EP p).biUnion (fP p)).card ≤ ∑ p : Fin N, (EP p).card := by
        apply Finset.sum_le_sum
        intro p _
        have h3 : ((EP p).biUnion (fP p)).card ≤ ∑ v ∈ EP p, (fP p v).card :=
          Finset.card_biUnion_le (s := EP p) (t := fP p)
        have h4 : ∑ v ∈ EP p, (fP p v).card ≤ ∑ _v ∈ EP p, 1 := by
          apply Finset.sum_le_sum
          intro v _
          dsimp only [fP]
          split_ifs <;> simp
        simp only [Finset.sum_const, smul_eq_mul, mul_one] at h4
        omega
      omega
    have hCovL_card : CovL.card ≤ ∑ l : Fin N, (EL l).card := by
      have h1 : CovL.card ≤ ∑ l : Fin N, ((EL l).biUnion (fL l)).card :=
        Finset.card_biUnion_le (s := Finset.univ) (t := fun l : Fin N => (EL l).biUnion (fL l))
      have h2 : ∑ l : Fin N, ((EL l).biUnion (fL l)).card ≤ ∑ l : Fin N, (EL l).card := by
        apply Finset.sum_le_sum
        intro l _
        have h3 : ((EL l).biUnion (fL l)).card ≤ ∑ u ∈ EL l, (fL l u).card :=
          Finset.card_biUnion_le (s := EL l) (t := fL l)
        have h4 : ∑ u ∈ EL l, (fL l u).card ≤ ∑ _u ∈ EL l, 1 := by
          apply Finset.sum_le_sum
          intro u _
          dsimp only [fL]
          split_ifs <;> simp
        simp only [Finset.sum_const, smul_eq_mul, mul_one] at h4
        omega
      omega
    have hSumEP : ∑ p : Fin N, (EP p).card ≤ GP.card + GUP.card := by
      rw [hSumAP, hSumUP, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun p _ => hEP_le p
    have hSumEL : ∑ l : Fin N, (EL l).card ≤ GLines.card + GUL.card := by
      rw [hSumAL, hSumUL, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun l _ => hEL_le l
    have hMain : N * (q + 1) ≤ C.gates.length := by
      have h1 := Finset.card_le_card hCov
      have h2 := Finset.card_union_le CovP CovL
      rw [hIncCount] at h1
      omega
    have hNq : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
    change N * q ≤ 100 * C.gates.length
    omega
  · by_cases hfew : cc ≤ q
    · exact fewCross q N S C hq hN hcard huniq hAO hout hright hsound
        (show 1 ≤ cc by omega) hfew (show 100 * cc < N * q by omega)
    · exact manyCross q N S C hq hN hcard huniq hAO hout hright hsound
        (show q < cc by omega) (show 100 * cc < N * q by omega)
