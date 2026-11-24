import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.ReadK

-- Count the selected pairs in a circuit using only their active gates.
-- After the two single-read bounds, twenty-four pairs per active gate remain for double rereads.
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_3686_671
    (active : ∀ (N : ℕ) (C : Circuit) (T : Fin N → Finset (Fin N)),
      let edge (p l : Fin N) := pairInput (Fin.castAdd N p) (Fin.natAdd N l)
      Monotone2 C → circuitFun (N + N) C (fun _ => false) = false →
      (∃ l p, p ∈ T l) → (∀ l p, p ∈ T l → circuitFun (N + N) C (edge p l) = true) →
      ∃ D : Circuit, IsAO2 (N + N) D ∧
        D.size ≤ Fintype.card {j : Fin C.size //
          (C.wires (List.replicate (N + N) false)).getD (N + N + j.val) false = false ∧
          ∃ l p, p ∈ T l ∧ gateVal (N + N) C j.val (edge p l) = true} ∧
        (∀ z, circuitFun (N + N) D z = true → circuitFun (N + N) C z = true) ∧
        ∀ l p, p ∈ T l → circuitFun (N + N) D (edge p l) = true)
    (lines : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), Fintype.card { x8 : Fin x1 // x7 (Fin.natAdd x1 x8) = Bool.true } ≤ (1 : ℕ) → (¬∃ (x9 : Fin x1) (x10 : Fin x1), x2 x9 x10 ∧ x7 (Fin.castAdd x1 x9) = Bool.true ∧ x7 (Fin.natAdd x1 x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Bool.false) → Fintype.card { x8 : Fin x1 × Fin x1 // x2 x8.1 x8.2 ∧ PEqualNP.ReadK.lineSingle x4 (x1 + x1) (fun (x9 : ℕ) => Decidable.decide (x1 ≤ x9)) (↑x8.1) (x1 + ↑x8.2) = Bool.true } ≤ (10 : ℕ) * x4.size)
    (points : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (10 : ℕ) * x5.size)
    (double : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
      22 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      IsAO2 (N + N) D →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) D z = false) →
      ∀ E : Finset (Fin N × Fin N),
        (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N + N) D
          (pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)) = true ∧
          lineSingle D (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
          lineSingle D (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false) →
        E.card ≤ 24 * D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 = (x1 * x1 + x1).succ →     (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →       (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →         PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →           have x10 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x10 : Finset (Fin x2)) (x11 : Fin (x2 + x2)) => Fin.addCases (fun (x12 : Fin x2) => Decidable.decide ¬∃ x13 ∈ x10, x3 x12 x13) (fun (x12 : Fin x2) => Decidable.decide (x12 ∈ x10)) x11;           (∀ (x11 : Finset (Fin x2)), x11.card ≤ x1 → x5.eval (List.ofFn (x10 x11)) = Bool.false) →             have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };             have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x2 x13) (Fin.natAdd x2 x14);             ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ x5.eval (List.ofFn (x13 x16 x15)) = Bool.true ∧ x12.eval (List.ofFn (x13 x16 x15)) = Bool.false) → (22 : ℕ) * Fintype.card { x16 : Fin x2 // (x14 x16).Nonempty } < ∑ x16 : Fin x2, (x14 x16).card → ∑ x17 : Fin x2, (x14 x17).card ≤ (44 : ℕ) * Fintype.card { x17 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x17) Bool.false = Bool.false ∧ ∃ (x18 : Fin x2), ∃ x19 ∈ x14 x18, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 (↑x17) (x13 x19 x18) = Bool.true } := by
  classical
  intro q N I instI C hN hcol huniq hmin maxInput maximal pruned edge T hT hdense
  let n : ℕ := N + N
  have hmono : Monotone2 C := hmin.1
  let runW : List Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_nil : ∀ x, runW [] x = x := fun _ => rfl
  have hrun_snoc : ∀ gs g x, runW (gs ++ [g]) x =
      runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)] := by
    intro gs g x
    simp [runW]
  have hrun_append : ∀ g1 g2 x, runW (g1 ++ g2) x = runW g2 (runW g1 x) := by
    intro g1 g2 x
    simp [runW]
  have hrun_len : ∀ gs x, (runW gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [runW]
    | append_singleton gs g ih =>
      rw [hrun_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
      omega
  have hrun_prefix_getD : ∀ g1 g2 x i, i < x.length + g1.length →
      (runW (g1 ++ g2) x).getD i false = (runW g1 x).getD i false := by
    intro g1 g2 x i hi
    induction g2 using List.reverseRecOn with
    | nil => simp
    | append_singleton g2 g ih =>
      rw [← List.append_assoc, hrun_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left]
      · rw [← List.getD_eq_getElem?_getD]
        exact ih
      · rw [hrun_len, List.length_append]
        omega
  have hrun_gate_getD : ∀ gs x k (hk : k < gs.length),
      (runW gs x).getD (x.length + k) false =
        (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (runW (gs.take k) x).getD i false) := by
    intro gs x k hk
    have hsplit : gs = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by
      rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
    conv_lhs => rw [hsplit]
    have hlenk : (gs.take k).length = k := List.length_take_of_le hk.le
    rw [hrun_prefix_getD (gs.take k ++ [gs[k]'hk]) (gs.drop (k + 1)) x (x.length + k)
      (by simp; omega)]
    rw [hrun_snoc]
    have hlenw : (runW (gs.take k) x).length = x.length + k := by rw [hrun_len, hlenk]
    rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
    rfl
  have heval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have heval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hrun_mono : ∀ gs, (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ x y : List Bool, x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (runW gs x).getD i false = true → (runW gs y).getD i false = true := by
    intro gs hgs x y hxy hle
    induction gs using List.reverseRecOn with
    | nil => exact hle
    | append_singleton gs g ih =>
      have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
        fun g' hg' => hgs g' (List.mem_append_left _ hg')
      have ih' := ih hgs'
      have hlen_eq : (runW gs x).length = (runW gs y).length := by rw [hrun_len, hrun_len, hxy]
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
      intro i hi
      rw [hrun_snoc] at hi ⊢
      by_cases hlt : i < (runW gs x).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
        exact ih' i hi
      · by_cases heq : i = (runW gs x).length
        · subst heq
          rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length] at hi
          rw [hlen_eq, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
          simp only [Option.getD_some] at hi ⊢
          rcases hg with hop | hop <;> rw [hop] at hi ⊢
          · simp only [heval_and, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
            rintro b ⟨j, hj, rfl⟩
            exact ih' j (hi _ ⟨j, hj, rfl⟩)
          · simp only [heval_or, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
            obtain ⟨_, ⟨j, hj, rfl⟩, htrue⟩ := hi
            exact ⟨_, ⟨j, hj, rfl⟩, ih' j htrue⟩
        · have hge : (runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)]).length ≤ i := by
            simp; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hi
          cases hi
  have hC_ao : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rcases (hmono g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- Every false input is dominated by the maximal avoiding input on the same lines.
  have hsound (z : Fin n → Bool) (hz : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q)
      (hno : ¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
      circuitFun n C z = false := by
    let Y := Finset.univ.filter fun l : Fin N => z (Fin.natAdd N l) = true
    have hcard : Y.card ≤ q := by simpa only [Fintype.card_subtype] using hz
    have hle (i : Fin n) : z i = true → maxInput Y i = true := by
      refine Fin.addCases (motive := fun j => z j = true → maxInput Y j = true) ?_ ?_ i
      · intro p hp
        simp only [maxInput, Fin.addCases_left, decide_eq_true_eq]
        rintro ⟨l, hl, hI⟩
        exact hno ⟨p, l, hI, hp, (Finset.mem_filter.mp hl).2⟩
      · intro l hl
        simp only [maxInput, Fin.addCases_right, decide_eq_true_eq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
    have hlist (i : ℕ) : (List.ofFn z).getD i false = true →
        (List.ofFn (maxInput Y)).getD i false = true := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      split <;> simp_all
    cases hv : circuitFun n C z with
    | false => rfl
    | true =>
      have ht : C.eval (List.ofFn (maxInput Y)) = true :=
        hrun_mono C.gates hC_ao _ _ (by simp [n]) hlist C.output hv
      rw [maximal Y hcard] at ht
      contradiction
  have needed : ∃ l p, p ∈ T l := by
    by_contra! none
    have empty (l : Fin N) : T l = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (none l)
    simp [empty] at hdense
  have hq : 22 ≤ q := by
    by_contra! small
    have deg (l : Fin N) : (T l).card ≤ q + 1 := by
      have sub : T l ⊆ Finset.univ.filter (fun p : Fin N => I p l) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hT l p hp).1
      exact (Finset.card_le_card sub).trans (by simpa only [Fintype.card_subtype] using (hcol l).le)
    have bounded (l : Fin N) : (T l).card ≤ if (T l).Nonempty then 22 else 0 := by
      split_ifs with hn
      · exact (deg l).trans (by omega)
      · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
    have total := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin N))) => bounded l)
    have sumBound :
        (∑ l : Fin N, if (T l).Nonempty then 22 else 0) =
          22 * Fintype.card {l : Fin N // (T l).Nonempty} := by
      rw [← Finset.sum_filter, Fintype.card_subtype]
      simp [Nat.mul_comm]
    rw [sumBound] at total
    omega
  have hN' : N = q ^ 2 + q + 1 := by simpa [Nat.pow_two, Nat.succ_eq_add_one] using hN
  have hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l') := by
    intro p p' l l' hp hl h
    obtain ⟨l₀,_,unique⟩ := huniq p p' hp
    exact hl ((unique l ⟨h.1,h.2.1⟩).trans (unique l' ⟨h.2.2.1,h.2.2.2⟩).symm)
  have hzero : circuitFun n C (fun _ => false) = false := by
    apply hsound
    · simp
    · rintro ⟨_,_,_,hx,_⟩
      cases hx
  obtain ⟨D,ao,budget,below,kept⟩ := active N C T hmono hzero needed
    (fun l p hp => (hT l p hp).2.1)
  have soundD (z : Fin n → Bool) (hz : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q)
      (hno : ¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
      circuitFun n D z = false := by
    cases v : circuitFun n D z with
    | false => rfl
    | true =>
      have bad := below z v
      rw [hsound z hz hno] at bad
      cases bad
  have lineBound := lines N I D hfour ao (fun z hz hno => soundD z (hz.trans (by omega)) hno)
  have pointBound := points q N I D (by omega) hN' hcol huniq ao soundD
  let ET : Finset (Fin N × Fin N) := Finset.univ.filter fun e => e.1 ∈ T e.2
  have sum_card : ∑ l : Fin N, (T l).card = ET.card := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.card_filter]
    congr 1
    ext p
    simp
  let yl (e : Fin N × Fin N) : Bool :=
    lineSingle D n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val)
  let xp (e : Fin N × Fin N) : Bool :=
    lineSingle D n (fun i => decide (i < N)) e.1.val (N + e.2.val)
  let EL := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ yl e = true)
  let EP := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ xp e = true)
  let ED := ET.filter (fun e => yl e = false ∧ xp e = false)
  have countL : EL.card ≤ 10 * D.size := by
    rw [Fintype.card_subtype] at lineBound
    exact lineBound
  have countP : EP.card ≤ 10 * D.size := by
    rw [Fintype.card_subtype] at pointBound
    exact pointBound
  have countD : ED.card ≤ 24 * D.size := by
    apply double q N I D hq hN' hcol huniq ao soundD ED
    intro e he
    obtain ⟨hes,hy,hx⟩ := Finset.mem_filter.mp he
    have hm := (Finset.mem_filter.mp hes).2
    exact ⟨(hT e.2 e.1 hm).1, kept e.2 e.1 hm, hy, hx⟩
  have cover : ET ⊆ EL ∪ EP ∪ ED := by
    intro e he
    have inc := (hT e.2 e.1 (Finset.mem_filter.mp he).2).1
    cases hy : yl e
    · cases hx : xp e
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, hy, hx⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, inc, hx⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, inc, hy⟩))
  have hsize := Finset.card_le_card cover
  have hu1 := Finset.card_union_le EL EP
  have hu2 := Finset.card_union_le (EL ∪ EP) ED
  rw [sum_card]
  have final : ET.card ≤ 44 * D.size := by omega
  exact final.trans (Nat.mul_le_mul_left 44 budget)
