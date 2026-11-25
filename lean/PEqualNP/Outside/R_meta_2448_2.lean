import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Cut L-meta-2448 via pair-sound AND gates.
-- First: every graph edge function is computed by some monotone fan-in-two circuit.
-- Second: on a triangle-free 4-cycle-free graph, every minimal monotone circuit can be
-- replaced by a no-larger one whose AND gates are false on all non-edges and singletons.
-- From pair-soundness and 4-cycle-freeness, every AND gate automatically owns a star.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2448_2
    (hExist : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅)
    (hPairSound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G →
      IsMinimalMonoCircuit n C →
      circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          ∀ u v : Fin n, gateVal n D j (pairInput u v) = true → G.Adj u v) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by
  classical
  intro n G _ htri hc4
  have hNoC4 : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hap, hbp⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨haq, hbq⟩ := (Finset.mem_filter.mp hq).2
    exact (hc4 a p b q hap hbp.symm hbq haq.symm).resolve_left hab
  have hExSize : ∃ s : ℕ, ∃ C : Circuit,
      Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ C.size = s := by
    obtain ⟨C0, hM0, hF0⟩ := hExist n G
    exact ⟨C0.size, C0, hM0, hF0, rfl⟩
  let sMin := Nat.find hExSize
  obtain ⟨Cmin, hMmin, hFmin, hSmin⟩ := Nat.find_spec hExSize
  have hIsMin : IsMinimalMonoCircuit n Cmin := by
    refine ⟨hMmin, fun E hME hFE => ?_⟩
    rw [hSmin]
    exact Nat.find_min' hExSize ⟨E, hME, hFmin ▸ hFE, rfl⟩
  obtain ⟨D, hMD, hFD, hSizeD, hPS⟩ := hPairSound n G Cmin htri hNoC4 hIsMin hFmin
  have hLeastD : ∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size := by
    intro E hME hFE
    exact hSizeD.trans (hIsMin.2 E hME (hFE.trans hFmin.symm))
  -- Local definitional equalities (by rfl) avoid generating module-level equation lemmas.
  have gateAtDef : ∀ j : ℕ, gateAt D j = D.gates.getD j ⟨GateOp.or, []⟩ := fun _ => rfl
  have gateValDef : ∀ (j : ℕ) (x : Fin n → Bool),
      gateVal n D j x = (D.wires (List.ofFn x)).getD (n + j) false := fun _ _ => rfl
  have pairInputDef : ∀ (u v w : Fin n),
      pairInput u v w = decide (w = u ∨ w = v) := fun _ _ _ => rfl
  have evalAndDef : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have evalOrDef : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have coneStepDef : ∀ (cs : List (List ℕ)) (g : Gate),
      coneStep n cs g =
        cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) [])] := fun _ _ => rfl
  -- Core helpers for straight-line circuit evaluation, monotonicity, and cones.
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepWire w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepWire w g) i (by simp [stepWire]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have gateAt_eq : ∀ (j : ℕ) (hj : j < D.gates.length), gateAt D j = D.gates[j]'hj := by
    intro j hj
    rw [gateAtDef, List.getD_eq_getElem _ _ hj]
  have wireVal_gate : ∀ (j : ℕ) (hj : j < D.gates.length) (x : Fin n → Bool),
      gateVal n D j x =
        (gateAt D j).op.eval
          ((gateAt D j).inputs.map fun i =>
            if i < n + j then (D.wires (List.ofFn x)).getD i false else false) := by
    intro j hj x
    let pre := D.gates.take j
    let post := D.gates.drop (j + 1)
    let gj := D.gates[j]'hj
    have hsplit : D.gates = pre ++ gj :: post := by
      simpa [pre, post, gj] using (List.take_append_drop j D.gates).symm.trans
        (by rw [List.cons_getElem_drop_succ])
    have hpre_len : pre.length = j := by simp [pre]; omega
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = n + j := by
      rw [foldl_len, List.length_ofFn, hpre_len]
    have hwires : D.wires (List.ofFn x) = post.foldl stepWire (stepWire w0 gj) := by
      change D.gates.foldl stepWire (List.ofFn x) = _
      rw [hsplit, List.foldl_append, List.foldl_cons]
    have hval_j : (D.wires (List.ofFn x)).getD (n + j) false =
        gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
      rw [hwires, foldl_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire, hw0_len])]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ n + j), hw0_len]
    have hval_lt : ∀ i, i < n + j →
        (D.wires (List.ofFn x)).getD i false = w0.getD i false := by
      intro i hi
      rw [hwires, foldl_getD_lt post (stepWire w0 gj) i (by simp [stepWire, hw0_len]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w0.length)]
    have hval_ge : ∀ i, ¬ i < n + j → w0.getD i false = false := by
      intro i hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w0.length ≤ i)]
    change (D.wires (List.ofFn x)).getD (n + j) false = _
    rw [hval_j, gateAt_eq j hj]
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases hi : i < n + j
    · rw [if_pos hi, hval_lt i hi]
    · rw [if_neg hi, hval_ge i hi]
  have wireVal_input : ∀ (w : ℕ) (hw : w < n) (x : Fin n → Bool),
      (D.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro w hw x
    change (D.gates.foldl stepWire (List.ofFn x)).getD w false = _
    rw [foldl_getD_lt D.gates (List.ofFn x) w (by simp [hw])]
    rw [List.getD_eq_getElem _ _ (by simp [hw])]
    exact List.getElem_ofFn _
  -- Monotonicity of wire values for Monotone2 circuits.
  have wire_mono : ∀ (x y : Fin n → Bool),
      (∀ i : Fin n, x i = true → y i = true) →
      ∀ w : ℕ, (D.wires (List.ofFn x)).getD w false = true →
        (D.wires (List.ofFn y)).getD w false = true := by
    intro x y hxy
    have hstep : ∀ (gs : List Gate),
        (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ (wx wy : List Bool), wx.length = wy.length →
        (∀ w, wx.getD w false = true → wy.getD w false = true) →
        ∀ w, (gs.foldl stepWire wx).getD w false = true →
          (gs.foldl stepWire wy).getD w false = true := by
      intro gs
      induction gs with
      | nil => intro _ wx wy _ hle w hw; exact hle w hw
      | cons g gs ih =>
        intro hgs wx wy hlen hle
        have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g List.mem_cons_self
        apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
          (stepWire wx g) (stepWire wy g) (by simp [stepWire, hlen])
        intro w hw
        by_cases hlt : w < wx.length
        · have hw' : wx.getD w false = true := by
            simpa [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] using hw
          have hy' := hle w hw'
          simpa [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left (hlen ▸ hlt)] using hy'
        · by_cases heq : w = wx.length
          · subst heq
            have hw' : g.op.eval (g.inputs.map fun i => wx.getD i false) = true := by
              simpa [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl] using hw
            have hy' : g.op.eval (g.inputs.map fun i => wy.getD i false) = true := by
              rcases hg with hop | hop
              · rw [hop] at hw' ⊢
                simp [evalAndDef] at hw' ⊢
                intro i hi
                exact hle i (hw' i hi)
              · rw [hop] at hw' ⊢
                simp [evalOrDef] at hw' ⊢
                obtain ⟨i, hi, hti⟩ := hw'
                exact ⟨i, hi, hle i hti⟩
            simpa [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : wy.length ≤ wx.length), hlen] using hy'
          · exfalso
            have hge : (stepWire wx g).length ≤ w := by simp [stepWire]; omega
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hw
    apply hstep D.gates
    · intro g hg
      have h := (hMD g hg).1
      simpa using h
    · simp
    · intro w hw
      by_cases hlt : w < n
      · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn] at hw ⊢
        exact hxy ⟨w, hlt⟩ hw
      · exfalso
        have hge : (List.ofFn x).length ≤ w := by simp; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hw
  -- Cone properties: length, earlier-gate invariance, direct reads, and transitivity.
  have cone_foldl_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      simp [coneStepDef]
      omega
  have cone_foldl_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ),
      i < cs.length → (gs.foldl (coneStep n) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons, ih (coneStep n cs g) i (by simp [coneStepDef]; omega)]
      simp [coneStepDef, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have cone_direct : ∀ (j : ℕ) (hj : j < D.gates.length) (w : ℕ),
      w ∈ (gateAt D j).inputs → n ≤ w → w < n + j → InCone n D (w - n) j := by
    intro j hj w hw hlo hhi
    let pre := D.gates.take j
    let post := D.gates.drop (j + 1)
    let gj := D.gates[j]'hj
    have hsplit : D.gates = pre ++ gj :: post := by
      simp [pre, post, gj]
    have hpre_len : pre.length = j := by simp [pre]; omega
    let cs0 := pre.foldl (coneStep n) []
    have hcs0_len : cs0.length = j := by rw [cone_foldl_len, List.length_nil, Nat.zero_add, hpre_len]
    have hcones : cones n D = post.foldl (coneStep n) (coneStep n cs0 gj) := by
      change D.gates.foldl (coneStep n) [] = _
      rw [hsplit, List.foldl_append, List.foldl_cons]
    have hj_eq : (cones n D).getD j [] =
        (gj.inputs.filter (fun u => decide (n ≤ u ∧ u < n + cs0.length))).flatMap
          (fun u => (u - n) :: cs0.getD (u - n) []) := by
      rw [hcones, cone_foldl_getD_lt post (coneStep n cs0 gj) j (by simp [coneStepDef, hcs0_len])]
      simp [coneStepDef, List.getD_eq_getElem?_getD, hcs0_len]
    change w - n ∈ (cones n D).getD j []
    rw [hj_eq]
    rw [gateAt_eq j hj] at hw
    apply List.mem_flatMap.mpr
    refine ⟨w, List.mem_filter.mpr ⟨hw, by simp [hcs0_len, hlo, hhi]⟩, List.mem_cons_self⟩
  have cone_trans : ∀ (j : ℕ) (i : ℕ) (k : ℕ),
      InCone n D k i → InCone n D i j → InCone n D k j := by
    have hinv : ∀ (gs : List Gate) (cs : List (List ℕ)),
        (∀ a < cs.length, ∀ b ∈ cs.getD a [], b < a ∧ ∀ c ∈ cs.getD b [], c ∈ cs.getD a []) →
        ∀ a < (gs.foldl (coneStep n) cs).length,
          ∀ b ∈ (gs.foldl (coneStep n) cs).getD a [],
            b < a ∧ ∀ c ∈ (gs.foldl (coneStep n) cs).getD b [],
              c ∈ (gs.foldl (coneStep n) cs).getD a [] := by
      intro gs
      induction gs with
      | nil => intro cs hcs; exact hcs
      | cons g gs ih =>
        intro cs hcs
        rw [List.foldl_cons]
        apply ih (coneStep n cs g)
        intro a ha b hb
        by_cases hlt : a < cs.length
        · have hb' : b ∈ cs.getD a [] := by
            simpa [coneStepDef, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] using hb
          obtain ⟨hba, htr⟩ := hcs a hlt b hb'
          refine ⟨hba, fun c hc => ?_⟩
          have hc' : c ∈ cs.getD b [] := by
            simpa [coneStepDef, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : b < cs.length)] using hc
          simpa [coneStepDef, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] using htr c hc'
        · have heq : a = cs.length := by simp [coneStepDef] at ha; omega
          subst heq
          have hget : (coneStep n cs g).getD cs.length [] =
              (g.inputs.filter (fun u => decide (n ≤ u ∧ u < n + cs.length))).flatMap
                (fun u => (u - n) :: cs.getD (u - n) []) := by
            simp [coneStepDef, List.getD_eq_getElem?_getD]
          rw [hget] at hb
          obtain ⟨u, hu, hbu⟩ := List.mem_flatMap.mp hb
          obtain ⟨_, hbounds⟩ := List.mem_filter.mp hu
          simp only [decide_eq_true_eq] at hbounds
          have hun : u - n < cs.length := by omega
          rcases List.mem_cons.mp hbu with rfl | hbu_tail
          · refine ⟨hun, fun c hc => ?_⟩
            have hc' : c ∈ cs.getD (u - n) [] := by
              simpa [coneStepDef, List.getD_eq_getElem?_getD, List.getElem?_append_left hun] using hc
            rw [hget]
            exact List.mem_flatMap.mpr ⟨u, hu, List.mem_cons_of_mem _ hc'⟩
          · obtain ⟨hb_lt, htr⟩ := hcs (u - n) hun b hbu_tail
            refine ⟨by omega, fun c hc => ?_⟩
            have hc' : c ∈ cs.getD b [] := by
              simpa [coneStepDef, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : b < cs.length)] using hc
            rw [hget]
            exact List.mem_flatMap.mpr ⟨u, hu, List.mem_cons_of_mem _ (htr c hc')⟩
    have hD := hinv D.gates [] (by intro a ha; simp at ha)
    intro j i k hki hij
    by_cases hj : j < (cones n D).length
    · exact (hD j hj i hij).2 k hki
    · exfalso
      have hnone : (cones n D).getD j [] = [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (cones n D).length ≤ j)]
      change i ∈ (cones n D).getD j [] at hij
      rw [hnone] at hij
      simp at hij
  -- Cone-OR decomposition: if no AND in j's strict cone fires on pairInput u v,
  -- any wire inside j's cone firing on pairInput u v already fires on u or on v alone.
  have cone_or_decomp : ∀ (j : ℕ) (u v : Fin n),
      j < D.gates.length →
      (∀ k < j, InCone n D k j → (gateAt D k).op = GateOp.and →
        gateVal n D k (pairInput u v) = false) →
      ∀ w : ℕ,
        (w < n ∨ (n ≤ w ∧ w < n + j ∧ InCone n D (w - n) j)) →
        (D.wires (List.ofFn (pairInput u v))).getD w false = true →
        (D.wires (List.ofFn (pairInput u u))).getD w false = true ∨
        (D.wires (List.ofFn (pairInput v v))).getD w false = true := by
    intro j u v hj hnoAnd w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hscope hw
      rcases hscope with hlt | ⟨hlo, hhi, hcone⟩
      · simp only [wireVal_input w hlt, pairInputDef, decide_eq_true_eq] at hw ⊢
        rcases hw with rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (Or.inl rfl)
      · let k := w - n
        have hwk : w = n + k := by omega
        have hkj : k < j := by omega
        have hkD : k < D.gates.length := by omega
        have hkVal : gateVal n D k (pairInput u v) = true := by
          simpa [gateValDef, hwk] using hw
        have hkop_cases : (gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or := by
          have hmem : gateAt D k ∈ D.gates := by rw [gateAt_eq k hkD]; exact List.getElem_mem hkD
          simpa using (hMD (gateAt D k) hmem).1
        have hkop : (gateAt D k).op = GateOp.or := by
          rcases hkop_cases with hand | hor
          · exfalso
            have hf := hnoAnd k hkj hcone hand
            rw [hkVal] at hf
            exact Bool.noConfusion hf
          · exact hor
        rw [wireVal_gate k hkD, hkop] at hkVal
        simp only [evalOrDef, List.any_eq_true, List.mem_map, id_eq] at hkVal
        obtain ⟨_, ⟨w', hw'mem, rfl⟩, hw't⟩ := hkVal
        by_cases hw'lt : w' < n + k
        · rw [if_pos hw'lt] at hw't
          have hw'scope : w' < n ∨ (n ≤ w' ∧ w' < n + j ∧ InCone n D (w' - n) j) := by
            by_cases hw'in : w' < n
            · exact Or.inl hw'in
            · refine Or.inr ⟨by omega, by omega, ?_⟩
              exact cone_trans j k (w' - n) (cone_direct k hkD w' hw'mem (by omega) hw'lt) hcone
          have hsub := ih w' (by omega) hw'scope hw't
          rw [hwk]
          rcases hsub with hu' | hv'
          · left
            change gateVal n D k (pairInput u u) = true
            rw [wireVal_gate k hkD, hkop]
            simp only [evalOrDef, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨true, ⟨w', hw'mem, by rw [if_pos hw'lt, hu']⟩, rfl⟩
          · right
            change gateVal n D k (pairInput v v) = true
            rw [wireVal_gate k hkD, hkop]
            simp only [evalOrDef, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨true, ⟨w', hw'mem, by rw [if_pos hw'lt, hv']⟩, rfl⟩
        · rw [if_neg hw'lt] at hw't
          exact Bool.noConfusion hw't
  -- Prove HasStarProfile n G D from pair-soundness and 4-cycle-freeness.
  have hStar : HasStarProfile n G D := by
    intro j hj hop
    have hmemj : gateAt D j ∈ D.gates := by rw [gateAt_eq j hj]; exact List.getElem_mem hj
    have hlenj : (gateAt D j).inputs.length ≤ 2 := (hMD (gateAt D j) hmemj).2
    rcases hlist : (gateAt D j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · left
      intro u v _ hown
      have ht : gateVal n D j (pairInput u u) = true := by
        rw [wireVal_gate j hj, hop, hlist]; rfl
      exact G.loopless.irrefl u (hPS j hj hop u u ht)
    · left
      intro u v _ hown
      obtain ⟨_, _, hval, hnoAnd⟩ := hown
      rw [wireVal_gate j hj, hop, hlist] at hval
      simp only [evalAndDef, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true] at hval
      by_cases ha : a < n + j
      · rw [if_pos ha] at hval
        have hascope : a < n ∨ (n ≤ a ∧ a < n + j ∧ InCone n D (a - n) j) := by
          by_cases hain : a < n
          · exact Or.inl hain
          · exact Or.inr ⟨by omega, ha, cone_direct j hj a (by rw [hlist]; simp) (by omega) ha⟩
        rcases cone_or_decomp j u v hj hnoAnd a hascope hval with hu | hv
        · have ht : gateVal n D j (pairInput u u) = true := by
            rw [wireVal_gate j hj, hop, hlist]
            simp only [evalAndDef, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, if_pos ha, hu]
          exact G.loopless.irrefl u (hPS j hj hop u u ht)
        · have ht : gateVal n D j (pairInput v v) = true := by
            rw [wireVal_gate j hj, hop, hlist]
            simp only [evalAndDef, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, if_pos ha, hv]
          exact G.loopless.irrefl v (hPS j hj hop v v ht)
      · rw [if_neg ha] at hval
        exact Bool.noConfusion hval
    · by_cases hab : a < n + j ∧ b < n + j
      · let Sa (x : Fin n) : Prop := (D.wires (List.ofFn (pairInput x x))).getD a false = true
        let Sb (y : Fin n) : Prop := (D.wires (List.ofFn (pairInput y y))).getD b false = true
        have hEdge : ∀ x y : Fin n, Sa x → Sb y → G.Adj x y := by
          intro x y hx hy
          have hax : (D.wires (List.ofFn (pairInput x y))).getD a false = true :=
            wire_mono (pairInput x x) (pairInput x y)
              (fun i hi => by simp [pairInputDef] at hi ⊢; left; exact hi) a hx
          have hby : (D.wires (List.ofFn (pairInput x y))).getD b false = true :=
            wire_mono (pairInput y y) (pairInput x y)
              (fun i hi => by simp [pairInputDef] at hi ⊢; right; exact hi) b hy
          have hval : gateVal n D j (pairInput x y) = true := by
            rw [wireVal_gate j hj, hop, hlist]
            simp only [evalAndDef, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, if_pos hab.1, if_pos hab.2, hax, hby]
          exact hPS j hj hop x y hval
        have hSmall : (∀ x1 x2 : Fin n, Sa x1 → Sa x2 → x1 = x2) ∨
            (∀ y1 y2 : Fin n, Sb y1 → Sb y2 → y1 = y2) := by
          by_contra hboth
          push Not at hboth
          obtain ⟨⟨x1, x2, hx1, hx2, hneX⟩, ⟨y1, y2, hy1, hy2, hneY⟩⟩ := hboth
          have h11 := hEdge x1 y1 hx1 hy1
          have h21 := (hEdge x2 y1 hx2 hy1).symm
          have h22 := hEdge x2 y2 hx2 hy2
          have h12 := (hEdge x1 y2 hx1 hy2).symm
          rcases hc4 x1 y1 x2 y2 h11 h21 h22 h12 with hx | hy
          · exact hneX hx
          · exact hneY hy
        have hOwnSplit : ∀ u v : Fin n, Owns n D j u v → (Sa u ∨ Sa v) ∧ (Sb u ∨ Sb v) := by
          intro u v hown
          obtain ⟨_, _, hval, hnoAnd⟩ := hown
          rw [wireVal_gate j hj, hop, hlist] at hval
          simp only [evalAndDef, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, Bool.and_eq_true, if_pos hab.1, if_pos hab.2] at hval
          have hascope : a < n ∨ (n ≤ a ∧ a < n + j ∧ InCone n D (a - n) j) := by
            by_cases hain : a < n
            · exact Or.inl hain
            · exact Or.inr ⟨by omega, hab.1, cone_direct j hj a (by rw [hlist]; simp) (by omega) hab.1⟩
          have hbscope : b < n ∨ (n ≤ b ∧ b < n + j ∧ InCone n D (b - n) j) := by
            by_cases hbin : b < n
            · exact Or.inl hbin
            · exact Or.inr ⟨by omega, hab.2, cone_direct j hj b (by rw [hlist]; simp) (by omega) hab.2⟩
          exact ⟨cone_or_decomp j u v hj hnoAnd a hascope hval.1,
                 cone_or_decomp j u v hj hnoAnd b hbscope hval.2⟩
        rcases hSmall with hSa | hSb
        · by_cases hex : ∃ c : Fin n, Sa c
          · obtain ⟨c, hc⟩ := hex
            right
            refine ⟨c, fun u v _ hown => ?_⟩
            rcases (hOwnSplit u v hown).1 with hu | hv
            · exact Or.inl (hSa u c hu hc)
            · exact Or.inr (hSa v c hv hc)
          · left
            intro u v _ hown
            rcases (hOwnSplit u v hown).1 with hu | hv
            · exact hex ⟨u, hu⟩
            · exact hex ⟨v, hv⟩
        · by_cases hex : ∃ c : Fin n, Sb c
          · obtain ⟨c, hc⟩ := hex
            right
            refine ⟨c, fun u v _ hown => ?_⟩
            rcases (hOwnSplit u v hown).2 with hu | hv
            · exact Or.inl (hSb u c hu hc)
            · exact Or.inr (hSb v c hv hc)
          · left
            intro u v _ hown
            rcases (hOwnSplit u v hown).2 with hu | hv
            · exact hex ⟨u, hu⟩
            · exact hex ⟨v, hv⟩
      · left
        intro u v _ hown
        obtain ⟨_, _, hval, _⟩ := hown
        rw [wireVal_gate j hj, hop, hlist] at hval
        simp only [evalAndDef, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true, Bool.and_eq_true] at hval
        by_cases ha : a < n + j
        · have hb : ¬ b < n + j := fun hb => hab ⟨ha, hb⟩
          rw [if_neg hb] at hval
          exact Bool.noConfusion hval.2
        · rw [if_neg ha] at hval
          exact Bool.noConfusion hval.1
    · exfalso
      rw [hlist] at hlenj
      simp at hlenj
  exact ⟨D, hMD, hFD, hLeastD, hStar⟩
