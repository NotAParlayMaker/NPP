import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

-- Reduction of L-meta-2582 into TopForm normalization and the non-star block case.
-- Proved inside this reduction: passing to a least circuit for the incidence graph,
-- proving that Ustar = empty implies IsReadK 2 (in fact read-1) via the TopForm OR-chain
-- to the output, and proving that Ustar nonempty implies junk nonempty.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2582_1
    (hTopForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧ TopForm G C')
    (hOffStar : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      (∀ a b : Fin (N + N), G.Adj a b ↔
        ∃ p l : Fin N, I p l ∧
          ((a = Fin.castAdd N p ∧ b = Fin.natAdd N l) ∨
           (b = Fin.castAdd N p ∧ a = Fin.natAdd N l))) →
      IsLeastAO G C → TopForm G C → (Ustar G C).Nonempty → (junk G C).Nonempty →
      ∃ D : Circuit, IsAO2 (N + N) D ∧ circuitFun (N + N) D = graphFun G ∅ ∧
        D.size ≤ C.size ∧ IsReadK (N + N) D 2) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2 := by
  classical
  intro q N I decI C hq hN hline huniq hAO hfun
  let n : ℕ := N + N
  -- Definitional equations avoiding on-demand equation lemmas in this module.
  have op_and_eval : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have op_or_eval : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have gateAt_def : ∀ (D : Circuit) (j : ℕ), gateAt D j = D.gates.getD j ⟨GateOp.or, []⟩ := fun _ _ => rfl
  have opnd_def : ∀ (D : Circuit) (a : ℕ) (b : Fin 2), opnd D a b = (gateAt D a).inputs.getD b 0 := fun _ _ _ => rfl
  have pairInput_def : ∀ (u v w : Fin n), pairInput u v w = decide (w = u ∨ w = v) := fun _ _ _ => rfl
  have setInput_def : ∀ (S : Finset (Fin n)) (i : Fin n), setInput S i = decide (i ∈ S) := fun _ _ => rfl
  have setList_def : ∀ (S : Finset (Fin n)),
      setList S = ((List.finRange n).filter fun i => decide (i ∈ S)).map Fin.val := fun _ => rfl
  have capAdd_def : ∀ (u v : List ℕ),
      capAdd 2 u v = List.zipWith (fun a b => min (a + b) 3) u v := fun _ _ => rfl
  have andStep_def : ∀ (A B : List (List ℕ)),
      andStep 2 A B = (A.flatMap fun u => B.map fun v => capAdd 2 u v).foldl insertNew [] := fun _ _ => rfl
  have leafVectors_def : ∀ (S : List ℕ) (w : ℕ),
      leafVectors S 2 w = if w ∈ S then [S.map fun j => if j = w then 1 else 0] else [] := fun _ _ => rfl
  have coneStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := fun _ _ => rfl
  have orStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      orStep n cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) [])
        else [])] := by
    intro cs g
    delta orStep
    by_cases hop : g.op = GateOp.or <;> simp [hop]
  have mem_orIn : ∀ (D : Circuit) (w : ℕ) (t : Fin n),
      t ∈ orIn n D w ↔ (t : ℕ) = w ∨ ∃ k < D.gates.length,
        OrReaches n D w k ∧ (gateAt D k).op = GateOp.or ∧ (t : ℕ) ∈ (gateAt D k).inputs := by
    intro D w t
    delta orIn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  let G : SimpleGraph (Fin n) := {
    Adj := fun a b => ∃ p l : Fin N, I p l ∧
      ((a = Fin.castAdd N p ∧ b = Fin.natAdd N l) ∨
       (b = Fin.castAdd N p ∧ a = Fin.natAdd N l))
    symm := ⟨by
      rintro a b ⟨p, l, hpl, h | h⟩
      · exact ⟨p, l, hpl, Or.inr h⟩
      · exact ⟨p, l, hpl, Or.inl h⟩⟩
    loopless := ⟨by
      rintro a ⟨p, l, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · have h := congrArg Fin.val (h1.symm.trans h2)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        omega
      · have h := congrArg Fin.val (h1.symm.trans h2)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        omega⟩
  }
  have hGadj : ∀ a b : Fin n, G.Adj a b ↔
      ∃ p l : Fin N, I p l ∧
        ((a = Fin.castAdd N p ∧ b = Fin.natAdd N l) ∨
         (b = Fin.castAdd N p ∧ a = Fin.natAdd N l)) := fun _ _ => Iff.rfl
  have hGraphFun : ∀ z : Fin n → Bool,
      graphFun G ∅ z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
    intro z
    delta graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, ha, hb⟩
      · exact ⟨p, l, hpl, ha, hb⟩
      · exact ⟨p, l, hpl, hb, ha⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact ⟨Fin.castAdd N p, Fin.natAdd N l, ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
  have hfunG : circuitFun n C = graphFun G ∅ := by
    funext z
    rw [hfun z, hGraphFun z]
  have hNpos : 0 < N := by subst hN; nlinarith
  have hGne : G.edgeFinset.Nonempty := by
    let l0 : Fin N := ⟨0, hNpos⟩
    have hc := hline l0
    have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l0)).card := by omega
    obtain ⟨p0, hp0⟩ := Finset.card_pos.mp hpos
    have hI0 : I p0 l0 := (Finset.mem_filter.mp hp0).2
    refine ⟨s(Fin.castAdd N p0, Fin.natAdd N l0), ?_⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨p0, l0, hI0, Or.inl ⟨rfl, rfl⟩⟩
  -- Step 1: Pass to a least AO2 circuit C0 for G, then put into TopForm C1 via hTopForm.
  have hExSize : ∃ s : ℕ, ∃ C' : Circuit, IsAO2 n C' ∧ circuitFun n C' = graphFun G ∅ ∧ C'.size = s :=
    ⟨C.size, C, hAO, hfunG, rfl⟩
  obtain ⟨C0, hAO0, hfun0, hsz0⟩ := Nat.find_spec hExSize
  have hC0le : C0.size ≤ C.size := by
    rw [hsz0]
    exact Nat.find_min' hExSize ⟨C, hAO, hfunG, rfl⟩
  have hLeast0 : IsLeastAO G C0 := by
    refine ⟨hAO0, hfun0, fun D hDAO hDfun => ?_⟩
    rw [hsz0]
    exact Nat.find_min' hExSize ⟨D, hDAO, hDfun, rfl⟩
  obtain ⟨C1, hLeast1, hsz1, hTop1⟩ := hTopForm n G C0 hGne hLeast0
  have hC1le : C1.size ≤ C.size := hsz1.le.trans hC0le
  have mem_tops : ∀ (a : ℕ), a ∈ tops G C1 ↔
      a < C1.gates.length ∧ (gateAt C1 a).op = GateOp.and ∧ BelowF G C1 a := by
    intro a
    delta tops gatesWhere
    exact (@Finset.mem_filter ℕ (fun j => (gateAt C1 j).op = GateOp.and ∧ BelowF G C1 j)
      (fun j => @instDecidableAnd _ _ (gateOpDecEq _ _) _)
      (Finset.range C1.gates.length) a).trans (and_congr_left' Finset.mem_range)
  -- General evaluation helpers for circuits on n inputs.
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldlW_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepW]
      omega
  have foldlW_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have foldlW_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepW w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, foldlW_getD_lt gs (stepW w g) w.length (by simp [stepW])]
        simp only [List.getElem_cons_zero]
        have h1 : (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepW, List.getD_eq_getElem?_getD]
        rw [h1]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldlW_getD_lt gs (stepW w g) i (by simp [stepW]; omega)]
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have hrec := ih (stepW w g) j hj'
        have hl : (stepW w g).length = w.length + 1 := by simp [stepW]
        rw [hl] at hrec
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact hrec
  have gateAt_eq : ∀ (D : Circuit) (j : ℕ) (hj : j < D.gates.length), gateAt D j = D.gates[j] := by
    intro D j hj
    rw [gateAt_def]
    simp [List.getD_eq_getElem?_getD, hj]
  have wireVal_input : ∀ (D : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n),
      wireVal n D w x = x ⟨w, hw⟩ := by
    intro D x w hw
    change (D.gates.foldl stepW (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [foldlW_getD_lt D.gates (List.ofFn x) w (by simpa using hw)]
    simp [List.getD_eq_getElem?_getD, hw]
  have wireVal_ge : ∀ (D : Circuit) (x : Fin n → Bool) (w : ℕ),
      n + D.gates.length ≤ w → wireVal n D w x = false := by
    intro D x w hw
    change (D.gates.foldl stepW (List.ofFn x)).getD w false = false
    have hlen : (D.gates.foldl stepW (List.ofFn x)).length = n + D.gates.length := by
      rw [foldlW_len, List.length_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have wireVal_gate : ∀ (D : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < D.gates.length),
      wireVal n D (n + j) x = (gateAt D j).op.eval ((gateAt D j).inputs.map fun i =>
        if i < n + j then wireVal n D i x else false) := by
    intro D x j hj
    rw [gateAt_eq D j hj]
    have h := foldlW_gate D.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at h
    exact h
  have wireVal_gate_ao2 : ∀ (D : Circuit) (hD : IsAO2 n D) (x : Fin n → Bool) (j : ℕ) (hj : j < D.gates.length),
      wireVal n D (n + j) x = (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => wireVal n D i x) := by
    intro D hD x j hj
    rw [wireVal_gate D x j hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [ite_eq_left (hD.2.1 j hj i hi)]
  have wireVal_or : ∀ (D : Circuit) (hD : IsAO2 n D) (x : Fin n → Bool) (j : ℕ) (hj : j < D.gates.length),
      (gateAt D j).op = GateOp.or →
      (wireVal n D (n + j) x = true ↔ ∃ i ∈ (gateAt D j).inputs, wireVal n D i x = true) := by
    intro D hD x j hj hop
    rw [wireVal_gate_ao2 D hD x j hj, hop, op_or_eval]
    simp
  have wireVal_and : ∀ (D : Circuit) (hD : IsAO2 n D) (x : Fin n → Bool) (j : ℕ) (hj : j < D.gates.length),
      (gateAt D j).op = GateOp.and →
      (wireVal n D (n + j) x = true ↔ ∀ i ∈ (gateAt D j).inputs, wireVal n D i x = true) := by
    intro D hD x j hj hop
    rw [wireVal_gate_ao2 D hD x j hj, hop, op_and_eval]
    simp
  have opnd_inputs : ∀ (D : Circuit) (hD : IsAO2 n D) (j : ℕ) (hj : j < D.gates.length),
      (gateAt D j).inputs = [opnd D j 0, opnd D j 1] := by
    intro D hD j hj
    have hlen : (gateAt D j).inputs.length = 2 := by
      rw [gateAt_eq D j hj]
      exact hD.2.2 _ (List.getElem_mem hj)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    rw [opnd_def, opnd_def, hab]
    rfl
  have opnd_lt : ∀ (D : Circuit) (hD : IsAO2 n D) (j : ℕ) (hj : j < D.gates.length) (b : Fin 2),
      opnd D j b < n + j := by
    intro D hD j hj b
    apply hD.2.1 j hj
    rw [opnd_inputs D hD j hj]
    fin_cases b <;> simp
  -- Helpers for cones and InCone.
  have coneFold_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, coneStep_def]
      simp
      omega
  have coneFold_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ),
      k < cs.length → (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro cs k hk
      rw [List.foldl_cons, ih (coneStep n cs g) k (by rw [coneStep_def]; simp; omega), coneStep_def]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have inCone_iff : ∀ (D : Circuit) (k i : ℕ) (hk : k < D.gates.length),
      InCone n D i k ↔ ∃ w ∈ (gateAt D k).inputs, n ≤ w ∧ w < n + k ∧
        (i = w - n ∨ InCone n D i (w - n)) := by
    intro D k i hk
    have hsplit : D.gates = D.gates.take k ++ D.gates[k] :: D.gates.drop (k + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hga : gateAt D k = D.gates[k] := gateAt_eq D k hk
    let pre := (D.gates.take k).foldl (coneStep n) []
    have hplen : pre.length = k := by
      simp only [pre, coneFold_len, List.length_nil, Nat.zero_add, List.length_take]
      omega
    have hc : cones n D = (D.gates.drop (k + 1)).foldl (coneStep n) (coneStep n pre D.gates[k]) := by
      delta cones
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have h1 : (cones n D).getD k [] = (coneStep n pre D.gates[k]).getD k [] := by
      rw [hc, coneFold_getD_lt _ _ k (by rw [coneStep_def]; simp [hplen])]
    have h2 : ∀ m < k, (cones n D).getD m [] = pre.getD m [] := by
      intro m hm
      rw [hc, coneFold_getD_lt _ _ m (by rw [coneStep_def]; simp [hplen]; omega), coneStep_def]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : m < pre.length)]
    delta InCone
    rw [h1, hga]
    have hget : (coneStep n pre D.gates[k]).getD k [] =
        (D.gates[k].inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
          (fun w => (w - n) :: pre.getD (w - n) []) := by
      rw [coneStep_def, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hplen, Nat.sub_self]
      rfl
    rw [hget, hplen]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hw, hn, hlt⟩, hi | hi⟩
      · exact ⟨w, hw, hn, hlt, Or.inl hi⟩
      · refine ⟨w, hw, hn, hlt, Or.inr ?_⟩
        rw [h2 (w - n) (by omega)]
        exact hi
    · rintro ⟨w, hw, hn, hlt, hi | hi⟩
      · exact ⟨w, ⟨hw, hn, hlt⟩, Or.inl hi⟩
      · refine ⟨w, ⟨hw, hn, hlt⟩, Or.inr ?_⟩
        rw [← h2 (w - n) (by omega)]
        exact hi
  -- Helpers for orSets and OrReaches.
  have orFold_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, orStep_def]
      simp
      omega
  have orFold_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ),
      k < cs.length → (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro cs k hk
      rw [List.foldl_cons, ih (orStep n cs g) k (by rw [orStep_def]; simp; omega), orStep_def]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have orSets_mem_iff : ∀ (D : Circuit) (k x : ℕ) (hk : k < D.gates.length),
      x ∈ (orSets n D).getD k [] ↔ x = k ∨ ((gateAt D k).op = GateOp.or ∧
        ∃ w ∈ (gateAt D k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n D).getD (w - n) []) := by
    intro D k x hk
    have hsplit : D.gates = D.gates.take k ++ D.gates[k] :: D.gates.drop (k + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hga : gateAt D k = D.gates[k] := gateAt_eq D k hk
    let pre := (D.gates.take k).foldl (orStep n) []
    have hplen : pre.length = k := by
      simp only [pre, orFold_len, List.length_nil, Nat.zero_add, List.length_take]
      omega
    have hc : orSets n D = (D.gates.drop (k + 1)).foldl (orStep n) (orStep n pre D.gates[k]) := by
      delta orSets
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have h1 : (orSets n D).getD k [] = (orStep n pre D.gates[k]).getD k [] := by
      rw [hc, orFold_getD_lt _ _ k (by rw [orStep_def]; simp [hplen])]
    have h2 : ∀ m < k, (orSets n D).getD m [] = pre.getD m [] := by
      intro m hm
      rw [hc, orFold_getD_lt _ _ m (by rw [orStep_def]; simp [hplen]; omega), orStep_def]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : m < pre.length)]
    rw [h1, hga]
    have hget : (orStep n pre D.gates[k]).getD k [] =
        pre.length :: (if D.gates[k].op = GateOp.or then
          (D.gates[k].inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
            (fun w => pre.getD (w - n) [])
          else []) := by
      rw [orStep_def, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hplen, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
    rw [hget, hplen]
    by_cases hop : D.gates[k].op = GateOp.or
    · simp only [hop, ↓reduceIte, true_and, List.mem_cons, List.mem_flatMap, List.mem_filter,
        decide_eq_true_eq]
      constructor
      · rintro (rfl | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨w, hw, hn, hlt, ?_⟩
          rw [h2 (w - n) (by omega)]
          exact hx
      · rintro (rfl | ⟨w, hw, hn, hlt, hx⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
          rw [← h2 (w - n) (by omega)]
          exact hx
    · simp [hop]
  have orSets_inCone : ∀ (D : Circuit) (k x : ℕ),
      k < D.gates.length → x ∈ (orSets n D).getD k [] → x = k ∨ InCone n D x k := by
    intro D k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hk hx
      rw [orSets_mem_iff D k x hk] at hx
      rcases hx with rfl | ⟨_, w, hw, hn, hlt, hx'⟩
      · exact Or.inl rfl
      · right
        rw [inCone_iff D k x hk]
        exact ⟨w, hw, hn, hlt, ih (w - n) (by omega) x (by omega) hx'⟩
  have orIn_val_true : ∀ (D : Circuit) (hD : IsAO2 n D) (w : ℕ) (t : Fin n) (x : Fin n → Bool),
      t ∈ orIn n D w → x t = true → wireVal n D w x = true := by
    intro D hD w t x ht hxt
    rw [mem_orIn] at ht
    rcases ht with rfl | ⟨k, hk, hreach, hop, hmem⟩
    · rw [wireVal_input D x t.val t.isLt]
      exact hxt
    · have hkval : wireVal n D (n + k) x = true := by
        rw [wireVal_or D hD x k hk hop]
        exact ⟨t.val, hmem, by rw [wireVal_input D x t.val t.isLt]; exact hxt⟩
      obtain ⟨hnw, hmk⟩ := hreach
      have hprop : ∀ m, m < D.gates.length → k ∈ (orSets n D).getD m [] →
          wireVal n D (n + m) x = true := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ih =>
          intro hm hkm
          rw [orSets_mem_iff D m k hm] at hkm
          rcases hkm with rfl | ⟨hopm, u, hu, hnu, hltu, hku⟩
          · exact hkval
          · rw [wireVal_or D hD x m hm hopm]
            refine ⟨u, hu, ?_⟩
            have heq : n + (u - n) = u := by omega
            rw [← heq]
            exact ih (u - n) (by omega) (by omega) hku
      have hlt : w - n < D.gates.length := by
        by_contra hge
        have hlen : (orSets n D).length = D.gates.length := by
          delta orSets; rw [orFold_len]; simp
        have hdef : (orSets n D).getD (w - n) [] = [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (orSets n D).length ≤ w - n)]
        rw [hdef] at hmk
        simp at hmk
      have heq : n + (w - n) = w := by omega
      rw [← heq]
      exact hprop (w - n) hlt hmk
  -- Split on whether Ustar G C1 is nonempty.
  by_cases hU : (Ustar G C1).Nonempty
  · -- Case 1: Ustar G C1 is nonempty. Prove (junk G C1).Nonempty and apply hOffStar.
    obtain ⟨e, heU⟩ := hU
    have heG : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp heU).1
    have heNS : e ∉ starEdges G C1 := (Finset.mem_sdiff.mp heU).2
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := (SimpleGraph.mem_edgeFinset.mp heG)
      let x := pairInput u v
      have hC1fun : circuitFun n C1 = graphFun G ∅ := hLeast1.2.1
      have hAO1 : IsAO2 n C1 := hLeast1.1
      have hout_val : wireVal n C1 C1.output x = true := by
        have h1 : circuitFun n C1 x = true := by
          rw [hC1fun]
          delta graphFun
          rw [Bool.or_eq_true]
          right
          exact decide_eq_true ⟨u, v, huv,
            by rw [show x u = pairInput u v u from rfl, pairInput_def]; simp,
            by rw [show x v = pairInput u v v from rfl, pairInput_def]; simp⟩
        exact h1
      have hout_lt : C1.output < n + C1.gates.length := by
        by_contra hge
        have h0 := wireVal_ge C1 x C1.output (Nat.le_of_not_lt hge)
        rw [hout_val] at h0
        cases h0
      have hout_below : ∀ y : Fin n → Bool, wireVal n C1 C1.output y = true → graphFun G ∅ y = true := by
        intro y hy
        rw [← hC1fun]
        exact hy
      -- Trace down from a wire below F that is true at x to find a top a ∈ tops G C1 true at x.
      have findTop : ∀ w, w < n + C1.gates.length → wireVal n C1 w x = true →
          (∀ y : Fin n → Bool, wireVal n C1 w y = true → graphFun G ∅ y = true) →
          ∃ a ∈ tops G C1, gateVal n C1 a x = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hw hwx hwb
          by_cases hwn : w < n
          · exfalso
            let t : Fin n := ⟨w, hwn⟩
            have h1 : wireVal n C1 w (pairInput t t) = true := by
              rw [wireVal_input C1 (pairInput t t) w hwn, pairInput_def]
              simp [t]
            have h2 := hwb (pairInput t t) h1
            have h2' : decide (∃ a b : Fin n, G.Adj a b ∧ pairInput t t a = true ∧ pairInput t t b = true) = true := by
              change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput t t a = true) ||
                decide (∃ a b : Fin n, G.Adj a b ∧ pairInput t t a = true ∧ pairInput t t b = true)) = true at h2
              simpa using h2
            obtain ⟨a, b, hab, ha, hb⟩ := of_decide_eq_true h2'
            rw [pairInput_def] at ha hb
            simp only [or_self, decide_eq_true_eq] at ha hb
            subst ha; subst hb
            exact G.loopless.irrefl _ hab
          · let j := w - n
            have hj : j < C1.gates.length := by omega
            have hnj : n + j = w := by omega
            have hmemj : gateAt C1 j ∈ C1.gates := by
              rw [gateAt_eq C1 j hj]; exact List.getElem_mem hj
            rcases hAO1.1 (gateAt C1 j) hmemj with hop | hop
            · refine ⟨j, ?_, by change wireVal n C1 (n + j) x = true; rwa [hnj]⟩
              rw [mem_tops]
              refine ⟨hj, hop, fun y hy => hwb y ?_⟩
              change wireVal n C1 (n + j) y = true at hy
              rwa [← hnj]
            · have hwx' : wireVal n C1 (n + j) x = true := hnj.symm ▸ hwx
              obtain ⟨i, hi, hix⟩ := (wireVal_or C1 hAO1 x j hj hop).mp hwx'
              have hilt : i < w := by
                have := hAO1.2.1 j hj i hi
                omega
              apply ih i hilt (by omega) hix
              intro y hiy
              apply hwb y
              rw [← hnj, wireVal_or C1 hAO1 y j hj hop]
              exact ⟨i, hi, hiy⟩
      obtain ⟨a, haTop, hax⟩ := findTop C1.output hout_lt hout_val hout_below
      obtain ⟨haLt, haOp, haBel⟩ := (mem_tops a).mp haTop
      -- Trace down through ORs from any wire true at x to either an input in orIn or an AND gate in OrReaches.
      have traceOr : ∀ w, w < n + C1.gates.length → wireVal n C1 w x = true →
          (∃ t : Fin n, t ∈ orIn n C1 w ∧ x t = true) ∨
          (∃ h < C1.gates.length, OrReaches n C1 w h ∧ (gateAt C1 h).op = GateOp.and) := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hw hwx
          by_cases hwn : w < n
          · left
            refine ⟨⟨w, hwn⟩, ?_, ?_⟩
            · rw [mem_orIn]; exact Or.inl rfl
            · rwa [wireVal_input C1 x w hwn] at hwx
          · let j := w - n
            have hj : j < C1.gates.length := by omega
            have hnj : n + j = w := by omega
            have hmemj : gateAt C1 j ∈ C1.gates := by
              rw [gateAt_eq C1 j hj]; exact List.getElem_mem hj
            rcases hAO1.1 (gateAt C1 j) hmemj with hop | hop
            · right
              refine ⟨j, hj, ⟨by omega, ?_⟩, hop⟩
              rw [orSets_mem_iff C1 j j hj]
              exact Or.inl rfl
            · have hwx' : wireVal n C1 (n + j) x = true := hnj.symm ▸ hwx
              obtain ⟨i, hi, hix⟩ := (wireVal_or C1 hAO1 x j hj hop).mp hwx'
              have hilt : i < n + j := hAO1.2.1 j hj i hi
              by_cases hin : i < n
              · left
                refine ⟨⟨i, hin⟩, ?_, ?_⟩
                · rw [mem_orIn]
                  right
                  refine ⟨j, hj, ⟨by omega, ?_⟩, hop, hi⟩
                  rw [orSets_mem_iff C1 j j hj]
                  exact Or.inl rfl
                · rwa [wireVal_input C1 x i hin] at hix
              · rcases ih i (by omega) (by omega) hix with ⟨t, ht, htx⟩ | ⟨h, hh, hreach, hoph⟩
                · left
                  refine ⟨t, ?_, htx⟩
                  rw [mem_orIn] at ht ⊢
                  rcases ht with hti | ⟨k, hk, hkr, hopk, htk⟩
                  · omega
                  · right
                    refine ⟨k, hk, ⟨by omega, ?_⟩, hopk, htk⟩
                    rw [orSets_mem_iff C1 j k hj]
                    exact Or.inr ⟨hop, i, hi, by omega, hilt, hkr.2⟩
                · right
                  refine ⟨h, hh, ⟨by omega, ?_⟩, hoph⟩
                  rw [orSets_mem_iff C1 j h hj]
                  exact Or.inr ⟨hop, i, hi, by omega, hilt, hreach.2⟩
      have haSides : wireVal n C1 (opnd C1 a 0) x = true ∧ wireVal n C1 (opnd C1 a 1) x = true := by
        have h1 := (wireVal_and C1 hAO1 x a haLt haOp).mp hax
        rw [opnd_inputs C1 hAO1 a haLt] at h1
        exact ⟨h1 _ (by simp), h1 _ (by simp)⟩
      have junkFromOr : ∀ (b : Fin 2) (h : ℕ), h < C1.gates.length →
          OrReaches n C1 (opnd C1 a b) h → (gateAt C1 h).op = GateOp.and →
          (junk G C1).Nonempty := by
        intro b h hh hreach hoph
        have hinCone : InCone n C1 h a := by
          rw [inCone_iff C1 a h haLt]
          refine ⟨opnd C1 a b, ?_, hreach.1, opnd_lt C1 hAO1 a haLt b, ?_⟩
          · rw [opnd_inputs C1 hAO1 a haLt]; fin_cases b <;> simp
          · exact orSets_inCone C1 (opnd C1 a b - n) h (by have := opnd_lt C1 hAO1 a haLt b; omega) hreach.2
        have hnotBel : ¬ BelowF G C1 h := fun hbh => hTop1 h hh a haLt hoph hbh haOp hinCone
        have hdirty : IsDirtyAnd n G C1 h := by
          refine ⟨hoph, hh, ?_⟩
          by_contra hno
          apply hnotBel
          intro y hy
          by_contra hfy
          exact hno ⟨y, hy, Bool.eq_false_iff.mpr hfy⟩
        refine ⟨h, ?_⟩
        delta junk gatesWhere
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
      have hjunk : (junk G C1).Nonempty := by
        rcases traceOr (opnd C1 a 0) (by have := opnd_lt C1 hAO1 a haLt 0; omega) haSides.1 with
          ⟨t0, ht0, hxt0⟩ | ⟨h, hh, hr, hoph⟩
        · rcases traceOr (opnd C1 a 1) (by have := opnd_lt C1 hAO1 a haLt 1; omega) haSides.2 with
            ⟨t1, ht1, hxt1⟩ | ⟨h, hh, hr, hoph⟩
          · exfalso
            have hne01 : t0 ≠ t1 := by
              intro heq
              subst heq
              have hv0 := orIn_val_true C1 hAO1 (opnd C1 a 0) t0 (pairInput t0 t0) ht0
                (by rw [pairInput_def]; simp)
              have hv1 := orIn_val_true C1 hAO1 (opnd C1 a 1) t0 (pairInput t0 t0) ht1
                (by rw [pairInput_def]; simp)
              have hva : gateVal n C1 a (pairInput t0 t0) = true := by
                change wireVal n C1 (n + a) (pairInput t0 t0) = true
                rw [wireVal_and C1 hAO1 (pairInput t0 t0) a haLt haOp, opnd_inputs C1 hAO1 a haLt]
                intro i hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact hv0
                · exact hv1
              have hgf := haBel (pairInput t0 t0) hva
              have hgf' : decide (∃ p1 p2 : Fin n, G.Adj p1 p2 ∧ pairInput t0 t0 p1 = true ∧ pairInput t0 t0 p2 = true) = true := by
                change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput t0 t0 a = true) ||
                  decide (∃ p1 p2 : Fin n, G.Adj p1 p2 ∧ pairInput t0 t0 p1 = true ∧ pairInput t0 t0 p2 = true)) = true at hgf
                simpa using hgf
              obtain ⟨p1, p2, hp12, hp1, hp2⟩ := of_decide_eq_true hgf'
              rw [pairInput_def] at hp1 hp2
              simp only [or_self, decide_eq_true_eq] at hp1 hp2
              subst hp1; subst hp2
              exact G.loopless.irrefl _ hp12
            have hxt0' : t0 = u ∨ t0 = v := by
              rw [show x t0 = pairInput u v t0 from rfl, pairInput_def, decide_eq_true_eq] at hxt0
              exact hxt0
            have hxt1' : t1 = u ∨ t1 = v := by
              rw [show x t1 = pairInput u v t1 from rfl, pairInput_def, decide_eq_true_eq] at hxt1
              exact hxt1
            have hsym : s(u, v) = s(t0, t1) := by
              rcases hxt0' with rfl | rfl <;> rcases hxt1' with rfl | rfl
              · exact (hne01 rfl).elim
              · rfl
              · exact Sym2.eq_swap
              · exact (hne01 rfl).elim
            apply heNS
            rw [hsym]
            delta starEdges
            exact Finset.mem_biUnion.mpr ⟨a, haTop, Finset.mem_image.mpr
              ⟨(t0, t1), Finset.mem_product.mpr ⟨ht0, ht1⟩, rfl⟩⟩
          · exact junkFromOr 1 h hh hr hoph
        · exact junkFromOr 0 h hh hr hoph
      obtain ⟨D, hDAO, hDfun, hDsz, hDread⟩ :=
        hOffStar q N I G C1 hq hN (fun l => by rw [Fintype.card_subtype]; exact hline l)
          huniq hGadj hLeast1 hTop1 ⟨s(u, v), heU⟩ hjunk
      exact ⟨D, hDAO, fun y => by rw [congrFun hDfun y, hGraphFun y], hDsz.trans hC1le, hDread⟩
  · -- Case 2: Ustar G C1 = ∅. Prove IsReadK n C1 2 directly!
    have hUempty : Ustar G C1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    have hAO1 : IsAO2 n C1 := hLeast1.1
    have hC1fun : circuitFun n C1 = graphFun G ∅ := hLeast1.2.1
    -- Step 2a: Dead-gate elimination: every gate j < C1.gates.length with n + j ≠ C1.output has a reader.
    have hasReader : ∀ j, j < C1.gates.length → n + j ≠ C1.output →
        ∃ r < C1.gates.length, n + j ∈ (gateAt C1 r).inputs := by
      intro j hj hjo
      by_contra hno
      push Not at hno
      let shift (w : ℕ) : ℕ := if n + j < w then w - 1 else w
      let C' : Circuit := {
        gates := (C1.gates.eraseIdx j).map (fun g => ⟨g.op, g.inputs.map shift⟩)
        output := shift C1.output
      }
      have hlenC' : C'.gates.length = C1.gates.length - 1 := by
        simp [C', List.length_eraseIdx, hj]
      have hgateC' : ∀ k (hk : k < C'.gates.length),
          let orig := if k < j then k else k + 1
          orig < C1.gates.length ∧
          gateAt C' k = ⟨(gateAt C1 orig).op, (gateAt C1 orig).inputs.map shift⟩ := by
        intro k hk
        dsimp only
        have hlen1 : (C1.gates.eraseIdx j).length = C1.gates.length - 1 := by
          simp [List.length_eraseIdx, hj]
        have hk' : k < (C1.gates.eraseIdx j).length := by omega
        by_cases hkj : k < j
        · simp only [hkj, ↓reduceIte]
          refine ⟨by omega, ?_⟩
          rw [gateAt_eq C' k hk, gateAt_eq C1 k (by omega)]
          simp only [C', List.getElem_map, List.getElem_eraseIdx, hkj, ↓reduceDIte]
        · simp only [hkj, ↓reduceIte]
          refine ⟨by omega, ?_⟩
          rw [gateAt_eq C' k hk, gateAt_eq C1 (k + 1) (by omega)]
          simp only [C', List.getElem_map, List.getElem_eraseIdx, hkj, ↓reduceDIte]
      have hAO' : IsAO2 n C' := by
        refine ⟨?_, ?_, ?_⟩
        · intro g hg
          simp only [C', List.mem_map] at hg
          obtain ⟨g0, hg0, rfl⟩ := hg
          exact hAO1.1 g0 (List.mem_of_mem_eraseIdx hg0)
        · intro k hk w hw
          obtain ⟨horig, hg⟩ := hgateC' k hk
          rw [hg] at hw
          simp only [List.mem_map] at hw
          obtain ⟨u, hu, rfl⟩ := hw
          by_cases hkj : k < j
          · simp only [hkj, ↓reduceIte] at hu
            have hult := hAO1.2.1 k (by omega) u hu
            have hsh : shift u = u := by simp only [shift]; rw [ite_eq_right (by omega)]
            rw [hsh]; omega
          · simp only [hkj, ↓reduceIte] at hu
            have hult := hAO1.2.1 (k + 1) (by omega) u hu
            have hne : u ≠ n + j := fun heq => hno (k + 1) (by omega) (heq ▸ hu)
            simp only [shift]
            split_ifs <;> omega
        · intro g hg
          simp only [C', List.mem_map] at hg
          obtain ⟨g0, hg0, rfl⟩ := hg
          simp [hAO1.2.2 g0 (List.mem_of_mem_eraseIdx hg0)]
      have hvalEq : ∀ (x : Fin n → Bool) (w : ℕ), w ≠ n + j → w < n + C1.gates.length →
          wireVal n C' (shift w) x = wireVal n C1 w x := by
        intro x w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hne hwlt
          by_cases hwn : w < n
          · have hsh : shift w = w := by simp only [shift]; rw [ite_eq_right (by omega)]
            rw [hsh, wireVal_input C' x w hwn, wireVal_input C1 x w hwn]
          · let m := w - n
            have hm : m < C1.gates.length := by omega
            have hmj : m ≠ j := by omega
            by_cases hlt : m < j
            · have hsh : shift w = n + m := by simp only [shift]; rw [ite_eq_right (by omega)]; omega
              have hnw : n + m = w := by omega
              have hk' : m < C'.gates.length := by omega
              rw [hsh, ← hnw, wireVal_gate_ao2 C' hAO' x m hk', wireVal_gate_ao2 C1 hAO1 x m hm]
              have hg := (hgateC' m hk').2
              simp only [hlt, ↓reduceIte] at hg
              rw [hg, List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              have hult := hAO1.2.1 m hm u hu
              exact ih u (by omega) (by omega) (by omega)
            · have hgt : j < m := by omega
              have hsh : shift w = n + (m - 1) := by simp only [shift]; rw [ite_eq_left (by omega)]; omega
              have hnw : n + m = w := by omega
              have hk' : m - 1 < C'.gates.length := by omega
              rw [hsh, ← hnw, wireVal_gate_ao2 C' hAO' x (m - 1) hk', wireVal_gate_ao2 C1 hAO1 x m hm]
              have hg := (hgateC' (m - 1) hk').2
              have hnotlt : ¬ (m - 1 < j) := by omega
              have hsucc : m - 1 + 1 = m := by omega
              simp only [hnotlt, ↓reduceIte, hsucc] at hg
              rw [hg, List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              have hult := hAO1.2.1 m hm u hu
              have hune : u ≠ n + j := fun heq => hno m hm (heq ▸ hu)
              exact ih u (by omega) hune (by omega)
      have hfunC' : circuitFun n C' = graphFun G ∅ := by
        rw [← hC1fun]
        funext x
        change wireVal n C' (shift C1.output) x = wireVal n C1 C1.output x
        by_cases hout : C1.output < n + C1.gates.length
        · exact hvalEq x C1.output hjo.symm hout
        · have hge1 : n + C1.gates.length ≤ C1.output := Nat.le_of_not_lt hout
          have hge2 : n + C'.gates.length ≤ shift C1.output := by
            simp only [shift]
            split_ifs <;> omega
          rw [wireVal_ge C' x (shift C1.output) hge2, wireVal_ge C1 x C1.output hge1]
      have hszLe := hLeast1.2.2 C' hAO' hfunC'
      change C1.gates.length ≤ C'.gates.length at hszLe
      omega
    -- Step 2b: Helpers for readVectors on C1 with cap k = 2 (using GateOp.casesOn to avoid extra matchers).
    have mem_insertNew : ∀ (a v : List ℕ) (A : List (List ℕ)),
        v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
      intro a v A
      delta insertNew
      by_cases ha : a ∈ A
      · simp only [ha, ↓reduceIte]
        exact ⟨Or.inl, fun h => h.elim id (fun e => e ▸ ha)⟩
      · simp [ha]
    have mem_fold_insertNew : ∀ (v : List ℕ) (B A : List (List ℕ)),
        v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
      intro v B
      induction B with
      | nil => intro A; simp
      | cons b B ih =>
        intro A
        simp only [List.foldl_cons, ih, mem_insertNew, List.mem_cons]
        tauto
    have mem_andStep : ∀ (v : List ℕ) (A B : List (List ℕ)),
        v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
      intro v A B
      rw [andStep_def]
      simp [mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]
    let rvBody (S : List ℕ) (ins : List (List (List ℕ))) (op : GateOp) : List (List ℕ) :=
      GateOp.casesOn (motive := fun _ => List (List ℕ)) op
        (ins.foldl (andStep 2) [S.map fun _ => 0])
        (ins.foldl (fun acc A => A.foldl insertNew acc) [])
        []
        (fun _ => [])
        []
    let stepRV (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
      R ++ [rvBody S (g.inputs.map fun i => R.getD i []) g.op]
    have rv_eq_foldl : ∀ (S : List ℕ),
        readVectors C1 n S 2 = C1.gates.foldl (stepRV S) ((List.range n).map (leafVectors S 2)) := by
      intro S
      delta readVectors
      congr 1
      funext R g
      rcases g with ⟨op, ins⟩
      cases op <;> rfl
    have rvFold_len : ∀ (S : List ℕ) (gs : List Gate) (R : List (List (List ℕ))),
        (gs.foldl (stepRV S) R).length = R.length + gs.length := by
      intro S gs
      induction gs with
      | nil => intro R; simp
      | cons g gs ih =>
        intro R
        rw [List.foldl_cons, ih]
        simp [stepRV]
        omega
    have rvFold_getD_lt : ∀ (S : List ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ),
        i < R.length → (gs.foldl (stepRV S) R).getD i [] = R.getD i [] := by
      intro S gs
      induction gs with
      | nil => intro _ _ _; rfl
      | cons g gs ih =>
        intro R i hi
        rw [List.foldl_cons, ih (stepRV S R g) i (by simp [stepRV]; omega)]
        simp [stepRV, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have rv_input : ∀ (S : List ℕ) (w : ℕ), w < n →
        (readVectors C1 n S 2).getD w [] = leafVectors S 2 w := by
      intro S w hw
      rw [rv_eq_foldl S, rvFold_getD_lt S C1.gates _ w (by simp [hw])]
      simp [List.getD_eq_getElem?_getD, hw]
    have rv_gate : ∀ (S : List ℕ) (k : ℕ) (hk : k < C1.gates.length),
        (readVectors C1 n S 2).getD (n + k) [] =
          rvBody S ((gateAt C1 k).inputs.map fun i => (readVectors C1 n S 2).getD i []) (gateAt C1 k).op := by
      intro S k hk
      have hsplit : C1.gates = C1.gates.take k ++ C1.gates[k] :: C1.gates.drop (k + 1) := by
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      have hga : gateAt C1 k = C1.gates[k] := gateAt_eq C1 k hk
      let R0 := (List.range n).map (leafVectors S 2)
      let pre := (C1.gates.take k).foldl (stepRV S) R0
      have hplen : pre.length = n + k := by
        simp only [pre, rvFold_len, R0, List.length_map, List.length_range, List.length_take]
        omega
      have hc : readVectors C1 n S 2 =
          (C1.gates.drop (k + 1)).foldl (stepRV S) (stepRV S pre C1.gates[k]) := by
        rw [rv_eq_foldl S]
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have h1 : (readVectors C1 n S 2).getD (n + k) [] = (stepRV S pre C1.gates[k]).getD (n + k) [] := by
        rw [hc, rvFold_getD_lt S _ _ (n + k) (by simp [stepRV, hplen])]
      have h2 : ∀ i < n + k, (readVectors C1 n S 2).getD i [] = pre.getD i [] := by
        intro i hi
        rw [hc, rvFold_getD_lt S _ _ i (by simp [stepRV, hplen]; omega)]
        simp [stepRV, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pre.length)]
      rw [h1, hga]
      have hmap : C1.gates[k].inputs.map (fun i => pre.getD i []) =
          C1.gates[k].inputs.map (fun i => (readVectors C1 n S 2).getD i []) := by
        apply List.map_congr_left
        intro i hi
        have hilt := hAO1.2.1 k hk i (by rw [hga]; exact hi)
        exact (h2 i hilt).symm
      have hget : (stepRV S pre C1.gates[k]).getD (n + k) [] =
          rvBody S (C1.gates[k].inputs.map fun i => pre.getD i []) C1.gates[k].op := by
        change (pre ++ [rvBody S (C1.gates[k].inputs.map fun i => pre.getD i []) C1.gates[k].op]).getD (n + k) [] = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hplen, Nat.sub_self]
        rfl
      rw [hget, hmap]
    have rv_or_step : ∀ (S : List ℕ) (k : ℕ) (hk : k < C1.gates.length),
        (gateAt C1 k).op = GateOp.or →
        ∀ i ∈ (gateAt C1 k).inputs, ∀ v ∈ (readVectors C1 n S 2).getD i [],
          v ∈ (readVectors C1 n S 2).getD (n + k) [] := by
      intro S k hk hop i hi v hv
      rw [rv_gate S k hk, hop]
      change v ∈ (((gateAt C1 k).inputs.map fun j => (readVectors C1 n S 2).getD j []).foldl
        (fun acc A => A.foldl insertNew acc) [])
      have hfold : ∀ (Ls : List (List (List ℕ))) (acc : List (List ℕ)),
          (v ∈ acc ∨ ∃ A ∈ Ls, v ∈ A) → v ∈ Ls.foldl (fun a B => B.foldl insertNew a) acc := by
        intro Ls
        induction Ls with
        | nil =>
          intro acc h
          rcases h with h | ⟨_, h, _⟩
          · exact h
          · simp at h
        | cons L Ls ih =>
          intro acc h
          rw [List.foldl_cons]
          apply ih
          rw [mem_fold_insertNew]
          rcases h with h | ⟨A, hA, hvA⟩
          · exact Or.inl (Or.inl h)
          · rcases List.mem_cons.mp hA with rfl | hA'
            · exact Or.inl (Or.inr hvA)
            · exact Or.inr ⟨A, hA', hvA⟩
      apply hfold
      right
      exact ⟨(readVectors C1 n S 2).getD i [], List.mem_map.mpr ⟨i, hi, rfl⟩, hv⟩
    have rv_orIn : ∀ (S : List ℕ) (w : ℕ) (t : Fin n),
        t ∈ orIn n C1 w → t.val ∈ S →
        (S.map fun j => if j = t.val then 1 else 0) ∈ (readVectors C1 n S 2).getD w [] := by
      intro S w t ht htS
      let ev := S.map fun j => if j = t.val then 1 else 0
      have hleaf : ev ∈ (readVectors C1 n S 2).getD t.val [] := by
        rw [rv_input S t.val t.isLt, leafVectors_def]
        simp [htS, ev]
      rw [mem_orIn] at ht
      rcases ht with rfl | ⟨k, hk, hreach, hop, hmem⟩
      · exact hleaf
      · have hkv : ev ∈ (readVectors C1 n S 2).getD (n + k) [] :=
          rv_or_step S k hk hop t.val hmem ev hleaf
        have hprop : ∀ m, m < C1.gates.length → k ∈ (orSets n C1).getD m [] →
            ev ∈ (readVectors C1 n S 2).getD (n + m) [] := by
          intro m
          induction m using Nat.strong_induction_on with
          | _ m ih =>
            intro hm hkm
            rw [orSets_mem_iff C1 m k hm] at hkm
            rcases hkm with rfl | ⟨hopm, u, hu, hnu, hltu, hku⟩
            · exact hkv
            · apply rv_or_step S m hm hopm u hu
              have heq : n + (u - n) = u := by omega
              rw [← heq]
              exact ih (u - n) (by omega) (by omega) hku
        obtain ⟨hnw, hmk⟩ := hreach
        have hlt : w - n < C1.gates.length := by
          by_contra hge
          have hlen : (orSets n C1).length = C1.gates.length := by
            delta orSets; rw [orFold_len]; simp
          have hdef : (orSets n C1).getD (w - n) [] = [] := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (orSets n C1).length ≤ w - n)]
          rw [hdef] at hmk
          simp at hmk
        have heq : n + (w - n) = w := by omega
        rw [← heq]
        exact hprop (w - n) hlt hmk
    -- Step 2c: Propagate any vector at a top a ∈ tops G C1 up to C1.output along OR gates!
    have rv_top_to_out : ∀ (S : List ℕ) (a : ℕ) (ha : a ∈ tops G C1) (v : List ℕ),
        v ∈ (readVectors C1 n S 2).getD (n + a) [] →
        v ∈ (readVectors C1 n S 2).getD C1.output [] := by
      intro S a ha v hva
      obtain ⟨haLt, haOp, haBel⟩ := (mem_tops a).mp ha
      have hwalk : ∀ d j, C1.gates.length - j = d → j < C1.gates.length →
          (j = a ∨ InCone n C1 a j) →
          v ∈ (readVectors C1 n S 2).getD (n + j) [] →
          v ∈ (readVectors C1 n S 2).getD C1.output [] := by
        intro d
        induction d using Nat.strong_induction_on with
        | _ d ih =>
          intro j hdj hj hreach hvj
          by_cases hjo : n + j = C1.output
          · rwa [← hjo]
          · obtain ⟨r, hr, hmem⟩ := hasReader j hj hjo
            have hlt : j < r := by
              have := hAO1.2.1 r hr (n + j) hmem
              omega
            have hcone : InCone n C1 a r := by
              rw [inCone_iff C1 r a hr]
              refine ⟨n + j, hmem, by omega, by omega, ?_⟩
              simpa using hreach.elim (fun e => Or.inl e.symm) Or.inr
            have hopr : (gateAt C1 r).op = GateOp.or := by
              have hmemr : gateAt C1 r ∈ C1.gates := by
                rw [gateAt_eq C1 r hr]; exact List.getElem_mem hr
              rcases hAO1.1 (gateAt C1 r) hmemr with hop | hop
              · exact (hTop1 a haLt r hr haOp haBel hop hcone).elim
              · exact hop
            have hvr : v ∈ (readVectors C1 n S 2).getD (n + r) [] :=
              rv_or_step S r hr hopr (n + j) hmem v hvj
            exact ih (C1.gates.length - r) (by omega) r rfl hr (Or.inr hcone) hvr
      exact hwalk (C1.gates.length - a) a rfl haLt (Or.inl rfl) hva
    -- Step 2d: Prove IsReadK n C1 2!
    have hRead2 : IsReadK n C1 2 := by
      intro S hPI
      have hStrue : graphFun G ∅ (setInput S) = true := by
        rw [← hC1fun]
        exact hPI.1
      delta graphFun at hStrue
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq] at hStrue
      obtain ⟨u, v, huv, huS, hvS⟩ := hStrue
      rw [setInput_def, decide_eq_true_eq] at huS hvS
      have hne : u ≠ v := G.ne_of_adj huv
      have hstar : s(u, v) ∈ starEdges G C1 := by
        by_contra hns
        have hmem : s(u, v) ∈ Ustar G C1 :=
          Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv, hns⟩
        rw [hUempty] at hmem
        exact Finset.notMem_empty _ hmem
      delta starEdges at hstar
      obtain ⟨a, haTop, hpair⟩ := Finset.mem_biUnion.mp hstar
      obtain ⟨⟨x0, x1⟩, hx01, hseq⟩ := Finset.mem_image.mp hpair
      obtain ⟨hx0, hx1⟩ := Finset.mem_product.mp hx01
      have hne01 : x0 ≠ x1 := by
        intro heq
        subst heq
        have := (Sym2.eq_iff.mp hseq)
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne rfl
      have hx0S : x0 ∈ S := by
        rcases Sym2.eq_iff.mp hseq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact huS
        · exact hvS
      have hx1S : x1 ∈ S := by
        rcases Sym2.eq_iff.mp hseq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hvS
        · exact huS
      let L := setList S
      have hx0L : x0.val ∈ L := by
        rw [show L = setList S from rfl, setList_def]
        simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        exact ⟨x0, hx0S, rfl⟩
      have hx1L : x1.val ∈ L := by
        rw [show L = setList S from rfl, setList_def]
        simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        exact ⟨x1, hx1S, rfl⟩
      have hv0 := rv_orIn L (opnd C1 a 0) x0 hx0 hx0L
      have hv1 := rv_orIn L (opnd C1 a 1) x1 hx1 hx1L
      obtain ⟨haLt, haOp, _⟩ := (mem_tops a).mp haTop
      let e0 := L.map fun j => if j = x0.val then 1 else 0
      let e1 := L.map fun j => if j = x1.val then 1 else 0
      let v01 := capAdd 2 (capAdd 2 (L.map fun _ => 0) e0) e1
      have hva : v01 ∈ (readVectors C1 n L 2).getD (n + a) [] := by
        rw [rv_gate L a haLt, haOp, opnd_inputs C1 hAO1 a haLt]
        change v01 ∈ ([(readVectors C1 n L 2).getD (opnd C1 a 0) [],
          (readVectors C1 n L 2).getD (opnd C1 a 1) []].foldl (andStep 2) [L.map fun _ => 0])
        simp only [List.foldl_cons, List.foldl_nil]
        rw [mem_andStep]
        refine ⟨capAdd 2 (L.map fun _ => 0) e0, ?_, e1, hv1, rfl⟩
        rw [mem_andStep]
        exact ⟨L.map fun _ => 0, by simp, e0, hv0, rfl⟩
      have hvout : v01 ∈ (readVectors C1 n L 2).getD C1.output [] :=
        rv_top_to_out L a haTop v01 hva
      have hsmall : v01.all (fun c => decide (c ≤ 2)) = true := by
        have hneVal : x0.val ≠ x1.val := fun h => hne01 (Fin.ext h)
        have hgen : ∀ (M : List ℕ),
            (capAdd 2 (capAdd 2 (M.map fun _ => 0) (M.map fun j => if j = x0.val then 1 else 0))
              (M.map fun j => if j = x1.val then 1 else 0)).all (fun c => decide (c ≤ 2)) = true := by
          intro M
          induction M with
          | nil => rfl
          | cons m ms ih =>
            rw [capAdd_def, capAdd_def]
            by_cases h0 : m = x0.val <;> by_cases h1 : m = x1.val
            · exact (hneVal (h0.symm.trans h1)).elim
            all_goals
              simp only [List.map_cons, List.zipWith_cons_cons, h0, h1, hneVal, hneVal.symm,
                ↓reduceIte, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨by decide, by rw [← capAdd_def, ← capAdd_def]; exact ih⟩
        exact hgen L
      delta readsAtMost
      exact List.any_eq_true.mpr ⟨v01, hvout, hsmall⟩
    exact ⟨C1, hAO1, fun y => by rw [congrFun hC1fun y, hGraphFun y], hC1le, hRead2⟩
