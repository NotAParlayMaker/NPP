import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_4801_1
  (flatBound :
    have x1 : Fin 13 → Bool := fun (x1 : Fin 13) =>
      decide (x1 = (0 : Fin 13) ∨ x1 = (1 : Fin 13) ∨ x1 = (3 : Fin 13) ∨ x1 = (9 : Fin 13));
    have x2 : Circuit → Prop := fun (x2 : Circuit) =>
      (∀ (x3 x4 : Fin 13), x1 (x3 - x4) = Bool.true →
        x2.eval ((List.ofFn fun (x6 : Fin 13) => decide (x6 = x3)) ++
          List.ofFn fun (x6 : Fin 13) => decide (x6 = x4)) = Bool.true) ∧
      ∀ (x3 : Finset (Fin 13)), x3.card = (4 : ℕ) →
        (∀ (x5 : Fin 13), {x6 ∈ x3 | x1 (x6 - x5) = Bool.true}.card ≤ (2 : ℕ)) →
        x2.eval ((List.ofFn fun (x6 : Fin 13) => decide (x6 ∈ x3)) ++
          List.ofFn fun (x6 : Fin 13) => decide (∀ x7 ∈ x3, x1 (x7 - x6) = Bool.false)) = Bool.false;
    ∀ (x3 : Circuit), Monotone2 x3 → ReadsBack (26 : ℕ) x3 → x2 x3 →
      (¬∃ (x7 : ℕ) (x8 : ℕ), (gateAt x3 x7).op = GateOp.and ∧
        (gateAt x3 x8).op = GateOp.and ∧
        InCone (26 : ℕ) x3 x7 x8) → (64 : ℕ) ≤ x3.size)
  (coldLift :
    have x1 : Fin 13 → Bool := fun (x1 : Fin 13) =>
      decide (x1 = (0 : Fin 13) ∨ x1 = (1 : Fin 13) ∨ x1 = (3 : Fin 13) ∨ x1 = (9 : Fin 13));
    have x2 : Finset (Fin 13) → Prop := fun (x2 : Finset (Fin 13)) =>
      x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin 13), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ);
    have x3 : Finset (Fin 13) → List Bool := fun (x3 : Finset (Fin 13)) =>
      (List.ofFn fun (x4 : Fin 13) => decide (x4 ∈ x3)) ++
          List.ofFn fun (x4 : Fin 13) => decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false);
    have x4 : Circuit → Prop := fun (x4 : Circuit) =>
      (∀ (x5 x6 : Fin 13), x1 (x5 - x6) = Bool.true →
        x4.eval ((List.ofFn fun (x8 : Fin 13) => decide (x8 = x5)) ++
          List.ofFn fun (x8 : Fin 13) => decide (x8 = x6)) = Bool.true) ∧
      ∀ (x5 : Finset (Fin 13)), x2 x5 → x4.eval (x3 x5) = Bool.false;
    ∀ (x5 : Circuit), Monotone2 x5 → ReadsBack (26 : ℕ) x5 → x4 x5 →
      (∃ (x9 : ℕ) (x10 : ℕ), (gateAt x5 x9).op = GateOp.and ∧
        (gateAt x5 x10).op = GateOp.and ∧
        InCone (26 : ℕ) x5 x9 x10 ∧
        ∀ (x11 : Finset (Fin 13)), x2 x11 → (x5.wires (x3 x11)).getD ((26 : ℕ) + x9) Bool.false = Bool.false) →
      ∃ (x10 : Circuit), Monotone2 x10 ∧ ReadsBack (26 : ℕ) x10 ∧ x4 x10 ∧
        (x10.size < x5.size ∨ x10.size = x5.size ∧ andPairs (26 : ℕ) x10 < andPairs (26 : ℕ) x5))
  (core :
    let S := singerLines3
    let row (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
    let fit (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let inner (C : Circuit) (i : ℕ) := (gateAt C i).op = .and ∧
      ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
    let K (C : Circuit) (i : ℕ) := (incidences S).filter fun e =>
      ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false
    ∀ C, fit C → (∃ i, inner C i) →
      (∀ i, inner C i → (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+i) false = true) ∧
        2 ≤ (K C i).card) →
      (∀ D, fit D → C.size ≤ D.size) →
      (∀ D, fit D → D.size = C.size → andPairs 26 C ≤ andPairs 26 D) → 64 ≤ C.size)
  : ∀ (x1 : Circuit), IsAO2 (26 : ℕ) x1 → x1.size < (64 : ℕ) →
    (∀ (x4 : Fin 26 → Bool), x1.eval (List.ofFn x4) = Bool.true ↔
      ∃ (x5 : Fin 13) (x6 : Fin 13), (x5 = x6 ∨ x5 = x6 + (1 : Fin 13) ∨ x5 = x6 + (3 : Fin 13) ∨ x5 = x6 + (9 : Fin 13)) ∧
        x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) →
    ∃ (x5 : Circuit), IsAO2 (26 : ℕ) x5 ∧ x5.size ≤ x1.size ∧
      (∀ (x6 : Fin 26 → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6)) ∧
      ¬∃ (x6 : ℕ) (x7 : ℕ), (gateAt x5 x6).op = GateOp.and ∧
        (gateAt x5 x7).op = GateOp.and ∧
        InCone (26 : ℕ) x5 x6 x7 := by
  classical
  -- Replacing the inputs of one AND by raw wires can only remove nested AND pairs.
  have coneOrder (n : ℕ) (C : Circuit) (i : ℕ) (hi : i < C.gates.length)
      (r : Gate) (hold : (gateAt C i).op = .and)
      (hr : ∀ w ∈ r.inputs, w < n) :
      let D : Circuit := {C with gates := C.gates.set i r}
      andPairs n D ≤ andPairs n C ∧
        (andPairs n D = andPairs n C →
          ∀ a b, (gateAt C a).op = .and → (gateAt C b).op = .and → InCone n C a b →
            (gateAt D a).op = .and ∧ (gateAt D b).op = .and ∧ InCone n D a b) := by
    let _ := gateOpDecEq
    let sub (a b : List (List ℕ)) :=
      a.length = b.length ∧ ∀ j k, k ∈ a.getD j [] → k ∈ b.getD j []
    have refl (a : List (List ℕ)) : sub a a := ⟨rfl, fun _ _ h => h⟩
    have step (a b : List (List ℕ)) (u v : Gate) (hs : sub a b)
        (hw : ∀ w ∈ u.inputs, n ≤ w → w ∈ v.inputs) :
        sub (coneStep n a u) (coneStep n b v) := by
      let body (cs : List (List ℕ)) (g : Gate) :=
        (g.inputs.filter fun w => decide (n ≤ w ∧ w < n + cs.length)).flatMap
          (fun w => (w - n) :: cs.getD (w - n) [])
      have hbody : ∀ k ∈ body a u, k ∈ body b v := by
        intro k hk
        obtain ⟨w, hwU, hk⟩ := List.mem_flatMap.mp hk
        have hfilter := List.mem_filter.mp hwU
        have hRangeP := of_decide_eq_true hfilter.2
        apply List.mem_flatMap.mpr
        refine ⟨w, List.mem_filter.mpr ⟨hw w hfilter.1 hRangeP.1, ?_⟩, ?_⟩
        · exact decide_eq_true ⟨hRangeP.1, hs.1 ▸ hRangeP.2⟩
        · rcases List.mem_cons.mp hk with heq | hprev
          · exact List.mem_cons.mpr (Or.inl heq)
          · exact List.mem_cons.mpr (Or.inr (hs.2 (w-n) k hprev))
      change sub (a ++ [body a u]) (b ++ [body b v])
      refine ⟨by simp [hs.1], ?_⟩
      intro j k hk
      by_cases hj : j < a.length
      · rw [List.getD_append _ _ _ _ hj] at hk
        rw [List.getD_append _ _ _ _ (hs.1 ▸ hj)]
        exact hs.2 j k hk
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hj)] at hk
        rw [List.getD_append_right _ _ _ _ (hs.1 ▸ Nat.le_of_not_lt hj), ← hs.1]
        generalize j - a.length = d at hk ⊢
        cases d with
        | zero => exact hbody k hk
        | succ t =>
          change k ∈ ([] : List ℕ) at hk
          exact (List.not_mem_nil hk).elim
    have tail (gs : List Gate) (a b : List (List ℕ)) (hs : sub a b) :
        sub (gs.foldl (coneStep n) a) (gs.foldl (coneStep n) b) := by
      induction gs generalizing a b with
      | nil => exact hs
      | cons g gs ih =>
        exact ih _ _ (step a b g g hs (fun _ h _ => h))
    let D : Circuit := {C with gates := C.gates.set i r}
    let pre := C.gates.take i
    let post := C.gates.drop (i+1)
    have old : C.gates = pre ++ C.gates[i] :: post := by
      change C.gates = C.gates.take i ++ C.gates[i] :: C.gates.drop (i+1)
      rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    have new : D.gates = pre ++ r :: post := by
      change C.gates.set i r = _
      rw [List.set_eq_take_append_cons_drop, ite_eq_left hi]
    have hdep : sub (cones n D) (cones n C) := by
      change sub (D.gates.foldl (coneStep n) []) (C.gates.foldl (coneStep n) [])
      rw [new, old, List.foldl_append, List.foldl_append]
      exact tail post _ _
        (step _ _ r C.gates[i] (refl _) (fun w hm hn => (Nat.not_lt_of_ge hn (hr w hm)).elim))
    have len : D.gates.length = C.gates.length := by
      change (C.gates.set i r).length = _
      simp
    have op (j : ℕ) (hj : (gateAt D j).op = .and) : (gateAt C j).op = .and := by
      by_cases e : j = i
      · simpa only [e] using hold
      · have same : gateAt D j = gateAt C j := by
          change (C.gates.set i r)[j]?.getD ⟨.or,[]⟩ = C.gates[j]?.getD ⟨.or,[]⟩
          simp [Ne.symm e]
        simpa only [same] using hj
    let P (E : Circuit) := ((Finset.range E.gates.length ×ˢ Finset.range E.gates.length).filter
      fun (p : ℕ × ℕ) => (gateAt E p.1).op = .and ∧ (gateAt E p.2).op = .and ∧ InCone n E p.1 p.2)
    have included : P D ⊆ P C := by
      intro p hp
      simp only [P, Finset.mem_filter] at hp ⊢
      exact ⟨by simpa only [len] using hp.1, op _ hp.2.1, op _ hp.2.2.1, hdep.2 p.2 p.1 hp.2.2.2⟩
    have andBound (E : Circuit) (j : ℕ) (hj : (gateAt E j).op = .and) : j < E.gates.length := by
      by_contra! he
      change (E.gates.getD j ⟨.or,[]⟩).op = .and at hj
      rw [List.getD_eq_default _ _ he] at hj
      cases hj
    show (P D).card ≤ (P C).card ∧ _
    refine ⟨Finset.card_le_card included, ?_⟩
    intro he a b ha hb hab
    change (P D).card = (P C).card at he
    have equal : P D = P C := Finset.eq_of_subset_of_card_le included he.ge
    have mem : (a,b) ∈ P C := by
      simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨andBound C _ ha, andBound C _ hb⟩, ha, hb, hab⟩
    rw [← equal] at mem
    exact (Finset.mem_filter.mp mem).2
  -- If forcing an inner gate off loses at most one flag, restore that flag locally.
  have patch :
      let S := singerLines3
      let fit := fun C : Circuit =>
        Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
          ∀ Q, IsQuadrangle S Q → C.eval (incidenceInput Q (missLines S Q)) = false
      let K := fun (C : Circuit) (i : ℕ) =>
        (incidences S).filter fun e =>
          ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval
            (incidenceInput {e.1} {e.2}) = false
      ∀ (C : Circuit) (i : ℕ), fit C → i < C.gates.length → (K C i).card ≤ 1 →
        ∃ r : Gate,
          (r = ⟨.or, []⟩ ∨ ∃ p l : Fin 13, p ∈ S l ∧ r = ⟨.and, [p.val, 13 + l.val]⟩) ∧
          let D : Circuit := {C with gates := C.gates.set i r}
          fit D ∧ ∀ Q, IsQuadrangle S Q →
            (D.wires (incidenceInput Q (missLines S Q))).getD (26 + i) false = false := by
    intro S fit K

    let leW := fun (a b : List Bool) =>
      a.length = b.length ∧ ∀ k, a.getD k false = true → b.getD k false = true

    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

    have leW_refl (a : List Bool) : leW a a := ⟨rfl, fun _ h => h⟩

    have extend (a b : List Bool) (u v : Bool) (hab : leW a b) (huv : u = true → v = true) :
        leW (a ++ [u]) (b ++ [v]) := by
      refine ⟨?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, hab.1]
      intro k h
      by_cases hk : k < a.length
      · rw [List.getD_append a [u] false k hk] at h
        rw [List.getD_append b [v] false k (hab.1 ▸ hk)]
        exact hab.2 k h
      · rw [List.getD_append_right a [u] false k (Nat.le_of_not_lt hk)] at h
        rw [List.getD_append_right b [v] false k (hab.1 ▸ Nat.le_of_not_lt hk), ← hab.1]
        cases hsub : k - a.length with
        | zero =>
          rw [hsub] at h
          exact huv h
        | succ t =>
          have hf : ([u] : List Bool).getD (t + 1) false = false := rfl
          rw [hsub, hf] at h
          contradiction

    let gateValue (w : List Bool) (g : Gate) : Bool :=
      g.op.eval (g.inputs.map fun i => w.getD i false)

    have gateValueMono (a b : List Bool) (g : Gate)
        (hOp : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hab : leW a b) :
        gateValue a g = true → gateValue b g = true := by
      unfold gateValue
      change g.op = .and ∨ g.op = .or at hOp
      rcases hOp with hAnd | hOr
      · rw [hAnd]
        change ((g.inputs.map fun k => a.getD k false).all id = true →
          (g.inputs.map fun k => b.getD k false).all id = true)
        intro h
        apply List.all_eq_true.mpr
        intro value mem
        obtain ⟨k,hk,rfl⟩ := List.mem_map.mp mem
        exact hab.2 k (List.all_eq_true.mp h _ (List.mem_map.mpr ⟨k,hk,rfl⟩))
      · rw [hOr]
        change ((g.inputs.map fun k => a.getD k false).any id = true →
          (g.inputs.map fun k => b.getD k false).any id = true)
        simp only [List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨_, ⟨k,hk,rfl⟩,hkV⟩
        exact ⟨_, ⟨k,hk,rfl⟩,hab.2 k hkV⟩

    have stepMono (a b : List Bool) (g : Gate) (hOp : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
        (hab : leW a b) : leW (step a g) (step b g) :=
      extend a b _ _ hab (gateValueMono a b g hOp hab)

    have foldMono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
        (a b : List Bool) (hab : leW a b) : leW (gs.foldl step a) (gs.foldl step b) := by
      induction gs generalizing a b with
      | nil => exact hab
      | cons g gs ih =>
        exact ih (fun d hd => hg d (List.mem_cons_of_mem _ hd)) _ _
          (stepMono a b g (hg g List.mem_cons_self) hab)

    let setGate (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

    let zeroGate : Gate := ⟨.or, []⟩

    let oldPrefix (C : Circuit) (j : ℕ) (x : List Bool) : List Bool :=
      (C.gates.take j).foldl step x

    have getOf {m : ℕ} (x : Fin m → Bool) (i : Fin m) :
        (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      exact List.getElem_ofFn _

    have foldKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi

    have foldLength (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [step]; omega

    have setWires (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
        (x : List Bool) :
        (setGate C j g).wires x = (C.gates.drop (j + 1)).foldl step (step (oldPrefix C j x) g) := by
      change (C.gates.set j g).foldl step x = _
      rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]

    have oldWires (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (x : List Bool) :
        C.wires x = (C.gates.drop (j + 1)).foldl step (step (oldPrefix C j x) C.gates[j]) := by
      have eq : C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) = C.gates := by
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      change C.gates.foldl step x = _
      nth_rw 1 [← eq]
      rw [List.foldl_append, List.foldl_cons]

    have setBelow (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
        (g : Gate) (mono : Monotone2 C) (x : List Bool)
        (h : gateValue (oldPrefix C j x) g = true → gateValue (oldPrefix C j x) C.gates[j] = true) :
        leW ((setGate C j g).wires x) (C.wires x) := by
      rw [setWires C j hj, oldWires C j hj]
      apply foldMono _ (fun b hb => (mono b (List.mem_of_mem_drop hb)).1)
      exact extend _ _ _ _ (leW_refl _) h

    have setZeroBelow (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
        (g : Gate) (mono : Monotone2 C) (x : List Bool) :
        leW ((setGate C j zeroGate).wires x) ((setGate C j g).wires x) := by
      rw [setWires C j hj, setWires C j hj]
      apply foldMono _ (fun b hb => (mono b (List.mem_of_mem_drop hb)).1)
      apply extend _ _ _ _ (leW_refl _)
      intro h
      cases h

    have sameAtGate (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
        (g : Gate) (x : List Bool)
        (eq : gateValue (oldPrefix C j x) g = gateValue (oldPrefix C j x) C.gates[j]) :
        (setGate C j g).eval x = C.eval x := by
      change ((setGate C j g).wires x).getD C.output false = (C.wires x).getD C.output false
      rw [setWires C j hj, oldWires C j hj]
      change ((C.gates.drop (j + 1)).foldl step
        (oldPrefix C j x ++ [gateValue (oldPrefix C j x) g])).getD C.output false =
        ((C.gates.drop (j + 1)).foldl step
          (oldPrefix C j x ++ [gateValue (oldPrefix C j x) C.gates[j]])).getD C.output false
      rw [eq]

    have minorModel {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
        (mono : Monotone2 C) (back : ReadsBack n C) (g : Gate)
        (legal : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (earlier : ∀ i ∈ g.inputs, i < n+j) :
        let E := setGate C j g
        Monotone2 E ∧ ReadsBack n E ∧ E.size = C.size ∧ gateAt E j = g ∧
          ∀ k ≠ j, gateAt E k = gateAt C k := by
      let E := setGate C j g
      have hl : E.gates.length = C.gates.length := by
        change (C.gates.set j g).length = C.gates.length
        exact List.length_set
      have atJ : gateAt E j = g := by
        change (C.gates.set j g).getD j ⟨.or,[]⟩ = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hj]
        rfl
      have atOther (k : ℕ) (h : k ≠ j) : gateAt E k = gateAt C k := by
        change (C.gates.set j g).getD k ⟨.or,[]⟩ = C.gates.getD k ⟨.or,[]⟩
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h.symm]
      refine ⟨?_, ?_, hl, atJ, atOther⟩
      · intro t ht
        obtain ⟨k,hk,eq⟩ := List.getElem_of_mem ht
        have atK : gateAt E k = t := (List.getD_eq_getElem _ _ hk).trans eq
        by_cases h : k = j
        · subst k
          rw [atJ] at atK
          exact atK ▸ legal
        · rw [atOther k h] at atK
          have hk' : k < C.gates.length := hl ▸ hk
          have newer : C.gates[k] = t := (List.getD_eq_getElem _ _ hk').symm.trans atK
          exact mono t (newer ▸ List.getElem_mem hk')
      · intro k hk i hi
        by_cases h : k = j
        · subst k
          rw [atJ] at hi
          exact earlier i hi
        · rw [atOther k h] at hi
          exact back k (hl ▸ hk) i hi

    let rawAnd (p l : Fin 13) : Gate := ⟨.and, [p.val, 13 + l.val]⟩
    have rowLen (X Y : Finset (Fin 13)) : (incidenceInput X Y).length = 26 := by
      change (List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ Y))).length = 26
      simp
    have pointRead (X Y : Finset (Fin 13)) (p : Fin 13) :
        (incidenceInput X Y).getD p.val false = decide (p ∈ X) := by
      change (List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ Y))).getD p.val false = _
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using p.isLt)]
      exact getOf _ p
    have lineRead (X Y : Finset (Fin 13)) (l : Fin 13) :
        (incidenceInput X Y).getD (13 + l.val) false = decide (l ∈ Y) := by
      change (List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ Y))).getD (13 + l.val) false = _
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega),
        List.length_ofFn, Nat.add_sub_cancel_left]
      exact getOf _ l

    have rawPrefix (C : Circuit) (i : ℕ) (p l : Fin 13) (X Y : Finset (Fin 13)) :
        gateValue (oldPrefix C i (incidenceInput X Y)) (rawAnd p l) =
          (decide (p ∈ X) && decide (l ∈ Y)) := by
      have hp : p.val < (incidenceInput X Y).length := by
        rw [rowLen]
        have := p.isLt
        omega
      have hl : 13 + l.val < (incidenceInput X Y).length := by
        rw [rowLen]
        have := l.isLt
        omega
      have wp : (oldPrefix C i (incidenceInput X Y)).getD p.val false = decide (p ∈ X) :=
        (foldKeep (C.gates.take i) (incidenceInput X Y) p.val hp).trans (pointRead X Y p)
      have wl : (oldPrefix C i (incidenceInput X Y)).getD (13 + l.val) false = decide (l ∈ Y) :=
        (foldKeep (C.gates.take i) (incidenceInput X Y) (13 + l.val) hl).trans (lineRead X Y l)
      have evaluateAnd (a b : Bool) : GateOp.eval .and [a, b] = (a && b) := by
        cases a <;> cases b <;> rfl
      change GateOp.eval .and [(oldPrefix C i (incidenceInput X Y)).getD p.val false,
        (oldPrefix C i (incidenceInput X Y)).getD (13 + l.val) false] = _
      rw [wp, wl, evaluateAnd]

    have flagLe (p l : Fin 13) (X Y : Finset (Fin 13)) (hp : p ∈ X) (hl : l ∈ Y) :
        leW (incidenceInput {p} {l}) (incidenceInput X Y) := by
      refine ⟨by simp only [rowLen], fun k h => ?_⟩
      by_cases hk : k < 13
      · let u : Fin 13 := ⟨k, hk⟩
        rw [pointRead {p} {l} u] at h
        rw [pointRead X Y u]
        have eq : u = p := Finset.mem_singleton.mp (of_decide_eq_true h)
        exact decide_eq_true (eq.symm ▸ hp)
      · by_cases hk' : k < 26
        · let u : Fin 13 := ⟨k - 13, by omega⟩
          have eq : 13 + u.val = k := by dsimp [u]; omega
          rw [← eq, lineRead] at h
          rw [← eq, lineRead]
          have eq' : u = l := Finset.mem_singleton.mp (of_decide_eq_true h)
          exact decide_eq_true (eq'.symm ▸ hl)
        · rw [List.getD_eq_default _ _ (by rw [rowLen]; omega)] at h
          cases h

    have atWire (C : Circuit) (i : ℕ) (hi : i < C.gates.length) (g : Gate)
        (X Y : Finset (Fin 13)) :
        ((setGate C i g).wires (incidenceInput X Y)).getD (26 + i) false =
          gateValue (oldPrefix C i (incidenceInput X Y)) g := by
      have plen : (oldPrefix C i (incidenceInput X Y)).length = 26 + i := by
        change ((C.gates.take i).foldl step (incidenceInput X Y)).length = _
        rw [foldLength, rowLen, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
      rw [setWires C i hi, foldKeep _ _ _ (by rw [← plen]; simp [step])]
      rw [← plen]
      change (oldPrefix C i (incidenceInput X Y) ++
        [gateValue (oldPrefix C i (incidenceInput X Y)) g]).getD _ false = _
      simp

    intro C i hfit hi few
    have mono : Monotone2 C := hfit.1
    have back : ReadsBack 26 C := hfit.2.1
    have goodOld : RightOnIncidentPairs S C := hfit.2.2.1
    have badOld : ∀ Q, IsQuadrangle S Q → C.eval (incidenceInput Q (missLines S Q)) = false :=
      hfit.2.2.2
    have memK (p l : Fin 13) :
        (p, l) ∈ K C i ↔ p ∈ S l ∧ (setGate C i zeroGate).eval (incidenceInput {p} {l}) = false := by
      have hm : (p, l) ∈ incidences S ↔ p ∈ S l := by
        delta incidences
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [K]
      rw [Finset.mem_filter, hm]

    have finish (g : Gate)
        (shape : g = zeroGate ∨ ∃ p l : Fin 13, p ∈ S l ∧ g = rawAnd p l)
        (legal : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (earlier : ∀ k ∈ g.inputs, k < 26 + i)
        (downs : ∀ X Y : Finset (Fin 13),
          leW ((setGate C i g).wires (incidenceInput X Y)) (C.wires (incidenceInput X Y)))
        (good : RightOnIncidentPairs S (setGate C i g))
        (clean : ∀ Q, IsQuadrangle S Q →
          ((setGate C i g).wires (incidenceInput Q (missLines S Q))).getD (26 + i) false = false) :
        ∃ r : Gate, (r = zeroGate ∨ ∃ p l : Fin 13, p ∈ S l ∧ r = rawAnd p l) ∧
          fit (setGate C i r) ∧ ∀ Q, IsQuadrangle S Q →
            ((setGate C i r).wires (incidenceInput Q (missLines S Q))).getD (26 + i) false = false := by
      have hm := minorModel C i hi mono back g legal earlier
      refine ⟨g, shape, ⟨hm.1, hm.2.1, good, ?_⟩, clean⟩
      intro Q hQ
      cases e : (setGate C i g).eval (incidenceInput Q (missLines S Q))
      · rfl
      · have h := (downs Q (missLines S Q)).2 C.output e
        change C.eval (incidenceInput Q (missLines S Q)) = true at h
        rw [badOld Q hQ] at h
        cases h

    by_cases nonempty : (K C i).Nonempty
    · obtain ⟨⟨p, l⟩, hlost⟩ := nonempty
      obtain ⟨incident, lost⟩ := (memK p l).mp hlost
      have orig := goodOld l p incident
      let r := rawAnd p l
      have oldTrue : gateValue (oldPrefix C i (incidenceInput {p} {l})) C.gates[i] = true := by
        cases e : gateValue (oldPrefix C i (incidenceInput {p} {l})) C.gates[i]
        · have eq := sameAtGate C i hi zeroGate (incidenceInput {p} {l}) (by
            change false = _
            exact e.symm)
          rw [lost, orig] at eq
          cases eq
        · rfl
      have downs (X Y : Finset (Fin 13)) :
          leW ((setGate C i r).wires (incidenceInput X Y)) (C.wires (incidenceInput X Y)) := by
        apply setBelow C i hi r mono
        intro h
        change gateValue (oldPrefix C i (incidenceInput X Y)) (rawAnd p l) = true at h
        rw [rawPrefix] at h
        obtain ⟨hp, hl⟩ := Bool.and_eq_true_iff.mp h
        have pref := foldMono (C.gates.take i)
          (fun g hg => (mono g (List.mem_of_mem_take hg)).1) _ _
          (flagLe p l X Y (of_decide_eq_true hp) (of_decide_eq_true hl))
        exact gateValueMono _ _ _ (mono C.gates[i] (List.getElem_mem hi)).1 pref oldTrue
      have good : RightOnIncidentPairs S (setGate C i r) := by
        intro l' p' inc'
        cases e : (setGate C i zeroGate).eval (incidenceInput {p'} {l'})
        · have eq := Finset.card_le_one.mp few (p', l') ((memK p' l').mpr ⟨inc', e⟩) (p, l) hlost
          have pe : p' = p := congrArg Prod.fst eq
          have le : l' = l := congrArg Prod.snd eq
          subst p'
          subst l'
          have he := sameAtGate C i hi r (incidenceInput {p} {l}) (by
            change gateValue (oldPrefix C i (incidenceInput {p} {l})) (rawAnd p l) = _
            rw [rawPrefix, oldTrue]
            simp)
          exact he.trans orig
        · exact (setZeroBelow C i hi r mono _).2 C.output e
      refine finish r (Or.inr ⟨p, l, incident, rfl⟩) (by simp [r, rawAnd]) ?_ downs good ?_
      · intro k hk
        change k ∈ [p.val, 13 + l.val] at hk
        rcases List.mem_pair.mp hk with e | e <;> have hp := p.isLt <;> have hl := l.isLt <;> omega
      · intro Q hQ
        change ((setGate C i (rawAnd p l)).wires (incidenceInput Q (missLines S Q))).getD (26 + i) false = false
        rw [atWire C i hi, rawPrefix]
        by_cases hp : p ∈ Q
        · have miss : l ∉ missLines S Q := by
            intro h
            delta missLines at h
            exact (Finset.disjoint_left.mp (Finset.mem_filter.mp h).2) incident hp
          rw [decide_eq_false miss, Bool.and_false]
        · rw [decide_eq_false hp, Bool.false_and]
    · have good : RightOnIncidentPairs S (setGate C i zeroGate) := by
        intro l p inc
        cases e : (setGate C i zeroGate).eval (incidenceInput {p} {l})
        · exact False.elim (nonempty ⟨(p, l), (memK p l).mpr ⟨inc, e⟩⟩)
        · rfl
      refine finish zeroGate (Or.inl rfl) (by simp [zeroGate]) (by intro k hk; cases hk)
        (fun X Y => setBelow C i hi zeroGate mono _ (by intro h; cases h)) good ?_
      intro Q hQ
      rw [atWire C i hi]
      rfl
  intro C ao tiny correct
  let S := singerLines3
  let row (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
  let fit (D : Circuit) := Monotone2 D ∧ ReadsBack 26 D ∧ RightOnIncidentPairs S D ∧
    ∀ Q, IsQuadrangle S Q → D.eval (row Q) = false
  let inner (D : Circuit) (i : ℕ) := (gateAt D i).op = .and ∧
    ∃ j, (gateAt D j).op = .and ∧ InCone 26 D i j
  let K (D : Circuit) (i : ℕ) := (incidences S).filter fun e =>
    ({D with gates := D.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false
  let db (a : Fin 13) : Bool := decide (a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 9)
  let oldQ (Q : Finset (Fin 13)) := Q.card = 4 ∧
    ∀ l : Fin 13, (Q.filter fun p => db (p - l) = true).card ≤ 2
  let oldRow (Q : Finset (Fin 13)) := (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
    List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, db (p-l) = false)
  have geom : ∀ p l : Fin 13, p ∈ S l ↔ db (p - l) = true := by
    decide +kernel
  have edge : ∀ p l : Fin 13, p ∈ S l ↔ p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9 := by
    decide +kernel
  have quad (Q : Finset (Fin 13)) : IsQuadrangle S Q ↔ oldQ Q := by
    have eq (l : Fin 13) : Q ∩ S l = Q.filter fun p => db (p - l) = true := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact and_congr_right fun _ => geom p l
    change (_ ∧ ∀ l, (Q ∩ S l).card ≤ 2) ↔
      (_ ∧ ∀ l, (Q.filter fun p => db (p-l) = true).card ≤ 2)
    simp only [eq]
  have rowEq (Q : Finset (Fin 13)) : row Q = oldRow Q := by
    change List.ofFn _ ++ List.ofFn _ = List.ofFn _ ++ List.ofFn _
    apply congrArg (List.append (List.ofFn fun p : Fin 13 => decide (p ∈ Q)))
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change (l ∈ (Finset.univ.filter fun w : Fin 13 => Disjoint (S w) Q)) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right]
    exact forall₂_congr fun p _ => by rw [geom]; simp
  have legacy (D : Circuit) :
      (RightOnIncidentPairs S D ∧ ∀ Q, IsQuadrangle S Q → D.eval (row Q) = false) ↔
      ((∀ p l : Fin 13, db (p-l) = true →
        D.eval ((List.ofFn fun a : Fin 13 => decide (a = p)) ++
          List.ofFn fun b : Fin 13 => decide (b = l)) = true) ∧
        ∀ Q, oldQ Q → D.eval (oldRow Q) = false) := by
    constructor
    · rintro ⟨pos, neg⟩
      refine ⟨?_, ?_⟩
      · intro p l hp
        have h := pos l p ((geom p l).mpr hp)
        change D.eval ((List.ofFn fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
          List.ofFn fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))) = true at h
        simpa only [Finset.mem_singleton] using h
      · intro Q hQ
        rw [← rowEq]
        exact neg Q ((quad Q).mpr hQ)
    · rintro ⟨pos, neg⟩
      refine ⟨?_, ?_⟩
      · intro l p hp
        change D.eval ((List.ofFn fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
          List.ofFn fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))) = true
        simpa only [Finset.mem_singleton] using pos p l ((geom p l).mp hp)
      · intro Q hQ
        rw [rowEq]
        exact neg Q ((quad Q).mp hQ)
  have coordinates (X Y : Finset (Fin 13)) :
      ∃ x : Fin 26 → Bool, incidenceInput X Y = List.ofFn x ∧
        (∀ p, x (Fin.castAdd 13 p) = true ↔ p ∈ X) ∧
        (∀ l, x (Fin.natAdd 13 l) = true ↔ l ∈ Y) := by
    let x : Fin 26 → Bool := Fin.addCases (motive := fun _ => Bool) (fun p : Fin 13 => decide (p ∈ X))
      (fun l : Fin 13 => decide (l ∈ Y))
    refine ⟨x, ?_, ?_, ?_⟩
    · change (_ ++ _) = List.ofFn x
      rw [List.ofFn_add (n := 13) (m := 13)]
      congr 1
    · intro p
      simp [x]
    · intro l
      simp only [x, Fin.addCases_right, decide_eq_true_eq]
  have inputFit : fit C := by
    refine ⟨?_, ao.2.1, ?_, ?_⟩
    · intro g hg
      exact ⟨by simpa using ao.1 g hg, (ao.2.2 g hg).le⟩
    · intro l p hp
      obtain ⟨x, hx, hP, hL⟩ := coordinates {p} {l}
      rw [hx]
      exact (correct x).mpr ⟨p, l, (edge p l).mp hp, (hP _).mpr (by simp), (hL _).mpr (by simp)⟩
    · intro Q hQ
      obtain ⟨x, hx, hP, hL⟩ := coordinates Q (missLines S Q)
      change C.eval (incidenceInput Q (missLines S Q)) = false
      rw [hx]
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,hpl,hp,hl⟩ := (correct x).mp h
      have hmiss := (hL l).mp hl
      change l ∈ (Finset.univ.filter fun w : Fin 13 => Disjoint (S w) Q) at hmiss
      exact Finset.disjoint_left.mp (Finset.mem_filter.mp hmiss).2 ((edge p l).mpr hpl) ((hP p).mp hp)
  -- Minimize gate count, then nested AND pairs among circuits passing the same tests.
  let sizes (s : ℕ) := ∃ D : Circuit, fit D ∧ D.size = s
  have sizesNE : ∃ s, sizes s := ⟨C.size, C, inputFit, rfl⟩
  let m := Nat.find sizesNE
  have mOK : sizes m := Nat.find_spec sizesNE
  let counts (k : ℕ) := ∃ D : Circuit, fit D ∧ D.size = m ∧ andPairs 26 D = k
  have countsNE : ∃ k, counts k := by
    obtain ⟨D, hD, hs⟩ := mOK
    exact ⟨andPairs 26 D, D, hD, hs, rfl⟩
  obtain ⟨E, fitE, sizeE, countE⟩ := Nat.find_spec countsNE
  have minSize (D : Circuit) (hD : fit D) : E.size ≤ D.size := by
    rw [sizeE]
    exact Nat.find_min' sizesNE ⟨D, hD, rfl⟩
  have minCount (D : Circuit) (hD : fit D) (hs : D.size = E.size) :
      andPairs 26 E ≤ andPairs 26 D := by
    rw [countE]
    exact Nat.find_min' countsNE ⟨D, hD, hs.trans sizeE, rfl⟩
  have tinyE : E.size < 64 := lt_of_le_of_lt (minSize C inputFit) tiny
  have coldImpossible (D : Circuit) (hD : fit D)
      (hsize : D.size ≤ E.size) (hcount : andPairs 26 D ≤ andPairs 26 E)
      (i j : ℕ) (hi : (gateAt D i).op = .and) (hj : (gateAt D j).op = .and)
      (hcone : InCone 26 D i j)
      (hfalse : ∀ Q, IsQuadrangle S Q → (D.wires (row Q)).getD (26+i) false = false) :
      False := by
    obtain ⟨A, ha, hb, hc, changeD⟩ :=
      coldLift D hD.1 hD.2.1 ((legacy D).mp hD.2.2)
        ⟨i, j, hi, hj, hcone, fun Q hQ => by
          change (D.wires (oldRow Q)).getD (26+i) false = false
          rw [← rowEq]
          exact hfalse Q ((quad Q).mpr hQ)⟩
    have fitA : fit A := ⟨ha, hb, (legacy A).mpr hc⟩
    rcases changeD with hlt | ⟨hs, hlt⟩
    · exact (Nat.not_lt_of_ge (minSize A fitA)) (lt_of_lt_of_le hlt hsize)
    · have hsame : A.size = E.size := le_antisymm (hs.le.trans hsize) (minSize A fitA)
      exact (Nat.not_lt_of_ge (minCount A fitA hsame)) (lt_of_lt_of_le hlt hcount)
  have nonflat : ∃ i, inner E i := by
    by_contra h
    have none : ¬∃ i j, (gateAt E i).op = .and ∧ (gateAt E j).op = .and ∧ InCone 26 E i j := by
      rintro ⟨i,j,hi,hj,hc⟩
      exact h ⟨i, hi, j, hj, hc⟩
    have tests := (legacy E).mp fitE.2.2
    exact (Nat.not_le_of_lt tinyE) (flatBound E fitE.1 fitE.2.1
      ⟨tests.1, fun Q hcard hlines => tests.2 Q ⟨hcard, hlines⟩⟩ none)
  have robust (i : ℕ) (hi : inner E i) :
      (∃ Q, IsQuadrangle S Q ∧ (E.wires (row Q)).getD (26+i) false = true) ∧
      2 ≤ (K E i).card := by
    obtain ⟨hai,j,haj,hij⟩ := hi
    constructor
    · by_contra hhot
      exact coldImpossible E fitE le_rfl le_rfl i j hai haj hij (fun Q hQ =>
        Bool.eq_false_iff.mpr fun ht => hhot ⟨Q, hQ, ht⟩)
    · by_contra hcard
      have hiBound : i < E.gates.length := by
        by_contra! out
        change (E.gates.getD i ⟨.or, []⟩).op = .and at hai
        rw [List.getD_eq_default _ _ out] at hai
        cases hai
      obtain ⟨r, raw, fitD, hfalse⟩ := patch E i fitE hiBound (by omega : (K E i).card ≤ 1)
      let D : Circuit := {E with gates := E.gates.set i r}
      have hs : D.size = E.size := by
        exact List.length_set
      have predecessors : ∀ w ∈ r.inputs, w < 26 := by
        intro w hw
        rcases raw with rfl | ⟨p,l,_,rfl⟩
        · cases hw
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact lt_trans p.isLt (by decide)
          · have := l.isLt
            omega
      obtain ⟨le, retain⟩ := coneOrder 26 E i hiBound r hai predecessors
      have eq : andPairs 26 D = andPairs 26 E := le_antisymm le (minCount D fitD hs)
      obtain ⟨di, dj, dc⟩ := retain eq i j hai haj hij
      exact coldImpossible D fitD hs.le le i j di dj dc hfalse
  exact False.elim ((Nat.not_le_of_lt tinyE) (core E fitE nonflat robust (minSize) (minCount)))
