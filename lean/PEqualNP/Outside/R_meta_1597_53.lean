import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover

-- The last 24 rows cover every false input under coordinatewise inclusion.
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_1597_53
    (finalAnd :
      let rows : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,
        15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
      let x := fun (r : Fin 40) (i : Fin 11) => (rows.getD r.val 0).testBit i.val
      ∀ D : Circuit, IsAO2 11 D → D.size ≤ 21 → D.output + 1 = 11 + D.size →
        let isAnd := fun j : ℕ => (gateAt D j).op = .and
        let bad := fun j : ℕ => ∃ r : Fin 24, gateVal 11 D j (x (r.natAdd 16)) = true
        (∀ r : Fin 40, circuitFun 11 D (x r) = decide (r.val < 16)) →
        (∀ i < D.size, ∀ j < D.size, isAnd i → ¬ bad i →
          isAnd j → ¬ InCone 11 D i j) →
        (∃ i j : ℕ, i < D.size ∧ j < D.size ∧ i ≠ j ∧
          isAnd i ∧ bad i ∧ isAnd j ∧ bad j) →
        (gateAt D (D.output - 11)).op = .and → False)
    (finalOr :
      let rows : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,
        15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
      let x := fun (r : Fin 40) (i : Fin 11) => (rows.getD r.val 0).testBit i.val
      ∀ D : Circuit, IsAO2 11 D → D.size ≤ 21 → D.output + 1 = 11 + D.size →
        let isAnd := fun j : ℕ => (gateAt D j).op = .and
        let bad := fun j : ℕ => ∃ r : Fin 24, gateVal 11 D j (x (r.natAdd 16)) = true
        (∀ r : Fin 40, circuitFun 11 D (x r) = decide (r.val < 16)) →
        (∀ i < D.size, ∀ j < D.size, isAnd i → ¬ bad i →
          isAnd j → ¬ InCone 11 D i j) →
        (∃ i j : ℕ, i < D.size ∧ j < D.size ∧ i ≠ j ∧
          isAnd i ∧ bad i ∧ isAnd j ∧ bad j) →
        (gateAt D (D.output - 11)).op = .or → False)
    : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → (∀ a ∈ PEqualNP.TopForm.tops G C, Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧ (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧ ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C → ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧ ∀ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K → K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → PEqualNP.TopForm.TopForm (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → 2 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D).card → 22 ≤ D.size := by
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have getD_app_lt : ∀ (w t : List Bool) (i : ℕ), i < w.length →
      (w ++ t).getD i false = w.getD i false := by
    intro w t i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_app_self : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g0 gs ih =>
      intro w i hi
      rw [List.foldl_cons]
      have hlt : i < (stepW w g0).length := by
        change i < (w ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (stepW w g0) i hlt]
      exact getD_app_lt w _ i hi
  have foldl_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl stepW w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; simp at h
    | cons g0 gs ih =>
      intro w j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : w.length < (stepW w g0).length := by
          change w.length < (w ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [foldl_getD_lt gs (stepW w g0) w.length hlt]
        change (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]).getD w.length false = _
        rw [getD_app_self w _]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · have hilt : i < (stepW w g0).length := by
            change i < (w ++ [_]).length
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          simp only [hi, ↓reduceIte, foldl_getD_lt gs (stepW w g0) i hilt]
          exact (getD_app_lt w _ i hi).symm
        · simp only [hi, ↓reduceIte]
          exact getD_ge w i (Nat.le_of_not_lt hi)
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen : (stepW w g0).length + j' = w.length + (j' + 1) := by
          change (w ++ [_]).length + j' = w.length + (j' + 1)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (stepW w g0) j' g hj
  have wires_gate (n : ℕ) (C : Circuit) : ∀ (x : Fin n → Bool) (j : ℕ) (g : Gate),
      C.gates[j]? = some g →
      (C.wires (List.ofFn x)).getD (n + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
    intro x j g hj
    have h := foldl_gate C.gates (List.ofFn x) j g hj
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    rw [hlen] at h
    exact h
  have wires_inp (n : ℕ) (C : Circuit) : ∀ (x : Fin n → Bool) (w : ℕ) (hw : w < n),
      (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro x w hw
    have h := foldl_getD_lt C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw)
    change (C.gates.foldl stepW (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

  have wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
      (C.wires (List.ofFn x)).length = n + C.gates.length := by
    have hfold (gs : List Gate) : ∀ w, (gs.foldl stepW w).length = w.length + gs.length := by
      induction gs with
      | nil => intro; simp
      | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp only [stepW,List.length_append,List.length_cons,List.length_nil]
        omega
    change (C.gates.foldl stepW (List.ofFn x)).length = _
    rw [hfold, List.length_ofFn]

  have gate_read (C : Circuit) (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
      gateAt C j = g := by
    change C.gates.getD j ⟨.or,[]⟩ = g
    rw [List.getD_eq_getElem?_getD,h]
    rfl

  have and_inputs (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hg : C.gates[j]? = some g) (hop : g.op = .and) :
      gateVal n C j x = true ↔
        ∀ w ∈ g.inputs, w < n+j ∧ (C.wires (List.ofFn x)).getD w false = true := by
    unfold gateVal
    rw [wires_gate n C _ _ _ hg, hop]
    change (g.inputs.map _).all id = true ↔ _
    simp only [List.all_eq_true,List.mem_map]
    constructor
    · intro h k hk
      by_cases e : k < n+j
      · exact ⟨e, by simpa only [e, ↓reduceIte,id_eq] using h _ ⟨k,hk,rfl⟩⟩
      · have bad := h _ ⟨k,hk,rfl⟩
        simp [e] at bad
    · rintro h _ ⟨k, hk, rfl⟩
      rcases h k hk with ⟨e,he⟩
      simpa only [e, ↓reduceIte,id_eq] using he

  have or_inputs (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hg : C.gates[j]? = some g) (hop : g.op = .or) :
      gateVal n C j x = true ↔
        ∃ w ∈ g.inputs, w < n+j ∧ (C.wires (List.ofFn x)).getD w false = true := by
    unfold gateVal
    rw [wires_gate n C _ _ _ hg, hop]
    change (g.inputs.map _).any id = true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨_, h, hp⟩
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
      by_cases e : k < n+j
      · exact ⟨k,hk,e,by simpa only [e, ↓reduceIte,id_eq] using hp⟩
      · simp [e] at hp
    · rintro ⟨k,hk,e,he⟩
      refine ⟨_,List.mem_map.mpr ⟨k,hk,rfl⟩,?_⟩
      simpa only [e, ↓reduceIte,id_eq] using he


  have active_bound (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
      (ht : (C.wires (List.ofFn x)).getD w false = true) : w < n + C.gates.length := by
    by_contra! he
    have hge : (C.wires (List.ofFn x)).length ≤ w := by rwa [wires_len n C x]
    rw [List.getD_eq_default _ _ hge] at ht
    contradiction

  have wire_mono (n : ℕ) (C : Circuit) (mono : Monotone2 C) (x y : Fin n → Bool)
      (inc : ∀ a, x a = true → y a = true) :
      ∀ w, (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ht
      by_cases hw : w < n
      · rw [wires_inp n C y w hw]
        apply inc
        simpa only [wires_inp n C x w hw] using ht
      · have bound := active_bound n C x w ht
        let j := w-n
        have jlt : j < C.gates.length := by dsimp [j]; omega
        have row : w = n+j := by dsimp [j]; omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem jlt
        have mem : g ∈ C.gates := List.getElem_mem jlt
        rw [row] at ht ⊢
        change gateVal n C j x = true at ht
        change gateVal n C j y = true
        rcases (mono g mem).1 with e | e
        · apply (and_inputs n C y j g hg e).mpr
          intro a ha
          obtain ⟨early,hit⟩ := (and_inputs n C x j g hg e).mp ht a ha
          exact ⟨early,ih a (row ▸ early) hit⟩
        · obtain ⟨a,ha,early,hit⟩ := (or_inputs n C x j g hg e).mp ht
          exact (or_inputs n C y j g hg e).mpr ⟨a,ha,early,ih a (row ▸ early) hit⟩

  have outputReal (n : ℕ) (D : Circuit) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (nonempty : G.edgeFinset.Nonempty) (computes : circuitFun n D = graphFun G ∅) :
      n ≤ D.output ∧ D.output < n + D.size := by
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have foldLength (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
    have foldPrefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    constructor
    · by_contra low
      have hp : D.output < n := Nat.lt_of_not_ge low
      let p : Fin n := ⟨D.output, hp⟩
      let x (i : Fin n) := decide (i = p)
      have noSingle : ¬ ∃ a ∈ (∅ : Finset (Fin n)), x a = true := by simp
      have noPair : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        rintro ⟨u, v, adj, xu, xv⟩
        have uEq : u = p := of_decide_eq_true xu
        have vEq : v = p := of_decide_eq_true xv
        rw [uEq, vEq] at adj
        exact G.irrefl adj
      have reject : graphFun G ∅ x = false := by
        change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
          decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = false
        rw [decide_eq_false noSingle, decide_eq_false noPair]
        rfl
      have accept : circuitFun n D x = true := by
        change (D.gates.foldl step (List.ofFn x)).getD D.output false = true
        have bound : D.output < (List.ofFn x).length := by
          simpa only [List.length_ofFn] using hp
        rw [foldPrefix _ _ _ bound, List.getD_eq_getElem _ _ bound, List.getElem_ofFn]
        change x p = true
        exact decide_eq_true rfl
      have eq := congrFun computes x
      rw [accept, reject] at eq
      cases eq
    · by_contra high
      have past : n + D.size ≤ D.output := Nat.le_of_not_gt high
      obtain ⟨u, v, adj⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp
        (SimpleGraph.edgeFinset_nonempty.mp nonempty)
      let x (i : Fin n) := decide (i = u ∨ i = v)
      have accept : graphFun G ∅ x = true := by
        change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
          decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true
        have pair : ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true :=
          ⟨u, v, adj, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
        rw [decide_eq_true pair, Bool.or_true]
      have length : (D.wires (List.ofFn x)).length = n + D.size := by
        change (D.gates.foldl step (List.ofFn x)).length = n + D.gates.length
        rw [foldLength, List.length_ofFn]
      have reject : circuitFun n D x = false := List.getD_eq_default _ _ (length.symm ▸ past)
      have eq := congrFun computes x
      rw [reject, accept] at eq
      cases eq

  have outputLast (n : ℕ) (D : Circuit) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (least : IsLeastAO G D) (actual : n ≤ D.output ∧ D.output < n + D.size) :
      D.output + 1 = n + D.size := by
    obtain ⟨lower, upper⟩ := actual
    let k := D.output - n + 1
    let E : Circuit := ⟨D.gates.take k, D.output⟩
    have sizeBound : k ≤ D.gates.length := by
      change D.output < n + D.gates.length at upper
      dsimp [k]
      omega
    have sizeExact : (D.gates.take k).length = k := by
      rw [List.length_take, Nat.min_eq_left sizeBound]
    have model : IsAO2 n E := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        exact least.1.1 g (List.mem_of_mem_take hg)
      · intro i hi j hj
        change i < (D.gates.take k).length at hi
        have oldBound : i < D.gates.length := by rw [sizeExact] at hi; omega
        have gateEq : gateAt E i = gateAt D i := by
          change (D.gates.take k).getD i ⟨.or, []⟩ = D.gates.getD i ⟨.or, []⟩
          rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ oldBound, List.getElem_take]
        rw [gateEq] at hj
        exact least.1.2.1 i oldBound j hj
      · intro g hg
        exact least.1.2.2 g (List.mem_of_mem_take hg)
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have foldLength (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
    have foldKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    have eqFun : circuitFun n E = circuitFun n D := by
      funext x
      let w := List.ofFn x
      let pre := (D.gates.take k).foldl step w
      have preLength : pre.length = n + k := by
        change ((D.gates.take k).foldl step (List.ofFn x)).length = _
        rw [foldLength, List.length_ofFn, sizeExact]
      have inPrefix : D.output < pre.length := by
        rw [preLength]
        dsimp [k]
        omega
      have split : D.gates.foldl step w = (D.gates.drop k).foldl step pre := by
        calc
          _ = (D.gates.take k ++ D.gates.drop k).foldl step w :=
            congrArg (fun gs => gs.foldl step w) (List.take_append_drop k D.gates).symm
          _ = _ := by rw [List.foldl_append]
      change pre.getD D.output false = (D.gates.foldl step w).getD D.output false
      rw [split]
      exact (foldKeep _ _ _ inPrefix).symm
    have minimal := least.2.2 E model (eqFun.trans least.2.1)
    change D.gates.length ≤ (D.gates.take k).length at minimal
    rw [sizeExact] at minimal
    change D.output + 1 = n + D.gates.length
    dsimp [k] at minimal sizeBound
    omega

  intro _ _ D least top jTwo
  let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
    (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let _ : DecidableRel G.Adj := inferInstanceAs (DecidableRel (edgeGraph 11 _).Adj)
  let rows : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,
    15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let x (r : Fin 40) (i : Fin 11) := (rows.getD r.val 0).testBit i.val
  have fit : ∀ r : Fin 40, graphFun G ∅ (x r) = decide (r.val < 16) := by decide +kernel
  have cover : ∀ y : Fin 11 → Bool, graphFun G ∅ y = false →
      ∃ r : Fin 24, ∀ i, y i = true → x (r.natAdd 16) i = true := by decide +kernel
  have someEdge : G.edgeFinset.Nonempty := by decide +kernel
  classical
  change IsLeastAO G D at least
  change TopForm G D at top
  change 2 ≤ (junk G D).card at jTwo
  have ao := least.1
  have cMono : Monotone2 D := fun g h => ⟨ao.1 g h, (ao.2.2 g h).le⟩
  have inputOk (r : Fin 40) : circuitFun 11 D (x r) = decide (r.val < 16) := by
    rw [least.2.1, fit]
  let bad (j : ℕ) := ∃ r : Fin 24, gateVal 11 D j (x (r.natAdd 16)) = true
  have badSpec (j : ℕ) : bad j ↔ ∃ y : Fin 11 → Bool, gateVal 11 D j y = true ∧ graphFun G ∅ y = false := by
    constructor
    · rintro ⟨r,hit⟩
      have h : ¬ (r.natAdd 16).val < 16 := by
        change ¬ 16 + r.val < 16
        omega
      exact ⟨x (r.natAdd 16), hit, (fit _).trans (decide_eq_false h)⟩
    · rintro ⟨y,hit,negative⟩
      obtain ⟨r,sub⟩ := cover y negative
      exact ⟨r,wire_mono 11 D cMono y _ sub (11+j) hit⟩
  have orderTest : ∀ i < D.size, ∀ j < D.size, (gateAt D i).op = .and → ¬ bad i →
      (gateAt D j).op = .and → ¬ InCone 11 D i j := by
    intro i hi j hj iAnd iClean jAnd
    apply top i hi j hj iAnd _ jAnd
    intro y hit
    cases h : graphFun G ∅ y with
    | true => rfl
    | false => exact False.elim (iClean ((badSpec i).mpr ⟨y,hit,h⟩))
  have mark (j : ℕ) (member : j ∈ junk G D) :
      j < D.size ∧ (gateAt D j).op = .and ∧ bad j := by
    change j ∈ (Finset.range D.gates.length).filter (IsDirtyAnd 11 G D) at member
    obtain ⟨bound, dirty⟩ := Finset.mem_filter.mp member
    exact ⟨Finset.mem_range.mp bound, dirty.1, (badSpec j).mpr dirty.2.2⟩
  have two : ∃ i j : ℕ, i < D.size ∧ j < D.size ∧ i ≠ j ∧
      (gateAt D i).op = .and ∧ bad i ∧ (gateAt D j).op = .and ∧ bad j := by
    obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp jTwo
    have iMark := mark i hi
    have jMark := mark j hj
    exact ⟨i,j,iMark.1,jMark.1,ne,iMark.2.1,iMark.2.2,jMark.2⟩
  have out := outputReal 11 D G someEdge least.2.1
  have final := outputLast 11 D G least out
  have idx : D.output - 11 < D.gates.length := by
    change D.output - 11 < D.size
    omega
  let g := D.gates[D.output - 11]
  have get : D.gates[D.output - 11]? = some g := List.getElem?_eq_getElem idx
  have atOut : gateAt D (D.output - 11) = g := by
    change D.gates.getD (D.output - 11) ⟨.or,[]⟩ = g
    rw [List.getD_eq_getElem?_getD,get]
    rfl
  have gateOp : (gateAt D (D.output - 11)).op = .and ∨ (gateAt D (D.output - 11)).op = .or := by
    rw [atOut]
    exact ao.1 g (List.getElem_mem idx)
  by_contra! short
  have small : D.size ≤ 21 := by omega
  rcases gateOp with isAnd | isOr
  · exact finalAnd D ao small final inputOk orderTest two isAnd
  · exact finalOr D ao small final inputOk orderTest two isOr
