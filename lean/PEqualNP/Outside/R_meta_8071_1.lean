import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8071_1
    (hTwo : ∀ (G : SimpleGraph (Fin 11)) [_inst : DecidableRel G.Adj],
      G = edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        (junk G C).card = 2 →
        (∃ a b : ℕ, a ∈ junk G C ∧ b ∈ junk G C ∧ a ≠ b ∧ ¬InCone 11 C a b ∧ ¬InCone 11 C b a) →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G C → ∃ g ∈ junk G C, gateVal 11 C g (pairInput u v) = true) →
        5 ≤ (Ustar G C).card →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (hThreeOrMore : ∀ (G : SimpleGraph (Fin 11)) [_inst : DecidableRel G.Adj],
      G = edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
          (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        3 ≤ (junk G C).card →
        (∃ a b : ℕ, a ∈ junk G C ∧ b ∈ junk G C ∧ a ≠ b ∧ ¬InCone 11 C a b ∧ ¬InCone 11 C b a) →
        (∀ u v : Fin 11, s(u, v) ∈ Ustar G C → ∃ g ∈ junk G C, gateVal 11 C g (pairInput u v) = true) →
        5 ≤ (Ustar G C).card →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  let G : SimpleGraph (Fin 11) := edgeGraph 11
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  dsimp only
  intro C hsize hleast htop hjunk hinc hcover hthree hdouble
  by_cases h5 : 5 ≤ (Ustar G C).card
  · rcases lt_or_eq_of_le hjunk with hj3 | hj2
    · exact hThreeOrMore G rfl C hsize hleast htop hj3 hinc hcover h5 hdouble
    · exact hTwo G rfl C hsize hleast htop hj2.symm hinc hcover h5 hdouble
  have hU4 : (Ustar G C).card ≤ 4 := by omega
  letI : DecidableEq GateOp := gateOpDecEq
  let n : ℕ := 11
  have hAO : IsAO2 n C := hleast.1
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepWire]; omega
  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]; exact key
  let val (C' : Circuit) (x : List Bool) (u : ℕ) : Bool := (C'.wires x).getD u false
  have gateAt_eq {C' : Circuit} {j : ℕ} (hj : j < C'.gates.length) : gateAt C' j = C'.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have gateAt_mem {C' : Circuit} {j : ℕ} (hj : j < C'.gates.length) : gateAt C' j ∈ C'.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj
  have val_input {C' : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C' x u = x.getD u false := by
    change (C'.gates.foldl stepWire x).getD u false = x.getD u false
    exact foldl_getD_lt _ _ _ (by omega)
  have val_ge {C' : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C'.gates.length ≤ u) : val C' x u = false := by
    change (C'.gates.foldl stepWire x).getD u false = false
    apply getD_ge; change (C'.gates.foldl stepWire x).length ≤ u; rw [foldl_length]; omega
  have val_gate {C' : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C'.gates.length) :
      val C' x (n + j) = (gateAt C' j).op.eval ((gateAt C' j).inputs.map fun i =>
        if i < n + j then val C' x i else false) := by
    rw [← hx, gateAt_eq hj]; exact foldl_getD_gate C'.gates x j hj
  have val_or {C' : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C'.gates.length) (hop : (gateAt C' r).op = GateOp.or) :
      val C' x (n + r) = true ↔ ∃ i ∈ (gateAt C' r).inputs, i < n + r ∧ val C' x i = true := by
    rw [val_gate hx hr, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [ite_eq_right hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
  have val_and {C' : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C'.gates.length) (hop : (gateAt C' r).op = GateOp.and) :
      val C' x (n + r) = true ↔ ∀ i ∈ (gateAt C' r).inputs, i < n + r ∧ val C' x i = true := by
    rw [val_gate hx hr, hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
      · rw [ite_eq_right hlt] at h'; cases h'
    · intro h i hi
      rw [ite_eq_left (h i hi).1]; exact (h i hi).2
  have val_ofFn (C' : Circuit) (x : Fin n → Bool) (u : Fin n) :
      val C' (List.ofFn x) u.val = x u := by
    rw [val_input (by simp [n]) u.isLt]; fin_cases u <;> rfl
  have gateVal_eq_val (C' : Circuit) (j : ℕ) (x : Fin n → Bool) :
      gateVal n C' j x = val C' (List.ofFn x) (n + j) := rfl
  -- OrStep and reachability
  let OrStep (w w' : ℕ) : Prop :=
    ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      w' ∈ (gateAt C k).inputs ∧ w' < n + k
  have orStep_up {x : List Bool} (hx : x.length = n) {w w' : ℕ}
      (h : Relation.ReflTransGen OrStep w w') (hv : val C x w' = true) :
      val C x w = true := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hstep _ ih =>
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩
  have or_trace {x : List Bool} (hx : x.length = n) :
      ∀ w : ℕ, val C x w = true →
        ∃ w', Relation.ReflTransGen OrStep w w' ∧ val C x w' = true ∧
          (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hw : w < n
      · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
      · by_cases hlen : n + C.gates.length ≤ w
        · rw [val_ge hx hlen] at hv; cases hv
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < C.gates.length := by omega
          by_cases hop : (gateAt C k).op = GateOp.or
          · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
            obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
            exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
          · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩
  have pairInput_left (u v : Fin n) : pairInput u v u = true := by simp [pairInput]
  have pairInput_true (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by simp [pairInput]
  have graphFun_pair (u v : Fin n) :
      graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, pairInput_true]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (G.irrefl hab).elim
      · exact hab
      · exact hab.symm
      · exact (G.irrefl hab).elim
    · intro h; exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
  have operand_trace (u v : Fin n) (p : ℕ)
      (hv : val C (List.ofFn (pairInput u v)) p = true) :
      (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen OrStep p t.val) ∨
      (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
        Relation.ReflTransGen OrStep p (n + h) ∧
        val C (List.ofFn (pairInput u v)) (n + h) = true) := by
    obtain ⟨w', hr, hv', hw'⟩ := or_trace (by simp [n]) p hv
    rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
    · left; refine ⟨⟨w', hlt⟩, ?_, hr⟩
      have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
      rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
      exact (pairInput_true u v _).mp h1.symm
    · right; exact ⟨h, hh, hop, hr, hv'⟩
  have reach_var_val (x : Fin n → Bool) (p : ℕ) (t : Fin n)
      (hr : Relation.ReflTransGen OrStep p t.val) (ht : x t = true) :
      val C (List.ofFn x) p = true :=
    orStep_up (by simp [n]) hr (by rw [val_ofFn]; exact ht)
  have edge_trace (u v : Fin n) (huv : graphFun G ∅ (pairInput u v) = true) :
      ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
        Relation.ReflTransGen OrStep C.output (n + a) ∧
        val C (List.ofFn (pairInput u v)) (n + a) = true := by
    have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
      congrFun hleast.2.1
    rcases operand_trace u v C.output (by rw [hout]; exact huv) with ⟨t, _, hr⟩ | h
    · exfalso
      have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
      rw [hout] at h1
      exact G.irrefl ((graphFun_pair t t).mp h1)
    · exact h
  have below_of_reach (a : ℕ) (hr : Relation.ReflTransGen OrStep C.output (n + a))
      (x : Fin n → Bool) (hv : val C (List.ofFn x) (n + a) = true) : graphFun G ∅ x = true := by
    have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
      congrFun hleast.2.1
    rw [← hout]; exact orStep_up (by simp [n]) hr hv
  -- Cones & OrSets characterization
  have cones_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [coneStep]; omega
  have cones_char (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk; simp only [coneStep, List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩; refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]; exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩; refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)] at h3; exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp only [coneStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]; simp [hlen]
        rw [e2, e1]; simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩; refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]; exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩; rw [key (w - n) (by omega)] at h3; exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          simp only [coneStep, List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_none (by simp; omega)]; rfl
        rw [e0]; constructor <;> intro h0
        · simp at h0
        · rcases h0 with ⟨h0, _⟩; simp at h0; omega
  have inCone_iff (i j : ℕ) :
      InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
        (i = k ∨ InCone n C i k) := by
    have h := cones_char C.gates i j
    unfold InCone cones gateAt; rw [h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩; refine ⟨h0, w - n, by omega, ?_, h3⟩
      rwa [show n + (w - n) = w from by omega]
    · rintro ⟨h0, k, hk, hw, h3⟩; refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
      simpa [n] using h3
  have orStep_le {w w' : ℕ} (h : Relation.ReflTransGen OrStep w w') : w' ≤ w := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact le_rfl
    | head hstep _ ih => obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep; omega
  have orStep_cone {w w' : ℕ} (h : Relation.ReflTransGen OrStep w w') :
      ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro k h' h1 h2; left; omega
    | @head a c hstep hrest ih =>
      intro k h' h1 h2
      obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
      have hk : k0 = k := Nat.add_left_cancel (e.symm.trans h1); subst hk
      have hle := orStep_le hrest
      obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
      subst hk1; right; rw [inCone_iff]
      exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
  have operand_cone {a p h : ℕ} (ha : a < C.gates.length)
      (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
      (hr : Relation.ReflTransGen OrStep p (n + h)) : InCone n C h a := by
    have hle := orStep_le hr
    obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
    rw [inCone_iff]; exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
  have orSets_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [orStep]; omega
  have orSets_char (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
            i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j; rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep n) []).length = gs.length := by rw [orSets_len]; simp
      have key : ∀ k, k < gs.length →
          (orStep n (gs.foldl (orStep n) []) g).getD k [] =
            (gs.foldl (orStep n) []).getD k [] := by
        intro k hk; simp only [orStep, List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]; constructor
        · rintro ⟨_, h3⟩; refine ⟨by simp; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩; rw [key (w - n) (by omega)]; exact h3
        · rintro ⟨_, h3⟩; refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3; exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
            simp only [orStep, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]; simp [hlen, hop]
          rw [e2]; simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl h3⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - n) (by omega)]; exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - n) (by omega)] at h3; exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
            simp only [orStep, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]; simp [hlen, hop]
          rw [e2]; simp only [List.mem_singleton]; constructor
          · intro h3; exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
          simp only [orStep, List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_none (by simp; omega)]; rfl
        rw [e0]; constructor <;> intro h0
        · simp at h0
        · rcases h0 with ⟨h0, _⟩; simp at h0; omega
  have orReaches_iff (k g : ℕ) :
      OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
    have h := orSets_char C.gates g k
    unfold OrReaches orSets gateAt; simp only [Nat.add_sub_cancel_left]; rw [h]
    constructor
    · rintro ⟨_, hk, h3⟩; refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
    · rintro ⟨hk, h3⟩; refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
  have reach_orReaches {w w2 : ℕ} (h : Relation.ReflTransGen OrStep w w2) :
      ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro g h1 hg; subst h1; exact (orReaches_iff g g).mpr ⟨hg, Or.inl rfl⟩
    | @head a c hstep hrest ih =>
      intro g h1 hg; obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (orReaches_iff k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩
  have orReaches_reach (g : ℕ) : ∀ w, OrReaches n C w g →
      Relation.ReflTransGen OrStep w (n + g) ∧ g < C.gates.length := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h; have hnw : n ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp h
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
  have mem_orIn_reach {p : ℕ} (u : Fin n) (hu : u ∈ orIn n C p) :
      Relation.ReflTransGen OrStep p u.val := by
    simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rcases hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
  have reach_mem_orIn {p : ℕ} (u : Fin n) (hr : Relation.ReflTransGen OrStep p u.val) :
      u ∈ orIn n C p := by
    simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
  have topData {a : ℕ} (ha : a ∈ tops G C) :
      a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
  have junkData {a : ℕ} (ha : a ∈ junk G C) :
      a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
    rcases Finset.mem_filter.mp ha with ⟨_, hop, hal, hd⟩; exact ⟨hal, hop, hd⟩
  have binaryInputs {a : ℕ} (ha : a < C.gates.length) : ∃ p q, (gateAt C a).inputs = [p, q] :=
    List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  have opndMem {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) : opnd C a b ∈ (gateAt C a).inputs := by
    obtain ⟨p, q, hpq⟩ := binaryInputs ha; fin_cases b <;> simp [opnd, hpq]
  have opndBound {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) : opnd C a b < n + a :=
    hAO.2.1 a ha _ (opndMem ha b)
  have andValBoth {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      (x : Fin n → Bool) :
      gateVal n C a x = true ↔
        val C (List.ofFn x) (opnd C a 0) = true ∧ val C (List.ofFn x) (opnd C a 1) = true := by
    rw [gateVal_eq_val, val_and (by simp [n]) ha hop]; constructor
    · intro h; exact ⟨(h _ (opndMem ha 0)).2, (h _ (opndMem ha 1)).2⟩
    · intro h i hi; refine ⟨hAO.2.1 a ha i hi, ?_⟩
      obtain ⟨p, q, hpq⟩ := binaryInputs ha
      rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
      · simpa [opnd, hpq] using h.1
      · have e : i = q := List.mem_singleton.mp hq; subst i; simpa [opnd, hpq] using h.2
  have andValOperands {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      (x : Fin n → Bool) :
      gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
    rw [andValBoth ha hop]; constructor
    · intro h b; fin_cases b; exact h.1; exact h.2
    · intro h; exact ⟨h 0, h 1⟩
  have operandReachCone {a h : ℕ} (ha : a < C.gates.length) {b : Fin 2}
      (hr : OrReaches n C (opnd C a b) h) : InCone n C h a :=
    operand_cone ha (opndMem ha b) (opndBound ha b) (orReaches_reach h _ hr).1
  have operandOrAndJunk {a h : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) (hh : (gateAt C h).op = GateOp.and) :
      h ∈ junk G C := by
    have hlen := (orReaches_reach h _ hr).2
    have hnb : ¬ BelowF G C h := fun hb => htop h hlen a ha hh hb hop (operandReachCone ha hr)
    have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
      by_contra hne; apply hnb; intro x hx; by_contra hf
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
  have inputsAsOpnd {m z : ℕ} (hm : m < C.gates.length) (hz : z ∈ (gateAt C m).inputs) :
      ∃ b : Fin 2, z = opnd C m b := by
    obtain ⟨p, q, hpq⟩ := binaryInputs hm
    rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
    · exact ⟨0, by simp [opnd, hpq]⟩
    · have e : z = q := List.mem_singleton.mp hq; exact ⟨1, by simpa [opnd, hpq] using e⟩
  have sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
      (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
      val C (List.ofFn x) (opnd C a b) = true :=
    reach_var_val x _ t (mem_orIn_reach t ht) hx
  have andFromInputs {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
      {x : Fin n → Bool} {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
      (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
    (andValBoth ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩
  have topAdj {a : ℕ} (ha : a ∈ tops G C) {u v : Fin n}
      (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) : G.Adj u v := by
    obtain ⟨hl, ho, hb⟩ := topData ha
    exact (graphFun_pair u v).mp (hb _ (andFromInputs hl ho hu hv (pairInput_left u v) (by simp [pairInput])))
  have acceptedTop {u v : Fin n} (hadj : G.Adj u v) :
      ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
    obtain ⟨a, hl, ho, hr, hv⟩ := edge_trace u v ((graphFun_pair u v).mpr hadj)
    have hand := (hAO.1 _ (gateAt_mem hl)).resolve_right ho
    have hb : BelowF G C a := fun x hx => below_of_reach a hr x (gateVal_eq_val C a x ▸ hx)
    refine ⟨a, ?_, hv⟩
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using And.intro hl (And.intro hand hb)
  have operandSupport {a : ℕ} (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and)
      {b : Fin 2} {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
      (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
        ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
    rcases operand_trace u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
    · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
    · have hr' := reach_orReaches hr j rfl hj
      exact .inr ⟨j, operandOrAndJunk ha ho hr' ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩
  have andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr; intro v hv
    simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with he | ⟨k, _, hr, ho, _⟩
    · have := v.isLt; omega
    · rcases (orReaches_iff j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
      · subst k; rw [hj] at ho; cases ho
      · rw [hj] at hof; cases hof
  have lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen OrStep w (n + j)) :
      w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
        n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧ Relation.ReflTransGen OrStep w (n + m) := by
    rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
    · exact .inl eq.symm
    · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep; exact .inr ⟨m, hm, ho, hi, hb, hz⟩
  have residualTrace {u v : Fin n} (he : s(u, v) ∈ Ustar G C) :
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
        OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
    obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
    have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
    obtain ⟨a, ha, hv⟩ := acceptedTop adj'
    obtain ⟨hl, ho, _⟩ := topData ha
    have h := (andValOperands hl ho _).mp hv
    rcases operandSupport hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
    · rcases operandSupport hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
      · have hxy : x ≠ y := (topAdj ha hx hy).ne
        apply (miss ?_).elim
        unfold starEdges
        refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
          ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩⟩
        rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
        · exact (hxy rfl).elim
        · rfl
        · exact Sym2.eq_swap
        · exact (hxy rfl).elim
      · exact ⟨a, ha, 1, j, hj, hr, hjv⟩
    · exact ⟨a, ha, 0, j, hj, hr, hjv⟩
  have lastOrOutside {j m : ℕ} (hj : j ∈ junk G C) (hm : m < C.gates.length)
      (ho : (gateAt C m).op = GateOp.or) (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
      m ∈ orN G C \ lam G C := by
    obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
    have hNotBelow : ¬ BelowF G C m := by
      intro h
      have hvm : gateVal n C m x = true := (val_or (by simp [n]) hm ho).mpr ⟨n + j, hi, hb, hjx⟩
      exact Bool.noConfusion (hx.symm.trans (h x hvm))
    apply Finset.mem_sdiff.mpr; refine ⟨?_, ?_⟩
    · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using And.intro hm (And.intro ho hNotBelow)
    · intro hl
      obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
      obtain ⟨b, be⟩ := inputsAsOpnd hm hi
      have hnonempty : (orIn n C (opnd C m b)).Nonempty := by fin_cases b; exact h0; exact h1
      rw [← be, andRawEmpty hjop] at hnonempty
      exact Finset.not_nonempty_empty hnonempty
  have hUne : (Ustar G C).Nonempty := Finset.card_pos.mp (by dsimp only [G]; omega)
  have hres : (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty := by
    obtain ⟨e, he⟩ := hUne
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨a, ha, b, j, hj, hr, _⟩ := residualTrace he
      rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨m, hl, ho, hi, hb, _⟩
      · have hz : side (n := n) C a b = ∅ := by
          change orIn n C (opnd C a b) = ∅; rw [heq]; exact andRawEmpty (junkData hj).2.1
        left; refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
        fin_cases b; exact .inl hz; exact .inr hz
      · exact .inr ⟨m, lastOrOutside hj hl ho hi hb⟩
  have hcr1 : 1 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by
    rcases hres with h | h
    · have := Finset.card_pos.mpr h; omega
    · have := Finset.card_pos.mpr h; omega
  rcases lt_or_eq_of_le hjunk with hj3 | hj2
  · dsimp only [G] at hU4 hcr1; omega
  · have hJ : (junk G C).card = 2 := hj2.symm
    by_cases h2 : 2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card
    · dsimp only [G] at hU4 h2; omega
    -- Show that (junk G C).card = 2 and ¬(2 ≤ 2 * c + r) contradicts hinc (two incomparable junk gates).
    exfalso
    have hE : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSmall : (orN G C \ lam G C).card ≤ 1 := by omega
    obtain ⟨a, b, hab, hPair⟩ : ∃ a b : ℕ, a < b ∧ junk G C = {a, b} := by
      obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hJ
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact ⟨i, j, hlt, he⟩
      · exact ⟨j, i, hlt, he.trans (Finset.pair_comm _ _)⟩
    have ha : a ∈ junk G C := by simp [hPair]
    have hb : b ∈ junk G C := by simp [hPair]
    have noLaterJunk {k : ℕ} (hk : k ∈ junk G C) (hlt : b < k) : False := by
      simp only [hPair, Finset.mem_insert, Finset.mem_singleton] at hk; omega
    have readData {j k : ℕ} (h : k ∈ readers n C j) : k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
      simpa only [readers, Finset.mem_filter, Finset.mem_range] using h
    have readLt {j k : ℕ} (h : k ∈ readers n C j) : j < k := by
      have hlt := hAO.2.1 k (readData h).1 _ (readData h).2; omega
    have junkNotBelow {j : ℕ} (hj : j ∈ junk G C) : ¬ BelowF G C j := by
      obtain ⟨_, _, x, hx, hf⟩ := junkData hj; intro h; exact Bool.false_ne_true (hf.symm.trans (h x hx))
    have emptySide {t : ℕ} (ht : t ∈ tops G C) {d : Fin 2} (h : side (n := n) C t d = ∅) :
        t ∈ centreless G C := by
      apply Finset.mem_filter.mpr; refine ⟨ht, ?_⟩; fin_cases d; exact .inl h; exact .inr h
    have classifyReader {j k : ℕ} (hd : ¬ BelowF G C j) (hz : orIn n C (n + j) = ∅)
        (hr : k ∈ readers n C j) : k ∈ junk G C ∨ k ∈ orN G C \ lam G C := by
      obtain ⟨hk, hin⟩ := readData hr
      obtain ⟨d, hd_eq⟩ := inputsAsOpnd hk hin
      have hs : side (n := n) C k d = ∅ := by change orIn n C (opnd C k d) = ∅; rwa [← hd_eq]
      rcases hAO.1 _ (gateAt_mem hk) with hand | hor
      · left
        have hnb : ¬ BelowF G C k := by
          intro hbelow
          have ht : k ∈ tops G C := by
            simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using And.intro hk (And.intro hand hbelow)
          have hcen := emptySide ht hs; rw [hE] at hcen; exact Finset.notMem_empty _ hcen
        have hw : ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
          by_contra hnone; apply hnb; intro x hx; by_contra hf
          exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hand, hk, hw⟩
      · right
        have hnb : ¬ BelowF G C k := by
          intro hbelow; apply hd; intro x hx
          exact hbelow x ((val_or (by simp [n]) hk hor).mpr ⟨_, hin, hAO.2.1 k hk _ hin, hx⟩)
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using And.intro hk (And.intro hor hnb)
        · intro hlam
          obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hlam
          have hn : (orIn n C (opnd C k d)).Nonempty := by fin_cases d; exact h0; exact h1
          rw [← hd_eq, hz] at hn; exact Finset.not_nonempty_empty hn
    -- leastRead via delDead
    let shiftW (k w : ℕ) : ℕ := if w < n + k then w else w - 1
    let unshiftW (k w : ℕ) : ℕ := if w < n + k then w else w + 1
    let unshiftG (k j : ℕ) : ℕ := if j < k then j else j + 1
    let shiftGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftW k)⟩
    let delDead (k : ℕ) : Circuit := ⟨(C.gates.eraseIdx k).map (shiftGate k), shiftW k C.output⟩
    have leastRead {j : ℕ} (hj : j < C.gates.length) (hd : ¬ BelowF G C j) : (readers n C j).Nonempty := by
      have hout : C.output ≠ n + j := by
        intro heq; apply hd; intro x hx
        have h : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hleast.2.1 x
        rw [heq] at h; exact h.symm.trans hx
      by_contra hnone
      have hno : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs := fun k hk hmem =>
        hnone ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hmem⟩⟩
      have hdl : (delDead j).gates.length = C.gates.length - 1 := by
        simp [delDead, List.length_eraseIdx_of_lt hj]
      have delDead_gateAt (k : ℕ) (hk : k < (delDead j).gates.length) :
          gateAt (delDead j) k = shiftGate j (gateAt C (unshiftG j k)) := by
        have hk_lt : k < C.gates.length - 1 := by rw [← hdl]; exact hk
        have hk_e : k < (C.gates.eraseIdx j).length := by rw [List.length_eraseIdx_of_lt hj]; exact hk_lt
        rw [gateAt_eq hk]; simp only [delDead, List.getElem_map, unshiftG]
        split_ifs with hjk
        · rw [List.getElem_eraseIdx_of_lt hk_e hjk, gateAt_eq (C' := C) (j := k) (by omega)]
        · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq (C' := C) (j := k + 1) (by omega)]
      have hRB' : ReadsBack n (delDead j) := by
        intro k hk w' hw'
        rw [delDead_gateAt k hk] at hw'; simp only [shiftGate, List.mem_map] at hw'
        obtain ⟨w, hw, rfl⟩ := hw'
        have hk_len : k < C.gates.length - 1 := by rw [← hdl]; exact hk
        have hk0_lt : unshiftG j k < C.gates.length := by unfold unshiftG; split_ifs <;> omega
        have hw_lt : w < n + unshiftG j k := hAO.2.1 (unshiftG j k) hk0_lt w hw
        have hw_ne : w ≠ n + j := fun heq => hno (unshiftG j k) hk0_lt (heq ▸ hw)
        dsimp only [shiftW]; dsimp only [unshiftG] at hw_lt; split_ifs at hw_lt ⊢ <;> omega
      have hAO' : IsAO2 n (delDead j) := by
        have mapped : ∀ g ∈ (delDead j).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
          intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
          have hm := List.mem_of_mem_eraseIdx hg'
          exact ⟨hAO.1 g' hm, by simp [shiftGate, hAO.2.2 g' hm]⟩
        exact ⟨fun g hg => (mapped g hg).1, hRB', fun g hg => (mapped g hg).2⟩
      have heval : ∀ (x : List Bool) (hx : x.length = n) (w : ℕ),
          val (delDead j) x w = val C x (unshiftW j w) := by
        intro x hx w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          by_cases hw_oob : n + (delDead j).gates.length ≤ w
          · have huw : n + C.gates.length ≤ unshiftW j w := by dsimp only [unshiftW]; split_ifs <;> omega
            rw [val_ge hx hw_oob, val_ge hx huw]
          · push Not at hw_oob
            by_cases hwn : w < n
            · have huw : unshiftW j w = w := by dsimp only [unshiftW]; split_ifs <;> omega
              rw [huw, val_input hx hwn, val_input hx hwn]
            · set k := w - n with hk_def
              have hw_eq : w = n + k := by omega
              have hk_lt : k < (delDead j).gates.length := by omega
              have hk0_lt : unshiftG j k < C.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
              have huw : unshiftW j (n + k) = n + unshiftG j k := by dsimp only [unshiftW, unshiftG]; split_ifs <;> omega
              rw [hw_eq, huw, val_gate hx hk_lt, val_gate hx hk0_lt, delDead_gateAt k hk_lt]
              simp only [shiftGate, List.map_map]; congr 1; apply List.map_congr_left
              intro u hu
              have hu_lt : shiftW j u < n + k := by
                apply hRB' k hk_lt; rw [delDead_gateAt k hk_lt]; simp only [shiftGate, List.mem_map]; exact ⟨u, hu, rfl⟩
              have hu_ne : u ≠ n + j := fun heq => hno (unshiftG j k) hk0_lt (heq ▸ hu)
              have hu0_lt : u < n + unshiftG j k := hAO.2.1 (unshiftG j k) hk0_lt u hu
              have hush : unshiftW j (shiftW j u) = u := by dsimp only [unshiftW, shiftW]; split_ifs <;> omega
              simp only [Function.comp_apply, ite_eq_left hu_lt, ite_eq_left hu0_lt]
              rw [ih (shiftW j u) (by omega), hush]
      have hfun : circuitFun 11 (delDead j) = graphFun G ∅ := by
        funext x; rw [← hleast.2.1]
        have h1 := heval (List.ofFn x) (by simp [n]) (delDead j).output
        have hush : unshiftW j (shiftW j C.output) = C.output := by dsimp only [unshiftW, shiftW]; split_ifs <;> omega
        simpa [circuitFun, Circuit.eval, val, delDead, hush] using h1
      have hle := hleast.2.2 (delDead j) hAO' hfun
      have hsize : (delDead j).size + 1 = C.size := by
        unfold Circuit.size at hj ⊢; simp [delDead, List.length_eraseIdx_of_lt hj]; omega
      omega
    obtain ⟨m, hbm⟩ := leastRead (junkData hb).1 (junkNotBelow hb)
    have hbmLt := readLt hbm
    have hm := (classifyReader (junkNotBelow hb) (andRawEmpty (junkData hb).2.1) hbm).resolve_left
      (fun hk => noLaterJunk hk hbmLt)
    have mUnique {k : ℕ} (hk : k ∈ orN G C \ lam G C) : k = m :=
      Finset.card_le_one.mp hSmall k hk m hm
    have twoInputs {m0 p q : ℕ} (hm0 : m0 < C.gates.length) (hpq : p ≠ q)
        (hp : p ∈ (gateAt C m0).inputs) (hq : q ∈ (gateAt C m0).inputs)
        {w : ℕ} (hw : w ∈ (gateAt C m0).inputs) : w = p ∨ w = q := by
      obtain ⟨r, s, hrs⟩ := binaryInputs hm0
      simp only [hrs, List.mem_cons, List.not_mem_nil, or_false] at hp hq hw; omega
    have orEmpty {m0 : ℕ} (h : ∀ w ∈ (gateAt C m0).inputs, orIn n C w = ∅) :
        orIn n C (n + m0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro u hu
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w, hw, tail⟩
      · have := u.isLt; omega
      · obtain ⟨k, _, he, _, hi, _⟩ := hw
        have e : k = m0 := Nat.add_left_cancel he.symm
        subst e
        have hu' := reach_mem_orIn u tail; rw [h w hi] at hu'; exact Finset.notMem_empty _ hu'
    have noAM (ham : m ∈ readers n C a) : False := by
      have hmData : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
        simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using (Finset.mem_sdiff.mp hm).1
      have hmEmpty : orIn n C (n + m) = ∅ := by
        apply orEmpty; intro w hw
        rcases twoInputs hmData.1 (show n + a ≠ n + b by omega)
            (readData ham).2 (readData hbm).2 hw with rfl | rfl
        · exact andRawEmpty (junkData ha).2.1
        · exact andRawEmpty (junkData hb).2.1
      obtain ⟨k, hmk⟩ := leastRead hmData.1 hmData.2.2
      have hmkLt := readLt hmk
      rcases classifyReader hmData.2.2 hmEmpty hmk with hk | hk
      · exact noLaterJunk hk (hbmLt.trans hmkLt)
      · have := mUnique hk; omega
    have aRead {k : ℕ} (hk : k ∈ readers n C a) : k = b := by
      rcases classifyReader (junkNotBelow ha) (andRawEmpty (junkData ha).2.1) hk with hj | hj
      · have hlt := readLt hk
        simp only [hPair, Finset.mem_insert, Finset.mem_singleton] at hj; omega
      · exact (noAM (mUnique hj ▸ hk)).elim
    obtain ⟨k, hak⟩ := leastRead (junkData ha).1 (junkNotBelow ha)
    have habRead : b ∈ readers n C a := aRead hak ▸ hak
    have habCone : InCone n C a b := (inCone_iff a b).mpr
      ⟨(readData habRead).1, a, hab, (readData habRead).2, Or.inl rfl⟩
    obtain ⟨x7, x8, hx7, hx8, hne, h78, h87⟩ := hinc
    rw [hPair] at hx7 hx8
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx7 hx8
    rcases hx7 with rfl | rfl <;> rcases hx8 with rfl | rfl
    · exact hne rfl
    · exact h78 habCone
    · exact h87 habCone
    · exact hne rfl
