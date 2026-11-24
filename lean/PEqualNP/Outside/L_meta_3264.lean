import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_3264

/-- One more gate on a wire list. -/
def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wireStep x := rfl

theorem wireStep_length (w : List Bool) (g : Gate) : (wireStep w g).length = w.length + 1 := by
  simp [wireStep]

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq_foldl]
  induction C.gates generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, wireStep_length, List.length_cons]; omega

/-- The wires of a circuit with one more gate. -/
theorem wires_snoc (gs : List Gate) (o : ℕ) (g : Gate) (x : List Bool) :
    ({ gates := gs ++ [g], output := o } : Circuit).wires x =
      (({ gates := gs, output := o } : Circuit).wires x ++
        [g.op.eval (g.inputs.map fun i => (({ gates := gs, output := o } : Circuit).wires x).getD i false)]) := by
  simp [Circuit.wires, List.foldl_append]

/-- An input wire keeps its value through the gates. -/
theorem foldl_getD_prefix (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    (gs.foldl wireStep x).getD k false = x.getD k false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wireStep x g) (by rw [wireStep_length]; omega)]
    exact List.getD_append _ _ _ _ hk

theorem ofFn_getD {n : ℕ} (w : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn w).getD i false = w ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

theorem wires_input (C : Circuit) {n : ℕ} (w : Fin n → Bool) (i : ℕ) (h : i < n) :
    (C.wires (List.ofFn w)).getD i false = w ⟨i, h⟩ := by
  rw [wires_eq_foldl, foldl_getD_prefix _ _ i (by simp [h])]
  exact ofFn_getD w i h

/-- A wire past the end of the list reads `false`. -/
theorem wires_getD_ge (C : Circuit) (x : List Bool) (i : ℕ) (h : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  rw [List.getD_eq_default _ _ (by rw [wires_length]; exact h)]

/-- Where a wire of the old circuit lives in the new one: a point wire stays put; a line wire, or a gate wire, moves up. -/
def lift (h x1 : ℕ) (i : ℕ) : ℕ := if i < x1 then i else h + i

/-- The same gate, reading the moved wires. -/
def liftGate (h x1 : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (lift h x1)⟩

theorem lift_big (h x1 m : ℕ) (hx1 : x1 ≤ h) (k : ℕ) (hk : h + m ≤ k) : h + h + m ≤ lift h x1 k := by
  unfold lift
  split
  · omega
  · omega

theorem lift_eq (h x1 m : ℕ) (hx1 : x1 ≤ h) (i : ℕ) (hi : h + m ≤ i) : lift h x1 i = h + i := by
  unfold lift
  split
  · omega
  · rfl

theorem lift_lt (h x1 m : ℕ) (hx1 : x1 ≤ h) (k : ℕ) (hk : k < h + m) : lift h x1 k < h + h + m := by
  unfold lift
  split
  · omega
  · omega

theorem lift_foldl (h x1 m : ℕ) (hx1 : x1 ≤ h) (gs : List Gate) (x y : List Bool)
    (hx : x.length = h + m) (hy : y.length = h + h + m)
    (hxy : ∀ i, i < h + m → x.getD i false = y.getD (lift h x1 i) false) (k : ℕ) :
    ((gs.map (liftGate h x1)).foldl wireStep y).getD (lift h x1 k) false =
      (gs.foldl wireStep x).getD k false := by
  induction gs generalizing x y m with
  | nil =>
    by_cases hk : k < h + m
    · rw [List.map_nil, List.foldl_nil, List.foldl_nil]; exact (hxy k hk).symm
    · rw [List.map_nil, List.foldl_nil, List.foldl_nil,
        List.getD_eq_default y false (hy.trans_le (lift_big h x1 m hx1 k (by omega))),
        List.getD_eq_default x false (by rw [hx]; omega)]
  | cons g gs ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hv : g.op.eval (g.inputs.map fun i => x.getD i false) =
        g.op.eval ((g.inputs.map (lift h x1)).map fun i => y.getD i false) := by
      refine congrArg (GateOp.eval g.op) ?_
      simp only [List.map_map, Function.comp_def]
      refine List.map_congr_left (fun i _ => ?_)
      by_cases hi : i < h + m
      · exact hxy i hi
      · rw [List.getD_eq_default x false (by rw [hx]; omega),
          List.getD_eq_default y false (hy.trans_le (lift_big h x1 m hx1 i (by omega)))]
    refine ih (m + 1) _ _ (by rw [wireStep_length, hx]; omega) (by rw [wireStep_length, hy]; omega) ?_
    intro i hi
    by_cases hi' : i < h + m
    · have hx' : i < x.length := by rw [hx]; exact hi'
      have hy' : lift h x1 i < y.length := by
        rw [hy]
        exact lift_lt h x1 m hx1 i hi'
      rw [wireStep, wireStep, List.getD_append _ _ _ _ hx', List.getD_append _ _ _ _ hy']
      exact hxy i hi'
    · have him : i = h + m := by omega
      subst i
      rw [wireStep, wireStep]
      have e0 : h + (h + m) - (h + h + m) = 0 := by omega
      rw [List.getD_append_right _ _ _ _ hx.le, lift_eq h x1 m hx1 (h + m) (Nat.le_refl _),
        List.getD_append_right _ _ _ _ (by rw [hy]; omega), hx, hy, Nat.sub_self, e0,
        List.getD_cons_zero, List.getD_cons_zero]
      simp only [liftGate]
      exact hv

/-- The lifted circuit computes, on the new inputs, what the old one computes on the old ones. -/
theorem lift_eval (h x1 : ℕ) (hx1 : x1 ≤ h) (C : Circuit) (x y : List Bool)
    (hx : x.length = h) (hy : y.length = h + h)
    (hxy : ∀ i, i < h → x.getD i false = y.getD (lift h x1 i) false) :
    ({ gates := C.gates.map (liftGate h x1), output := lift h x1 C.output } : Circuit).eval y =
      C.eval x := by
    unfold Circuit.eval
    rw [wires_eq_foldl, wires_eq_foldl]
    exact lift_foldl h x1 0 hx1 C.gates x y (by omega) (by omega) hxy C.output

theorem lift_gateAt (h x1 : ℕ) (C : Circuit) (j : ℕ) :
    gateAt { gates := C.gates.map (liftGate h x1), output := lift h x1 C.output } j =
      liftGate h x1 (gateAt C j) := by
  show (C.gates.map (liftGate h x1)).getD j (liftGate h x1 ⟨GateOp.or, []⟩) =
    liftGate h x1 (C.gates.getD j ⟨GateOp.or, []⟩)
  exact List.getD_map _ _ _

theorem lift_IsAO2 (h x1 : ℕ) (hx1 : x1 ≤ h) (C : Circuit) (hC : IsAO2 h C) :
    IsAO2 (h + h) { gates := C.gates.map (liftGate h x1), output := lift h x1 C.output } := by
  obtain ⟨h1, h2, h3⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact h1 g' hg'
  · intro j hj i hi
    rw [lift_gateAt] at hi
    have hj' : j < C.gates.length := by simpa using hj
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    have hlt := h2 j hj' i' hi'
    unfold lift
    split
    · omega
    · omega
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa only [liftGate, List.length_map] using h3 g' hg'

/-- One more pair or-ed into the output of `C`. -/
def extend (h : ℕ) (C : Circuit) (p : Fin h × Fin h) : Circuit :=
  { gates := C.gates ++ [⟨GateOp.and, [p.1.val, h + p.2.val]⟩,
      ⟨GateOp.or, [C.output, h + h + C.size]⟩],
    output := h + h + C.size + 1 }

theorem extend_eval (h : ℕ) (C : Circuit) (p : Fin h × Fin h) (w : Fin (h + h) → Bool)
    (ho : C.output < h + h + C.size) :
    (extend h C p).eval (List.ofFn w) =
      (C.eval (List.ofFn w) || (w (Fin.castAdd h p.1) && w (Fin.natAdd h p.2))) := by
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  have hw' : ∀ o : ℕ, ({ gates := C.gates, output := o } : Circuit).wires (List.ofFn w) =
      C.wires (List.ofFn w) := fun _ => rfl
  have hlen : (C.wires (List.ofFn w)).length = h + h + C.size := by
    rw [wires_length, List.length_ofFn]; rfl
  unfold extend Circuit.eval
  rw [show C.gates ++ [⟨GateOp.and, [p.1.val, h + p.2.val]⟩, ⟨GateOp.or, [C.output, h + h + C.size]⟩] =
      (C.gates ++ [⟨GateOp.and, [p.1.val, h + p.2.val]⟩]) ++ [⟨GateOp.or, [C.output, h + h + C.size]⟩] from by
    simp]
  rw [wires_snoc, wires_snoc, hw']
  simp only
  set A := GateOp.and.eval (List.map (fun i => (C.wires (List.ofFn w)).getD i false) [p.1.val, h + p.2.val]) with hA
  set B := GateOp.or.eval
      (List.map (fun i => (C.wires (List.ofFn w) ++ [A]).getD i false) [C.output, h + h + C.size]) with hB
  have hlenA : (C.wires (List.ofFn w) ++ [A]).length = h + h + C.size + 1 := by
    rw [List.length_append, hlen]; simp
  rw [List.getD_append_right (C.wires (List.ofFn w) ++ [A]) [B] false (h + h + C.size + 1) hlenA.le,
    hlenA, Nat.sub_self, List.getD_cons_zero]
  simp only [hB, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
  rw [List.getD_append (C.wires (List.ofFn w)) [A] false C.output (by rw [hlen]; omega)]
  rw [List.getD_append_right (C.wires (List.ofFn w)) [A] false (h + h + C.size) hlen.le, hlen,
    Nat.sub_self, List.getD_cons_zero]
  simp only [Bool.or_false, hA, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true]
  rw [wires_input C w p.1.val (by omega), wires_input C w (h + p.2.val) (by omega)]
  rfl

theorem extend_circuitFun (h : ℕ) (C : Circuit) (p : Fin h × Fin h) (w : Fin (h + h) → Bool)
    (ho : C.output < h + h + C.size) :
    circuitFun (h + h) (extend h C p) w =
      (circuitFun (h + h) C w || (w (Fin.castAdd h p.1) && w (Fin.natAdd h p.2))) := by
  unfold circuitFun
  exact extend_eval h C p w ho

theorem extend_IsAO2 (h : ℕ) (C : Circuit) (p : Fin h × Fin h) (hC : IsAO2 (h + h) C)
    (ho : C.output < h + h + C.size) : IsAO2 (h + h) (extend h C p) := by
  obtain ⟨h1, h2, h3⟩ := hC
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  have hsz : C.size = C.gates.length := rfl
  rw [hsz] at ho
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [extend] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h1 g hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact Or.inl rfl
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact Or.inr rfl
        · exact absurd hg List.not_mem_nil
  · intro j hj i hi
    simp only [extend, List.length_append, List.length_cons, List.length_nil] at hj
    simp only [gateAt, extend] at hi
    rcases Nat.lt_or_ge j C.gates.length with hj' | hj'
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact lt_of_lt_of_le (h2 j hj' i hi) (by omega)
    · rcases Nat.eq_or_lt_of_le hj' with hj1 | hj2
      · subst j
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero] at hi
        rcases List.mem_cons.mp hi with rfl | hi
        · omega
        · rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · exact absurd hi List.not_mem_nil
      · have hj3 : j = C.gates.length + 1 := by omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, List.getD_cons_succ,
          List.getD_cons_zero] at hi
        rcases List.mem_cons.mp hi with rfl | hi
        · omega
        · rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · exact absurd hi List.not_mem_nil
  · intro g hg
    simp only [extend] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h3 g hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · simp
      · rcases List.mem_cons.mp hg with rfl | hg
        · simp
        · exact absurd hg List.not_mem_nil

/-- The old inputs read off the new ones: a point of the left copy, or a line of the right copy. -/
def oldInput (x1 x2 : ℕ) (w : Fin (x1 + x2 + (x1 + x2)) → Bool) (i : Fin (x1 + x2)) : Bool :=
  if i.val < x1 then w (Fin.castAdd (x1 + x2) i) else w (Fin.natAdd (x1 + x2) i)

theorem lift_ge (h x1 : ℕ) (i : ℕ) (hi : x1 ≤ i) : lift h x1 i = h + i := by
  unfold lift
  split
  · omega
  · rfl

theorem lift_lt' (x1 x2 : ℕ) (i : Fin (x1 + x2)) : lift (x1 + x2) x1 i.val < x1 + x2 + (x1 + x2) := by
  unfold lift
  split
  · omega
  · omega

theorem oldInput_eq (x1 x2 : ℕ) (w : Fin (x1 + x2 + (x1 + x2)) → Bool) (i : Fin (x1 + x2)) :
    oldInput x1 x2 w i = w ⟨lift (x1 + x2) x1 i.val, lift_lt' x1 x2 i⟩ := by
  unfold oldInput
  split
  · next hlt =>
    exact congrArg w (Fin.ext (by unfold lift; simp [hlt]))
  · next hlt =>
    exact congrArg w
      (Fin.ext (by simp only [Fin.val_natAdd, lift_ge (x1 + x2) x1 i.val (by omega)]))

theorem oldInput_point (x1 x2 : ℕ) (w : Fin (x1 + x2 + (x1 + x2)) → Bool) (u : Fin x1) :
    oldInput x1 x2 w (Fin.castAdd x2 u) = w (Fin.castAdd (x1 + x2) (Fin.castAdd x2 u)) := by
  simp [oldInput, Fin.val_castAdd, u.isLt]

theorem oldInput_line (x1 x2 : ℕ) (w : Fin (x1 + x2 + (x1 + x2)) → Bool) (v : Fin x2) :
    oldInput x1 x2 w (Fin.natAdd x1 v) = w (Fin.natAdd (x1 + x2) (Fin.natAdd x1 v)) := by
  simp [oldInput, Fin.val_natAdd]

/-- The old inputs with exactly one edge on. -/
def witInput (x1 x2 : ℕ) (u : Fin x1) (v : Fin x2) : Fin (x1 + x2) → Bool :=
  fun i => decide (i = Fin.castAdd x2 u ∨ i = Fin.natAdd x1 v)

theorem witInput_point (x1 x2 : ℕ) (u : Fin x1) (v : Fin x2) :
    witInput x1 x2 u v (Fin.castAdd x2 u) = true := by
  simp [witInput]

theorem witInput_line (x1 x2 : ℕ) (u : Fin x1) (v : Fin x2) :
    witInput x1 x2 u v (Fin.natAdd x1 v) = true := by
  simp [witInput]

/-- Two conditions on the inputs, decided together. -/
theorem decide_and_bool {n : ℕ} (w : Fin n → Bool) (x y : Fin n) :
    decide (w x = true ∧ w y = true) = (w x && w y) := by
  cases w x <;> cases w y <;> simp

theorem main_aux (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (hne : x3.Nonempty) (x4 : Circuit)
    (hAO : IsAO2 (x1 + x2) x4)
    (hfun : ∀ x7 : Fin (x1 + x2) → Bool, circuitFun (x1 + x2) x4 x7 =
      decide (∃ u : Fin x1, ∃ v : Fin x2, (u, v) ∈ x3 ∧ x7 (Fin.castAdd x2 u) = true ∧
        x7 (Fin.natAdd x1 v) = true))
    (S : Finset (Fin (x1 + x2) × Fin (x1 + x2))) :
    ∃ x11 : Circuit, IsAO2 (x1 + x2 + (x1 + x2)) x11 ∧ x11.size ≤ x4.size + 2 * S.card ∧
      ∀ x12 : Fin (x1 + x2 + (x1 + x2)) → Bool, circuitFun (x1 + x2 + (x1 + x2)) x11 x12 =
        decide (∃ x13 x14 : Fin (x1 + x2), (x13, x14) ∈
          Finset.image (fun q : Fin x1 × Fin x2 => (Fin.castAdd x2 q.1, Fin.natAdd x1 q.2)) x3 ∪ S ∧
          x12 (Fin.castAdd (x1 + x2) x13) = true ∧ x12 (Fin.natAdd (x1 + x2) x14) = true) := by
  have hx1 : x1 ≤ x1 + x2 := Nat.le_add_right x1 x2
  obtain ⟨e, he⟩ := hne
  have hout : x4.output < x1 + x2 + x4.gates.length := by
    by_contra hc
    have h1 : circuitFun (x1 + x2) x4 (witInput x1 x2 e.1 e.2) = false := by
      unfold circuitFun Circuit.eval
      refine wires_getD_ge _ _ _ ?_
      simp only [List.length_ofFn]
      omega
    have h2 : circuitFun (x1 + x2) x4 (witInput x1 x2 e.1 e.2) = true := by
      rw [hfun (witInput x1 x2 e.1 e.2)]
      exact decide_eq_true_iff.mpr
        ⟨e.1, e.2, he, witInput_point x1 x2 e.1 e.2, witInput_line x1 x2 e.1 e.2⟩
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hbase : ∀ w : Fin (x1 + x2 + (x1 + x2)) → Bool,
      circuitFun (x1 + x2 + (x1 + x2))
        { gates := x4.gates.map (liftGate (x1 + x2) x1), output := lift (x1 + x2) x1 x4.output } w =
      circuitFun (x1 + x2) x4 (oldInput x1 x2 w) := by
    intro w
    unfold circuitFun
    refine lift_eval (x1 + x2) x1 hx1 x4 (List.ofFn (oldInput x1 x2 w)) (List.ofFn w) (by simp) (by simp) ?_
    intro i hi
    rw [ofFn_getD, ofFn_getD]
    exact oldInput_eq x1 x2 w ⟨i, hi⟩
  obtain ⟨C, hCAO, hCout, hCsize, hCfun⟩ :
      (∃ C : Circuit, IsAO2 (x1 + x2 + (x1 + x2)) C ∧ C.output < x1 + x2 + (x1 + x2) + C.size ∧
        C.size ≤ x4.size + 2 * S.card ∧
        ∀ x12 : Fin (x1 + x2 + (x1 + x2)) → Bool, circuitFun (x1 + x2 + (x1 + x2)) C x12 =
          decide (∃ x13 x14 : Fin (x1 + x2), (x13, x14) ∈
            Finset.image (fun q : Fin x1 × Fin x2 => (Fin.castAdd x2 q.1, Fin.natAdd x1 q.2)) x3 ∪ S ∧
            x12 (Fin.castAdd (x1 + x2) x13) = true ∧ x12 (Fin.natAdd (x1 + x2) x14) = true)) := by
    refine Finset.induction_on S ?_ ?_
    · refine ⟨{ gates := x4.gates.map (liftGate (x1 + x2) x1), output := lift (x1 + x2) x1 x4.output },
        lift_IsAO2 _ _ hx1 x4 hAO, ?_, ?_, ?_⟩
      · simp only [Circuit.size, List.length_map]
        unfold lift
        split
        · omega
        · omega
      · simp [Circuit.size]
      · intro w
        rw [hbase w, hfun (oldInput x1 x2 w)]
        refine decide_eq_decide.mpr ⟨?_, ?_⟩
        · rintro ⟨u, v, huv, hw1, hw2⟩
          rw [oldInput_point] at hw1
          rw [oldInput_line] at hw2
          exact ⟨Fin.castAdd x2 u, Fin.natAdd x1 v,
            Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨(u, v), huv, rfl⟩)), hw1, hw2⟩
        · rintro ⟨a, b, hab, hw1, hw2⟩
          rw [Finset.union_empty] at hab
          obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp hab
          simp only [Prod.mk.injEq] at hq'
          obtain ⟨rfl, rfl⟩ := hq'
          exact ⟨q.1, q.2, hq, by rw [oldInput_point]; exact hw1, by rw [oldInput_line]; exact hw2⟩
    · intro q s hq ih
      obtain ⟨C, hCAO, hCout, hCsize, hCfun⟩ := ih
      have hs : C.size = C.gates.length := rfl
      rw [hs] at hCout hCsize
      have hs4 : x4.size = x4.gates.length := rfl
      rw [hs4] at hCsize
      refine ⟨extend (x1 + x2) C q, extend_IsAO2 _ _ _ hCAO hCout, ?_, ?_, ?_⟩
      · simp only [extend, Circuit.size, List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [extend, Circuit.size, List.length_append, List.length_cons, List.length_nil]
        rw [Finset.card_insert_of_notMem hq]; omega
      · intro w
        rw [extend_circuitFun (x1 + x2) C q w hCout, hCfun w]
        rw [← decide_and_bool w (Fin.castAdd (x1 + x2) q.1) (Fin.natAdd (x1 + x2) q.2),
          ← Bool.decide_or]
        refine decide_eq_decide.mpr ⟨?_, ?_⟩
        · rintro (⟨a, b, hab, hw1, hw2⟩ | ⟨hw1, hw2⟩)
          · rcases Finset.mem_union.mp hab with h1 | h2
            · exact ⟨a, b, Finset.mem_union.mpr (Or.inl h1), hw1, hw2⟩
            · exact ⟨a, b, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem h2)), hw1, hw2⟩
          · exact ⟨q.1, q.2, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self q s)), hw1, hw2⟩
        · rintro ⟨a, b, hab, hw1, hw2⟩
          rcases Finset.mem_union.mp hab with h1 | h2
          · exact Or.inl ⟨a, b, Finset.mem_union.mpr (Or.inl h1), hw1, hw2⟩
          · rcases Finset.mem_insert.mp h2 with h3 | h3
            · exact Or.inr ⟨by rw [← h3]; exact hw1, by rw [← h3]; exact hw2⟩
            · exact Or.inl ⟨a, b, Finset.mem_union.mpr (Or.inr h3), hw1, hw2⟩
  exact ⟨C, hCAO, hCsize, hCfun⟩

end PEqualNP.Outside.L_meta_3264

theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro x1 x2 x3 x4 hne hAO hfun h img S
  exact PEqualNP.Outside.L_meta_3264.main_aux x1 x2 x3 hne x4 hAO hfun S
