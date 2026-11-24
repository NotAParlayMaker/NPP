import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4680

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

private def dualOp : GateOp → GateOp
  | GateOp.and => GateOp.or
  | GateOp.or => GateOp.and
  | op => op

private def dualWire (bound i : ℕ) : ℕ :=
  if i < bound then i + 1 else 0

private def dualGate (bound : ℕ) (g : Gate) : Gate :=
  ⟨dualOp g.op, g.inputs.map (dualWire bound)⟩

private def dualGatesAux : ℕ → List Gate → List Gate
  | _, [] => []
  | bound, g :: gs => dualGate bound g :: dualGatesAux (bound + 1) gs

private lemma dualGatesAux_length (b : ℕ) (gs : List Gate) :
    (dualGatesAux b gs).length = gs.length := by
  induction gs generalizing b with
  | nil => rfl
  | cons g gs ih => simp [dualGatesAux, ih]

private lemma dualGatesAux_mono (b : ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ dualGatesAux b gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing b with
  | nil => intro g hg; simp [dualGatesAux] at hg
  | cons g gs ih =>
    intro g' hg'
    simp only [dualGatesAux, List.mem_cons] at hg'
    rcases hg' with rfl | hrest
    · rcases hm g (List.mem_cons_self ..) with ⟨hop, hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      refine ⟨?_, by simpa [dualGate] using hlen⟩
      rcases hop with h1 | h2
      · exact Or.inr (by simp [dualGate, dualOp, h1])
      · exact Or.inl (by simp [dualGate, dualOp, h2])
    · exact ih (b + 1) (fun x hx => hm x (List.mem_cons_of_mem g hx)) g' hrest

private lemma dualGatesAux_getElem_op (b : ℕ) (gs : List Gate) :
    ∀ (j : ℕ) (hj : j < gs.length),
      ((dualGatesAux b gs)[j]'(by rw [dualGatesAux_length]; exact hj)).op = dualOp (gs[j]'hj).op := by
  induction gs generalizing b with
  | nil => intro j hj; simp at hj
  | cons g gs ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j => exact ih (b + 1) j (by simpa using hj)

private lemma getD_dualWire (w : List Bool) (i : ℕ) :
    (true :: w.map (!·)).getD (dualWire w.length i) false = !(w.getD i false) := by
  unfold dualWire
  by_cases h : i < w.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
    cases hw : w[i]? with
    | none =>
      have := List.getElem?_eq_none_iff.mp hw
      omega
    | some b => rfl
  · rw [if_neg h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero]
    rw [List.getElem?_eq_none (by omega)]
    rfl

private lemma any_not_eq_not_all (l : List Bool) :
    (l.map (!·)).any id = !(l.all id) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [ih]

private lemma all_not_eq_not_any (l : List Bool) :
    (l.map (!·)).all id = !(l.any id) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [ih]

private lemma eval_dualOp {op : GateOp}
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (l : List Bool) :
    (dualOp op).eval (l.map (!·)) = !(op.eval l) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · exact any_not_eq_not_all l
  · exact all_not_eq_not_any l

private lemma foldl_dual (gs : List Gate) :
    ∀ (w : List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
      (dualGatesAux w.length gs).foldl step (true :: w.map (!·)) =
        true :: (gs.foldl step w).map (!·) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hm
    have hg := hm g (List.mem_cons_self ..)
    have hmap :
        ((dualGate w.length g).inputs.map fun j => (true :: w.map (!·)).getD j false) =
        (g.inputs.map fun i => w.getD i false).map (!·) := by
      simp only [dualGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact getD_dualWire w i
    have hstep :
        step (true :: w.map (!·)) (dualGate w.length g) =
        true :: (step w g).map (!·) := by
      simp only [step, hmap, List.map_append, List.map_cons, List.map_nil, List.cons_append]
      rw [show (dualGate w.length g).op = dualOp g.op from rfl, eval_dualOp hg]
    have hlen : (step w g).length = w.length + 1 := by
      simp [step]
    simp only [dualGatesAux, List.foldl_cons, hstep, ← hlen]
    exact ih (step w g) (fun x hx => hm x (List.mem_cons_of_mem g hx))

private lemma dual_circuit_main (x1 : Circuit) (hm : Monotone2 x1) :
    ∃ x3 : Circuit,
      Monotone2 x3 ∧
      Nat.card { x4 : Fin x3.gates.length // (x3.gates.get x4).op = GateOp.and } ≤
        {x4 : Fin x1.gates.length | (x1.gates.get x4).op = GateOp.or}.ncard ∧
      ∀ x4 : Fin 26 → Bool,
        circuitFun 27 x3 (fun x5 : Fin (26 + 1) => Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5) =
          !circuitFun 26 x1 x4 := by
  let x3 : Circuit := ⟨dualGatesAux 26 x1.gates, dualWire (26 + x1.gates.length) x1.output⟩
  have hlen : x3.gates.length = x1.gates.length := dualGatesAux_length 26 x1.gates
  refine ⟨x3, dualGatesAux_mono 26 x1.gates hm, ?_, ?_⟩
  · have hiff : ∀ j : Fin x3.gates.length,
        (x3.gates.get j).op = GateOp.and ↔ (x1.gates.get (j.cast hlen)).op = GateOp.or := by
      intro j
      have hop := dualGatesAux_getElem_op 26 x1.gates j.val (by omega)
      have hget3 : (x3.gates.get j).op = dualOp (x1.gates.get (j.cast hlen)).op := hop
      rw [hget3]
      have hm1 := (hm (x1.gates.get (j.cast hlen)) (List.get_mem _ _)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm1
      rcases hm1 with h1 | h2
      · rw [h1]; simp [dualOp]
      · rw [h2]; simp [dualOp]
    let e : { j : Fin x3.gates.length // (x3.gates.get j).op = GateOp.and } ≃
        { j : Fin x1.gates.length | (x1.gates.get j).op = GateOp.or } :=
      { toFun := fun ⟨j, hj⟩ => ⟨j.cast hlen, (hiff j).mp hj⟩
        invFun := fun ⟨j, hj⟩ => ⟨j.cast hlen.symm, (hiff (j.cast hlen.symm)).mpr (by simpa using hj)⟩
        left_inv := fun ⟨j, _⟩ => by ext; rfl
        right_inv := fun ⟨j, _⟩ => by ext; rfl }
    rw [Nat.card_congr e, Nat.card_coe_set_eq]
  · intro x4
    have hin :
        List.ofFn (fun x5 : Fin (26 + 1) => Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5) =
        true :: (List.ofFn x4).map (!·) := by
      rw [List.ofFn_succ]
      simp
    have hwlen : (List.ofFn x4).length = 26 := List.length_ofFn
    have hwires : x3.wires (true :: (List.ofFn x4).map (!·)) =
        true :: (x1.wires (List.ofFn x4)).map (!·) := by
      have hfd := foldl_dual x1.gates (List.ofFn x4) (fun g hg => (hm g hg).1)
      rw [hwlen] at hfd
      exact hfd
    have hfull_len : (x1.wires (List.ofFn x4)).length = 26 + x1.gates.length := by
      change (x1.gates.foldl step (List.ofFn x4)).length = 26 + x1.gates.length
      rw [foldl_length, List.length_ofFn]
    change (x3.wires (List.ofFn (fun x5 : Fin (26 + 1) => Fin.cases true (fun x6 : Fin 26 => !x4 x6) x5))).getD
        (dualWire (26 + x1.gates.length) x1.output) false =
      !((x1.wires (List.ofFn x4)).getD x1.output false)
    rw [hin, hwires, ← hfull_len]
    exact getD_dualWire (x1.wires (List.ofFn x4)) x1.output

end PEqualNP.Outside.L_meta_4680

theorem PEqualNP.Outside.L_meta_4680 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ Nat.card { x4 : Fin x3.gates.length // (x3.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and } ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x3 fun (x5 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.cases Bool.true (fun (x6 : Fin (26 : ℕ)) => !x4 x6) x5) = !PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 :=
  PEqualNP.Outside.L_meta_4680.dual_circuit_main
