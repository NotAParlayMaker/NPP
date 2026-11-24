import PEqualNP.Defs
import Mathlib.Data.Fintype.Powerset

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 3000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2193_421
    (low : ∀ (C : Circuit), FanInTwo C → C.size ≤ 14 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (residual : ∀ (C : Circuit) (j : Fin 13), C.size = 13 → FanInTwo C →
      (∀ k : Fin C.gates.length, ∀ i ∈ (C.gates.get k).inputs, i < 10 + k.val) →
      (∀ i : Fin 9, ∃ g ∈ C.gates, i.val ∈ g.inputs) →
      2 ≤ j.val → j.val < 12 →
      let W := fun (x : Fin 9 → Bool) => C.wires (List.ofFn x ++ [x 0 || x 1])
      (∃ x y : Fin 9 → Bool,
        (W x).getD (10 + j.val) false = true ∧ (W x).getD 22 false = false ∧
        (W y).getD (10 + j.val) false = false ∧ (W y).getD 22 false = true) →
      ∃ x : Fin 9 → Bool,
        ((W x).getD (10 + j.val) false && (W x).getD 22 false) ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : Fin (13 : ℕ)),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ (x5 : Fin x1.length), ∀ x6 ∈ (x1.get x5).inputs, x6 < (10 : ℕ) + ↑x5) →         (∀ (x6 : Fin (9 : ℕ)), ∃ x7 ∈ x1, ↑x6 ∈ x7.inputs) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ))]);             (x8.getD ((10 : ℕ) + ↑x2) Bool.false && x8.getD (22 : ℕ) Bool.false) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro gs j hlen hf hvalid hreads
  let edge (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

  let seed (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 1]

  let gateOn (g : Gate) (w : List Bool) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  let step (w : List Bool) (g : Gate) : List Bool := w ++ [gateOn g w]

  have seedLen (x : Fin 9 → Bool) : (seed x).length = 10 := by
    simp [seed]

  have seedRead9 (x : Fin 9 → Bool) :
      (seed x).getD 9 false = (x 0 || x 1) := by
    simp [seed]

  have seedReadRaw (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
      (seed x).getD i false = x (Fin.ofNat 9 i) := by
    have hp : i < (List.ofFn x).length := by simpa using hi
    change (List.ofFn x ++ [x 0 || x 1]).getD i false = _
    rw [List.getD_append _ _ _ _ hp, List.getD_eq_getElem _ _ hp,
      List.getElem_ofFn]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt hi).symm

  let scope (pins : List ℕ) : Finset (Fin 9) :=
    ((pins.toFinset.erase 9).image (Fin.ofNat 9)) ∪ if 9 ∈ pins then {0,1} else ∅

  have scopeCard (pins : List ℕ) : (scope pins).card ≤ pins.length + 1 := by
    have hbase := (Finset.card_image_le (f := Fin.ofNat 9)
      (s := pins.toFinset.erase 9)).trans Finset.card_erase_le
    have hnum := List.toFinset_card_le (l := pins)
    by_cases h : 9 ∈ pins
    · have hmem : 9 ∈ pins.toFinset := List.mem_toFinset.mpr h
      have hc : (pins.toFinset.erase 9).card = pins.toFinset.card - 1 :=
        Finset.card_erase_of_mem hmem
      have hpos : 0 < pins.toFinset.card := Finset.card_pos.mpr ⟨9,hmem⟩
      have hu := Finset.card_union_le ((pins.toFinset.erase 9).image (Fin.ofNat 9))
        ({0,1} : Finset (Fin 9))
      have htwo : ({0,1} : Finset (Fin 9)).card = 2 := by decide
      rw [htwo] at hu
      have hImage := Finset.card_image_le (f := Fin.ofNat 9) (s := pins.toFinset.erase 9)
      simp only [scope, ite_eq_left h]
      omega
    · simp only [scope, ite_eq_right h, Finset.union_empty]
      exact (hbase.trans hnum).trans (Nat.le_succ _)

  have scopeRead (pins : List ℕ) (x y : Fin 9 → Bool)
      (same : ∀ v ∈ scope pins, x v = y v) (i : ℕ) (hi : i ∈ pins) :
      (seed x).getD i false = (seed y).getD i false := by
    by_cases hr : i < 9
    · rw [seedReadRaw x i hr, seedReadRaw y i hr]
      apply same
      apply Finset.mem_union_left
      apply Finset.mem_image_of_mem
      exact Finset.mem_erase.mpr ⟨by omega, List.mem_toFinset.mpr hi⟩
    · by_cases he : i = 9
      · subst i
        have h0 : (0 : Fin 9) ∈ scope pins := by simp [scope, hi]
        have h1 : (1 : Fin 9) ∈ scope pins := by simp [scope, hi]
        rw [seedRead9, seedRead9, same 0 h0, same 1 h1]
      · rw [List.getD_eq_default _ _ (by rw [seedLen]; omega),
            List.getD_eq_default _ _ (by rw [seedLen]; omega)]

  have scopeGate (g : Gate) (pins : List ℕ) (x y : Fin 9 → Bool)
      (hg : ∀ i ∈ g.inputs, i ∈ pins) (same : ∀ v ∈ scope pins, x v = y v) :
      gateOn g (seed x) = gateOn g (seed y) :=
    congrArg g.op.eval (List.map_congr_left (fun i hi =>
      scopeRead pins x y same i (hg i hi)))

  have appendRead (x : Fin 9 → Bool) (b : Bool) (i : ℕ) (hi : i ≠ 10) :
      (seed x ++ [b]).getD i false = (seed x).getD i false := by
    by_cases hb : i < 10
    · exact List.getD_append _ _ _ _ (by rwa [seedLen])
    · rw [List.getD_eq_default _ _ (by simp [seedLen]; omega),
          List.getD_eq_default _ _ (by rw [seedLen]; omega)]

  have appendRead10 (x : Fin 9 → Bool) (b : Bool) :
      (seed x ++ [b]).getD 10 false = b := by
    rw [List.getD_append_right _ _ _ _ (by rw [seedLen])]
    simp only [seedLen, Nat.sub_self, List.getD_cons_zero]

  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

  have firstSupport (g : Gate) (gs : List Gate) (hf : g.inputs.length ≤ 2) :
      ∃ S : Finset (Fin 9), S.card ≤ 4 ∧
        ∀ x y : Fin 9 → Bool, (∀ v ∈ S, x v = y v) →
          ((Circuit.mk (g :: gs) 0).wires (seed x)).getD 10 false =
            ((Circuit.mk (g :: gs) 0).wires (seed y)).getD 10 false := by
    have value (x : Fin 9 → Bool) :
        ((Circuit.mk (g :: gs) 0).wires (seed x)).getD 10 false = gateOn g (seed x) := by
      change (gs.foldl step (step (seed x) g)).getD 10 false = _
      rw [keep _ _ _ (by simp [step, seedLen])]
      exact appendRead10 x _
    refine ⟨scope g.inputs, (scopeCard _).trans (by omega), ?_⟩
    intro x y same
    rw [value x, value y]
    exact scopeGate g _ x y (fun _ h => h) same

  have secondSupport (f g : Gate) (gs : List Gate)
      (hf : f.inputs.length ≤ 2) (hg : g.inputs.length ≤ 2) :
      ∃ S : Finset (Fin 9), S.card ≤ 4 ∧
        ∀ x y : Fin 9 → Bool, (∀ v ∈ S, x v = y v) →
          ((Circuit.mk (f :: g :: gs) 0).wires (seed x)).getD 11 false =
            ((Circuit.mk (f :: g :: gs) 0).wires (seed y)).getD 11 false := by
    have value (x : Fin 9 → Bool) :
        ((Circuit.mk (f :: g :: gs) 0).wires (seed x)).getD 11 false =
          gateOn g (step (seed x) f) := by
      change (gs.foldl step (step (step (seed x) f) g)).getD 11 false = _
      rw [keep _ _ _ (by simp [step, seedLen])]
      have hlen11 : (step (seed x) f).length = 11 := by simp [step, seedLen]
      change (step (seed x) f ++ [gateOn g (step (seed x) f)]).getD 11 false = _
      rw [List.getD_append_right _ _ _ _ (by rw [hlen11])]
      simp only [hlen11, Nat.sub_self, List.getD_cons_zero]
    by_cases h10 : 10 ∈ g.inputs
    · let pins := f.inputs ++ g.inputs.erase 10
      have hp : pins.length ≤ 3 := by
        simp only [pins, List.length_append, List.length_erase_of_mem h10]
        omega
      refine ⟨scope pins, (scopeCard _).trans (by omega), ?_⟩
      intro x y same
      rw [value x, value y]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      by_cases he : i = 10
      · subst i
        change (seed x ++ [gateOn f (seed x)]).getD 10 false = _
        simp only [step, appendRead10]
        exact scopeGate f pins x y (fun j hj => List.mem_append_left _ hj) same
      · simp only [step, appendRead _ _ i he]
        apply scopeRead pins x y same i
        exact List.mem_append_right _ ((List.mem_erase_of_ne he).mpr hi)
    · refine ⟨scope g.inputs, (scopeCard _).trans (by omega), ?_⟩
      intro x y same
      rw [value x, value y]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      have he : i ≠ 10 := fun eq => h10 (eq ▸ hi)
      simp only [step, appendRead _ _ i he]
      exact scopeRead g.inputs x y same i hi

  have uncovered : ∀ S : Finset (Fin 9), S.card ≤ 4 →
      ∃ e ∈ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ),
        Fin.ofNat 9 (e / 10) ∉ S ∧ Fin.ofNat 9 (e % 10) ∉ S := by decide

  have coveringTrue (g : (Fin 9 → Bool) → Bool) (S : Finset (Fin 9))
      (hs : S.card ≤ 4) (dep : ∀ x y, (∀ v ∈ S, x v = y v) → g x = g y)
      (above : ∀ x, edge x = true → g x = true) (x : Fin 9 → Bool) : g x = true := by
    obtain ⟨e,hem,hea,heb⟩ := uncovered S hs
    let y : Fin 9 → Bool := fun v => if v ∈ S then x v else true
    have hy : edge y = true := by
      apply List.any_eq_true.mpr
      exact ⟨e,hem,by simp only [y, ite_eq_right hea, ite_eq_right heb, Bool.true_and]⟩
    exact (dep x y (by intro v hv; simp [y,hv])).trans (above y hy)

  have edgeEq (x7 : Fin 9 → Bool) : (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) = edge x7 := by
    simp only [edge, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  simp only [edgeEq]

  let head : Gate := ⟨.or, [0, 1]⟩
  have headSeed (x : Fin 9 → Bool) : step (List.ofFn x) head = seed x := by
    have r0 : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      rfl
    have r1 : (List.ofFn x).getD 1 false = x 1 := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      rfl
    change List.ofFn x ++
      [([(List.ofFn x).getD 0 false, (List.ofFn x).getD 1 false] : List Bool).any id] = seed x
    simp only [seed, List.any_cons, List.any_nil, id_eq, r0, r1, Bool.or_false]
  have bad (k : ℕ) :
      ∃ x : Fin 9 → Bool, ((Circuit.mk gs 0).wires (seed x)).getD k false ≠ edge x := by
    let D : Circuit := ⟨head :: gs, k⟩
    have hd : FanInTwo D := by
      intro g hg
      change g ∈ head :: gs at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [head]
      · exact hf g hg
    have hsize : D.size ≤ 14 := by
      change (head :: gs).length ≤ 14
      rw [List.length_cons, hlen]
    obtain ⟨x, hx⟩ := low D hd hsize
    change (gs.foldl step (step (List.ofFn x) head)).getD k false ≠ edge x at hx
    rw [headSeed x] at hx
    exact ⟨x, hx⟩

  classical
  let u (x : Fin 9 → Bool) :=
    ((Circuit.mk gs 0).wires (seed x)).getD (10 + j.val) false
  let v (x : Fin 9 → Bool) := ((Circuit.mk gs 0).wires (seed x)).getD 22 false
  change ∃ x : Fin 9 → Bool, (u x && v x) ≠ edge x
  by_contra noWitness
  have comp (x : Fin 9 → Bool) : (u x && v x) = edge x := by
    by_contra wrong
    exact noWitness ⟨x, wrong⟩
  have above (x : Fin 9 → Bool) (hx : edge x = true) : u x = true :=
    (Bool.and_eq_true_iff.mp ((comp x).trans hx)).1

  have early (hj : j.val < 2) : False := by
    have small : ∃ S : Finset (Fin 9), S.card ≤ 4 ∧
        ∀ x y : Fin 9 → Bool, (∀ i ∈ S, x i = y i) → u x = u y := by
      obtain ⟨f, g, tail, hs⟩ : ∃ f g tail, gs = f :: g :: tail := by
        cases gs with
        | nil => simp at hlen
        | cons f gs =>
          cases gs with
          | nil => simp at hlen
          | cons g tail => exact ⟨f, g, tail, rfl⟩
      have hF := (hf f (by simp [hs])).2
      have hG := (hf g (by simp [hs])).2
      by_cases hz : j.val = 0
      · simpa only [u, hz, Nat.add_zero, hs] using firstSupport f (g :: tail) hF
      · have ho : j.val = 1 := by omega
        simpa only [u, ho, hs] using secondSupport f g tail hF hG
    obtain ⟨S, hS, dep⟩ := small
    obtain ⟨x, hx⟩ := bad 22
    apply hx
    have ut : u x = true := coveringTrue u S hS dep above x
    simpa only [ut, Bool.true_and] using comp x

  have diffA : ∃ x : Fin 9 → Bool, u x = true ∧ v x = false := by
    obtain ⟨x, hx⟩ := bad (10 + j.val)
    change u x ≠ edge x at hx
    rw [← comp x] at hx
    refine ⟨x, ?_⟩
    cases hu : u x <;> cases hv : v x <;> simp [hu, hv] at hx ⊢
  have diffB : ∃ x : Fin 9 → Bool, u x = false ∧ v x = true := by
    obtain ⟨x, hx⟩ := bad 22
    change v x ≠ edge x at hx
    rw [← comp x] at hx
    refine ⟨x, ?_⟩
    cases hu : u x <;> cases hv : v x <;> simp [hu, hv] at hx ⊢
  obtain ⟨a, ha, ha'⟩ := diffA
  obtain ⟨b, hb, hb'⟩ := diffB
  have hjLower : 2 ≤ j.val := by
    by_contra hh
    exact early (by omega)
  have hjUpper : j.val < 12 := by
    have hj := j.isLt
    by_contra h
    have e : 10 + j.val = 22 := by omega
    have same : u a = v a := by
      dsimp only [u, v]
      rw [e]
    rw [ha, ha'] at same
    contradiction
  exact noWitness (residual ⟨gs, 0⟩ j hlen hf hvalid hreads hjLower hjUpper
    ⟨a, b, ha, ha', hb, hb'⟩)
