import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_3057_415
    (binary : let edge := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ (D : Circuit), FanInTwo D → (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = edge x) →
        13 ≤ D.gates.countP (fun g => g.op.eval [true]))
    (degenerate : let edge := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ i ∈ ([0,9,10] : List (Fin 11)), ∀ C : Circuit, Monotone2 C → C.size = 13 → C.output = 23 →
        ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [!x 0]
          C.eval (w ++ [!(w.getD i.val false)]) ≠ edge x)
    (distinct : let edge := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ i ∈ ([1,2,3,4,6] : List (Fin 11)), ∀ C : Circuit, Monotone2 C → C.size = 13 → C.output = 23 →
        ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [!x 0]
          C.eval (w ++ [!(w.getD i.val false)]) ≠ edge x) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (512 : ℕ)),             have x7 : Fin (9 : ℕ) → Bool := fun (x7 : Fin (9 : ℕ)) => Decidable.decide (↑x6 / (2 : ℕ) ^ (↑x7 % (9 : ℕ)) % (2 : ℕ) = (1 : ℕ));             have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];             x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x9.1 && x7 x9.2 := by
  let edge := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  intro pins pinSize C fan size
  by_contra! agreed
  let D : Circuit := ⟨⟨.not,[0]⟩ :: ⟨.not,pins⟩ :: C.gates, C.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    simp only [D,List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · exact ⟨by simp, pinSize⟩
    · exact fan g hg
  have encode (x : Fin 9 → Bool) :
      ∃ m : Fin 512, ∀ i : Fin 9, decide (m.val / 2 ^ (i.val % 9) % 2 = 1) = x i := by
    let pack (bits : List (Fin 9)) : ℕ := bits.foldr (fun i rest => 2 ^ i.val ||| rest) 0
    have bound (bits : List (Fin 9)) : pack bits < 512 := by
      induction bits with
      | nil => decide
      | cons i rest ih =>
        have hi : 2 ^ i.val < 2 ^ 9 := Nat.pow_lt_pow_right (by decide) i.isLt
        exact Nat.or_lt_two_pow hi ih
    have bit (bits : List (Fin 9)) (i : Fin 9) :
        (pack bits).testBit i.val = decide (i ∈ bits) := by
      induction bits with
      | nil => simp [pack]
      | cons j js ih =>
        change (2 ^ j.val ||| pack js).testBit i.val = _
        rw [Nat.testBit_or, Nat.testBit_two_pow, ih]
        by_cases same : i = j
        · subst j
          simp
        · have ne : j.val ≠ i.val := fun h => same (Fin.ext h.symm)
          simp [same, ne]
    let bits := ((List.finRange 9).filter x)
    refine ⟨⟨pack bits, bound bits⟩, fun i => ?_⟩
    rw [Nat.mod_eq_of_lt i.isLt, ← Nat.testBit_eq_decide_div_mod_eq, bit]
    simp [bits]
  have computes (x : Fin 9 → Bool) :
      C.eval (w x ++ [GateOp.not.eval (pins.map fun i => (w x).getD i false)]) = edge x := by
    obtain ⟨m,hm⟩ := encode x
    let z (i : Fin 9) := decide (m.val / 2 ^ (i.val % 9) % 2 = 1)
    have eq : z = x := funext hm
    have checked : C.eval (w z ++ [GateOp.not.eval (pins.map fun i => (w z).getD i false)]) =
        edge z := not_not.mp (agreed m)
    rwa [eq] at checked
  have input (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have full (x : Fin 9 → Bool) : D.eval (List.ofFn x) = edge x := by
    let u := List.ofFn x ++ [GateOp.not.eval [(List.ofFn x).getD 0 false]]
    change C.eval (u ++ [GateOp.not.eval (pins.map fun i => u.getD i false)]) = edge x
    have eq : u = w x := by
      dsimp only [u,w]
      rw [show (List.ofFn x).getD 0 false = x 0 from input x 0]
      rfl
    rw [eq]
    exact computes x
  have needed := binary D fanD full
  have nbin : 13 ≤ C.gates.countP (fun g => g.op.eval [true]) := needed
  have partition : C.gates.countP (fun g => g.op.eval [true]) +
      C.gates.countP (fun g => !(g.op.eval [true])) = C.gates.length := by
    simpa only [decide_not, Bool.decide_coe] using
      (List.length_eq_countP_add_countP (fun g : Gate => g.op.eval [true]) (l := C.gates)).symm
  have exactSize : C.size = 13 := by
    change C.gates.length = 13
    change C.gates.length ≤ 13 at size
    omega
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨op,arity⟩ := fan g hg
    refine ⟨?_,arity⟩
    have none : C.gates.countP (fun g => !(g.op.eval [true])) = 0 := by
      change C.gates.length ≤ 13 at size
      omega
    have good := List.countP_eq_zero.mp none g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    rcases op with a | b | n
    · exact Or.inl a
    · exact Or.inr b
    · exact (good (by rw [n]; rfl)).elim
  have outputLast : C.output = 23 := by
    let evalStep (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
    have length (gs : List Gate) (u : List Bool) :
        (gs.foldl evalStep u).length = u.length + gs.length := by
      induction gs generalizing u with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldl_cons, ih, evalStep, List.length_append,
          List.length_cons, List.length_nil]
        omega
    have retains (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i < u.length) :
        (gs.foldl evalStep u).getD i false = u.getD i false := by
      induction gs generalizing u with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [evalStep]; omega)]
        exact List.getD_append _ _ _ _ hi
    by_cases above : 24 ≤ C.output
    · let x : Fin 9 → Bool := fun _ => true
      have e := full x
      change (D.gates.foldl evalStep (List.ofFn x)).getD C.output false = edge x at e
      have dl : D.gates.length = 15 := by
        change C.gates.length = 13 at exactSize
        simp [D,exactSize]
      have out : (D.gates.foldl evalStep (List.ofFn x)).length ≤ C.output := by
        rw [length, List.length_ofFn, dl]
        exact above
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none out] at e
      exact False.elim (Bool.false_ne_true e)
    · by_contra early
      have below : C.output < 23 := by omega
      let T : Circuit := ⟨D.gates.take 14, D.output⟩
      have len : T.gates.length = 14 := by
        change C.gates.length = 13 at exactSize
        simp [T,D,exactSize]
      have fanT : FanInTwo T := fun g hg => fanD g (List.mem_of_mem_take hg)
      have computesT (x : Fin 9 → Bool) : T.eval (List.ofFn x) = edge x := by
        let u := T.gates.foldl evalStep (List.ofFn x)
        have ul : u.length = 23 := by rw [length, List.length_ofFn, len]
        have e : D.eval (List.ofFn x) = T.eval (List.ofFn x) := by
          change (D.gates.foldl evalStep (List.ofFn x)).getD C.output false = u.getD C.output false
          nth_rw 1 [← List.take_append_drop 14 D.gates]
          rw [List.foldl_append, retains _ u _ (by omega)]
        exact e.symm.trans (full x)
      have lower := binary T fanT computesT
      change 13 ≤ ((C.gates.take 12).countP (fun g => g.op.eval [true])) at lower
      have cap : (C.gates.take 12).length ≤ 12 := by simp
      have count : (C.gates.take 12).countP (fun g => g.op.eval [true]) ≤
          (C.gates.take 12).length := List.countP_le_length
      omega
  let p : Fin 11 := if h : pins.headD 10 < 10 then ⟨pins.headD 10, by omega⟩ else 10
  have same (x : Fin 9 → Bool) :
      GateOp.not.eval (pins.map fun i => (w x).getD i false) = !((w x).getD p.val false) := by
    have wl : (w x).length = 10 := by simp [w]
    have outside (i : ℕ) (hi : 10 ≤ i) : (w x).getD i false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    have value : (w x).getD (pins.headD 10) false = (w x).getD p.val false := by
      dsimp only [p]
      split
      · rfl
      · rename_i high
        rw [outside _ (by omega), outside _ (by decide)]
    rw [← value]
    cases pins with
    | nil =>
      exact congrArg Bool.not (outside 10 (by decide)).symm
    | cons i t => rfl
  have normalized (x : Fin 9 → Bool) : C.eval (w x ++ [!((w x).getD p.val false)]) = edge x := by
    rw [← same]
    exact computes x
  by_cases direct : p ∈ ([0,9,10] : List (Fin 11))
  · obtain ⟨x,hx⟩ := degenerate p direct C mono exactSize outputLast
    exact hx (normalized x)
  by_cases usual : p ∈ ([1,2,3,4,6] : List (Fin 11))
  · obtain ⟨x,hx⟩ := distinct p usual C mono exactSize outputLast
    exact hx (normalized x)
  let pi (i : Fin 9) : Fin 9 :=
    ([0,5,8,3,4,1,7,6,2] : List (Fin 9)).getD i.val 0
  let move (i : ℕ) : ℕ := if h : i < 9 then (pi ⟨i,h⟩).val else i
  have mapSmall : ∀ i < 9, move i < 9 := by
    intro i hi
    rw [show move i = (pi ⟨i,hi⟩).val from dite_eq_left hi]
    exact (pi ⟨i,hi⟩).isLt
  have fixed : ∀ i, 9 ≤ i → move i = i := by
    intro i hi
    exact dite_eq_right (by omega)
  have psmall : p.val < 9 := by
    have verify : ∀ j : Fin 11, ¬j ∈ ([0,9,10] : List (Fin 11)) →
        ¬j ∈ ([1,2,3,4,6] : List (Fin 11)) → j.val < 9 := by decide +kernel
    exact verify p direct usual
  let q : Fin 11 := ⟨move p.val, (mapSmall _ psmall).trans (by decide)⟩
  have representative : q ∈ ([1,2,3,4,6] : List (Fin 11)) := by
    have verify : ∀ j : Fin 11, ¬j ∈ ([0,9,10] : List (Fin 11)) →
        ¬j ∈ ([1,2,3,4,6] : List (Fin 11)) →
        ∃ k ∈ ([1,2,3,4,6] : List (Fin 11)), k.val = move j.val := by decide +kernel
    obtain ⟨k,hk,eq⟩ := verify p direct usual
    exact (Fin.ext eq : k = q) ▸ hk
  have preserve : ∀ x : Fin 9 → Bool, edge (x ∘ pi) = edge x := by decide +kernel
  have fixZero : pi 0 = 0 := rfl
  let tail (x : Fin 9 → Bool) (i : Fin 11) := w x ++ [!((w x).getD i.val false)]
  let pinRelabel (g : Gate) : Gate := ⟨g.op,g.inputs.map move⟩
  let E : Circuit := ⟨C.gates.map pinRelabel, move C.output⟩
  have monoE : Monotone2 E := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(mono a ha).1,by simpa only [pinRelabel,List.length_map] using (mono a ha).2⟩
  have sizeE : E.size = 13 := by
    change (C.gates.map pinRelabel).length = 13
    rw [List.length_map]
    exact exactSize
  let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
  let consistent (u v : List Bool) := u.length = v.length ∧ 11 ≤ u.length ∧
    ∀ i, u.getD i false = v.getD (move i) false
  have stable (u v : List Bool) (b : Bool) (h : consistent u v) : consistent (u++[b]) (v++[b]) := by
    obtain ⟨len,lower,same⟩ := h
    refine ⟨by simp [len],by simp; omega,fun i => ?_⟩
    by_cases small : i < 9
    · rw [List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by have := mapSmall i small; omega)]
      exact same i
    · rw [fixed i (by omega)]
      by_cases inside : i < u.length
      · rw [List.getD_append _ _ _ _ inside,List.getD_append _ _ _ _ (by omega)]
        simpa only [fixed i (by omega)] using same i
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),len]
  have transfer (gs : List Gate) (u v : List Bool) (h : consistent u v) :
      consistent (gs.foldl step u) ((gs.map pinRelabel).foldl step v) := by
    induction gs generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      change consistent (gs.foldl step (step u g)) ((gs.map pinRelabel).foldl step (step v (pinRelabel g)))
      apply ih
      have a : g.inputs.map (fun i => u.getD i false) =
          (pinRelabel g).inputs.map (fun i => v.getD i false) := by
        simp only [pinRelabel,List.map_map]
        apply List.map_congr_left
        exact fun i _ => h.2.2 i
      change consistent (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
        (v ++ [g.op.eval ((pinRelabel g).inputs.map fun i => v.getD i false)])
      rw [← a]
      exact stable _ _ _ h
  have base (x : Fin 9 → Bool) : consistent (tail (x ∘ pi) p) (tail x q) := by
    have wl (y : Fin 9 → Bool) : (w y).length = 10 := by simp [w]
    have raw (y : Fin 9 → Bool) (i : Fin 9) : (w y).getD i.val false = y i := by
      rw [show w y = List.ofFn y ++ [!y 0] from rfl, List.getD_append _ _ _ _ (by simp)]
      exact input y i
    have neg (y : Fin 9 → Bool) : (w y).getD 9 false = !y 0 := by
      rw [show w y = List.ofFn y ++ [!y 0] from rfl, List.getD_append_right _ _ _ _ (by simp)]
      rfl
    have pre : ∀ i, (w (x ∘ pi)).getD i false = (w x).getD (move i) false := by
      intro i
      by_cases h : i < 9
      · rw [show move i = (pi ⟨i,h⟩).val from dite_eq_left h]
        exact (raw (x ∘ pi) ⟨i,h⟩).trans (raw x (pi ⟨i,h⟩)).symm
      · rw [fixed i (by omega)]
        by_cases eq : i = 9
        · subst i
          rw [neg,neg]
          exact congrArg (fun j => !x j) fixZero
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by rw [wl]; omega),
            List.getElem?_eq_none (by rw [wl]; omega)]
    let b := !((w x).getD q.val false)
    have tails : (!((w (x ∘ pi)).getD p.val false)) = b := congrArg Bool.not (pre p.val)
    refine ⟨by simp [tail,wl],by simp [tail,wl],fun i => ?_⟩
    change ((w (x ∘ pi)) ++ [!((w (x ∘ pi)).getD p.val false)]).getD i false =
        ((w x) ++ [b]).getD (move i) false
    rw [tails]
    by_cases h : i < 10
    · have qh : move i < 10 := by
        by_cases small : i < 9
        · have := mapSmall i small
          omega
        · rwa [fixed i (by omega)]
      rw [List.getD_append (w (x ∘ pi)) [b] false i (by rw [wl]; omega),
        List.getD_append (w x) [b] false (move i) (by rw [wl]; omega)]
      exact pre i
    · rw [fixed i (by omega),
        List.getD_append_right (w (x ∘ pi)) [b] false i (by rw [wl]; omega),
        List.getD_append_right (w x) [b] false i (by rw [wl]; omega),wl,wl]
  obtain ⟨x,hx⟩ := distinct q representative E monoE sizeE (by change move C.output = 23; rw [outputLast]; rfl)
  have value : C.eval (tail (x ∘ pi) p) = E.eval (tail x q) :=
    (transfer C.gates _ _ (base x)).2.2 C.output
  exact hx (value.symm.trans ((normalized (x ∘ pi)).trans (preserve x)))
