import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3250_2
    (base : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool =>
          x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5) →
      16 ≤ C.size)
    (nonconst :
      let e := fun (x : Fin 9 → Bool) =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
      ∀ (v : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) (cut pin : ℕ) (d : Bool),
        v ≠ 0 → v ≠ 6 → PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        10 ≤ pin → pin < cut → cut ≤ 10 + C.size →
        (∀ g ∈ C.gates.take (cut - 10), v.val ∉ g.inputs) →
        (∀ x : Fin 9 → Bool,
          e (Function.update x v false) ≠ e (Function.update x v true) →
            (C.wires (row (Function.update x v false))).getD pin false = !d) →
        (∃ x : Fin 9 → Bool,
          (C.wires (row (Function.update x v false))).getD pin false ≠ !d) →
        (∀ x : Fin 9 → Bool,
          let b := (C.wires (row x)).getD pin false
          C.eval ((row x).set v.val (if d = true then x v || b else x v && b)) = e x) →
        False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Bool),   x2 ≠ (0 : Fin (9 : ℕ)) →     x2 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < x4 →               x4 ≤ (10 : ℕ) + x3.size →                 (∀ x14 ∈ List.take (x4 - (10 : ℕ)) x3.gates, ↑x2 ∉ x14.inputs) →                   (∀ (x15 : Fin (9 : ℕ) → Bool),                       have x16 : Fin (9 : ℕ) → Bool := Function.update x15 x2 Bool.false;                       x1 x16 ≠ x1 (Function.update x15 x2 Bool.true) → (x3.wires (List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))])).getD x5 Bool.false = !x6) →                     ∃ (x16 : Fin (9 : ℕ) → Bool),                       have x17 : List Bool := List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))];                       have x18 : Bool := (x3.wires x17).getD x5 Bool.false;                       x3.eval (x17.set (↑x2) (if x6 = Bool.true then x16 x2 || x18 else x16 x2 && x18)) ≠ x1 x16 := by
  intro x1 v C cut pin d hv0 hv6 fan small lo plt chi avoid sens
  let f := fun (x : Fin 9 → Bool) =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  have feq : ∀ x : Fin 9 → Bool, x1 x = f x := by
    intro x
    simp only [x1, f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  have wires_run (w : List Bool) : C.wires w = run C.gates w := rfl
  have len_run : ∀ gs : List Gate, ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons g gs ih =>
      intro w
      simp only [run, List.foldl_cons]
      rw [ih]
      simp [step]
      omega
  have wireOff (gs : List Gate) (a b : List Bool) (j : ℕ)
      (len : a.length = b.length) (h : ∀ i, i ≠ j → a[i]? = b[i]?)
      (hn : ∀ g ∈ gs, j ∉ g.inputs) : ∀ i, i ≠ j → (run gs a)[i]? = (run gs b)[i]? := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      have vals : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
        apply List.map_congr_left
        intro i hi
        have ne : i ≠ j := fun he => hn g (by simp) (he ▸ hi)
        simp only [List.getD_eq_getElem?_getD, h i ne]
      change ∀ i, i ≠ j → (run gs (a ++ [_]))[i]? = (run gs (b ++ [_]))[i]?
      rw [vals]
      apply ih
      · simp [len]
      · intro i hi
        by_cases hl : i < a.length
        · rw [List.getElem?_append_left hl, List.getElem?_append_left (by omega), h i hi]
        · rw [List.getElem?_append_right (show a.length ≤ i by omega),
            List.getElem?_append_right (show b.length ≤ i by omega), len]
      · exact fun g hg => hn _ (by simp [hg])
  have rowOff (x : Fin 9 → Bool) : ∀ i, i ≠ v.val →
      (row x)[i]? = (row (Function.update x v false))[i]? := by
    intro i hi
    unfold row
    by_cases hi9 : i < 9
    · rw [List.getElem?_append_left (by simpa using hi9), List.getElem?_append_left (by simpa using hi9)]
      simp only [List.getElem?_ofFn, hi9, dite_true]
      have hne : (⟨i, hi9⟩ : Fin 9) ≠ v := fun e => hi (congrArg Fin.val e)
      have hupd : Function.update x v false ⟨i, hi9⟩ = x ⟨i, hi9⟩ :=
        Function.update_of_ne hne false x
      exact congrArg some hupd.symm
    · rw [List.getElem?_append_right (show (List.ofFn x).length ≤ i by simpa using Nat.le_of_not_gt hi9),
        List.getElem?_append_right (show (List.ofFn (Function.update x v false)).length ≤ i by
          simpa using Nat.le_of_not_gt hi9)]
      have h0 : Function.update x v false 0 = x 0 := Function.update_of_ne (Ne.symm hv0) _ _
      have h6 : Function.update x v false 6 = x 6 := Function.update_of_ne (Ne.symm hv6) _ _
      simp [h0, h6]
  have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [run, List.foldl_cons]
      rw [ih (step w g) (by simp [step]; omega)]
      simp [step]
      exact List.getD_append _ _ _ _ h
  have pinEq (x : Fin 9 → Bool) :
      (C.wires (row x)).getD pin false =
        (C.wires (row (Function.update x v false))).getD pin false := by
    let gs := C.gates.take (cut - 10)
    have hav : ∀ g ∈ gs, v.val ∉ g.inputs := fun g hg => avoid g hg
    have pin_ne : pin ≠ v.val := by have := v.isLt; omega
    have glen : gs.length = cut - 10 := by
      have hle : cut - 10 ≤ C.gates.length := by
        change cut ≤ 10 + C.gates.length at chi
        omega
      simp [gs, List.length_take, Nat.min_eq_left hle]
    have plen (y : Fin 9 → Bool) : (run gs (row y)).length = cut := by
      rw [len_run, glen]
      simp [row]
      omega
    have pre (y : Fin 9 → Bool) :
        (C.wires (row y)).getD pin false = (run gs (row y)).getD pin false := by
      have split : gs ++ C.gates.drop (cut - 10) = C.gates := List.take_append_drop _ _
      have hlt : pin < (run gs (row y)).length := by rw [plen]; exact plt
      rw [wires_run, ← split]
      simp only [run, List.foldl_append]
      exact preserve (C.gates.drop (cut - 10)) (gs.foldl step (row y)) pin hlt
    rw [pre x, pre (Function.update x v false)]
    have hopt := wireOff gs (row x) (row (Function.update x v false)) v.val
      (by simp [row]) (rowOff x) hav pin pin_ne
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hopt]
  by_contra! ag
  have sensE : ∀ x : Fin 9 → Bool,
      f (Function.update x v false) ≠ f (Function.update x v true) →
        (C.wires (row (Function.update x v false))).getD pin false = !d := by
    intro x hs
    have hs1 : x1 (Function.update x v false) ≠ x1 (Function.update x v true) := by
      simpa [feq] using hs
    simpa [row] using sens x hs1
  by_cases hconst : ∀ x : Fin 9 → Bool,
      (C.wires (row (Function.update x v false))).getD pin false = !d
  · have rawPin (x : Fin 9 → Bool) : (C.wires (row x)).getD pin false = !d :=
      (pinEq x).trans (hconst x)
    have restore (x : Fin 9 → Bool) : (row x).set v.val (x v) = row x := by
      have room : v.val < (row x).length := by have := v.isLt; simp [row]; omega
      have found : (row x)[v.val] = x v := by
        unfold row
        have hv : v.val < (List.ofFn x).length := by simp
        rw [List.getElem_append_left hv]
        simpa [Fin.eta] using List.getElem_ofFn (f := x) (i := v.val) hv
      rw [← found, List.set_getElem_self room]
    have direct (x : Fin 9 → Bool) : C.eval (row x) = f x := by
      have h := ag x
      dsimp at h
      rw [feq] at h
      have hm : (if d = true then x v || (C.wires (row x)).getD pin false
          else x v && (C.wires (row x)).getD pin false) = x v := by
        cases d with
        | false =>
          rw [if_neg Bool.false_ne_true]
          have hb : (C.wires (row x)).getD pin false = true := by simpa using rawPin x
          rw [hb]
          exact Bool.and_true (x v)
        | true =>
          rw [if_pos rfl]
          have hb : (C.wires (row x)).getD pin false = false := by simpa using rawPin x
          rw [hb]
          exact Bool.or_false (x v)
      have heq : C.eval ((row x).set v.val (if d = true then x v || (C.wires (row x)).getD pin false
          else x v && (C.wires (row x)).getD pin false)) = f x :=
        Classical.not_not.mp (by simpa [row] using h)
      rw [hm, restore x] at heq
      exact heq
    have seeded : ∃ D : Circuit, FanInTwo D ∧ D.size = C.size + 1 ∧ circuitFun 9 D = f := by
      let D : Circuit := ⟨⟨.or, [0, 6]⟩ :: C.gates, C.output⟩
      have fanD : FanInTwo D := by
        intro g seen
        rcases List.mem_cons.mp seen with rfl | other
        · simp
        · exact fan g other
      refine ⟨D, fanD, rfl, ?_⟩
      funext x
      have init : step (List.ofFn x) ⟨.or, [0, 6]⟩ = row x := by
        change List.ofFn x ++ [x 0 || (x 6 || false)] = row x
        simp [row]
      change (C.gates.foldl step (step (List.ofFn x) ⟨.or, [0, 6]⟩)).getD C.output false = f x
      rw [init]
      exact direct x
    obtain ⟨D, fanD, sizeD, computesD⟩ := seeded
    have generalBound (fn : (Fin 9 → Bool) → Bool)
        (lower : ∀ c : Circuit, FanInTwo c →
          (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 4 && x 6)) →
          circuitFun 9 c = fn → 16 ≤ c.size)
        (c : Circuit) (fanin : FanInTwo c) (computes : circuitFun 9 c = fn) :
        15 ≤ c.size := by
      let shiftWire (i : ℕ) : ℕ := if i < 9 then i else i + 1
      let shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map shiftWire⟩
      let stepG (w : List Bool) (g : Gate) : List Bool :=
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      let Relation (old new : List Bool) : Prop :=
        9 ≤ old.length ∧ new.length = old.length + 1 ∧
          ∀ i, new.getD (shiftWire i) false = old.getD i false
      have relateInitial (x : Fin 9 → Bool) (value : Bool) :
          Relation (List.ofFn x) (List.ofFn x ++ [value]) := by
        refine ⟨by simp, by simp, ?_⟩
        intro i
        by_cases inside : i < 9
        · simp only [shiftWire, ite_eq_left inside]
          exact List.getD_append _ _ _ _ (by simpa using inside)
        · simp only [shiftWire, ite_eq_right inside]
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have relateAppend (old new : List Bool) (value : Bool) (r : Relation old new) :
          Relation (old ++ [value]) (new ++ [value]) := by
        obtain ⟨width, length, same⟩ := r
        refine ⟨by simp; omega, by simp [length], ?_⟩
        intro i
        by_cases oldInput : i < old.length
        · have newInput : shiftWire i < new.length := by
            unfold shiftWire
            split <;> omega
          rw [List.getD_append _ _ _ _ newInput, List.getD_append _ _ _ _ oldInput]
          exact same i
        · have past : old.length ≤ i := by omega
          have shift : shiftWire i = i + 1 := ite_eq_right (by omega)
          have npast : new.length ≤ shiftWire i := by omega
          rw [List.getD_append_right _ _ _ _ npast, List.getD_append_right _ _ _ _ past, shift, length]
          congr 1
          omega
      have relateFold (gs : List Gate) (old new : List Bool) (r : Relation old new) :
          Relation (gs.foldl stepG old) ((gs.map shiftGate).foldl stepG new) := by
        induction gs generalizing old new with
        | nil => exact r
        | cons g rest ih =>
          have inputs : ((g.inputs.map shiftWire).map fun i => new.getD i false) =
              (g.inputs.map fun i => old.getD i false) := by
            rw [List.map_map]
            exact List.map_congr_left fun i _ => r.2.2 i
          apply ih (stepG old g) (stepG new (shiftGate g))
          unfold stepG
          change Relation (old ++ [g.op.eval (g.inputs.map fun i => old.getD i false)])
            (new ++ [g.op.eval ((g.inputs.map shiftWire).map fun i => new.getD i false)])
          rw [inputs]
          exact relateAppend old new _ r
      have preserveInitial (gs : List Gate) (wires : List Bool) (i : ℕ) (h : i < wires.length) :
          (gs.foldl stepG wires).getD i false = wires.getD i false := by
        induction gs generalizing wires with
        | nil => rfl
        | cons gate rest ih =>
          rw [List.foldl_cons, ih (stepG wires gate) (by simp [stepG]; omega)]
          unfold stepG
          exact List.getD_append _ _ _ _ h
      let prefixed (c : Circuit) : Circuit :=
        ⟨⟨.and, [4, 6]⟩ :: c.gates.map shiftGate, shiftWire c.output⟩
      have prefixIsAnd (c : Circuit) (x : Fin 9 → Bool) :
          ((prefixed c).wires (List.ofFn x)).getD 9 false = (x 4 && x 6) := by
        change ((c.gates.map shiftGate).foldl stepG (stepG (List.ofFn x) ⟨.and, [4, 6]⟩)).getD 9 false = _
        rw [preserveInitial _ _ _ (by simp [stepG])]
        change (x 4 && (x 6 && true)) = (x 4 && x 6)
        simp
      have prefixComputes (c : Circuit) (x : Fin 9 → Bool) :
          circuitFun 9 (prefixed c) x = circuitFun 9 c x := by
        change ((c.gates.map shiftGate).foldl stepG (stepG (List.ofFn x) ⟨.and, [4, 6]⟩)).getD
          (shiftWire c.output) false = _
        exact (relateFold c.gates _ _ (relateInitial x _)).2.2 c.output
      have paddedFanIn : FanInTwo (prefixed c) := by
        intro g inside
        rcases List.mem_cons.mp inside with equal | inTail
        · subst g
          simp
        · obtain ⟨source, member, rfl⟩ := List.mem_map.mp inTail
          simpa [shiftGate] using fanin source member
      have paddedComputes : circuitFun 9 (prefixed c) = fn := by
        ext x
        rw [prefixComputes, computes]
      have bound := lower (prefixed c) paddedFanIn (prefixIsAnd c) paddedComputes
      change 16 ≤ (Gate.mk .and [4, 6] :: c.gates.map shiftGate).length at bound
      simp at bound
      change 15 ≤ c.gates.length
      omega
    have h15 := generalBound f base D fanD computesD
    omega
  · have hex : ∃ x : Fin 9 → Bool,
        (C.wires (row (Function.update x v false))).getD pin false ≠ !d :=
      not_forall.mp hconst
    have agreeE : ∀ x : Fin 9 → Bool,
        let b := (C.wires (row x)).getD pin false
        C.eval ((row x).set v.val (if d = true then x v || b else x v && b)) = f x := by
      intro x
      have h := ag x
      dsimp at h
      rw [feq] at h
      exact Classical.not_not.mp (by simpa [row] using h)
    exact nonconst v C cut pin d hv0 hv6 fan small lo plt chi avoid sensE hex agreeE
