import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The checked fourteen-gate bound excludes early outputs and unused precomputed wires.
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.R_meta_4336_219
    (fourteen : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (active : ∀ pair : Fin 9 × Fin 9, pair ∈ [(0,1), (0,2), (0,3), (0,4), (0,6), (4,6)] →
      ∀ C : Circuit, FanInTwo C → C.size = 14 → C.output = 23 →
      (∃ g ∈ C.gates,
        9 ∈ if GateOp.rec false false true (fun _ => false) false g.op = true
          then g.inputs.take 1 else g.inputs) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x pair.1 && x pair.2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [x6 x1.1 && x6 x1.2]) ≠ (fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) x6 := by
  intro pair valid C legal bound
  let f (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let input (x : Fin 9 → Bool) := List.ofFn x ++ [x pair.1 && x pair.2]
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  change ∃ x, C.eval (input x) ≠ f x
  by_contra! agree
  have impossible : ¬ HasCircuitSize 9 f 14 := by
    convert fourteen using 2
    funext x
    simp [f, List.any_cons, Bool.or_assoc] <;> rfl
  have boundList : C.gates.length ≤ 14 := bound
  have len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have outputExists : C.output < 10 + C.gates.length := by
    let x : Fin 9 → Bool := fun _ => true
    have hf : f x = true := by decide
    have h := agree x
    change (C.gates.foldl step (input x)).getD C.output false = f x at h
    rw [hf] at h
    by_contra! out
    have hw : (C.gates.foldl step (input x)).length = 10 + C.gates.length := by
      simp [len, input]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
    contradiction
  have outputLast : C.output = 23 := by
    by_contra h
    have earlier : C.output < 23 := by omega
    let start : Gate := ⟨.and, [pair.1.val, pair.2.val]⟩
    let front := C.gates.take 13
    have startEval (x : Fin 9 → Bool) : step (List.ofFn x) start = input x := by
      change List.ofFn x ++ [((List.ofFn x).getD pair.1.val false &&
        ((List.ofFn x).getD pair.2.val false && true))] = _
      have lookup (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
        rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
      rw [lookup, lookup]
      simp [input]
    apply impossible
    refine ⟨⟨start :: front, C.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hfront
      · simp [start]
      · exact legal g (List.mem_of_mem_take hfront)
    · change (start :: front).length ≤ 14
      simp [front]
    · intro x
      change (front.foldl step (step (List.ofFn x) start)).getD C.output false = f x
      rw [startEval, ← agree x]
      change _ = (C.gates.foldl step (input x)).getD C.output false
      have split : front ++ C.gates.drop 13 = C.gates := List.take_append_drop 13 C.gates
      have enough : C.output < (front.foldl step (input x)).length := by
        rw [len]
        simp [front, input]
        omega
      symm
      calc
        (C.gates.foldl step (input x)).getD C.output false =
            ((front ++ C.gates.drop 13).foldl step (input x)).getD C.output false :=
          congrArg (fun gs : List Gate => (gs.foldl step (input x)).getD C.output false) split.symm
        _ = _ := by rw [List.foldl_append, keep _ _ _ enough]
  have sizeExact : C.size = 14 := by
    change C.gates.length = 14
    omega
  let read (g : Gate) : List ℕ :=
    if GateOp.rec false false true (fun _ => false) false g.op = true then g.inputs.take 1 else g.inputs
  by_cases used : ∃ g ∈ C.gates, 9 ∈ read g
  · obtain ⟨x, hx⟩ := active pair valid C legal sizeExact outputLast used
    exact hx (agree x)
  have unused : ∀ g ∈ C.gates, 9 ∉ read g := fun g hg hr => used ⟨g, hg, hr⟩
  let rename (i : ℕ) := if i < 9 then i else i - 1
  let gate (g : Gate) : Gate := ⟨g.op, (read g).map rename⟩
  have evalRead (g : Gate) (v : ℕ → Bool) :
      g.op.eval (g.inputs.map v) = g.op.eval ((read g).map v) := by
    rcases g with ⟨op, args⟩
    cases op <;> try rfl
    cases args <;> rfl
  have compare (gs : List Gate) (none : ∀ g ∈ gs, 9 ∉ read g)
      (short full : List Bool) (enough : 9 ≤ short.length) (size : short.length + 1 = full.length)
      (same : ∀ i, i ≠ 9 → short.getD (rename i) false = full.getD i false) :
      ∀ i, i ≠ 9 → ((gs.map gate).foldl step short).getD (rename i) false =
        (gs.foldl step full).getD i false := by
    induction gs generalizing short full with
    | nil => exact same
    | cons g gs ih =>
      let value := g.op.eval (g.inputs.map fun i => full.getD i false)
      have equalGate : step short (gate g) = short ++ [value] := by
        change short ++ [g.op.eval (((read g).map rename).map (fun i => short.getD i false))] = _
        congr 2
        have result : value = g.op.eval ((read g).map fun i => full.getD i false) :=
          evalRead g (fun i => full.getD i false)
        rw [result, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact same i (fun eq => none g (by simp) (eq ▸ hi))
      change ∀ i, i ≠ 9 →
        ((gs.map gate).foldl step (step short (gate g))).getD (rename i) false =
          (gs.foldl step (step full g)).getD i false
      rw [equalGate]
      change ∀ i, i ≠ 9 →
        ((gs.map gate).foldl step (short ++ [value])).getD (rename i) false =
          (gs.foldl step (full ++ [value])).getD i false
      apply ih (fun g hg => none g (by simp [hg])) _ _ (by simp; omega) (by simp; omega)
      intro i hi
      have inRange : rename i < short.length ↔ i < full.length := by
        dsimp [rename]
        split <;> omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
      by_cases old : i < full.length
      · rw [if_pos old, if_pos (inRange.mpr old)]
        exact same i hi
      · rw [if_neg old, if_neg (fun h => old (inRange.mp h))]
        congr 2
        dsimp [rename]
        split <;> omega
  apply impossible
  refine ⟨⟨C.gates.map gate, rename C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨old, oldIn, rfl⟩ := List.mem_map.mp hg
    obtain ⟨op, arity⟩ := legal old oldIn
    refine ⟨op, ?_⟩
    change ((read old).map rename).length ≤ 2
    rw [List.length_map]
    unfold read
    split <;> simp_all
  · change (C.gates.map gate).length ≤ 14
    simpa using boundList
  · intro x
    rw [← agree x]
    change ((C.gates.map gate).foldl step (List.ofFn x)).getD (rename C.output) false =
      (C.gates.foldl step (input x)).getD C.output false
    apply compare C.gates unused _ _ (by simp) (by simp [input]) _ C.output (by omega)
    intro i hi
    simp only [input, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn]
    by_cases low : i < 9
    · simp [rename, low]
    · have old : 9 ≤ rename i := by simp [rename, low]; omega
      have gone : i - 9 ≠ 0 := by omega
      have absent : (List.ofFn x)[rename i]? = none :=
        List.getElem?_eq_none (by simpa only [List.length_ofFn] using old)
      simp only [absent, if_neg low, List.getElem?_singleton, if_neg gone, Option.getD_none]
