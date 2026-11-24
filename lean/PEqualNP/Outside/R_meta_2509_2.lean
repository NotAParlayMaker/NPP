import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2509_2 :
    (let f : (Fin 8 → Bool) → Bool := fun x =>
       (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)
     ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (k : Bool),
       PEqualNP.MetaComplexity.FanInTwo A →
       PEqualNP.MetaComplexity.FanInTwo B →
       (∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [k]) = (f x || x 0 || x 3)) →
       10 + B.gates.countP (fun g =>
         (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + A.size))
         ≤ A.size + B.size) →
    (let f : (Fin 8 → Bool) → Bool := fun x =>
       (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)
     ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (k : Bool),
       PEqualNP.MetaComplexity.FanInTwo A →
       PEqualNP.MetaComplexity.FanInTwo B →
       A.output + 1 = 8 + A.size →
       B.output ≠ 8 + A.size →
       B.gates.countP (fun g =>
         (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + A.size)) = 1 →
       11 ≤ A.size + B.size →
       A.size + B.size ≤ 13 →
       (∀ x : Fin 8 → Bool, f x = false → (x 0 || x 3) = true → PEqualNP.MetaComplexity.circuitFun 8 A x = !k) →
       (∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 A x]) = f x) →
       (∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [k]) = (f x || x 0 || x 3)) → False) →
    (let f : (Fin 8 → Bool) → Bool := fun x =>
       (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)
     ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (k : Bool),
       PEqualNP.MetaComplexity.FanInTwo A →
       PEqualNP.MetaComplexity.FanInTwo B →
       A.output + 1 = 8 + A.size →
       B.output ≠ 8 + A.size →
       B.gates.countP (fun g =>
         (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + A.size)) = 2 →
       12 ≤ A.size + B.size →
       A.size + B.size ≤ 13 →
       (∀ x : Fin 8 → Bool, f x = false → (x 0 || x 3) = true → PEqualNP.MetaComplexity.circuitFun 8 A x = !k) →
       (∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 A x]) = f x) →
       (∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [k]) = (f x || x 0 || x 3)) → False) →
    (let f : (Fin 8 → Bool) → Bool := fun x =>
       (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)
     ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (k : Bool),
       PEqualNP.MetaComplexity.FanInTwo A →
       PEqualNP.MetaComplexity.FanInTwo B →
       A.output + 1 = 8 + A.size →
       B.output ≠ 8 + A.size →
       B.gates.countP (fun g =>
         (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + A.size)) = 3 →
       A.size + B.size = 13 →
       (∀ x : Fin 8 → Bool, f x = false → (x 0 || x 3) = true → PEqualNP.MetaComplexity.circuitFun 8 A x = !k) →
       (∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 A x]) = f x) →
       (∀ x : Fin 8 → Bool, B.eval (A.wires (List.ofFn x) ++ [k]) = (f x || x 0 || x 3)) → False) →
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         (8 : ℕ) ≤ x4 →           x4 < (8 : ℕ) + x2.size →             have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);             have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;             (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = !x5) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [x5]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  intro saving hR1 hR2 hR3
  dsimp only at saving hR1 hR2 hR3 ⊢
  intro A B tap k fanA fanB budget notInput valid switches neutral
  by_contra hAll
  have forced : ∀ x : Fin 8 → Bool,
      B.eval (A.wires (List.ofFn x) ++ [k]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4) || x 0 || x 3) := by
    intro x
    by_contra hne
    exact hAll ⟨x, hne⟩
  let step := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) => gs.foldl step w
  let ren := fun (f : ℕ → ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map f)
  have growth : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ more, run gs w = w ++ more ∧ more.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp [run], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨rest, e, len⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: rest, ?_, by simp [len]⟩
      change run gs (step w g) = _
      rw [e]
      simp [step, List.append_assoc]
  have runLength : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (run gs w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨more, e, n⟩ := growth gs w
    simp [e, n]
  have runAppend : ∀ (l r : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      run (l ++ r) w = run r (run l w) := by
    intro l r w
    simp only [run, List.foldl_append]
  have getD_run_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (run gs w).getD i false = w.getD i false := by
    intro gs w i hi
    obtain ⟨more, e, _⟩ := growth gs w
    rw [e, List.getD_append _ _ false i hi]
  have translate : ∀ (f : ℕ → ℕ) (u v : List Bool),
      (∀ (z : List Bool) i, (v ++ z).getD (f i) false = (u ++ z).getD i false) →
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
        ∃ z, run gs u = u ++ z ∧ run (gs.map (ren f)) v = v ++ z ∧ z.length = gs.length := by
    intro f u v read gs
    induction gs using List.reverseRecOn with
    | nil => exact ⟨[], by simp [run], by simp [run], rfl⟩
    | append_singleton gs g ih =>
      obtain ⟨z, old, fresh, len⟩ := ih
      let b := g.op.eval (g.inputs.map fun i => (u ++ z).getD i false)
      refine ⟨z ++ [b], ?_, ?_, by simp [len]⟩
      · rw [runAppend, old]
        simp only [run, List.foldl_cons, List.foldl_nil, step, b, List.append_assoc]
      · rw [List.map_append, runAppend, fresh]
        simp only [List.map_cons, List.map_nil, run, List.foldl_cons, List.foldl_nil, step, ren,
          List.map_map, Function.comp_def, read, b, List.append_assoc]
  let stop := tap + 1 - 8
  let first := A.gates.take stop
  let rest := A.gates.drop stop
  let d := 8 + first.length
  let m := 8 + A.size
  have stopBound : stop ≤ A.gates.length := by
    change tap < 8 + A.gates.length at valid
    dsimp [stop]
    omega
  have firstLen : first.length = stop := by simp [first, Nat.min_eq_left stopBound]
  have lastAt : tap + 1 = d := by dsimp [d]; rw [firstLen]; dsimp [stop]; omega
  have restLen : d + rest.length = m := by
    change 8 + first.length + (A.gates.drop stop).length = 8 + A.gates.length
    rw [firstLen, List.length_drop]
    omega
  have parts : first ++ rest = A.gates := List.take_append_drop _ _
  let shift := fun i : ℕ => if i < d then i else i + 1
  let perm := fun i : ℕ => if i < d then i else if i < m then i + 1 else if i = m then d else i
  let P : PEqualNP.CircuitLowerBounds.Circuit := ⟨first, tap⟩
  let Q : PEqualNP.CircuitLowerBounds.Circuit := ⟨rest.map (ren shift) ++ B.gates.map (ren perm), perm B.output⟩
  have fp : PEqualNP.MetaComplexity.FanInTwo P := by
    intro g hg
    exact fanA g (parts ▸ List.mem_append_left rest hg)
  have fq : PEqualNP.MetaComplexity.FanInTwo Q := by
    intro g hg
    obtain left | right := List.mem_append.mp hg
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp left
      have h := fanA a (parts ▸ List.mem_append_right first ha)
      exact ⟨h.1, by simpa [ren] using h.2⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp right
      have h := fanB a ha
      exact ⟨h.1, by simpa [ren] using h.2⟩
  have total : P.size + Q.size = A.size + B.size := by
    change first.length + (rest.map (ren shift) ++ B.gates.map (ren perm)).length = A.gates.length + B.gates.length
    simp only [List.length_append, List.length_map]
    have h := congrArg List.length parts
    rw [List.length_append] at h
    omega
  have value : ∀ x : Fin 8 → Bool,
      PEqualNP.MetaComplexity.circuitFun 8 P x = (A.wires (List.ofFn x)).getD tap false := by
    intro x
    let u := run first (List.ofFn x)
    have hu : u.length = d := by simp [u, runLength, d]
    obtain ⟨z, old, _⟩ := growth rest u
    change u.getD tap false = (run A.gates (List.ofFn x)).getD tap false
    rw [← parts, runAppend]
    change _ = (run rest u).getD tap false
    rw [old, List.getD_append _ _ false tap (by omega)]
  have transport : ∀ (x : Fin 8 → Bool) (b : Bool),
      Q.eval (P.wires (List.ofFn x) ++ [b]) = B.eval (A.wires (List.ofFn x) ++ [b]) := by
    intro x b
    let u := run first (List.ofFn x)
    have hu : u.length = d := by simp [u, runLength, d]
    have inserted : ∀ (z : List Bool) (i : ℕ),
        ((u ++ [b]) ++ z).getD (shift i) false = (u ++ z).getD i false := by
      intro z i
      by_cases h : i < d
      · have a : i < u.length := by omega
        simp only [shift, ite_eq_left h, List.append_assoc, List.getD_append _ _ false i a]
      · have a : u.length ≤ i := by omega
        have a' : (u ++ [b]).length ≤ i + 1 := by simp [hu]; omega
        simp only [shift, ite_eq_right h, List.getD_append_right _ _ false _ a',
          List.getD_append_right _ _ false _ a, List.length_append, List.length_singleton]
        congr 1
        omega
    obtain ⟨z, old, new, len⟩ := translate shift u (u ++ [b]) inserted rest
    have lengthSum : (u ++ z).length = m := by simp [hu, len, restLen]
    have between : ∀ i : ℕ,
        ((u ++ [b]) ++ z).getD (perm i) false = ((u ++ z) ++ [b]).getD i false := by
      intro i
      by_cases firstPart : i < d
      · have a : i < u.length := by omega
        simp only [perm, ite_eq_left firstPart, List.append_assoc, List.getD_append _ _ false i a]
      by_cases middle : i < m
      · have e : perm i = shift i := by simp [perm, shift, firstPart, middle]
        rw [e, inserted]
        exact (List.getD_append (u ++ z) [b] false i (by rw [lengthSum]; exact middle)).symm
      by_cases endAt : i = m
      · subst i
        have hd : d ≤ m := by omega
        have e : perm m = d := by simp [perm, Nat.not_lt.mpr hd]
        rw [e, List.getD_append (u ++ [b]) z false d (by simp [hu]),
          List.getD_append_right u [b] false d (by omega),
          List.getD_append_right (u ++ z) [b] false m (by omega), hu, lengthSum]
        simp
      · have e : perm i = i := by simp [perm, firstPart, middle, endAt]
        rw [e]
        have ln : ((u ++ [b]) ++ z).length ≤ i := by simp [hu, len]; omega
        have lo : ((u ++ z) ++ [b]).length ≤ i := by
          rw [List.length_append, lengthSum, List.length_singleton]
          omega
        rw [List.getD_eq_default _ _ ln, List.getD_eq_default _ _ lo]
    let u0 := (u ++ z) ++ [b]
    let v0 := (u ++ [b]) ++ z
    have sizes : v0.length = u0.length := by simp [u0, v0]
    have hu0 : u0.length = m + 1 := by
      change ((u ++ z) ++ [b]).length = _
      rw [List.length_append, lengthSum, List.length_singleton]
    have atBase : ∀ (w : List Bool) (i : ℕ), (v0 ++ w).getD (perm i) false = (u0 ++ w).getD i false := by
      intro w i
      by_cases inside : i < u0.length
      · have bound : perm i < v0.length := by
          change (if i < d then i else if i < m then i + 1 else if i = m then d else i) < _
          rw [sizes, hu0]
          split_ifs <;> omega
        rw [List.getD_append _ _ false _ bound, List.getD_append _ _ false _ inside]
        exact between i
      · have e : perm i = i := by
          have a : ¬ i < d := by omega
          have a' : ¬ i < m := by omega
          have ne : i ≠ m := by omega
          simp [perm, a, a', ne]
        rw [e, List.getD_append_right _ _ false _ (by omega), List.getD_append_right _ _ false _ (by omega), sizes]
    obtain ⟨w, oldB, newB, _⟩ := translate perm u0 v0 atBase B.gates
    change (run (rest.map (ren shift) ++ B.gates.map (ren perm)) ((run first (List.ofFn x)) ++ [b])).getD (perm B.output) false =
      (run B.gates ((run A.gates (List.ofFn x)) ++ [b])).getD B.output false
    rw [runAppend, ← parts, runAppend]
    change (run (B.gates.map (ren perm)) (run (rest.map (ren shift)) (u ++ [b]))).getD _ _ =
      (run B.gates ((run rest u) ++ [b])).getD _ _
    rw [new, old]
    change (run (B.gates.map (ren perm)) v0).getD _ _ = (run B.gates u0).getD _ _
    rw [newB, oldB]
    exact atBase w B.output
  have hPout : P.output + 1 = 8 + P.size := lastAt
  have hLe13 : P.size + Q.size ≤ 13 := by omega
  have hSwitchP : ∀ x : Fin 8 → Bool,
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)) = false →
      (x 0 || x 3) = true → PEqualNP.MetaComplexity.circuitFun 8 P x = !k := by
    intro x hf hx03
    rw [value x]
    exact switches x hf hx03
  have hEvalFP : ∀ x : Fin 8 → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 P x]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4)) := by
    intro x
    rw [value x, transport x]
    exact neutral x
  have hEvalHP : ∀ x : Fin 8 → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [k]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4) || x 0 || x 3) := by
    intro x
    exact (transport x k).trans (forced x)
  have hCount := saving P Q k fp fq hEvalHP
  let s := 8 + P.size
  have hPwires_len : ∀ x : Fin 8 → Bool, (P.wires (List.ofFn x)).length = s := by
    intro x
    change (run P.gates (List.ofFn x)).length = 8 + P.gates.length
    rw [runLength, List.length_ofFn]
  let xZero : Fin 8 → Bool := fun _ => false
  let xUnit0 : Fin 8 → Bool := fun i => i == 0
  have hQout : Q.output ≠ s := by
    intro heq
    have hconst : ∀ x : Fin 8 → Bool, Q.eval (P.wires (List.ofFn x) ++ [k]) = k := by
      intro x
      change (run Q.gates (P.wires (List.ofFn x) ++ [k])).getD Q.output false = k
      rw [heq, getD_run_lt Q.gates (P.wires (List.ofFn x) ++ [k]) s
        (by rw [List.length_append, hPwires_len x, List.length_singleton]; omega)]
      rw [List.getD_append_right _ _ false s (by rw [hPwires_len x])]
      rw [hPwires_len x, Nat.sub_self]
      rfl
    have h0 : k = false := by
      have e := hEvalHP xZero
      rw [hconst xZero] at e
      exact e
    have h1 : k = true := by
      have e := hEvalHP xUnit0
      rw [hconst xUnit0] at e
      exact e
    rw [h0] at h1
    cases h1
  let r := List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate =>
    (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s) Q.gates
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    have hno : ∀ g ∈ Q.gates,
        (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s = false := by
      intro g hg
      have h := List.countP_eq_zero.mp hr0 g hg
      cases hc : (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s with
      | false => rfl
      | true => exact False.elim (h hc)
    have hind : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool),
        (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) →
        (∀ g ∈ gs, (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s = false) →
        w1.length = w2.length →
        s < w1.length →
        (∀ i, i ≠ s → w1.getD i false = w2.getD i false) →
        ∀ i, i ≠ s → (run gs w1).getD i false = (run gs w2).getD i false := by
      intro gs
      induction gs with
      | nil => intro w1 w2 _ _ _ _ hag i hi; exact hag i hi
      | cons g gs ih =>
        intro w1 w2 hfan hnoread hlen hslt hag i hi
        change (run gs (step w1 g)).getD i false = (run gs (step w2 g)).getD i false
        have hg_op : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hfan g (by simp)
        have hgn : (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).contains s = false :=
          hnoread g (by simp)
        have hval : g.op.eval (g.inputs.map fun j => w1.getD j false) =
            g.op.eval (g.inputs.map fun j => w2.getD j false) := by
          rcases hg_op with hand | hor | hnot
          · rw [hand] at hgn ⊢
            have hns : g.inputs.contains s = false := hgn
            have hmap : (g.inputs.map fun j => w1.getD j false) = (g.inputs.map fun j => w2.getD j false) := by
              apply List.map_congr_left
              intro j hj
              apply hag j
              intro hjs
              rw [hjs] at hj
              have hmem : g.inputs.contains s = true := List.elem_eq_true_of_mem hj
              rw [hns] at hmem
              cases hmem
            rw [hmap]
          · rw [hor] at hgn ⊢
            have hns : g.inputs.contains s = false := hgn
            have hmap : (g.inputs.map fun j => w1.getD j false) = (g.inputs.map fun j => w2.getD j false) := by
              apply List.map_congr_left
              intro j hj
              apply hag j
              intro hjs
              rw [hjs] at hj
              have hmem : g.inputs.contains s = true := List.elem_eq_true_of_mem hj
              rw [hns] at hmem
              cases hmem
            rw [hmap]
          · rw [hnot] at hgn ⊢
            have hns : (g.inputs.take 1).contains s = false := hgn
            cases hin : g.inputs with
            | nil => rfl
            | cons a as =>
              rw [hin] at hns
              have ha_ne : a ≠ s := by
                intro has
                have hmem : [a].contains s = true := by simp [has]
                change [a].contains s = false at hns
                rw [hns] at hmem
                cases hmem
              change (!(w1.getD a false)) = (!(w2.getD a false))
              rw [hag a ha_ne]
        apply ih (step w1 g) (step w2 g)
          (fun g' hg' => hfan g' (by simp [hg']))
          (fun g' hg' => hnoread g' (by simp [hg']))
          (by simp [step, hlen])
          (by simp [step]; omega)
          _ i hi
        intro j hj
        by_cases hjl : j < w1.length
        · have hjl2 : j < w2.length := by omega
          dsimp only [step]
          rw [List.getD_append _ _ false j hjl, List.getD_append _ _ false j hjl2, hag j hj]
        · by_cases hje : j = w1.length
          · subst hje
            dsimp only [step]
            rw [List.getD_append_right _ _ false _ (le_refl _),
                List.getD_append_right _ _ false _ (by omega),
                Nat.sub_self, hlen, Nat.sub_self]
            exact congrArg (fun b => [b].getD 0 false) hval
          · dsimp only [step]
            rw [List.getD_eq_default _ false (by rw [List.length_append, List.length_singleton]; omega),
                List.getD_eq_default _ false (by rw [List.length_append, List.length_singleton]; omega)]
    have heqEval : Q.eval (P.wires (List.ofFn xUnit0) ++ [PEqualNP.MetaComplexity.circuitFun 8 P xUnit0]) =
        Q.eval (P.wires (List.ofFn xUnit0) ++ [k]) := by
      apply hind Q.gates
        (P.wires (List.ofFn xUnit0) ++ [PEqualNP.MetaComplexity.circuitFun 8 P xUnit0])
        (P.wires (List.ofFn xUnit0) ++ [k])
        (fun g hg => (fq g hg).1)
        hno
        (by simp)
        (by rw [List.length_append, hPwires_len xUnit0, List.length_singleton]; omega)
        _ Q.output hQout
      intro i hi
      by_cases hil : i < s
      · rw [List.getD_append _ _ false i (by rw [hPwires_len xUnit0]; exact hil),
            List.getD_append _ _ false i (by rw [hPwires_len xUnit0]; exact hil)]
      · have hgt : s + 1 ≤ i := by omega
        rw [List.getD_eq_default _ false (by rw [List.length_append, hPwires_len xUnit0, List.length_singleton]; omega),
            List.getD_eq_default _ false (by rw [List.length_append, hPwires_len xUnit0, List.length_singleton]; omega)]
    rw [hEvalFP xUnit0, hEvalHP xUnit0] at heqEval
    cases heqEval
  have hr_le3 : r ≤ 3 := by
    change 10 + r ≤ P.size + Q.size at hCount
    omega
  rcases hr : r with _ | _ | _ | _ | r'
  · exact hr_ne_zero hr
  · exact hR1 P Q k fp fq hPout hQout hr (by change 10 + r ≤ P.size + Q.size at hCount; omega) hLe13 hSwitchP hEvalFP hEvalHP
  · exact hR2 P Q k fp fq hPout hQout hr (by change 10 + r ≤ P.size + Q.size at hCount; omega) hLe13 hSwitchP hEvalFP hEvalHP
  · exact hR3 P Q k fp fq hPout hQout hr (by change 10 + r ≤ P.size + Q.size at hCount; omega) hSwitchP hEvalFP hEvalHP
  · omega
