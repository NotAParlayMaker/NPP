import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3304_741
    (lower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 8 → Bool, ∀ y : Bool, C.eval (y :: List.ofFn x) =
        ((x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
          x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) ||
          (y && (x 0 || x 3)))) → 13 + PEqualNP.NotBracket.notCount C ≤ C.size)
    (normalized :
      have F : (Fin 8 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
      ∀ (P S : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ),
        PEqualNP.MetaComplexity.FanInTwo P → PEqualNP.MetaComplexity.FanInTwo S →
        5 ≤ P.size → P.size + S.size = 13 → 8 ≤ j → j < 8 + P.size →
        PEqualNP.NotBracket.notCount P = 0 → PEqualNP.NotBracket.notCount S = 1 →
        have w : (Fin 8 → Bool) → List Bool := fun x => P.wires (List.ofFn x)
        have z : (Fin 8 → Bool) → Bool := fun x => (w x).getD j false
        (∀ x, F x = false → (x 0 || x 3) = true → z x = true) →
        (∀ x, S.eval (w x ++ [z x]) = F x) →
        ∃ x, S.eval (w x ++ [false]) ≠ (F x || x 0 || x 3)) :
have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       (5 : ℕ) ≤ x2.size →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ)))
 := by
  classical
  dsimp only at normalized ⊢
  intro P S j hP hS hPmin hsize hjlo hjhi htrigger hbase
  by_contra! hcut
  let F : (Fin 8 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
      x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  let f (i : ℕ) : ℕ := if i < 8 then i + 1 else i + 2
  let G := PEqualNP.CircuitLowerBounds.Gate
  let step (w : List Bool) (g : G) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let remap (g : G) : G := ⟨g.op, g.inputs.map f⟩
  let nc := PEqualNP.NotBracket.notCount
  let p := fun g : G => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op .not)
  have append_match (a b : List Bool) (hl : 8 ≤ a.length) (he : b.length = a.length + 2)
      (hm : ∀ i, b.getD (f i) false = a.getD i false) (v : Bool) :
      ∀ i, (b ++ [v]).getD (f i) false = (a ++ [v]).getD i false := by
    intro i
    simp only [List.getD_eq_getElem?_getD]
    by_cases hi : i < a.length
    · have hi' : f i < b.length := by dsimp [f]; split <;> omega
      rw [List.getElem?_append_left hi', List.getElem?_append_left hi]
      simpa only [List.getD_eq_getElem?_getD] using hm i
    · have hf : f i = i + 2 := ite_eq_right (by omega)
      rw [List.getElem?_append_right (show b.length ≤ f i by omega),
        List.getElem?_append_right (by omega)]
      rw [show f i - b.length = i - a.length by omega]
  have simulate (gs : List G) (a b : List Bool) (hl : 8 ≤ a.length)
      (he : b.length = a.length + 2) (hm : ∀ i, b.getD (f i) false = a.getD i false) :
      (List.foldl step b (gs.map remap)).length = (List.foldl step a gs).length + 2 ∧
      8 ≤ (List.foldl step a gs).length ∧
      ∀ i, (List.foldl step b (gs.map remap)).getD (f i) false =
        (List.foldl step a gs).getD i false := by
    induction gs generalizing a b with
    | nil => exact ⟨he, hl, hm⟩
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hv : (remap g).op.eval ((remap g).inputs.map fun i => b.getD i false) =
          g.op.eval (g.inputs.map fun i => a.getD i false) := by
        simp only [remap, List.map_map, Function.comp_def, hm]
      apply ih
      · simp [step]; omega
      · simp [step]; omega
      · simpa only [step, hv] using append_match a b hl he hm
          (g.op.eval (g.inputs.map fun i => a.getD i false))
  let lift : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.not,[0]⟩] ++ P.gates.map remap ++ [⟨.and,[f j,9]⟩] ++ S.gates.map remap,
      f S.output⟩
  have hfan : PEqualNP.MetaComplexity.FanInTwo lift := by
    intro g hg
    simp only [lift, List.mem_append, List.mem_singleton, List.mem_map] at hg
    rcases hg with ((rfl | ⟨g', hg', rfl⟩) | rfl) | ⟨g', hg', rfl⟩
    · simp
    · simpa [remap] using hP g' hg'
    · simp
    · simpa [remap] using hS g' hg'
  have hcompute : ∀ (x : Fin 8 → Bool) (y : Bool),
      lift.eval (y :: List.ofFn x) = (F x || (y && (x 0 || x 3))) := by
    intro x y
    let a := List.ofFn x
    let b := y :: (a ++ [!y])
    have ha : a.length = 8 := by simp [a]
    have hb : b.length = a.length + 2 := by simp [b]
    have hmatch : ∀ i, b.getD (f i) false = a.getD i false := by
      intro i
      by_cases hi : i < 8
      · simp only [f, ite_eq_left hi, b, List.getD_cons_succ]
        rw [List.getD_append _ _ _ _ (by omega)]
      · have hn : f i ≥ b.length := by simp [f, hi, hb, ha]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hn,
          List.getElem?_eq_none (show a.length ≤ i by omega)]
    obtain ⟨hlen, hlong, hsim⟩ := simulate P.gates a b (by omega) hb hmatch
    let A := List.foldl step a P.gates
    let B := List.foldl step b (P.gates.map remap)
    let z := A.getD j false
    have hprefix : ∀ (gs : List G) (w : List Bool) (i : ℕ), i < w.length →
        (List.foldl step w gs).getD i false = w.getD i false := by
      intro gs
      induction gs with
      | nil => simp
      | cons g gs ih =>
        intro w i hi
        simp only [List.foldl_cons]
        rw [ih _ _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    have hneg : B.getD 9 false = !y := by
      change (List.foldl step b (P.gates.map remap)).getD 9 false = _
      rw [hprefix _ _ _ (by omega)]
      change (y :: (a ++ [!y])).getD (8 + 1) false = _
      rw [List.getD_cons_succ, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), ha]
      rfl
    have hy : step (y :: a) ⟨.not,[0]⟩ = b := by rfl
    have hz : step B ⟨.and,[f j,9]⟩ = B ++ [z && !y] := by
      simp only [step, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, id_eq, Bool.and_true, hneg, show B.getD (f j) false = z from hsim j]
    have hout : lift.eval (y :: a) = S.eval (A ++ [z && !y]) := by
      change (List.foldl step (y :: a) lift.gates).getD (f S.output) false = _
      simp only [lift, List.foldl_append, List.foldl_cons, List.foldl_nil, hy]
      change (List.foldl step (step B ⟨.and,[f j,9]⟩) (S.gates.map remap)).getD (f S.output) false = _
      rw [hz]
      exact (simulate S.gates (A ++ [z && !y]) (B ++ [z && !y])
        (by change 8 ≤ A.length at hlong; simp; omega)
        (by change B.length = A.length + 2 at hlen; simp; omega)
        (append_match A B hlong hlen hsim _)).2.2 S.output
    have hbase' : S.eval (A ++ [z]) = F x := hbase x
    have hcut' : S.eval (A ++ [false]) = (F x || x 0 || x 3) := hcut x
    cases y with
    | false =>
      rw [Bool.not_false, Bool.and_true] at hout
      simpa only [Bool.false_and, Bool.or_false] using hout.trans hbase'
    | true =>
      rw [Bool.not_true, Bool.and_false] at hout
      simpa only [Bool.true_and, Bool.or_assoc] using hout.trans hcut'
  have hll : 13 + nc lift ≤ lift.size := lower lift hfan hcompute
  have hcount : nc lift = nc P + nc S + 1 := by
    have hmap (gs : List G) : ((gs.map remap).filter p).length = (gs.filter p).length := by
      rw [List.filter_map, List.length_map]
      rfl
    change (lift.gates.filter p).length = (P.gates.filter p).length + (S.gates.filter p).length + 1
    simp only [lift, List.filter_append, List.length_append, hmap]
    change 1 + (P.gates.filter p).length + 0 + (S.gates.filter p).length = _
    omega
  have hlength : lift.size = P.size + S.size + 2 := by
    simp [lift, PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  have hsn : 1 ≤ nc S := by
    by_contra! h0
    have hn : nc S = 0 := by omega
    have noNot : ∀ g ∈ S.gates, g.op ≠ .not := by
      intro g hg hnot
      have hm : g ∈ S.gates.filter p := List.mem_filter.mpr ⟨hg, by simp [p, hnot]⟩
      change (S.gates.filter p).length = 0 at hn
      rw [List.length_eq_zero_iff.mp hn] at hm
      exact List.not_mem_nil hm
    have step_le (gs : List G) (p q : List Bool) (hpq : p.length = q.length)
        (hle : ∀ i, p.getD i false ≤ q.getD i false)
        (fan : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
        ∀ i, (List.foldl step p gs).getD i false ≤ (List.foldl step q gs).getD i false := by
      induction gs generalizing p q with
      | nil => exact hle
      | cons g gs ih =>
        have hvals : g.op.eval (g.inputs.map fun i => p.getD i false) ≤
            g.op.eval (g.inputs.map fun i => q.getD i false) := by
          rcases fan g (by simp) with he | he
          · rw [he]; simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.le_iff_imp,
              List.all_eq_true, List.mem_map, id_eq]
            intro h i hi
            obtain ⟨k, hk, rfl⟩ := hi
            exact Bool.le_iff_imp.mp (hle k) (h _ ⟨k, hk, rfl⟩)
          · rw [he]; simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.le_iff_imp,
              List.any_eq_true, List.mem_map, id_eq]
            rintro ⟨_, ⟨k, hk, rfl⟩, h⟩
            exact ⟨_, ⟨k, hk, rfl⟩, Bool.le_iff_imp.mp (hle k) h⟩
        simp only [List.foldl_cons]
        apply ih
        · simp [step, hpq]
        · intro i
          simp only [step, List.getD_eq_getElem?_getD]
          by_cases hi : i < p.length
          · rw [List.getElem?_append_left hi, List.getElem?_append_left (by omega)]
            exact hle i
          · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hpq]
            cases i - q.length with
            | zero => simpa using hvals
            | succ _ => simp
        · intro g hg
          exact fan g (by simp [hg])
    let x : Fin 8 → Bool := fun i => decide (i = 0)
    have hx : F x = false := by decide
    let w := P.wires (List.ofFn x)
    let z := w.getD j false
    have hcompare : S.eval (w ++ [false]) ≤ S.eval (w ++ [z]) := by
      apply step_le S.gates (w ++ [false]) (w ++ [z]) (by simp)
      · intro i
        simp only [List.getD_eq_getElem?_getD]
        by_cases hi : i < w.length
        · rw [List.getElem?_append_left hi, List.getElem?_append_left hi]
        · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
          cases i - w.length <;> simp
      · intro g hg
        simpa [noNot g hg] using (hS g hg).1
    have hb := hbase x
    have hc := hcut x
    change S.eval (w ++ [z]) = F x at hb
    change S.eval (w ++ [false]) = (F x || x 0 || x 3) at hc
    have hfalse : ¬ (true ≤ false) := by decide
    exact hfalse (by simpa [hb, hc, hx, x] using hcompare)
  have hs1 : nc S = 1 := by omega
  have hp0 : nc P = 0 := by omega
  have hs : P.size + S.size = 13 := by omega
  obtain ⟨x, hx⟩ := normalized P S j hP hS hPmin hs hjlo hjhi hp0 hs1 htrigger hbase
  exact hx (hcut x)
