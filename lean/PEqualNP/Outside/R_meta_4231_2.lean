import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4231_2
    (h1 :
      have x1 : List ℕ → ℕ → Fin (20 : ℕ) → Bool :=
        fun (x1 : List ℕ) (x2 : ℕ) (x3 : Fin (20 : ℕ)) =>
          (x1.getD (x2 / (3 : ℕ)) (0 : ℕ)).testBit ((20 : ℕ) * (x2 % (3 : ℕ)) + ↑x3)
      ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (4 : ℕ) ∧
        (∀ (x3 : Fin (4 : ℕ)),
          PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2
            (x1 [(882706627014164513 : ℕ), (72567803150337 : ℕ), (74801153180674 : ℕ),
                 (72062818869837956 : ℕ), (720866211591618600 : ℕ),
                 (720875007625924616 : ℕ), (8606712336 : ℕ)] ↑x3) = Bool.true) ∧
        ∀ (x3 : Fin (44 : ℕ)),
          PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2
            (x1 [(4665232155738143 : ℕ), (13518504604999695 : ℕ), (725368754528096277 : ℕ),
                 (730724029253162005 : ℕ), (866973350870287389 : ℕ),
                 (875963053248350355 : ℕ), (884986756446568478 : ℕ),
                 (903000063497490454 : ℕ), (954792603833647132 : ℕ),
                 (1012212425860929682 : ℕ), (1041183516279060867 : ℕ),
                 (1062218301194542225 : ℕ), (1078371242023506996 : ℕ),
                 (1142983005070916482 : ℕ), (1099479117384 : ℕ)] ↑x3) = Bool.false)
    (h2 :
      have x1 : List ℕ → ℕ → Fin (20 : ℕ) → Bool :=
        fun (x1 : List ℕ) (x2 : ℕ) (x3 : Fin (20 : ℕ)) =>
          (x1.getD (x2 / (3 : ℕ)) (0 : ℕ)).testBit ((20 : ℕ) * (x2 % (3 : ℕ)) + ↑x3)
      ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (18 : ℕ) ∧
        (∀ (x3 : Fin (16 : ℕ)),
          PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2
            (x1 [(882706627014164513 : ℕ), (72567803150337 : ℕ), (74801153180674 : ℕ),
                 (72062818869837956 : ℕ), (720866211591618600 : ℕ),
                 (720875007625924616 : ℕ), (8606712336 : ℕ)] (↑x3 + (4 : ℕ))) = Bool.true) ∧
        ∀ (x3 : Fin (44 : ℕ)),
          PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2
            (x1 [(4665232155738143 : ℕ), (13518504604999695 : ℕ), (725368754528096277 : ℕ),
                 (730724029253162005 : ℕ), (866973350870287389 : ℕ),
                 (875963053248350355 : ℕ), (884986756446568478 : ℕ),
                 (903000063497490454 : ℕ), (954792603833647132 : ℕ),
                 (1012212425860929682 : ℕ), (1041183516279060867 : ℕ),
                 (1062218301194542225 : ℕ), (1078371242023506996 : ℕ),
                 (1142983005070916482 : ℕ), (1099479117384 : ℕ)] ↑x3) = Bool.false) :
    have x1 : List ℕ → ℕ → Fin (20 : ℕ) → Bool := fun (x1 : List ℕ) (x2 : ℕ) (x3 : Fin (20 : ℕ)) => (x1.getD (x2 / (3 : ℕ)) (0 : ℕ)).testBit ((20 : ℕ) * (x2 % (3 : ℕ)) + ↑x3); ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (23 : ℕ) ∧ (∀ (x3 : Fin (20 : ℕ)), PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2 (x1 [(882706627014164513 : ℕ), (72567803150337 : ℕ), (74801153180674 : ℕ), (72062818869837956 : ℕ), (720866211591618600 : ℕ), (720875007625924616 : ℕ), (8606712336 : ℕ)] ↑x3) = Bool.true) ∧ ∀ (x3 : Fin (44 : ℕ)), PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2 (x1 [(4665232155738143 : ℕ), (13518504604999695 : ℕ), (725368754528096277 : ℕ), (730724029253162005 : ℕ), (866973350870287389 : ℕ), (875963053248350355 : ℕ), (884986756446568478 : ℕ), (903000063497490454 : ℕ), (954792603833647132 : ℕ), (1012212425860929682 : ℕ), (1041183516279060867 : ℕ), (1062218301194542225 : ℕ), (1078371242023506996 : ℕ), (1142983005070916482 : ℕ), (1099479117384 : ℕ)] ↑x3) = Bool.false := by
  obtain ⟨C1, hC1m, hC1s, hC1p, hC1n⟩ := h1
  obtain ⟨C2, hC2m, hC2s, hC2p, hC2n⟩ := h2
  let k : ℕ := C1.gates.length
  let shift : ℕ → ℕ := fun w => if w < 20 then w else w + k
  let shiftGate : Gate → Gate := fun g => { op := g.op, inputs := g.inputs.map shift }
  let out1 : ℕ := if C1.output < 20 + k then C1.output else 20 + k + C2.gates.length
  let out2 : ℕ := if C2.output < 20 + C2.gates.length then shift C2.output else 20 + k + C2.gates.length
  let C : Circuit :=
    { gates := C1.gates ++ C2.gates.map shiftGate ++ [{ op := GateOp.or, inputs := [out1, out2] }]
      output := 20 + k + C2.gates.length }
  have hgetD_left : ∀ (u v : List Bool) (i : ℕ), i < u.length →
      (u ++ v).getD i false = u.getD i false := by
    intro u v i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hgetD_right : ∀ (u v : List Bool) (i : ℕ), u.length ≤ i →
      (u ++ v).getD i false = v.getD (i - u.length) false := by
    intro u v i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]
  have hgetD_ge : ∀ (u : List Bool) (i : ℕ), u.length ≤ i → u.getD i false = false := by
    intro u i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    rfl
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hstep_ext : ∀ (gs : List Gate) (w : List Bool),
      ∃ ext : List Bool, ext.length = gs.length ∧ gs.foldl step w = w ++ ext := by
    intro gs
    induction gs with
    | nil =>
      intro w
      exact ⟨[], rfl, by simp⟩
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons]
      obtain ⟨ext, hext_len, hext⟩ := ih (step w g)
      refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ ext, ?_, ?_⟩
      · simp [hext_len]
      · rw [hext]; dsimp only [step]; rw [List.append_assoc]
  have hgetD_shift : ∀ (x mid tail : List Bool) (i : ℕ),
      x.length = 20 → mid.length = k →
      (x ++ mid ++ tail).getD (shift i) false = (x ++ tail).getD i false := by
    intro x mid tail i hx hmid
    by_cases hi : i < 20
    · have hs : shift i = i := by simp only [shift, hi, ↓reduceIte]
      rw [hs, List.append_assoc, hgetD_left x (mid ++ tail) i (by omega),
          hgetD_left x tail i (by omega)]
    · have hs : shift i = i + k := by simp only [shift, hi, ↓reduceIte]
      rw [hs, hgetD_right (x ++ mid) tail (i + k) (by rw [List.length_append]; omega),
          hgetD_right x tail i (by omega)]
      have hsub : i + k - (x ++ mid).length = i - x.length := by
        rw [List.length_append]; omega
      rw [hsub]
  have hstep_shift : ∀ (x mid : List Bool), x.length = 20 → mid.length = k →
      ∀ (gs : List Gate) (tail : List Bool),
        ∃ tail' : List Bool,
          tail'.length = tail.length + gs.length ∧
          gs.foldl step (x ++ tail) = x ++ tail' ∧
          (gs.map shiftGate).foldl step (x ++ mid ++ tail) = x ++ mid ++ tail' := by
    intro x mid hx hmid gs
    induction gs with
    | nil =>
      intro tail
      exact ⟨tail, by simp, rfl, rfl⟩
    | cons g gs ih =>
      intro tail
      simp only [List.map_cons, List.foldl_cons]
      have hmap : ((shiftGate g).inputs.map fun i => (x ++ mid ++ tail).getD i false) =
          g.inputs.map (fun i => (x ++ tail).getD i false) := by
        dsimp only [shiftGate]
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hgetD_shift x mid tail i hx hmid
      let b : Bool := g.op.eval (g.inputs.map fun i => (x ++ tail).getD i false)
      have hs1 : step (x ++ tail) g = x ++ (tail ++ [b]) := by
        dsimp only [step, b]; rw [List.append_assoc]
      have hs2 : step (x ++ mid ++ tail) (shiftGate g) = x ++ mid ++ (tail ++ [b]) := by
        dsimp only [step, b]; rw [hmap, List.append_assoc]
      rw [hs1, hs2]
      obtain ⟨tail', hlen, h1', h2'⟩ := ih (tail ++ [b])
      refine ⟨tail', ?_, h1', h2'⟩
      rw [hlen, List.length_append, List.length_singleton, List.length_cons]
      omega
  have hor_eval : ∀ (a b : Bool), GateOp.or.eval [a, b] = (a || b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have hCeval : ∀ (v : Fin 20 → Bool),
      circuitFun 20 C v = (circuitFun 20 C1 v || circuitFun 20 C2 v) := by
    intro v
    change (C.gates.foldl step (List.ofFn v)).getD C.output false =
      ((C1.gates.foldl step (List.ofFn v)).getD C1.output false ||
       (C2.gates.foldl step (List.ofFn v)).getD C2.output false)
    let x : List Bool := List.ofFn v
    have hx : x.length = 20 := List.length_ofFn
    obtain ⟨mid, hmid_len, hC1w⟩ := hstep_ext C1.gates x
    obtain ⟨tail', htail'_len, hC2w, hC2w_shift⟩ := hstep_shift x mid hx hmid_len C2.gates []
    have hC2w' : C2.gates.foldl step x = x ++ tail' := by
      simpa only [List.append_nil] using hC2w
    have hC2w_shift' : (C2.gates.map shiftGate).foldl step (x ++ mid) = x ++ mid ++ tail' := by
      simpa only [List.append_nil] using hC2w_shift
    have hfold : C.gates.foldl step x =
        step (x ++ mid ++ tail') { op := GateOp.or, inputs := [out1, out2] } := by
      dsimp only [C]
      rw [List.foldl_append, List.foldl_append, hC1w, hC2w_shift']
      rfl
    have htail_len : tail'.length = C2.gates.length := by
      rw [htail'_len, List.length_nil, Nat.zero_add]
    have hw_len : (x ++ mid ++ tail').length = 20 + k + C2.gates.length := by
      rw [List.length_append, List.length_append, hx, hmid_len, htail_len]
    rw [hfold, hC1w, hC2w']
    dsimp only [step, C]
    rw [hgetD_right (x ++ mid ++ tail') _ (20 + k + C2.gates.length) (by omega)]
    have hzero : 20 + k + C2.gates.length - (x ++ mid ++ tail').length = 0 := by omega
    rw [hzero]
    change GateOp.or.eval [(x ++ mid ++ tail').getD out1 false, (x ++ mid ++ tail').getD out2 false] = _
    rw [hor_eval]
    have ho1 : (x ++ mid ++ tail').getD out1 false = (x ++ mid).getD C1.output false := by
      by_cases hlt : C1.output < 20 + k
      · have heq : out1 = C1.output := by simp only [out1, hlt, ↓reduceIte]
        rw [heq, hgetD_left (x ++ mid) tail' C1.output (by rw [List.length_append]; omega)]
      · have heq : out1 = 20 + k + C2.gates.length := by simp only [out1, hlt, ↓reduceIte]
        rw [heq, hgetD_ge (x ++ mid ++ tail') _ (by omega),
            hgetD_ge (x ++ mid) C1.output (by rw [List.length_append]; omega)]
    have ho2 : (x ++ mid ++ tail').getD out2 false = (x ++ tail').getD C2.output false := by
      by_cases hlt : C2.output < 20 + C2.gates.length
      · have heq : out2 = shift C2.output := by simp only [out2, hlt, ↓reduceIte]
        rw [heq, hgetD_shift x mid tail' C2.output hx hmid_len]
      · have heq : out2 = 20 + k + C2.gates.length := by simp only [out2, hlt, ↓reduceIte]
        rw [heq, hgetD_ge (x ++ mid ++ tail') _ (by omega),
            hgetD_ge (x ++ tail') C2.output (by rw [List.length_append]; omega)]
    rw [ho1, ho2]
  have hCm : Monotone2 C := by
    intro g hg
    dsimp only [C] at hg
    rw [List.mem_append, List.mem_append] at hg
    rcases hg with (hg1 | hg2) | hg3
    · exact hC1m g hg1
    · rw [List.mem_map] at hg2
      obtain ⟨g0, hg0, rfl⟩ := hg2
      have h0 := hC2m g0 hg0
      exact ⟨h0.1, by dsimp only [shiftGate]; rw [List.length_map]; exact h0.2⟩
    · rw [List.mem_singleton] at hg3
      subst hg3
      exact ⟨Or.inr rfl, Nat.le_refl 2⟩
  have hCs : C.size ≤ 23 := by
    change C.gates.length ≤ 23
    change C1.gates.length ≤ 4 at hC1s
    change C2.gates.length ≤ 18 at hC2s
    dsimp only [C]
    rw [List.length_append, List.length_append, List.length_map, List.length_singleton]
    omega
  refine ⟨C, hCm, hCs, ?_, ?_⟩
  · intro i
    rw [hCeval]
    by_cases hi : i.val < 4
    · have hp1 := hC1p ⟨i.val, hi⟩
      rw [hp1]
      rfl
    · have hsub : i.val - 4 < 16 := by omega
      have hp2 := hC2p ⟨i.val - 4, hsub⟩
      have heq : i.val - 4 + 4 = i.val := by omega
      rw [heq] at hp2
      rw [hp2, Bool.or_true]
  · intro j
    rw [hCeval, hC1n j, hC2n j]
    rfl
