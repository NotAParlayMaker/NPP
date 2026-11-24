import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3252_1
    (exactCase : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      C.output < N + N + C.size →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D →
        PEqualNP.MetaComplexity.circuitFun (N + N) D = PEqualNP.MetaComplexity.circuitFun (N + N) C →
        C.size ≤ D.size) →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      N * q ≤ 100 * C.size)
    (errorCase : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      C.output < N + N + C.size →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D →
        PEqualNP.MetaComplexity.circuitFun (N + N) D = PEqualNP.MetaComplexity.circuitFun (N + N) C →
        C.size ≤ D.size) →
      (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      ∀ z : Fin (N + N) → Bool,
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = true →
        q < Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} →
        (∀ i : Fin (N + N), z i = true →
          PEqualNP.MetaComplexity.circuitFun (N + N) C (Function.update z i false) = false) →
        N * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x19 x21 (x12 + x20) ∧ x23 ∈ x19 x21 (x12 + x20) ∧ ¬∃ x24 < x12 + x20, ∃ x25 < x12 + x20, x19 x21 (x12 + x20) = x19 x21 x24 ∪ x19 x21 x25) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I decI hq hN hdeg huniq s o W
  dsimp only
  intro ho hraw hsteps hpos hneg _haxis
  let m : ℕ := N + N
  let one (a b : Fin N) : Bool := decide (b = a)
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have step_len (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) :
      (gs.foldl step x).length = x.length + gs.length := by
    induction gs generalizing x with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have step_keeps (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ)
      (hi : i < x.length) : (gs.foldl step x).getD i false = x.getD i false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step x g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have step_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ)
      (hj : j < gs.length) (hback : ∀ i ∈ gs[j].inputs, i < x.length + j) :
      (gs.foldl step x).getD (x.length + j) false =
        gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl step x).getD i false) := by
    induction gs generalizing x j with
    | nil => simp at hj
    | cons g gs ih =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero] at hback ⊢
        rw [List.foldl_cons, step_keeps _ _ _ (by simp [step]),
          List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
        change g.op.eval (g.inputs.map fun i => x.getD i false) = _
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ((step_keeps gs (step x g) i (by simp [step]; have := hback i hi; omega)).trans
          (List.getD_append _ _ _ _ (hback i hi))).symm
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have len : (step x g).length + j = x.length + (j + 1) := by simp [step]; omega
        have hback' : ∀ i ∈ gs[j].inputs, i < (step x g).length + j := by
          simpa only [List.getElem_cons_succ, len] using hback
        rw [List.foldl_cons, ← len]
        exact ih (step x g) j hj' hback'
  have step_mono (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (hao : ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (x y : List Bool) (hlen : x.length = y.length)
      (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
      ∀ i, (gs.foldl step x).getD i false = true → (gs.foldl step y).getD i false = true := by
    induction gs generalizing x y with
    | nil => exact hle
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun h hh => hao h (List.mem_cons_of_mem _ hh)) (step x g) (step y g)
        (by simp [step, hlen])
      intro i hi
      by_cases hix : i < x.length
      · rw [List.getD_append _ _ _ _ hix] at hi
        rw [List.getD_append _ _ _ _ (hlen ▸ hix)]
        exact hle i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
        cases ho : i - x.length with
        | zero =>
          have htop : g.op.eval (g.inputs.map fun k => x.getD k false) = true := by
            simpa [ho] using hi
          have htop' : g.op.eval (g.inputs.map fun k => y.getD k false) = true := by
            rcases hao g List.mem_cons_self with hop | hop
            · rw [hop] at htop ⊢
              change (g.inputs.map fun k => x.getD k false).all id = true at htop
              change (g.inputs.map fun k => y.getD k false).all id = true
              simp only [List.all_eq_true, List.mem_map, id_eq] at htop ⊢
              rintro _ ⟨k, hk, rfl⟩
              exact hle k (htop _ ⟨k, hk, rfl⟩)
            · rw [hop] at htop ⊢
              change (g.inputs.map fun k => x.getD k false).any id = true at htop
              change (g.inputs.map fun k => y.getD k false).any id = true
              simp only [List.any_eq_true, List.mem_map, id_eq] at htop ⊢
              obtain ⟨_, ⟨k, hk, rfl⟩, hk'⟩ := htop
              exact ⟨y.getD k false, ⟨k, hk, rfl⟩, hle k hk'⟩
          simpa [ho] using htop'
        | succ k => simp [ho] at hi
  have hNbig : 100 < N := by
    have hsq : 100 * 100 ≤ q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have rawShape (w : ℕ) (hw : w < m) :
      (∃ p : Fin N, W w = {z | z.1 p = true}) ∨
      (∃ l : Fin N, W w = {z | z.2 l = true}) := by
    by_cases hp : w < N
    · exact Or.inl ⟨⟨w, hp⟩, (hraw ⟨w, hp⟩).1⟩
    · let l : Fin N := ⟨w - N, by dsimp [m] at hw; omega⟩
      have hid : N + l.val = w := by dsimp [l]; omega
      exact Or.inr ⟨l, hid ▸ (hraw l).2⟩
  have hW_mono (w : ℕ) (hw : w < m + s) :
      ∀ x y : (Fin N → Bool) × (Fin N → Bool),
        (∀ p, x.1 p = true → y.1 p = true) → (∀ l, x.2 l = true → y.2 l = true) →
        x ∈ W w → y ∈ W w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x y h1 h2 hx
      by_cases hlt : w < m
      · rcases rawShape w hlt with ⟨p, hp⟩ | ⟨l, hl⟩
        · rw [hp] at hx ⊢
          exact h1 p hx
        · rw [hl] at hx ⊢
          exact h2 l hx
      · have hi : w - m < s := by omega
        have heq : m + (w - m) = w := by omega
        obtain ⟨a, b, hab, hmem⟩ := hsteps (w - m) hi
        have ha : a < w := by have := (max_lt_iff.mp hab).1; omega
        have hb : b < w := by have := (max_lt_iff.mp hab).2; omega
        rw [heq] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h | h
        · rw [h] at hx ⊢
          exact hx.imp (ih a ha (by omega) x y h1 h2) (ih b hb (by omega) x y h1 h2)
        · rw [h] at hx ⊢
          exact ih a ha (by omega) x y h1 h2 hx
        · rw [h] at hx
          exact hx.elim
        · rw [h] at hx ⊢
          exact ⟨ih a ha (by omega) x y h1 h2 hx.1, ih b hb (by omega) x y h1 h2 hx.2⟩
  have append_getD (P L : Fin N → Bool) (w : ℕ) (hw : w < m) :
      (List.ofFn (Fin.append P L)).getD w false =
        if h : w < N then P ⟨w, h⟩ else L ⟨w - N, by dsimp [m] at hw; omega⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa [m] using hw), List.getElem_ofFn]
    by_cases h : w < N
    · rw [dite_eq_left h]
      have heq : (⟨w, hw⟩ : Fin (N + N)) = Fin.castAdd N ⟨w, h⟩ := Fin.ext rfl
      rw [heq, Fin.append_left]
    · rw [dite_eq_right h]
      have heq : (⟨w, hw⟩ : Fin (N + N)) = Fin.natAdd N ⟨w - N, by dsimp [m] at hw; omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
      rw [heq, Fin.append_right]
  let WireSpec (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : ℕ) (opt : Option ℕ) : Prop :=
    (opt = none → W w = ∅) ∧
    (∀ u : ℕ, opt = some u → u < m + gs.length ∧
      ∀ P L : Fin N → Bool, (P, L) ∈ W w ↔
        (gs.foldl step (List.ofFn (Fin.append P L))).getD u false = true)
  have hdecompile (k : ℕ) (hk : k ≤ s) :
      ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (f : ℕ → Option ℕ),
        gs.length ≤ k ∧
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (∀ j < gs.length, ∀ u ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
          u < m + j) ∧
        (∀ g ∈ gs, g.inputs.length = 2) ∧
        (∀ w < m + k, WireSpec gs w (f w)) := by
    induction k with
    | zero =>
      refine ⟨[], fun w => some w, le_rfl, by simp, by simp, by simp, ?_⟩
      intro w hw
      have hwm : w < m := by omega
      refine ⟨fun h => (by cases h), ?_⟩
      intro u hu
      have hueq : u = w := (Option.some.inj hu).symm
      subst hueq
      refine ⟨by simpa using hwm, ?_⟩
      intro P L
      simp only [List.foldl_nil, append_getD P L u hwm]
      by_cases hp : u < N
      · rw [dite_eq_left hp, (hraw ⟨u, hp⟩).1]
        rfl
      · rw [dite_eq_right hp]
        let l : Fin N := ⟨u - N, by dsimp [m] at hwm; omega⟩
        have hid : N + l.val = u := by dsimp [l]; omega
        have hwraw : W u = {z | z.2 l = true} := hid ▸ (hraw l).2
        rw [hwraw]
        rfl
    | succ k ih =>
      obtain ⟨gs, f, hlen, hao, hback, htwo, hspec⟩ := ih (by omega)
      obtain ⟨a, b, hab, hmem⟩ := hsteps k (by omega)
      have ha : a < m + k := (max_lt_iff.mp hab).1
      have hb : b < m + k := (max_lt_iff.mp hab).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have addGate (op : PEqualNP.CircuitLowerBounds.GateOp)
          (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            op = PEqualNP.CircuitLowerBounds.GateOp.or)
          (u v : ℕ) (hu : u < m + gs.length) (hv : v < m + gs.length)
          (hval : ∀ P L : Fin N → Bool, (P, L) ∈ W (m + k) ↔
            op.eval [(gs.foldl step (List.ofFn (Fin.append P L))).getD u false,
              (gs.foldl step (List.ofFn (Fin.append P L))).getD v false] = true) :
          ∃ (gs' : List PEqualNP.CircuitLowerBounds.Gate) (f' : ℕ → Option ℕ),
            gs'.length ≤ k + 1 ∧
            (∀ g ∈ gs', g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
              g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            (∀ j < gs'.length, ∀ t ∈ (gs'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
              t < m + j) ∧
            (∀ g ∈ gs', g.inputs.length = 2) ∧
            (∀ w < m + (k + 1), WireSpec gs' w (f' w)) := by
        let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨op, [u, v]⟩
        let gs' := gs ++ [g0]
        let f' (w : ℕ) : Option ℕ := if w = m + k then some (m + gs.length) else f w
        refine ⟨gs', f', by simp [gs']; omega, ?_, ?_, ?_, ?_⟩
        · intro g hg
          simp only [gs', List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · exact hao g hg
          · exact hop
        · intro j hj t ht
          by_cases hjlt : j < gs.length
          · rw [show gs'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
              gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ from
              List.getD_append _ _ _ _ hjlt] at ht
            exact hback j hjlt t ht
          · have hjeq : j = gs.length := by simp [gs'] at hj; omega
            subst hjeq
            have hget : gs'.getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g0 := by
              simp [gs']
            rw [hget] at ht
            simp only [g0, List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl
            · exact hu
            · exact hv
        · intro g hg
          simp only [gs', List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · exact htwo g hg
          · rfl
        · intro w hw
          by_cases hwk : w = m + k
          · subst hwk
            refine ⟨fun h => (by simp [f'] at h), ?_⟩
            intro t ht
            have hteq : t = m + gs.length := (Option.some.inj (by simpa [f'] using ht)).symm
            subst hteq
            refine ⟨by simp [gs'], ?_⟩
            intro P L
            rw [hval P L]
            have hfold : gs'.foldl step (List.ofFn (Fin.append P L)) =
                step (gs.foldl step (List.ofFn (Fin.append P L))) g0 := by
              simp [gs', List.foldl_append]
            rw [hfold]
            have hgl : (gs.foldl step (List.ofFn (Fin.append P L))).length = m + gs.length := by
              rw [step_len]
              simp [m]
            unfold step
            rw [List.getD_append_right _ _ _ _ hgl.le, hgl, Nat.sub_self]
            rfl
          · have hspecw := hspec w (by omega)
            refine ⟨fun h => hspecw.1 (by simpa [f', hwk] using h), ?_⟩
            intro t ht
            have ht' : f w = some t := by simpa [f', hwk] using ht
            have hst := hspecw.2 t ht'
            refine ⟨by simp [gs']; omega, ?_⟩
            intro P L
            rw [hst.2 P L]
            have hfold : gs'.foldl step (List.ofFn (Fin.append P L)) =
                step (gs.foldl step (List.ofFn (Fin.append P L))) g0 := by
              simp [gs', List.foldl_append]
            rw [hfold]
            have hgl : (gs.foldl step (List.ofFn (Fin.append P L))).length = m + gs.length := by
              rw [step_len]
              simp [m]
            unfold step
            rw [List.getD_append _ _ _ _ (by rw [hgl]; exact hst.1)]
      have keepGate (val : Option ℕ) (hval : WireSpec gs (m + k) val) :
          ∃ (gs' : List PEqualNP.CircuitLowerBounds.Gate) (f' : ℕ → Option ℕ),
            gs'.length ≤ k + 1 ∧
            (∀ g ∈ gs', g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
              g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            (∀ j < gs'.length, ∀ t ∈ (gs'.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
              t < m + j) ∧
            (∀ g ∈ gs', g.inputs.length = 2) ∧
            (∀ w < m + (k + 1), WireSpec gs' w (f' w)) := by
        refine ⟨gs, fun w => if w = m + k then val else f w, by omega, hao, hback, htwo, ?_⟩
        intro w hw
        by_cases hwk : w = m + k
        · subst hwk
          simpa using hval
        · simpa [hwk] using hspec w (by omega)
      rcases hmem with hor | hcopy | hemp | hand
      · have hsa := hspec a ha
        have hsb := hspec b hb
        cases hfa : f a with
        | none =>
          have hea : W a = ∅ := hsa.1 hfa
          apply keepGate (f b)
          have heqW : W (m + k) = W b := by rw [hor, hea, Set.empty_union]
          refine ⟨fun h => by rw [heqW]; exact hsb.1 h, fun u hu => ?_⟩
          have hsu := hsb.2 u hu
          exact ⟨hsu.1, fun P L => by rw [heqW]; exact hsu.2 P L⟩
        | some u =>
          cases hfb : f b with
          | none =>
            have heb : W b = ∅ := hsb.1 hfb
            apply keepGate (f a)
            have heqW : W (m + k) = W a := by rw [hor, heb, Set.union_empty]
            refine ⟨fun h => by rw [heqW]; exact hsa.1 h, fun t ht => ?_⟩
            have hst := hsa.2 t ht
            exact ⟨hst.1, fun P L => by rw [heqW]; exact hst.2 P L⟩
          | some v =>
            have hsu := hsa.2 u hfa
            have hsv := hsb.2 v hfb
            apply addGate PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl) u v hsu.1 hsv.1
            intro P L
            rw [hor, Set.mem_union, hsu.2 P L, hsv.2 P L]
            change _ ↔ (_ || (_ || false)) = true
            simp only [Bool.or_false, Bool.or_eq_true, id_eq]
      · apply keepGate (f a)
        have hsa := hspec a ha
        refine ⟨fun h => by rw [hcopy]; exact hsa.1 h, fun t ht => ?_⟩
        have hst := hsa.2 t ht
        exact ⟨hst.1, fun P L => by rw [hcopy]; exact hst.2 P L⟩
      · exact keepGate none ⟨fun _ => hemp, fun _ h => (by cases h)⟩
      · have hsa := hspec a ha
        have hsb := hspec b hb
        cases hfa : f a with
        | none =>
          have hea : W a = ∅ := hsa.1 hfa
          exact keepGate none ⟨fun _ => by rw [hand, hea, Set.empty_inter],
            fun _ h => (by cases h)⟩
        | some u =>
          cases hfb : f b with
          | none =>
            have heb : W b = ∅ := hsb.1 hfb
            exact keepGate none ⟨fun _ => by rw [hand, heb, Set.inter_empty],
              fun _ h => (by cases h)⟩
          | some v =>
            have hsu := hsa.2 u hfa
            have hsv := hsb.2 v hfb
            apply addGate PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl) u v hsu.1 hsv.1
            intro P L
            rw [hand, Set.mem_inter_iff, hsu.2 P L, hsv.2 P L]
            change _ ↔ (_ && (_ && true)) = true
            simp only [Bool.and_true, Bool.and_eq_true, id_eq]
  have hI_nonempty : ∃ p0 l0 : Fin N, I p0 l0 := by
    let l0 : Fin N := ⟨0, by omega⟩
    have hc : 0 < Fintype.card {p : Fin N // I p l0} := by rw [hdeg l0]; omega
    obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hc
    exact ⟨p0, l0, hp0⟩
  obtain ⟨gs0, f0, hlen0, hao0, hback0, htwo0, hspec0⟩ := hdecompile s le_rfl
  have hfo := hspec0 o ho
  cases hfo_eq : f0 o with
  | none =>
    have heo : W o = ∅ := hfo.1 hfo_eq
    obtain ⟨p0, l0, hp0⟩ := hI_nonempty
    have hmem := hpos p0 l0 hp0
    rw [heo] at hmem
    exact hmem.elim
  | some o0 =>
    have hso0 := hfo.2 o0 hfo_eq
    let C0 : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs0, o0⟩
    have hC0_ao : PEqualNP.TopForm.IsAO2 (N + N) C0 := ⟨hao0, hback0, htwo0⟩
    have hC0_size : C0.size ≤ s := hlen0
    have hC0_eval (P L : Fin N → Bool) :
        (P, L) ∈ W o ↔ PEqualNP.MetaComplexity.circuitFun (N + N) C0 (Fin.append P L) = true :=
      hso0.2 P L
    have append_split (z : Fin (N + N) → Bool) :
        Fin.append (fun p : Fin N => z (Fin.castAdd N p)) (fun l : Fin N => z (Fin.natAdd N l)) = z := by
      funext k
      refine Fin.addCases (fun p => ?_) (fun l => ?_) k
      · rw [Fin.append_left]
      · rw [Fin.append_right]
    have cast_ne_nat (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have edge_eq_append (p l : Fin N) :
        (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) =
          Fin.append (one p) (one l) := by
      funext k
      refine Fin.addCases (fun a => ?_) (fun b => ?_) k
      · simp only [Fin.append_left, one, cast_ne_nat a l, or_false, Fin.castAdd_inj]
      · have hne : Fin.natAdd N b ≠ Fin.castAdd N p := (cast_ne_nat p b).symm
        simp only [Fin.append_right, one, hne, false_or, Fin.natAdd_inj]
    let Valid (D : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) D
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) ∧
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) D z = false)
    have hC0_valid : Valid C0 := by
      refine ⟨hC0_ao, ?_, ?_⟩
      · intro p l hI
        rw [edge_eq_append p l]
        exact (hC0_eval (one p) (one l)).mp (hpos p l hI)
      · intro z hz hno
        let P : Fin N → Bool := fun p => z (Fin.castAdd N p)
        let L : Fin N → Bool := fun l => z (Fin.natAdd N l)
        let P' : Fin N → Bool := fun p => decide (¬ ∃ l : Fin N, I p l ∧ L l = true)
        have hP_le : ∀ p, P p = true → P' p = true := by
          intro p hp
          apply decide_eq_true
          rintro ⟨l, hI, hl⟩
          exact hno ⟨p, l, hI, hp, hl⟩
        have hnotW : (P, L) ∉ W o := fun hmem =>
          hneg L hz (hW_mono o ho (P, L) (P', L) hP_le (fun _ h => h) hmem)
        have hnotC : PEqualNP.MetaComplexity.circuitFun (N + N) C0 (Fin.append P L) ≠ true :=
          fun ht => hnotW ((hC0_eval P L).mpr ht)
        rw [append_split z] at hnotC
        cases hval : PEqualNP.MetaComplexity.circuitFun (N + N) C0 z with
        | false => rfl
        | true => exact (hnotC hval).elim
    have hex : ∃ k : ℕ, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = k ∧ Valid D :=
      ⟨C0.size, C0, rfl, hC0_valid⟩
    obtain ⟨C, hCsize, hCvalid⟩ := Nat.find_spec hex
    have hC_le_s : C.size ≤ s := by
      have h1 : C.size ≤ C0.size := by
        rw [hCsize]
        exact Nat.find_min' hex ⟨C0, rfl, hC0_valid⟩
      exact h1.trans hC0_size
    have hC_ao : PEqualNP.TopForm.IsAO2 (N + N) C := hCvalid.1
    have hC_pos := hCvalid.2.1
    have hC_sound := hCvalid.2.2
    have hC_min : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) D →
        PEqualNP.MetaComplexity.circuitFun (N + N) D = PEqualNP.MetaComplexity.circuitFun (N + N) C →
        C.size ≤ D.size := by
      intro D hDao hDfun
      rw [hCsize]
      refine Nat.find_min' hex ⟨D, rfl, hDao, ?_, ?_⟩
      · intro p l hI
        rw [hDfun]
        exact hC_pos p l hI
      · intro z hz hno
        rw [hDfun]
        exact hC_sound z hz hno
    have hC_out : C.output < N + N + C.size := by
      by_contra hge
      obtain ⟨p0, l0, hp0⟩ := hI_nonempty
      have ht := hC_pos p0 l0 hp0
      have hlen : (C.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0)))).length = N + N + C.size := by
        change (C.gates.foldl step _).length = N + N + C.gates.length
        rw [step_len]
        simp
      have hf : PEqualNP.MetaComplexity.circuitFun (N + N) C
          (fun k : Fin (N + N) => decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0)) = false := by
        change (C.wires _).getD C.output false = false
        exact List.getD_eq_default _ _ (by omega)
      exact Bool.noConfusion (ht.symm.trans hf)
    suffices hgoal : N * q ≤ 100 * C.size from hgoal.trans (Nat.mul_le_mul_left 100 hC_le_s)
    by_cases hq200 : 200 ≤ q
    · let neg (z : Fin (N + N) → Bool) : Prop :=
        ¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
      let Q (k : ℕ) : Prop := ∃ z : Fin (N + N) → Bool,
        neg z ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ∧
        Fintype.card {i : Fin (N + N) // z i = true} = k
      by_cases herr : ∃ k, Q k
      · obtain ⟨z, hzneg, hzyes, hzcard⟩ := Nat.find_spec herr
        have hzgt : q < Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} := by
          by_contra hle
          have hf := hC_sound z (by omega) hzneg
          exact Bool.noConfusion (hzyes.symm.trans hf)
        have hzmin : ∀ i : Fin (N + N), z i = true →
            PEqualNP.MetaComplexity.circuitFun (N + N) C (Function.update z i false) = false := by
          intro i hi
          let y := Function.update z i false
          have hy_le : ∀ j, y j = true → z j = true := by
            intro j hj
            by_cases hji : j = i
            · simp [y, hji] at hj
            · simpa [y, Function.update_of_ne hji] using hj
          have hyneg : neg y := by
            rintro ⟨p, l, hI, hp, hl⟩
            exact hzneg ⟨p, l, hI, hy_le _ hp, hy_le _ hl⟩
          have hycard : Fintype.card {j : Fin (N + N) // y j = true} <
              Fintype.card {j : Fin (N + N) // z j = true} := by
            rw [Fintype.card_subtype, Fintype.card_subtype]
            have hsub : Finset.univ.filter (fun j : Fin (N + N) => y j = true) =
                (Finset.univ.filter (fun j : Fin (N + N) => z j = true)).erase i := by
              ext j
              by_cases hji : j = i
              · subst hji; simp [y]
              · simp [y, hji]
            rw [hsub]
            exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
          cases hyval : PEqualNP.MetaComplexity.circuitFun (N + N) C y with
          | false => rfl
          | true =>
            have hmink := Nat.find_min' herr (show Q (Fintype.card {j : Fin (N + N) // y j = true})
              from ⟨y, hyneg, hyval, rfl⟩)
            omega
        exact errorCase q N I C hq200 hN hdeg huniq hC_ao hC_out hC_min hC_pos hC_sound
          z hzneg hzyes hzgt hzmin
      · apply exactCase q N I C hq200 hN hdeg huniq hC_ao hC_out hC_min
        intro z
        by_cases hhit : ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
        · rw [decide_eq_true hhit]
          obtain ⟨p, l, hI, hp, hl⟩ := hhit
          let e : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
          have he : PEqualNP.MetaComplexity.circuitFun (N + N) C e = true := hC_pos p l hI
          apply step_mono C.gates hC_ao.1 (List.ofFn e) (List.ofFn z) (by simp) _ C.output he
          intro idx hidx
          by_cases hlt : idx < N + N
          · rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn] at hidx ⊢
            rcases of_decide_eq_true hidx with h1 | h2
            · rw [h1]; exact hp
            · rw [h2]; exact hl
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hidx
            cases hidx
        · rw [decide_eq_false hhit]
          cases hval : PEqualNP.MetaComplexity.circuitFun (N + N) C z with
          | false => rfl
          | true =>
            exact (herr ⟨Fintype.card {i : Fin (N + N) // z i = true}, z, hhit, hval, rfl⟩).elim
    · have reach : ∀ (k : ℕ), k ≤ C.gates.length → ∀ (V : Finset ℕ),
          (∀ w ∈ V, w < m + k) →
          ∃ U : Finset ℕ, U.card ≤ V.card + k ∧ (∀ u ∈ U, u < m) ∧
            ∀ x y : Fin (N + N) → Bool,
              (∀ u ∈ U, ∀ hu : u < N + N, x ⟨u, hu⟩ = y ⟨u, hu⟩) →
              ∀ w ∈ V, (C.gates.foldl step (List.ofFn x)).getD w false =
                (C.gates.foldl step (List.ofFn y)).getD w false := by
        intro k
        induction k with
        | zero =>
          intro _ V hV
          refine ⟨V, by omega, fun u hu => by simpa using hV u hu, ?_⟩
          intro x y hxy w hw
          have hwm : w < N + N := by simpa [m] using hV w hw
          rw [step_keeps C.gates (List.ofFn x) w (by simpa using hwm),
            step_keeps C.gates (List.ofFn y) w (by simpa using hwm),
            List.getD_eq_getElem _ _ (by simpa using hwm),
            List.getD_eq_getElem _ _ (by simpa using hwm),
            List.getElem_ofFn, List.getElem_ofFn]
          exact hxy w hw hwm
        | succ k ih =>
          intro hk V hV
          let w0 := m + k
          by_cases hmem : w0 ∈ V
          · have hlt : k < C.gates.length := by omega
            let g := C.gates[k]
            have hglen : g.inputs.length = 2 := hC_ao.2.2 g (List.getElem_mem hlt)
            obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
              cases h1 : g.inputs with
              | nil => simp [h1] at hglen
              | cons a t =>
                cases h2 : t with
                | nil => simp [h1, h2] at hglen
                | cons b r =>
                  cases h3 : r with
                  | nil => exact ⟨a, b, rfl⟩
                  | cons _ _ => simp [h1, h2, h3] at hglen
            have hbackk : ∀ i ∈ g.inputs, i < m + k := by
              intro i hi
              have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
                change C.gates.getD k _ = C.gates[k]
                exact List.getD_eq_getElem _ _ hlt
              exact hC_ao.2.1 k hlt i (hget.symm ▸ hi)
            have ha : a < m + k := hbackk a (by simp [hab])
            have hb : b < m + k := hbackk b (by simp [hab])
            let V' := insert a (insert b (V.erase w0))
            have hV'bound : ∀ w ∈ V', w < m + k := by
              intro w hw
              rcases Finset.mem_insert.mp hw with rfl | hw
              · exact ha
              rcases Finset.mem_insert.mp hw with rfl | hw
              · exact hb
              · obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hw
                have := hV w hin
                change w ≠ m + k at hne
                omega
            obtain ⟨U, hUcard, hUbound, hUagree⟩ := ih (by omega) V' hV'bound
            have hV'card : V'.card ≤ V.card + 1 := by
              have c1 := Finset.card_insert_le a (insert b (V.erase w0))
              have c2 := Finset.card_insert_le b (V.erase w0)
              have c3 := Finset.card_erase_add_one hmem
              dsimp [V']
              omega
            refine ⟨U, by omega, hUbound, ?_⟩
            intro x y hxy w hw
            by_cases hww0 : w = w0
            · subst hww0
              have hxlen : (List.ofFn x).length = m := by simp [m]
              have hylen : (List.ofFn y).length = m := by simp [m]
              have hgx := step_gate C.gates (List.ofFn x) k hlt (by simpa [hxlen] using hbackk)
              have hgy := step_gate C.gates (List.ofFn y) k hlt (by simpa [hylen] using hbackk)
              rw [hxlen] at hgx
              rw [hylen] at hgy
              change (C.gates.foldl step (List.ofFn x)).getD (m + k) false =
                (C.gates.foldl step (List.ofFn y)).getD (m + k) false
              rw [hgx, hgy]
              change g.op.eval (g.inputs.map _) = g.op.eval (g.inputs.map _)
              rw [hab]
              simp only [List.map_cons, List.map_nil]
              rw [hUagree x y hxy a (by simp [V']), hUagree x y hxy b (by simp [V'])]
            · exact hUagree x y hxy w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_erase.mpr ⟨hww0, hw⟩)))
          · have hV' : ∀ w ∈ V, w < m + k := by
              intro w hw
              have hne : w ≠ w0 := fun he => hmem (he ▸ hw)
              have := hV w hw
              dsimp [w0] at hne
              omega
            obtain ⟨U, hUcard, hUbound, hUagree⟩ := ih (by omega) V hV'
            exact ⟨U, by omega, hUbound, hUagree⟩
      obtain ⟨U, hUcard, hUbound, hUagree⟩ := reach C.gates.length le_rfl {C.output} (by
        intro w hw
        have he : w = C.output := Finset.mem_singleton.mp hw
        subst he
        exact hC_out)
      have hall : Finset.range m ⊆ U := by
        intro v hv
        have hvm : v < m := Finset.mem_range.mp hv
        by_contra hnot
        have hflip (x y : Fin (N + N) → Bool)
            (hdiff : ∀ j : Fin (N + N), j.val ≠ v → x j = y j) :
            PEqualNP.MetaComplexity.circuitFun (N + N) C x =
              PEqualNP.MetaComplexity.circuitFun (N + N) C y := by
          apply hUagree x y _ C.output (Finset.mem_singleton_self _)
          intro u hu hum
          exact hdiff ⟨u, hum⟩ (fun he => hnot (he ▸ hu))
        by_cases hp : v < N
        · let p : Fin N := ⟨v, hp⟩
          let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
          have hne : p ≠ p' := by
            intro he
            have hv' := congrArg Fin.val he
            by_cases hp0 : p.val = 0 <;> simp [p', hp0] at hv'
          obtain ⟨l, ⟨hIpl, _⟩, _⟩ := huniq p p' hne
          let x : Fin (N + N) → Bool := fun j => decide (j = Fin.natAdd N l)
          let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
          have hxy := hflip x y (by
            intro j hj
            have hjp : j ≠ Fin.castAdd N p := fun he => hj (congrArg Fin.val he)
            simp only [x, y, hjp, false_or])
          have hy : PEqualNP.MetaComplexity.circuitFun (N + N) C y = true := hC_pos p l hIpl
          have hx : PEqualNP.MetaComplexity.circuitFun (N + N) C x = false := by
            apply hC_sound x
            · rw [Fintype.card_subtype]
              have hsub : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) ⊆ {l} := by
                intro l' hl'
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, x,
                  decide_eq_true_eq] at hl'
                exact Finset.mem_singleton.mpr (Fin.ext (by
                  have := congrArg Fin.val hl'
                  simp only [Fin.val_natAdd] at this
                  omega))
              exact (Finset.card_le_card hsub).trans (by simp; omega)
            · rintro ⟨p1, l1, _, hp1, _⟩
              exact cast_ne_nat p1 l (of_decide_eq_true hp1)
          rw [hx, hy] at hxy
          exact Bool.noConfusion hxy
        · let l : Fin N := ⟨v - N, by dsimp [m] at hvm; omega⟩
          have hvl : N + l.val = v := by dsimp [l]; omega
          have hc : 0 < Fintype.card {p : Fin N // I p l} := by rw [hdeg l]; omega
          obtain ⟨⟨p, hIpl⟩⟩ := Fintype.card_pos_iff.mp hc
          let x : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p)
          let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
          have hxy := hflip x y (by
            intro j hj
            have hjl : j ≠ Fin.natAdd N l := fun he => hj (by
              have := congrArg Fin.val he
              simp only [Fin.val_natAdd] at this
              omega)
            simp only [x, y, hjl, or_false])
          have hy : PEqualNP.MetaComplexity.circuitFun (N + N) C y = true := hC_pos p l hIpl
          have hx : PEqualNP.MetaComplexity.circuitFun (N + N) C x = false := by
            apply hC_sound x
            · rw [Fintype.card_subtype]
              have hemp : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) = ∅ := by
                ext l'
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                  iff_false, x, decide_eq_true_eq]
                exact (cast_ne_nat p l').symm
              rw [hemp]
              simp
            · rintro ⟨p1, l1, _, _, hl1⟩
              exact cast_ne_nat p l1 (of_decide_eq_true hl1).symm
          rw [hx, hy] at hxy
          exact Bool.noConfusion hxy
      have hcard := Finset.card_le_card hall
      simp only [Finset.card_range, Finset.card_singleton] at hcard hUcard
      have hq199 : q ≤ 199 := by omega
      have hmul := Nat.mul_le_mul_left N hq199
      change N + N ≤ U.card at hcard
      change U.card ≤ 1 + C.size at hUcard
      omega
