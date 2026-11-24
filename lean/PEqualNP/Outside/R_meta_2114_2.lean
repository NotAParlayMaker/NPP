import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2114_2
    (hbudget :
      let f (x : Fin 9 -> Bool) :=
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      let r (C : Circuit) : Finset (Fin C.size) := {i : Fin C.size | 4 ∈ (C.gates.get i).inputs}
      ∀ C : Circuit, FanInTwo C -> circuitFun 9 C = f ->
        (r C).card = 2 ->
        (∀ i : Fin C.size, let g := C.gates.get i
          4 ∈ g.inputs -> g.op = GateOp.or ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
            ∀ w ∈ g.inputs, w < 9 + i.val) ->
        15 ≤ C.size)
    (hfixed :
      let f (x : Fin 9 -> Bool) :=
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      let r (C : Circuit) (v : Fin 9) : Finset (Fin C.size) :=
        {i : Fin C.size | v.val ∈ (C.gates.get i).inputs}
      ∀ C : Circuit, IsMinimalCircuit 9 C -> C.size = 15 -> circuitFun 9 C = f ->
        (∀ i : Fin C.size, let g := C.gates.get i
          (∀ w ∈ g.inputs, w < 9 + i.val) ∧ g.inputs.Nodup ∧
            (g.op = GateOp.not ∧ g.inputs.length = 1∨
              g.op ≠ GateOp.not ∧ g.inputs.length = 2)) ->
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)),
          (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
          ∀ i ∈ r C v, (C.gates.get i).op = GateOp.or) ->
        (r C 4).card = 2 -> False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x7 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x7).card = (2 : ℕ)) → False := by

  have hperm : ∀ (n : ℕ) (C : Circuit) (s : Equiv.Perm (Fin n)),
      ∃ (D : Circuit) (q : Fin C.size ≃ Fin D.size),
        D.size = C.size ∧
        (IsMinimalCircuit n C → IsMinimalCircuit n D) ∧
        (∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (x ∘ s)) ∧
        ∀ i : Fin C.size,
          let g := C.gates.get i
          let g' := D.gates.get (q i)
          g'.op = g.op ∧ g'.inputs.length = g.inputs.length ∧
          (g.inputs.Nodup → g'.inputs.Nodup) ∧
          ((∀ w ∈ g.inputs, w < n + i.val) → ∀ w ∈ g'.inputs, w < n + (q i).val) ∧
          (∀ v : Fin n, (s v).val ∈ g'.inputs ↔ v.val ∈ g.inputs) := by
    intro n C s
    let wmap (w : ℕ) : ℕ := if h : w < n then (s ⟨w, h⟩ : ℕ) else w
    let relGate (g : Gate) : Gate := ⟨g.op, g.inputs.map wmap⟩
    let D : Circuit := ⟨C.gates.map relGate, wmap C.output⟩
    have hsz : D.size = C.size := by
      simp [D, Circuit.size]
    let q : Fin C.size ≃ Fin D.size := finCongr hsz.symm
    have hqval (i : Fin C.size) : (q i).val = i.val := by
      simp [q, finCongr]
    have hget (i : Fin C.size) : D.gates.get (q i) = relGate (C.gates.get i) := by
      have hiC : i.val < C.gates.length := (by
        change i.val < C.size; exact i.isLt)
      have hiD : (q i).val < D.gates.length := (by
        change (q i).val < D.size; exact (q i).isLt)
      have hq : (q i).val = i.val := hqval i
      change D.gates[(q i).val]'hiD = relGate (C.gates[i.val]'hiC)
      simp [D, hq]
    have wmap_lt_n (w : ℕ) (hw : w < n) : wmap w < n := by
      simp [wmap, hw]
    have wmap_ge (w : ℕ) (hw : ¬ w < n) : wmap w = w := by
      simp [wmap, hw]
    have wmap_inj : Function.Injective wmap := by
      intro a b h
      by_cases ha : a < n
      · by_cases hb : b < n
        · have : s ⟨a, ha⟩ = s ⟨b, hb⟩ := by
            apply Fin.ext
            simpa [wmap, ha, hb] using h
          exact congrArg Fin.val (s.injective this)
        · have h1 : wmap a < n := wmap_lt_n a ha
          have h2 : wmap b = b := wmap_ge b hb
          omega
      · by_cases hb : b < n
        · have h1 : wmap b < n := wmap_lt_n b hb
          have h2 : wmap a = a := wmap_ge a ha
          omega
        · rw [wmap_ge a ha, wmap_ge b hb] at h
          exact h
    have getD_snoc (l : List Bool) (a d : Bool) : (l ++ [a]).getD l.length d = a := by
      have : l.length < (l ++ [a]).length := by simp
      rw [List.getD_eq_getElem (l := l ++ [a]) (n := l.length) d this]
      simp
    have ev_rel (g : Gate) (W W' : List Bool)
        (hbits : ∀ w : ℕ, W'.getD (wmap w) false = W.getD w false) :
        (relGate g).op.eval ((relGate g).inputs.map fun i => W'.getD i false) =
          g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact hbits a
    have step_rel (W W' : List Bool) (g : Gate)
        (hn : n ≤ W.length) (hlen : W.length = W'.length)
        (hbits : ∀ w : ℕ, W'.getD (wmap w) false = W.getD w false) :
        let a := g.op.eval (g.inputs.map fun i => W.getD i false)
        let W1 := W ++ [a]
        let W1' := W' ++ [a]
        W1.length = W1'.length ∧ n ≤ W1.length ∧
          ∀ w : ℕ, W1'.getD (wmap w) false = W1.getD w false := by
      intro a W1 W1'
      have ha : (relGate g).op.eval ((relGate g).inputs.map fun i => W'.getD i false) = a :=
        ev_rel g W W' hbits
      refine ⟨by simp [W1, W1', hlen], by simp [W1]; omega, ?_⟩
      intro w
      change (W' ++ [a]).getD (wmap w) false = (W ++ [a]).getD w false
      rcases Nat.lt_trichotomy w W.length with hw | hw | hw
      · have hlt : wmap w < W'.length := by
          by_cases hwn : w < n
          · have := wmap_lt_n w hwn
            omega
          · rw [wmap_ge w hwn]; omega
        have hwl : w < (W ++ [a]).length := by simp; omega
        have hlt' : wmap w < (W' ++ [a]).length := by simp; omega
        rw [List.getD_eq_getElem (l := W' ++ [a]) (n := wmap w) false hlt']
        rw [List.getD_eq_getElem (l := W ++ [a]) (n := w) false hwl]
        rw [List.getElem_append_left (by exact hlt), List.getElem_append_left hw]
        have := hbits w
        rw [List.getD_eq_getElem (l := W') (n := wmap w) false hlt] at this
        rw [List.getD_eq_getElem (l := W) (n := w) false hw] at this
        exact this
      · have heq : wmap w = W'.length := by
          have : ¬ w < n := Nat.not_lt.mpr (hw ▸ hn)
          rw [wmap_ge w this, hw, hlen]
        rw [heq, hw]
        exact (getD_snoc W' a false).trans (getD_snoc W a false).symm
      · have hge : ¬ w < n := by omega
        have hwmap : wmap w = w := wmap_ge w hge
        have h1 : (W ++ [a]).length ≤ w := by simp; omega
        have h2 : (W' ++ [a]).length ≤ wmap w := by
          rw [hwmap]; simp [hlen]; omega
        rw [List.getD_eq_default _ _ h2, List.getD_eq_default _ _ h1]
    have fold_rel (gs : List Gate) :
        ∀ W W' : List Bool, n ≤ W.length → W.length = W'.length →
          (∀ w : ℕ, W'.getD (wmap w) false = W.getD w false) →
          let W1 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W
          let W1' := (gs.map relGate).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W'
          W1.length = W1'.length ∧ n ≤ W1.length ∧
            ∀ w : ℕ, W1'.getD (wmap w) false = W1.getD w false := by
      induction gs with
      | nil =>
        intro W W' hn hlen hbits
        exact ⟨hlen, hn, hbits⟩
      | cons g gs ih =>
        intro W W' hn hlen hbits
        obtain ⟨h1, h2, h3⟩ := step_rel W W' g hn hlen hbits
        have ha :
            (relGate g).op.eval ((relGate g).inputs.map fun i => W'.getD i false) =
              g.op.eval (g.inputs.map fun i => W.getD i false) :=
          ev_rel g W W' hbits
        have hih := ih (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
          (W' ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) h2 h1 h3
        have heq :
            W' ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] =
              W' ++ [(relGate g).op.eval ((relGate g).inputs.map fun i => W'.getD i false)] :=
          congrArg (fun t => W' ++ [t]) ha.symm
        simp only [List.foldl_cons, List.map_cons, List.getD] at heq hih ⊢
        rw [← heq]
        exact hih
    have init_rel (x : Fin n → Bool) :
        n ≤ (List.ofFn (x ∘ s)).length ∧
          (List.ofFn (x ∘ s)).length = (List.ofFn x).length ∧
          ∀ w : ℕ, (List.ofFn x).getD (wmap w) false = (List.ofFn (x ∘ s)).getD w false := by
      refine ⟨by simp, by simp, ?_⟩
      intro w
      by_cases hw : w < n
      · have h1 : w < (List.ofFn (x ∘ s)).length := by simp [hw]
        have h2 : wmap w < (List.ofFn x).length := by
          simp; exact wmap_lt_n w hw
        rw [List.getD_eq_getElem (l := List.ofFn x) (n := wmap w) false h2]
        rw [List.getD_eq_getElem (l := List.ofFn (x ∘ s)) (n := w) false h1]
        simp [wmap, hw, List.getElem_ofFn]
      · have h1 : (List.ofFn (x ∘ s)).length ≤ w := by simp; omega
        have h2 : (List.ofFn x).length ≤ wmap w := by
          rw [wmap_ge w hw]; simp; omega
        rw [List.getD_eq_default _ _ h2, List.getD_eq_default _ _ h1]
    have hFan (E : Circuit) (hF : FanInTwo E) : FanInTwo ⟨E.gates.map relGate, wmap E.output⟩ := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hF g0 hg0).1, by simpa [relGate] using (hF g0 hg0).2⟩
    have hfun0 (x : Fin n → Bool) :
        circuitFun n D x = circuitFun n C (x ∘ s) := by
      unfold circuitFun Circuit.eval Circuit.wires
      obtain ⟨_, _, hbits⟩ := init_rel x
      obtain ⟨_, _, hall⟩ := fold_rel C.gates (List.ofFn (x ∘ s)) (List.ofFn x)
        (by simp) (by simp) (init_rel x).2.2
      have : (C.gates.map relGate).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x) =
        (D.gates).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x) := by
        simp [D]
      rw [← this]
      exact (hall C.output)
    refine ⟨D, q, hsz, ?min, hfun0, ?gates⟩
    · intro hCmin
      refine ⟨hFan C hCmin.1, ?_⟩
      intro D' hF' hfun'
      let E : Circuit := ⟨D'.gates.map (fun g => ⟨g.op, g.inputs.map
          (fun w => if h : w < n then (s.symm ⟨w, h⟩ : ℕ) else w)⟩),
        (if h : D'.output < n then (s.symm ⟨D'.output, h⟩ : ℕ) else D'.output)⟩
      -- Use the same construction with s.symm: but our lets are frozen to s.
      -- Instead argue with a specialized copy below after the refine? We need a
      -- general relabel fact. Prove a local copy for s.symm by applying hfun0's
      -- pattern. Simpler: instantiate the same construction inline for s.symm.
      have hszE : E.size = D'.size := by simp [E, Circuit.size]
      have hFE : FanInTwo E := by
        intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact ⟨(hF' g0 hg0).1, by simpa using (hF' g0 hg0).2⟩
      -- evaluation: circuitFun n E y = circuitFun n D' (y ∘ s.symm)
      -- We repeat fold_rel for π = s.symm. To avoid huge duplication, note
      -- D is relabel by s, so circuitFun D x = circuitFun C (x ∘ s).
      -- circuitFun D' x = circuitFun D x = circuitFun C (x ∘ s)
      -- Want circuitFun E y = circuitFun D' (y ∘ s.symm) = circuitFun C y
      -- Then C.size ≤ E.size = D'.size, and D.size = C.size.
      change D.size ≤ D'.size
      suffices hEfunEq : ∀ y : Fin n → Bool, circuitFun n E y = circuitFun n C y by
        have hEfun : circuitFun n E = circuitFun n C := funext hEfunEq
        have : C.size ≤ E.size := hCmin.2 E hFE hEfun
        simpa [hsz, hszE] using this
      intro y
      -- prove eval of E on y equals eval of D' on (y ∘ s.symm)
      -- by the same Rel argument with π = s.symm
      let wmap' (w : ℕ) : ℕ := if h : w < n then (s.symm ⟨w, h⟩ : ℕ) else w
      have wmap'_lt (w : ℕ) (hw : w < n) : wmap' w < n := by
        simp [wmap', hw]
      have wmap'_ge (w : ℕ) (hw : ¬ w < n) : wmap' w = w := by
        simp [wmap', hw]
      have ev' (g : Gate) (W W' : List Bool)
          (hbits : ∀ w : ℕ, W'.getD (wmap' w) false = W.getD w false) :
          (⟨g.op, g.inputs.map wmap'⟩ : Gate).op.eval
            ((⟨g.op, g.inputs.map wmap'⟩ : Gate).inputs.map fun i => W'.getD i false) =
            g.op.eval (g.inputs.map fun i => W.getD i false) := by
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hbits a
      have fold' (gs : List Gate) :
          ∀ W W' : List Bool, n ≤ W.length → W.length = W'.length →
            (∀ w : ℕ, W'.getD (wmap' w) false = W.getD w false) →
            let W1 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W
            let W1' := (gs.map (fun (g : Gate) => (⟨g.op, g.inputs.map wmap'⟩ : Gate))).foldl
              (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W'
            W1.length = W1'.length ∧ n ≤ W1.length ∧
              ∀ w : ℕ, W1'.getD (wmap' w) false = W1.getD w false := by
        induction gs with
        | nil => intro W W' hn hlen hbits; exact ⟨hlen, hn, hbits⟩
        | cons g gs ih =>
          intro W W' hn hlen hbits
          have ha := ev' g W W' hbits
          -- step
          let a := g.op.eval (g.inputs.map fun i => W.getD i false)
          have hlen1 : (W ++ [a]).length = (W' ++ [a]).length := by simp [hlen]
          have hn1 : n ≤ (W ++ [a]).length := by simp; omega
          have hbits1 : ∀ w : ℕ, (W' ++ [a]).getD (wmap' w) false = (W ++ [a]).getD w false := by
            intro w
            rcases Nat.lt_trichotomy w W.length with hw | hw | hw
            · have hlt : wmap' w < W'.length := by
                by_cases hwn : w < n
                · have := wmap'_lt w hwn; omega
                · rw [wmap'_ge w hwn]; omega
              have hwl : w < (W ++ [a]).length := by simp; omega
              have hlt' : wmap' w < (W' ++ [a]).length := by simp; omega
              rw [List.getD_eq_getElem (l := W' ++ [a]) (n := wmap' w) false hlt']
              rw [List.getD_eq_getElem (l := W ++ [a]) (n := w) false hwl]
              rw [List.getElem_append_left (by exact hlt), List.getElem_append_left hw]
              have := hbits w
              rw [List.getD_eq_getElem (l := W') (n := wmap' w) false hlt] at this
              rw [List.getD_eq_getElem (l := W) (n := w) false hw] at this
              exact this
            · have heq : wmap' w = W'.length := by
                have : ¬ w < n := Nat.not_lt.mpr (hw ▸ hn)
                rw [wmap'_ge w this, hw, hlen]
              rw [heq, hw]
              exact (getD_snoc W' a false).trans (getD_snoc W a false).symm
            · have hge : ¬ w < n := by omega
              have hwmap : wmap' w = w := wmap'_ge w hge
              have h1 : (W ++ [a]).length ≤ w := by simp; omega
              have h2 : (W' ++ [a]).length ≤ wmap' w := by
                rw [hwmap]; simp [hlen]; omega
              rw [List.getD_eq_default _ _ h2, List.getD_eq_default _ _ h1]
          have heq :
              W' ++ [a] =
                W' ++ [((⟨g.op, g.inputs.map wmap'⟩ : Gate).op.eval
                  ((⟨g.op, g.inputs.map wmap'⟩ : Gate).inputs.map fun i => W'.getD i false))] :=
            congrArg (fun t => W' ++ [t]) ha.symm
          simp only [List.foldl_cons, List.map_cons, List.getD] at heq ⊢
          rw [← heq]
          exact ih (W ++ [a]) (W' ++ [a]) hn1 hlen1 hbits1
      have init' :
          n ≤ (List.ofFn (y ∘ s.symm)).length ∧
            (List.ofFn (y ∘ s.symm)).length = (List.ofFn y).length ∧
            ∀ w : ℕ, (List.ofFn y).getD (wmap' w) false =
              (List.ofFn (y ∘ s.symm)).getD w false := by
        refine ⟨by simp, by simp, ?_⟩
        intro w
        by_cases hw : w < n
        · have h1 : w < (List.ofFn (y ∘ s.symm)).length := by simp [hw]
          have h2 : wmap' w < (List.ofFn y).length := by simp; exact wmap'_lt w hw
          rw [List.getD_eq_getElem (l := List.ofFn y) (n := wmap' w) false h2]
          rw [List.getD_eq_getElem (l := List.ofFn (y ∘ s.symm)) (n := w) false h1]
          simp [wmap', hw, List.getElem_ofFn]
        · have h1 : (List.ofFn (y ∘ s.symm)).length ≤ w := by simp; omega
          have h2 : (List.ofFn y).length ≤ wmap' w := by
            rw [wmap'_ge w hw]; simp; omega
          rw [List.getD_eq_default _ _ h2, List.getD_eq_default _ _ h1]
      unfold circuitFun Circuit.eval Circuit.wires
      obtain ⟨_, _, hall⟩ := fold' D'.gates (List.ofFn (y ∘ s.symm)) (List.ofFn y)
        (by simp) (by simp) init'.2.2
      have hE : E.gates = D'.gates.map (fun (g : Gate) => (⟨g.op, g.inputs.map wmap'⟩ : Gate)) ∧
          E.output = wmap' D'.output := by
        simp [E, wmap']
      rw [hE.1, hE.2]
      have := hall D'.output
      -- this : wires of mapped D' on y, getD (wmap' output) = wires of D' on (y ∘ s.symm), getD output
      -- which is circuitFun D' (y ∘ s.symm)
      change (List.getD
          ((D'.gates.map (fun (g : Gate) => (⟨g.op, g.inputs.map wmap'⟩ : Gate))).foldl
            (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (List.ofFn y))
          (wmap' D'.output) false) =
        circuitFun n C y
      have hL :
          (List.foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (List.ofFn (y ∘ s.symm)) D'.gates).getD D'.output false =
          circuitFun n D' (y ∘ s.symm) := by
        unfold circuitFun Circuit.eval Circuit.wires
        rfl
      have hD' : circuitFun n D' (y ∘ s.symm) = circuitFun n D (y ∘ s.symm) := by
        rw [hfun']
      have hDs : circuitFun n D (y ∘ s.symm) = circuitFun n C (y ∘ s.symm ∘ s) := hfun0 _
      have hss : y ∘ s.symm ∘ s = y := by
        funext i; simp
      rw [this, hL, hD', hDs, hss]
    · intro i
      rw [hget]
      refine ⟨rfl, by simp [relGate], ?_, ?_, ?_⟩
      · intro hnd
        simp [relGate]
        exact List.Nodup.map wmap_inj hnd
      · intro hwf w hw
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
        have hw0' := hwf w0 hw0
        by_cases hw0n : w0 < n
        · have := wmap_lt_n w0 hw0n
          omega
        · rw [wmap_ge w0 hw0n]
          exact hw0'
      · intro v
        simp [relGate, List.mem_map]
        constructor
        · intro ⟨w0, hw0, heq⟩
          have : wmap w0 = (s v).val := heq
          by_cases hw0n : w0 < n
          · have : s ⟨w0, hw0n⟩ = s v := by
              apply Fin.ext
              simpa [wmap, hw0n] using heq
            have := s.injective this
            have : w0 = v.val := Fin.ext_iff.mp this
            simpa [this] using hw0
          · have : wmap w0 = w0 := wmap_ge w0 hw0n
            have : w0 = (s v).val := by simpa [this] using heq
            have : (s v).val < n := (s v).isLt
            omega
        · intro hv
          exact ⟨v.val, hv, by simp [wmap]⟩

  classical
  dsimp only
  intro C hC hOr hDouble

  let f (x : Fin 9 -> Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let lows : List (Fin 9) := [4, 6, 7]
  let r (D : Circuit) (v : Fin 9) : Finset (Fin D.size) :=
    {i : Fin D.size | v.val ∈ (D.gates.get i).inputs}
  let clean (D : Circuit) := ∀ i : Fin D.size, let g := D.gates.get i
    (∀ w ∈ g.inputs, w < 9 + i.val) ∧ g.inputs.Nodup ∧
      (g.op = GateOp.not ∧ g.inputs.length = 1 ∨
        g.op ≠ GateOp.not ∧ g.inputs.length = 2)
  obtain ⟨v, hv, hvTwo⟩ := hDouble
  change v ∈ lows at hv
  change (r C v).card = 2 at hvTwo
  have hCclean : clean C := hC.2.2.2.1
  have hCfun : circuitFun 9 C = f := hC.2.2.1
  let rot : Equiv.Perm (Fin 9) :=
    ⟨![1, 2, 3, 8, 6, 0, 7, 4, 5], ![5, 0, 1, 2, 7, 8, 4, 6, 3],
      by intro i; fin_cases i <;> decide, by intro i; fin_cases i <;> decide⟩

  have hrotF (x : Fin 9 -> Bool) : f (x ∘ rot) = f x := by
    change (x 1 && x 2 || x 2 && x 3 || x 3 && x 8 || x 8 && x 6 || x 6 && x 1 ||
      x 1 && x 0 || x 2 && x 7 || x 3 && x 4 || x 8 && x 5 || x 0 && x 4 ||
      x 7 && x 5 || x 5 && x 0) = _
    unfold f
    ac_rfl
  have hrotL (u : Fin 9) : rot u ∈ lows ↔ u ∈ lows := by
    fin_cases u <;> decide
  have hchoose : ∃ s : Equiv.Perm (Fin 9), s v = 4 ∧
      (∀ u, s u ∈ lows ↔ u ∈ lows) ∧ (∀ x, f (x ∘ s) = f x) := by
    change v ∈ ([4, 6, 7] : List (Fin 9)) at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h
    · subst v
      exact ⟨Equiv.refl _, rfl, fun _ => Iff.rfl, fun _ => rfl⟩
    · subst v
      refine ⟨rot.trans rot, by decide, fun u => (hrotL (rot u)).trans (hrotL u), ?_⟩
      intro x
      change f ((x ∘ rot) ∘ rot) = f x
      rw [hrotF, hrotF]
    · subst v
      exact ⟨rot, by decide, hrotL, hrotF⟩

  obtain ⟨s, hsv, hsL, hsF⟩ := hchoose
  obtain ⟨D, q, hsize, hmin, hfun, hgate⟩ := hperm 9 C s
  have hDmin := hmin hC.1
  have hDfun : circuitFun 9 D = f := by
    funext x
    rw [hfun, hCfun, hsF]
  have hDclean : clean D := by
    intro j
    obtain ⟨i, rfl⟩ := q.surjective j
    obtain ⟨hap, hlen, hnd, hback, _⟩ := hgate i
    obtain ⟨hi, hin, hkind⟩ := hCclean i
    refine ⟨hback hi, hnd hin, ?_⟩
    simpa only [hap, hlen] using hkind
  have hmap (u : Fin 9) : (r C u).map q.toEmbedding = r D (s u) := by
    ext j
    obtain ⟨i, rfl⟩ := q.surjective j
    change q.toEmbedding i ∈ (r C u).map q.toEmbedding ↔ q i ∈ r D (s u)
    rw [Finset.mem_map']
    simp [r, (hgate i).2.2.2.2 u]
  have hDtwo : (r D 4).card = 2 := by
    rw [← hsv, ← hmap, Finset.card_map, hvTwo]

  have hDr (u : Fin 9) (hu : u ∈ lows) :
      (r D u).Nonempty ∧ (r D u).card ≤ 2 ∧ ∀ j ∈ r D u, (D.gates.get j).op = GateOp.or := by
    let w := s.symm u
    have hsw : s w = u := s.apply_symm_apply u
    have hw : w ∈ lows := (hsL w).mp (hsw.symm ▸ hu)
    have hCcount : (r C w).Nonempty ∧ (r C w).card ≤ 2 :=
      ⟨(hC.2.2.2.2 w hw).1, (hC.2.2.2.2 w hw).2.1⟩
    rw [← hsw, ← hmap]
    refine ⟨hCcount.1.map, by simpa only [Finset.card_map] using hCcount.2, ?_⟩
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact (hgate i).1.trans (hOr w hw i hi)
  have hDsize : D.size = 15 := by
    apply Nat.le_antisymm (hsize.trans_le hC.2.1)
    refine hbudget D hDmin.1 hDfun hDtwo ?_
    intro j
    dsimp only
    intro hj
    have hjr : j ∈ r D 4 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hop := (hDr 4 (by decide)).2.2 j hjr
    obtain ⟨hback, hnd, hk⟩ := hDclean j
    refine ⟨hop, ?_, hnd, hback⟩
    rcases hk with hk | hk
    · rw [hop] at hk
      exact (GateOp.noConfusion hk.1)
    · exact hk.2
  exact hfixed D hDmin hDsize hDfun hDclean hDr hDtwo
