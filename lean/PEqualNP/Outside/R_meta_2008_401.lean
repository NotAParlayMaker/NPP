import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.R_meta_2008_401
    (pointFocused : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      Monotone2 C →
      let one := fun (a b : Fin N) => decide (b = a)
      let wire := fun (t : ℕ) (p l : Fin N → Bool) => (C.wires (List.ofFn p ++ List.ofFn l)).getD t false
      (∀ p l, I p l → wire C.output (one p) (one l) = true) →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      ∀ (B : Finset ℕ) (owner : ℕ → Fin N),
        B ⊆ Finset.range C.size →
        (∀ j ∈ B, ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          ∀ w ∈ g.inputs, ∃ x : Fin N → Bool, wire w x (fun _ => false) ≠ wire w x (fun _ => true)) →
        (∀ j ∈ B, ∀ y : Fin N → Bool, Fintype.card {l : Fin N // y l = true} ≤ q →
          (∀ l, y l = true → ¬ I (owner j) l) → wire (N + N + j) (one (owner j)) y = false) →
        100 * B.card < N * q →
        48 * (N * q) ≤ 100 * {e : Fin N × Fin N | I e.1 e.2 ∧
          ∃ j ∈ B, owner j = e.1 ∧ wire (N + N + j) (one e.1) (one e.2) = true}.ncard →
        N * q ≤ 100 * C.size)
    (lineSeparating : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      Monotone2 C →
      let one := fun (a b : Fin N) => decide (b = a)
      let wire := fun (t : ℕ) (p l : Fin N → Bool) => (C.wires (List.ofFn p ++ List.ofFn l)).getD t false
      (∀ p l, I p l → wire C.output (one p) (one l) = true) →
      (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      ∀ (D : Finset ℕ),
        D ⊆ Finset.range C.size →
        (∀ j ∈ D, ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          ∀ w ∈ g.inputs, ∃ x : Fin N → Bool, wire w x (fun _ => false) ≠ wire w x (fun _ => true)) →
        100 * D.card < N * q →
        48 * (N * q) ≤ 100 * {e : Fin N × Fin N | I e.1 e.2 ∧
          ∃ j ∈ D, wire (N + N + j) (one e.1) (one e.2) = true ∧
            wire (N + N + j) (fun p => decide (¬ I p e.2)) (one e.2) = false}.ncard →
        N * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq hN hdeg huniq hmono hout hsorted hacc hsound S hmarked hSsmall
  classical
  have hNge : 10000 ≤ N := by nlinarith
  have hNpos : 0 < N := by omega
  let m : ℕ := N + N
  let s : ℕ := C.size
  have hs_eq : s = C.gates.length := rfl
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
      run (gs ++ [g]) w = step (run gs w) g := by
    simp [run, List.foldl_append]
  have run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih =>
      rw [run_snoc]
      simp [step, ih]
      omega
  have run_keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = w.getD i false
      rw [ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have step_getD (w : List Bool) (g : Gate) (i : ℕ) :
      (step w g).getD i false = if i < w.length then w.getD i false
        else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false) else false := by
    dsimp [step]
    rcases lt_trichotomy i w.length with hi | hi | hi
    · rw [List.getD_append _ _ _ _ hi]
      simp [hi]
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hi]
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
      have h1 : ¬ i < w.length := by omega
      have h2 : i ≠ w.length := by omega
      rw [hk]
      simp [h1, h2]
  have run_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
      (earlier : ∀ i ∈ gs[j].inputs, i < w.length + j) :
      (run gs w).getD (w.length + j) false =
        gs[j].op.eval (gs[j].inputs.map fun i => (run gs w).getD i false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero] at earlier ⊢
        change (run gs (step w g)).getD w.length false = _
        rw [run_keeps _ _ _ (by simp [step])]
        dsimp only [step]
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
        change g.op.eval (g.inputs.map fun i => w.getD i false) = _
        congr 1
        apply List.map_congr_left
        intro i hi
        exact (run_keeps _ _ _ (earlier i hi)).symm
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have len : (step w g).length + j = w.length + (j + 1) := by simp [step]; omega
        have earlier' : ∀ i ∈ gs[j].inputs, i < (step w g).length + j := by
          simpa only [List.getElem_cons_succ, len] using earlier
        change (run gs (step w g)).getD (w.length + (j + 1)) false = _
        rw [← len]
        exact ih (step w g) j hj' earlier'
  have run_mono (gs : List Gate) (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (a b : List Bool), a.length = b.length →
        (∀ i, a.getD i false = true → b.getD i false = true) →
        ∀ i, (run gs a).getD i false = true → (run gs b).getD i false = true := by
    induction gs with
    | nil =>
      intro a b _ h i hi
      exact h i hi
    | cons g gs ih =>
      intro a b hlen h i hi
      change (run gs (step b g)).getD i false = true
      apply ih (fun t ht => hao t (List.mem_cons_of_mem _ ht)) (step a g) (step b g)
        (by simp [step, hlen]) _ i hi
      intro k hk
      rw [step_getD] at hk ⊢
      rw [← hlen]
      split_ifs at hk ⊢ with h1 h2
      · exact h k hk
      · rcases hao g List.mem_cons_self with hop | hop
        · rw [hop] at hk ⊢
          change (g.inputs.map fun k => a.getD k false).all id = true at hk
          change (g.inputs.map fun k => b.getD k false).all id = true
          simp only [List.all_eq_true, List.mem_map, id_eq] at hk ⊢
          rintro _ ⟨u, hu, rfl⟩
          exact h u (hk _ ⟨u, hu, rfl⟩)
        · rw [hop] at hk ⊢
          change (g.inputs.map fun k => a.getD k false).any id = true at hk
          change (g.inputs.map fun k => b.getD k false).any id = true
          simp only [List.any_eq_true, List.mem_map, id_eq] at hk ⊢
          obtain ⟨_, ⟨u, hu, rfl⟩, hku⟩ := hk
          exact ⟨b.getD u false, ⟨u, hu, rfl⟩, h u hku⟩
  by_cases hq200 : q < 200
  · have hcast_ne_nat : ∀ (p l : Fin N), Fin.castAdd N p ≠ Fin.natAdd N l := by
      intro p l h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have hsens : ∀ k : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
        (∀ j : Fin (N + N), j ≠ k → x j = y j) ∧
        circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
      intro k
      by_cases hk : k.val < N
      · let p : Fin N := ⟨k.val, hk⟩
        have hkp : k = Fin.castAdd N p := Fin.ext rfl
        let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
        have hne : p ≠ p' := by
          intro h
          have hv := congrArg Fin.val h
          by_cases hp0 : p.val = 0 <;> simp [p', hp0] at hv
        obtain ⟨l, ⟨hIpl, _⟩, _⟩ := huniq p p' hne
        let x : Fin (N + N) → Bool := fun j => decide (j = Fin.natAdd N l)
        let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
        refine ⟨x, y, ?_, ?_⟩
        · intro j hj
          rw [hkp] at hj
          simp only [x, y, hj, false_or]
        · have hy : circuitFun (N + N) C y = true := hacc p l hIpl
          have hx : circuitFun (N + N) C x = false := by
            apply hsound x
            · rw [Fintype.card_subtype]
              have hsub : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) ⊆ {l} := by
                intro l' hl'
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, decide_eq_true_eq] at hl'
                have hval := congrArg Fin.val hl'
                simp only [Fin.val_natAdd] at hval
                exact Finset.mem_singleton.mpr (Fin.ext (by omega))
              exact (Finset.card_le_card hsub).trans (by simp; omega)
            · rintro ⟨p0, l0, _, hp0, _⟩
              simp only [x, decide_eq_true_eq] at hp0
              exact hcast_ne_nat p0 l hp0
          rw [hx, hy]
          decide
      · let l : Fin N := ⟨k.val - N, by omega⟩
        have hkl : k = Fin.natAdd N l := Fin.ext (by simp [l]; omega)
        have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l)).card := by
          rw [← Fintype.card_subtype, hdeg l]
          omega
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
        have hIpl : I p l := (Finset.mem_filter.mp hp).2
        let x : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p)
        let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
        refine ⟨x, y, ?_, ?_⟩
        · intro j hj
          rw [hkl] at hj
          simp only [x, y, hj, or_false]
        · have hy : circuitFun (N + N) C y = true := hacc p l hIpl
          have hx : circuitFun (N + N) C x = false := by
            apply hsound x
            · rw [Fintype.card_subtype]
              have hemp : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) = ∅ := by
                ext l'
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                  iff_false, x, decide_eq_true_eq]
                intro h
                exact hcast_ne_nat p l' h.symm
              rw [hemp]
              simp
            · rintro ⟨p0, l0, _, _, hl0⟩
              simp only [x, decide_eq_true_eq] at hl0
              exact hcast_ne_nat p l0 hl0.symm
          rw [hx, hy]
          decide
    have image_merge (X : Finset (Fin m)) (a b : Fin m) :
        X.card ≤ (X.image (fun x => if x = a then b else x)).card + 1 := by
      have h1 : X.erase a ⊆ X.image (fun x => if x = a then b else x) := by
        intro x hx
        rw [Finset.mem_erase] at hx
        exact Finset.mem_image.mpr ⟨x, hx.2, by simp [hx.1]⟩
      have h2 := Finset.card_le_card h1
      have h3 := Finset.pred_card_le_card_erase (s := X) (a := a)
      omega
    have ofFn_getD (f : Fin m → Bool) (i : ℕ) :
        (List.ofFn f).getD i false = if h : i < m then f ⟨i, h⟩ else false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      by_cases h : i < m <;> simp [h]
    have gate_key (W : (Fin m → Bool) → ℕ → Bool) (c : Fin m → Fin m)
        (hc : ∀ i, ∃ k, ∀ x y : Fin m → Bool, (∀ j, c j = c k → x j = y j) → W x i = W y i)
        (g : Gate) (hpair : ∃ a b, g.inputs = [a, b]) :
        ∃ c' : Fin m → Fin m,
          (Finset.univ.image c).card ≤ (Finset.univ.image c').card + 1 ∧
          (∀ v v', c v = c v' → c' v = c' v') ∧
          ∃ k, ∀ x y : Fin m → Bool, (∀ j, c' j = c' k → x j = y j) →
            g.op.eval (g.inputs.map (W x)) = g.op.eval (g.inputs.map (W y)) := by
      obtain ⟨a, b, hgi⟩ := hpair
      obtain ⟨ka, hka⟩ := hc a
      obtain ⟨kb, hkb⟩ := hc b
      refine ⟨fun v => if c v = c ka then c kb else c v, ?_, ?_, kb, ?_⟩
      · have e : Finset.univ.image (fun v => if c v = c ka then c kb else c v) =
            (Finset.univ.image c).image (fun x => if x = c ka then c kb else x) := by
          rw [Finset.image_image]
          rfl
        rw [e]
        exact image_merge (Finset.univ.image c) (c ka) (c kb)
      · intro v v' h
        simp only [h]
      · intro x y h
        have e : (if c kb = c ka then c kb else c kb) = c kb := by
          by_cases hck : c kb = c ka <;> simp [hck]
        simp only [e] at h
        have h1 : W x a = W y a := hka x y (fun j hj => h j (by simp [hj]))
        have h2 : W x b = W y b := hkb x y (fun j hj => h j (by simp [hj]))
        rw [hgi]
        simp only [List.map_cons, List.map_nil, h1, h2]
    have core (gs : List Gate) (hgs : ∀ g ∈ gs, ∃ a b, g.inputs = [a, b]) :
        ∃ c : Fin m → Fin m,
          m ≤ (Finset.univ.image c).card + gs.length ∧
          ∀ i, ∃ k, ∀ x y : Fin m → Bool, (∀ j, c j = c k → x j = y j) →
            (run gs (List.ofFn x)).getD i false = (run gs (List.ofFn y)).getD i false := by
      induction gs using List.reverseRecOn with
      | nil =>
        refine ⟨id, by simp, ?_⟩
        intro i
        by_cases him : i < m
        · refine ⟨⟨i, him⟩, ?_⟩
          intro x y h
          show (List.ofFn x).getD i false = (List.ofFn y).getD i false
          rw [ofFn_getD, ofFn_getD]
          simp only [him, dite_true]
          exact h _ rfl
        · refine ⟨⟨0, by omega⟩, ?_⟩
          intro x y _
          show (List.ofFn x).getD i false = (List.ofFn y).getD i false
          rw [ofFn_getD, ofFn_getD]
          simp [him]
      | append_singleton gs g ih =>
        obtain ⟨c, hc1, hc2⟩ := ih (fun g' hg' => hgs g' (by simp [hg']))
        obtain ⟨c', k1, k2, k3, hk3⟩ := gate_key (fun x i => (run gs (List.ofFn x)).getD i false)
          c hc2 g (hgs g (by simp))
        refine ⟨c', ?_, ?_⟩
        · rw [List.length_append, List.length_singleton]
          omega
        · intro i
          by_cases hi : i < m + gs.length
          · obtain ⟨k, hk⟩ := hc2 i
            refine ⟨k, ?_⟩
            intro x y h
            rw [run_snoc, run_snoc, step_getD, step_getD, run_len, run_len]
            simp only [List.length_ofFn, hi, ite_true]
            exact hk x y (fun j hj => h j (k2 j k hj))
          · by_cases hi2 : i = m + gs.length
            · refine ⟨k3, ?_⟩
              intro x y h
              rw [run_snoc, run_snoc, step_getD, step_getD, run_len, run_len]
              simp only [List.length_ofFn, hi2, ite_true, lt_irrefl, ite_false]
              exact hk3 x y h
            · refine ⟨⟨0, by omega⟩, ?_⟩
              intro x y _
              rw [run_snoc, run_snoc, step_getD, step_getD, run_len, run_len]
              simp [hi, hi2]
    have hpairs : ∀ g ∈ C.gates, ∃ a b, g.inputs = [a, b] := by
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨a, b, hab, _, _⟩ := hsorted j C.gates[j] (List.getElem?_eq_getElem hj)
      exact ⟨a, b, hab⟩
    obtain ⟨c, hc1, hc2⟩ := core C.gates hpairs
    obtain ⟨k, hk⟩ := hc2 C.output
    have hle : (Finset.univ.image c).card ≤ 1 := by
      have hall : ∀ i, c i = c k := by
        intro i
        obtain ⟨x, y, hxy, hne⟩ := hsens i
        by_contra hci
        apply hne
        change (run C.gates (List.ofFn x)).getD C.output false =
          (run C.gates (List.ofFn y)).getD C.output false
        apply hk
        intro j hj
        apply hxy
        rintro rfl
        exact hci hj
      rw [Finset.card_le_one]
      intro a ha a' ha'
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v', _, rfl⟩ := Finset.mem_image.mp ha'
      rw [hall v, hall v']
    have h2N : N + N ≤ C.size + 1 := by
      have : C.size = C.gates.length := rfl
      omega
    have hqle : q ≤ 199 := by omega
    have hmul := Nat.mul_le_mul_left N hqle
    omega
  have hq200ge : 200 ≤ q := by omega
  let one (a b : Fin N) : Bool := decide (b = a)
  let zero : Fin N → Bool := fun _ => false
  let allOne : Fin N → Bool := fun _ => true
  let wire (t : ℕ) (p l : Fin N → Bool) : Bool := (C.wires (List.ofFn p ++ List.ofFn l)).getD t false
  have ofFn_const_eq (b : Bool) : List.ofFn (fun _ : Fin N => b) = List.replicate N b := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  have ofFn_append_eq (p l : Fin N → Bool) :
      List.ofFn (Fin.append p l) = List.ofFn p ++ List.ofFn l :=
    List.ofFn_fin_append p l
  have wire_eq_cf (p l : Fin N → Bool) :
      wire C.output p l = circuitFun (N + N) C (Fin.append p l) := by
    show (C.wires (List.ofFn p ++ List.ofFn l)).getD C.output false =
      (C.wires (List.ofFn (Fin.append p l))).getD C.output false
    rw [ofFn_append_eq]
  have wire_pt (p : Fin N) (x y : Fin N → Bool) : wire p.val x y = x p := by
    change (run C.gates (List.ofFn x ++ List.ofFn y)).getD p.val false = x p
    rw [run_keeps C.gates _ p.val (by simp; omega)]
    rw [List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  have wire_ln (l : Fin N) (x y : Fin N → Bool) : wire (N + l.val) x y = y l := by
    change (run C.gates (List.ofFn x ++ List.ofFn y)).getD (N + l.val) false = y l
    rw [run_keeps C.gates _ (N + l.val) (by simp)]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  have hao : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have hmem := (hmono g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have wire_mono (t : ℕ) (x x' y y' : Fin N → Bool)
      (hx : ∀ p, x p = true → x' p = true) (hy : ∀ l, y l = true → y' l = true) :
      wire t x y = true → wire t x' y' = true := by
    apply run_mono C.gates hao (List.ofFn x ++ List.ofFn y) (List.ofFn x' ++ List.ofFn y') (by simp)
    intro i hi
    by_cases h1 : i < N
    · rw [List.getD_append _ _ _ _ (by simp [h1])] at hi ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
      simp only [h1, ↓reduceDIte, Option.getD_some] at hi ⊢
      exact hx ⟨i, h1⟩ hi
    · by_cases h2 : i < N + N
      · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi ⊢
        simp only [List.length_ofFn] at hi ⊢
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
        have hsub : i - N < N := by omega
        simp only [hsub, ↓reduceDIte, Option.getD_some] at hi ⊢
        exact hy ⟨i - N, hsub⟩ hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
        cases hi
  have wire_out_inc (p l : Fin N) (h : I p l) : wire C.output (one p) (one l) = true := by
    rw [wire_eq_cf]
    have hfun : Fin.append (one p) (one l) =
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) := by
      funext k
      refine Fin.addCases (fun a => ?_) (fun b => ?_) k
      · have hne : Fin.castAdd N a ≠ Fin.natAdd N l := by
          intro e
          have hv := congrArg Fin.val e
          change a.val = N + l.val at hv
          omega
        simp only [Fin.append_left, one, hne, or_false, Fin.castAdd_inj]
      · have hne : Fin.natAdd N b ≠ Fin.castAdd N p := by
          intro e
          have hv := congrArg Fin.val e
          change N + b.val = p.val at hv
          omega
        have hiff : Fin.natAdd N b = Fin.natAdd N l ↔ b = l := by
          constructor
          · intro e
            apply Fin.ext
            have hv := congrArg Fin.val e
            change N + b.val = N + l.val at hv
            omega
          · rintro rfl
            rfl
        simp only [Fin.append_right, one, hne, false_or, hiff]
    rw [hfun]
    exact hacc p l h
  have wire_out_zero (x : Fin N → Bool) : wire C.output x zero = false := by
    rw [wire_eq_cf]
    apply hsound (Fin.append x zero)
    · rw [Fintype.card_of_subtype (∅ : Finset (Fin N)) (by intro l; rw [Fin.append_right]; simp [zero])]
      simp
    · rintro ⟨p, l, _, _, hl⟩
      rw [Fin.append_right] at hl
      cases hl
  have wire_out_line (l : Fin N) : wire C.output (fun p => decide (¬ I p l)) (one l) = false := by
    rw [wire_eq_cf]
    apply hsound
    · rw [Fintype.card_of_subtype ({l} : Finset (Fin N)) (by intro r; rw [Fin.append_right]; simp [one])]
      simp
      omega
    · rintro ⟨p, r, hI, hp, hr⟩
      rw [Fin.append_left] at hp
      rw [Fin.append_right] at hr
      have hrl : r = l := of_decide_eq_true hr
      subst hrl
      exact (of_decide_eq_true hp) hI
  have wire_out_pt_avoid (p : Fin N) (y : Fin N → Bool)
      (hy : Fintype.card {l : Fin N // y l = true} ≤ q)
      (hno : ∀ l, y l = true → ¬ I p l) : wire C.output (one p) y = false := by
    rw [wire_eq_cf]
    apply hsound
    · simpa only [Fin.append_right] using hy
    · rintro ⟨r, l, hI, hr, hl⟩
      rw [Fin.append_left] at hr
      rw [Fin.append_right] at hl
      have hrp : r = p := of_decide_eq_true hr
      subst hrp
      exact hno l hl hI
  let gateOf (j : ℕ) : Gate := C.gates.getD j ⟨GateOp.or, []⟩
  let inA (j : ℕ) : ℕ := (gateOf j).inputs.getD 0 0
  let inB (j : ℕ) : ℕ := (gateOf j).inputs.getD 1 0
  let isOr (j : ℕ) : Bool := (gateOf j).op.eval [true, false]
  have gate_spec (j : ℕ) (hj : j < s) :
      C.gates[j]? = some (gateOf j) ∧
      (gateOf j).inputs = [inA j, inB j] ∧
      inA j < inB j ∧ inB j < m + j ∧
      ((isOr j = true ∧ (gateOf j).op = GateOp.or) ∨
       (isOr j = false ∧ (gateOf j).op = GateOp.and)) := by
    have hj' : j < C.gates.length := hj
    have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj'
    have hgd : gateOf j = C.gates[j] := by
      dsimp [gateOf]
      rw [List.getD_eq_getElem?_getD, hget]
      rfl
    have hget' : C.gates[j]? = some (gateOf j) := hgd ▸ hget
    obtain ⟨a, b, hab, hlt1, hlt2⟩ := hsorted j (gateOf j) hget'
    have ha : inA j = a := by simp [inA, hab]
    have hb : inB j = b := by simp [inB, hab]
    have hmem : gateOf j ∈ C.gates := by
      rw [hgd]
      exact List.getElem_mem hj'
    refine ⟨hget', by rw [ha, hb]; exact hab, by omega, by omega, ?_⟩
    rcases hao (gateOf j) hmem with hop | hop
    · right
      exact ⟨by dsimp [isOr]; rw [hop]; rfl, hop⟩
    · left
      exact ⟨by dsimp [isOr]; rw [hop]; rfl, hop⟩
  have wire_gate_eval (j : ℕ) (hj : j < s) (x y : Fin N → Bool) :
      wire (m + j) x y =
        if isOr j = true then wire (inA j) x y || wire (inB j) x y
        else wire (inA j) x y && wire (inB j) x y := by
    obtain ⟨hget, hins, hlt1, hlt2, hop⟩ := gate_spec j hj
    have hlen : (List.ofFn x ++ List.ofFn y).length = m := by simp [m]
    have hgd : C.gates[j] = gateOf j := by
      have := List.getElem?_eq_getElem (l := C.gates) (i := j) hj
      rw [hget] at this
      exact Option.some.inj this.symm
    have hearl : ∀ i ∈ C.gates[j].inputs, i < (List.ofFn x ++ List.ofFn y).length + j := by
      rw [hgd, hins, hlen]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    have hrg := run_gate C.gates (List.ofFn x ++ List.ofFn y) j hj hearl
    rw [hlen, hgd, hins] at hrg
    change (run C.gates (List.ofFn x ++ List.ofFn y)).getD (m + j) false = _
    rw [hrg]
    rcases hop with ⟨hor, hop'⟩ | ⟨hand, hop'⟩
    · rw [if_pos hor, hop']
      change ([wire (inA j) x y, wire (inB j) x y].any id) = (wire (inA j) x y || wire (inB j) x y)
      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
    · rw [if_neg (by rw [hand]; decide), hop']
      change ([wire (inA j) x y, wire (inB j) x y].all id) = (wire (inA j) x y && wire (inB j) x y)
      simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]
  let depLine (w : ℕ) : Prop := ∃ x : Fin N → Bool, wire w x zero ≠ wire w x allOne
  have pure_of_not_depLine (w : ℕ) (h : ¬ depLine w) (x y : Fin N → Bool) :
      wire w x y = wire w x zero := by
    have heq : wire w x zero = wire w x allOne := by
      by_contra hne
      exact h ⟨x, hne⟩
    rcases Bool.eq_false_or_eq_true (wire w x zero) with h0 | h0
    · exact (wire_mono w x x zero y (fun _ hp => hp) (fun _ hl => Bool.noConfusion hl) h0).trans h0.symm
    · rcases Bool.eq_false_or_eq_true (wire w x y) with hy | hy
      · have h1 : wire w x allOne = true :=
          wire_mono w x x y allOne (fun _ hp => hp) (fun _ _ => rfl) hy
        rw [h0, h1] at heq
        exact Bool.noConfusion heq
      · exact hy.trans h0.symm
  let Lcross : Finset ℕ := (Finset.range s).filter (fun j =>
    isOr j = false ∧ depLine (inA j) ∧ depLine (inB j))
  have hLcross_sub_range : Lcross ⊆ Finset.range s := Finset.filter_subset _ _
  have hLcross_spec (j : ℕ) (hj : j ∈ Lcross) :
      ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        ∀ w ∈ g.inputs, ∃ x : Fin N → Bool, wire w x (fun _ => false) ≠ wire w x (fun _ => true) := by
    obtain ⟨hr, hno, hdA, hdB⟩ := Finset.mem_filter.mp hj
    have hjs : j < s := Finset.mem_range.mp hr
    obtain ⟨hget, hins, _, _, hop⟩ := gate_spec j hjs
    have hand : (gateOf j).op = GateOp.and := by
      rcases hop with ⟨hor, _⟩ | ⟨_, hand⟩
      · rw [hor] at hno; cases hno
      · exact hand
    refine ⟨gateOf j, hget, hand, ?_⟩
    rw [hins]
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hdA
    · exact hdB
  have hLcross_sub_S : Lcross ⊆ S := by
    intro j hj
    obtain ⟨g, hget, hand, hdep⟩ := hLcross_spec j hj
    by_contra hnot
    apply hmarked j g hget hand hnot
    left
    intro w hw
    obtain ⟨x, hx⟩ := hdep w hw
    refine ⟨x, ?_⟩
    simpa only [wire, ofFn_const_eq] using hx
  have hLcross_small : 100 * Lcross.card < N * q :=
    (Nat.mul_le_mul_left 100 (Finset.card_le_card hLcross_sub_S)).trans_lt hSsmall
  let guard (j : ℕ) : ℕ := if ¬ depLine (inA j) then inA j else inB j
  let carr (j : ℕ) : ℕ := if ¬ depLine (inA j) then inB j else inA j
  have guard_spec (j : ℕ) (hj : j < s) (hand : isOr j = false) (hnot : j ∉ Lcross) :
      guard j < m + j ∧ carr j < m + j ∧
      (∀ x y : Fin N → Bool, wire (guard j) x y = wire (guard j) x zero) ∧
      (∀ x y : Fin N → Bool, wire (m + j) x y = (wire (guard j) x zero && wire (carr j) x y)) := by
    obtain ⟨_, _, hlt1, hlt2, _⟩ := gate_spec j hj
    have hnd : ¬ (depLine (inA j) ∧ depLine (inB j)) := by
      rintro ⟨hA, hB⟩
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hand, hA, hB⟩)
    by_cases hA : ¬ depLine (inA j)
    · have hg : guard j = inA j := if_pos hA
      have hc : carr j = inB j := if_pos hA
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro x y
        rw [hg]
        exact pure_of_not_depLine (inA j) hA x y
      · intro x y
        rw [wire_gate_eval j hj x y, hand, if_neg Bool.false_ne_true, hg, hc,
          pure_of_not_depLine (inA j) hA x y]
    · have hB : ¬ depLine (inB j) := by
        intro hdB
        exact hnd ⟨not_not.mp hA, hdB⟩
      have hg : guard j = inB j := if_neg hA
      have hc : carr j = inA j := if_neg hA
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro x y
        rw [hg]
        exact pure_of_not_depLine (inB j) hB x y
      · intro x y
        rw [wire_gate_eval j hj x y, hand, if_neg Bool.false_ne_true, hg, hc,
          pure_of_not_depLine (inB j) hB x y, Bool.and_comm]
  let stepT (x : Fin N → Bool) (t : ℕ → Bool) (j w : ℕ) : Bool :=
    if t (m + j) = true ∧ j < s ∧ j ∉ Lcross then
      if isOr j = true then
        t w || decide (w = inA j) || decide (w = inB j)
      else if wire (guard j) x zero = true then
        t w || decide (w = carr j)
      else t w
    else t w
  let Tstep (x : Fin N → Bool) : ℕ → (ℕ → Bool) :=
    Nat.rec (fun w => decide (w = C.output)) (fun k prev => stepT x prev (s - 1 - k))
  let T (w : ℕ) (x : Fin N → Bool) : Bool := Tstep x s w
  have stepT_preserve (x : Fin N → Bool) (t : ℕ → Bool) (j w : ℕ) (h : t w = true) :
      stepT x t j w = true := by
    dsimp [stepT]
    by_cases h1 : t (m + j) = true ∧ j < s ∧ j ∉ Lcross
    · rw [if_pos h1]
      by_cases h2 : isOr j = true
      · rw [if_pos h2]; simp [h]
      · rw [if_neg h2]
        by_cases h3 : wire (guard j) x zero = true
        · rw [if_pos h3]; simp [h]
        · rw [if_neg h3]; exact h
    · rw [if_neg h1]; exact h
  have stepT_ge (x : Fin N → Bool) (t : ℕ → Bool) (j w : ℕ) (hge : m + j ≤ w) :
      stepT x t j w = t w := by
    dsimp [stepT]
    by_cases h1 : t (m + j) = true ∧ j < s ∧ j ∉ Lcross
    · rw [if_pos h1]
      by_cases h2 : isOr j = true
      · rw [if_pos h2]
        obtain ⟨_, _, hlt1, hlt2, _⟩ := gate_spec j h1.2.1
        have hne1 : w ≠ inA j := by omega
        have hne2 : w ≠ inB j := by omega
        simp [hne1, hne2]
      · rw [if_neg h2]
        by_cases h3 : wire (guard j) x zero = true
        · rw [if_pos h3]
          have hand : isOr j = false := Bool.eq_false_iff.mpr h2
          obtain ⟨_, hltc, _, _⟩ := guard_spec j h1.2.1 hand h1.2.2
          have hne : w ≠ carr j := by omega
          simp [hne]
        · rw [if_neg h3]
    · rw [if_neg h1]
  have Tstep_mono_k (x : Fin N → Bool) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) (w : ℕ)
      (h : Tstep x k₁ w = true) : Tstep x k₂ w = true := by
    induction k₂ with
    | zero =>
      have : k₁ = 0 := by omega
      subst this
      exact h
    | succ k ih =>
      by_cases hle : k₁ ≤ k
      · exact stepT_preserve x (Tstep x k) (s - 1 - k) w (ih hle)
      · have : k₁ = k + 1 := by omega
        subst this
        exact h
  have Tstep_frozen (x : Fin N → Bool) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) (hk2 : k₂ ≤ s)
      (w : ℕ) (hw : m + (s - 1 - k₁) ≤ w) : Tstep x k₂ w = Tstep x k₁ w := by
    induction k₂ with
    | zero =>
      have : k₁ = 0 := by omega
      subst this
      rfl
    | succ k ih =>
      by_cases hle : k₁ ≤ k
      · change stepT x (Tstep x k) (s - 1 - k) w = Tstep x k₁ w
        rw [stepT_ge x (Tstep x k) (s - 1 - k) w (by omega)]
        exact ih hle (by omega)
      · have : k₁ = k + 1 := by omega
        subst this
        rfl
  have Tstep_at_gate (x : Fin N → Bool) (j : ℕ) (hj : j < s) :
      Tstep x (s - 1 - j) (m + j) = T (m + j) x := by
    dsimp [T]
    have h1 := Tstep_frozen x (s - 1 - j) s (by omega) le_rfl (m + j) (by omega)
    exact h1.symm
  have Tstep_iff (x : Fin N → Bool) (k : ℕ) (hk : k ≤ s) (w : ℕ) :
      Tstep x k w = true ↔
        w = C.output ∨
        ∃ j, s - k ≤ j ∧ j < s ∧ j ∉ Lcross ∧ T (m + j) x = true ∧
          ((isOr j = true ∧ (w = inA j ∨ w = inB j)) ∨
           (isOr j = false ∧ w = carr j ∧ wire (guard j) x zero = true)) := by
    induction k with
    | zero =>
      change decide (w = C.output) = true ↔ _
      simp only [decide_eq_true_eq, Nat.sub_zero]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨j, h1, h2, _⟩)
        · exact h
        · omega
    | succ k ih =>
      have hk' : k ≤ s := by omega
      let j0 : ℕ := s - 1 - k
      have hj0 : j0 < s := by dsimp [j0]; omega
      have hsub : s - (k + 1) = j0 := by dsimp [j0]; omega
      have hfrozen : Tstep x k (m + j0) = T (m + j0) x := by
        have : k = s - 1 - j0 := by dsimp [j0]; omega
        rw [this]
        exact Tstep_at_gate x j0 hj0
      change stepT x (Tstep x k) j0 w = true ↔ _
      rw [hsub]
      constructor
      · intro h
        dsimp [stepT] at h
        rcases Classical.em (Tstep x k (m + j0) = true ∧ j0 < s ∧ j0 ∉ Lcross) with h1 | h1
        · rw [if_pos h1] at h
          by_cases h2 : isOr j0 = true
          · rw [if_pos h2] at h
            simp only [Bool.or_eq_true, decide_eq_true_eq] at h
            rcases h with (ht | hA) | hB
            · rcases (ih hk').mp ht with rfl | ⟨j, hge, hjs, hnot, hT, hbr⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨j, by omega, hjs, hnot, hT, hbr⟩
            · exact Or.inr ⟨j0, le_rfl, hj0, h1.2.2, hfrozen ▸ h1.1, Or.inl ⟨h2, Or.inl hA⟩⟩
            · exact Or.inr ⟨j0, le_rfl, hj0, h1.2.2, hfrozen ▸ h1.1, Or.inl ⟨h2, Or.inr hB⟩⟩
          · rw [if_neg h2] at h
            by_cases h3 : wire (guard j0) x zero = true
            · rw [if_pos h3] at h
              simp only [Bool.or_eq_true, decide_eq_true_eq] at h
              rcases h with ht | hC
              · rcases (ih hk').mp ht with rfl | ⟨j, hge, hjs, hnot, hT, hbr⟩
                · exact Or.inl rfl
                · exact Or.inr ⟨j, by omega, hjs, hnot, hT, hbr⟩
              · exact Or.inr ⟨j0, le_rfl, hj0, h1.2.2, hfrozen ▸ h1.1,
                  Or.inr ⟨Bool.eq_false_iff.mpr h2, hC, h3⟩⟩
            · rw [if_neg h3] at h
              rcases (ih hk').mp h with rfl | ⟨j, hge, hjs, hnot, hT, hbr⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨j, by omega, hjs, hnot, hT, hbr⟩
        · rw [if_neg h1] at h
          rcases (ih hk').mp h with rfl | ⟨j, hge, hjs, hnot, hT, hbr⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨j, by omega, hjs, hnot, hT, hbr⟩
      · rintro (rfl | ⟨j, hge, hjs, hnot, hT, hbr⟩)
        · exact stepT_preserve x (Tstep x k) j0 C.output ((ih hk').mpr (Or.inl rfl))
        · by_cases heq : j = j0
          · subst heq
            have h1 : Tstep x k (m + j0) = true ∧ j0 < s ∧ j0 ∉ Lcross :=
              ⟨hfrozen.symm ▸ hT, hj0, hnot⟩
            dsimp [stepT]
            rw [if_pos h1]
            rcases hbr with ⟨hor, hw⟩ | ⟨hand, hw, hg⟩
            · rw [if_pos hor]
              rcases hw with rfl | rfl <;> simp
            · rw [if_neg (by rw [hand]; decide), if_pos hg]
              simp [hw]
          · have hgt : s - k ≤ j := by dsimp [j0] at hge heq; omega
            exact stepT_preserve x (Tstep x k) j0 w ((ih hk').mpr (Or.inr ⟨j, hgt, hjs, hnot, hT, hbr⟩))
  have T_iff (x : Fin N → Bool) (w : ℕ) :
      T w x = true ↔
        w = C.output ∨
        ∃ j < s, j ∉ Lcross ∧ T (m + j) x = true ∧
          ((isOr j = true ∧ (w = inA j ∨ w = inB j)) ∨
           (isOr j = false ∧ w = carr j ∧ wire (guard j) x zero = true)) := by
    have h := Tstep_iff x s le_rfl w
    simp only [Nat.sub_self, Nat.zero_le, true_and] at h
    exact h
  have T_mono (x x' : Fin N → Bool) (hx : ∀ p, x p = true → x' p = true) :
      ∀ k w, Tstep x k w = true → Tstep x' k w = true := by
    intro k
    induction k with
    | zero =>
      intro w hw
      exact hw
    | succ k ih =>
      intro w hw
      let j0 : ℕ := s - 1 - k
      change stepT x (Tstep x k) j0 w = true at hw
      change stepT x' (Tstep x' k) j0 w = true
      dsimp [stepT] at hw ⊢
      rcases Classical.em (Tstep x k (m + j0) = true ∧ j0 < s ∧ j0 ∉ Lcross) with h1 | h1
      · rw [if_pos h1] at hw
        have h1' : Tstep x' k (m + j0) = true ∧ j0 < s ∧ j0 ∉ Lcross :=
          ⟨ih (m + j0) h1.1, h1.2.1, h1.2.2⟩
        rw [if_pos h1']
        by_cases h2 : isOr j0 = true
        · rw [if_pos h2] at hw ⊢
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hw ⊢
          rcases hw with (ht | hA) | hB
          · exact Or.inl (Or.inl (ih w ht))
          · exact Or.inl (Or.inr hA)
          · exact Or.inr hB
        · rw [if_neg h2] at hw ⊢
          by_cases h3 : wire (guard j0) x zero = true
          · rw [if_pos h3] at hw
            have h3' : wire (guard j0) x' zero = true :=
              wire_mono (guard j0) x x' zero zero hx (fun _ h => h) h3
            rw [if_pos h3']
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hw ⊢
            rcases hw with ht | hC
            · exact Or.inl (ih w ht)
            · exact Or.inr hC
          · rw [if_neg h3] at hw
            by_cases h3' : wire (guard j0) x' zero = true
            · rw [if_pos h3']; simp [ih w hw]
            · rw [if_neg h3']; exact ih w hw
      · rw [if_neg h1] at hw
        exact stepT_preserve x' (Tstep x' k) j0 w (ih w hw)
  have T_mono' (w : ℕ) (x x' : Fin N → Bool) (hx : ∀ p, x p = true → x' p = true) :
      T w x = true → T w x' = true :=
    T_mono x x' hx s w
  have T_sound (x y : Fin N → Bool) :
      ∀ k w, Tstep x k w = true → wire w x y = true → wire C.output x y = true := by
    intro k
    induction k with
    | zero =>
      intro w hw hwire
      have heq : w = C.output := of_decide_eq_true hw
      rwa [← heq]
    | succ k ih =>
      intro w hw hwire
      let j0 : ℕ := s - 1 - k
      change stepT x (Tstep x k) j0 w = true at hw
      dsimp [stepT] at hw
      rcases Classical.em (Tstep x k (m + j0) = true ∧ j0 < s ∧ j0 ∉ Lcross) with h1 | h1
      · rw [if_pos h1] at hw
        by_cases h2 : isOr j0 = true
        · rw [if_pos h2] at hw
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hw
          rcases hw with (ht | rfl) | rfl
          · exact ih w ht hwire
          · apply ih (m + j0) h1.1
            rw [wire_gate_eval j0 h1.2.1 x y, if_pos h2, hwire, Bool.true_or]
          · apply ih (m + j0) h1.1
            rw [wire_gate_eval j0 h1.2.1 x y, if_pos h2, hwire, Bool.or_true]
        · rw [if_neg h2] at hw
          by_cases h3 : wire (guard j0) x zero = true
          · rw [if_pos h3] at hw
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hw
            rcases hw with ht | rfl
            · exact ih w ht hwire
            · apply ih (m + j0) h1.1
              have hand : isOr j0 = false := Bool.eq_false_iff.mpr h2
              obtain ⟨_, _, _, heval⟩ := guard_spec j0 h1.2.1 hand h1.2.2
              rw [heval x y, h3, hwire]
              rfl
          · rw [if_neg h3] at hw
            exact ih w hw hwire
      · rw [if_neg h1] at hw
        exact ih w hw hwire
  have T_sound' (w : ℕ) (x y : Fin N → Bool) :
      T w x = true → wire w x y = true → wire C.output x y = true :=
    T_sound x y s w
  have T_complete_aux (x : Fin N → Bool) (l : Fin N) :
      ∀ w < m + s, T w x = true → wire w x (one l) = true → wire w x zero = false →
        T (N + l.val) x = true ∨ ∃ j ∈ Lcross, T (m + j) x = true ∧ wire (m + j) x (one l) = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hTw h1 h0
      by_cases hpt : w < N
      · have e1 := wire_pt ⟨w, hpt⟩ x (one l)
        have e0 := wire_pt ⟨w, hpt⟩ x zero
        change wire w x (one l) = x ⟨w, hpt⟩ at e1
        change wire w x zero = x ⟨w, hpt⟩ at e0
        rw [e1] at h1
        rw [e0] at h0
        rw [h1] at h0
        cases h0
      · by_cases hln : w < m
        · let r : Fin N := ⟨w - N, by omega⟩
          have hr : N + r.val = w := by dsimp [r]; omega
          have e1 := wire_ln r x (one l)
          rw [hr, h1] at e1
          have hrl : r = l := of_decide_eq_true e1.symm
          left
          rw [← hrl, hr]
          exact hTw
        · let j : ℕ := w - m
          have hjs : j < s := by omega
          have hmj : m + j = w := by dsimp [j]; omega
          rw [← hmj] at hTw h1 h0
          by_cases hmem : j ∈ Lcross
          · exact Or.inr ⟨j, hmem, hTw, h1⟩
          · obtain ⟨_, _, hlt1, hlt2, _⟩ := gate_spec j hjs
            by_cases hor : isOr j = true
            · rw [wire_gate_eval j hjs x (one l), if_pos hor] at h1
              rw [wire_gate_eval j hjs x zero, if_pos hor] at h0
              simp only [Bool.or_eq_false_iff] at h0
              simp only [Bool.or_eq_true] at h1
              rcases h1 with hA | hB
              · have hTA : T (inA j) x = true :=
                  (T_iff x (inA j)).mpr (Or.inr ⟨j, hjs, hmem, hTw, Or.inl ⟨hor, Or.inl rfl⟩⟩)
                exact ih (inA j) (by omega) (by omega) hTA hA h0.1
              · have hTB : T (inB j) x = true :=
                  (T_iff x (inB j)).mpr (Or.inr ⟨j, hjs, hmem, hTw, Or.inl ⟨hor, Or.inr rfl⟩⟩)
                exact ih (inB j) (by omega) (by omega) hTB hB h0.2
            · have hand : isOr j = false := Bool.eq_false_iff.mpr hor
              obtain ⟨_, hltc, _, heval⟩ := guard_spec j hjs hand hmem
              rw [heval x (one l)] at h1
              rw [heval x zero] at h0
              simp only [Bool.and_eq_true] at h1
              rw [h1.1, Bool.true_and] at h0
              have hTC : T (carr j) x = true :=
                (T_iff x (carr j)).mpr (Or.inr ⟨j, hjs, hmem, hTw, Or.inr ⟨hand, rfl, h1.1⟩⟩)
              exact ih (carr j) (by omega) (by omega) hTC h1.2 h0
  have T_complete (p l : Fin N) (hI : I p l) :
      T (N + l.val) (one p) = true ∨
        ∃ j ∈ Lcross, T (m + j) (one p) = true ∧ wire (m + j) (one p) (one l) = true := by
    apply T_complete_aux (one p) l C.output hout
    · exact (T_iff (one p) C.output).mpr (Or.inl rfl)
    · exact wire_out_inc p l hI
    · exact wire_out_zero (one p)
  let M : ℕ := m + s
  let idxT (w : ℕ) : ℕ := 2 * M - 1 - w
  let H (v : ℕ) (x : Fin N → Bool) : Bool :=
    if v < M then wire v x zero else T (2 * M - 1 - v) x
  have H_mono (v : ℕ) (x x' : Fin N → Bool) (hx : ∀ p, x p = true → x' p = true) :
      H v x = true → H v x' = true := by
    dsimp [H]
    split_ifs
    · exact wire_mono v x x' zero zero hx (fun _ h => h)
    · exact T_mono' (2 * M - 1 - v) x x' hx
  have H_idxT (w : ℕ) (hw : w < M) (x : Fin N → Bool) : H (idxT w) x = T w x := by
    have hge : ¬ idxT w < M := by dsimp [idxT]; omega
    have hinv : 2 * M - 1 - idxT w = w := by dsimp [idxT]; omega
    dsimp [H]
    rw [if_neg hge, hinv]
  let P (v : ℕ) : Finset (Fin N) := Finset.univ.filter (fun p => H v (one p) = true)
  let IncW (w : ℕ) : Finset (ℕ × Bool) :=
    ((Finset.range s) ×ˢ ({false, true} : Finset Bool)).filter (fun e =>
      e.1 ∉ Lcross ∧
      ((isOr e.1 = true ∧ ((e.2 = false ∧ inA e.1 = w) ∨ (e.2 = true ∧ inB e.1 = w))) ∨
       (isOr e.1 = false ∧ e.2 = false ∧ carr e.1 = w)))
  let cost (v : ℕ) : ℕ :=
    if v < m then 0
    else if v < M then (if isOr (v - m) = true then 1 else 0)
    else if v < 2 * M then (IncW (2 * M - 1 - v)).card
    else 0
  have cost_low_sum : (∑ v ∈ Finset.range M, cost v) ≤ s := by
    have hle : ∀ v ∈ Finset.range M, cost v ≤ if m ≤ v then 1 else 0 := by
      intro v hv
      have hvM : v < M := Finset.mem_range.mp hv
      dsimp [cost]
      by_cases hvm : v < m
      · simp [hvm]
      · have hge : m ≤ v := by omega
        simp only [hvm, ite_false, hvM, ite_true, hge]
        split_ifs <;> omega
    calc (∑ v ∈ Finset.range M, cost v)
        ≤ ∑ v ∈ Finset.range M, (if m ≤ v then 1 else 0) := Finset.sum_le_sum hle
      _ = ((Finset.range M).filter (fun v => m ≤ v)).card := by
          rw [Finset.sum_boole, Nat.cast_id]
      _ ≤ (Finset.Ico m M).card := by
          apply Finset.card_le_card
          intro v hv
          obtain ⟨hr, hge⟩ := Finset.mem_filter.mp hv
          exact Finset.mem_Ico.mpr ⟨hge, Finset.mem_range.mp hr⟩
      _ = s := by simp [M]
  have IncW_disjoint : (↑(Finset.range M) : Set ℕ).PairwiseDisjoint IncW := by
    intro w₁ _ w₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e h1 h2
    have c1 := (Finset.mem_filter.mp h1).2.2
    have c2 := (Finset.mem_filter.mp h2).2.2
    rcases c1 with ⟨hor1, ⟨hf1, hw1⟩ | ⟨ht1, hw1⟩⟩ | ⟨hand1, hf1, hw1⟩ <;>
      rcases c2 with ⟨hor2, ⟨hf2, hw2⟩ | ⟨ht2, hw2⟩⟩ | ⟨hand2, hf2, hw2⟩
    · exact hne (hw1.symm.trans hw2)
    · rw [hf1] at ht2; cases ht2
    · rw [hor1] at hand2; cases hand2
    · rw [ht1] at hf2; cases hf2
    · exact hne (hw1.symm.trans hw2)
    · rw [hor1] at hand2; cases hand2
    · rw [hand1] at hor2; cases hor2
    · rw [hand1] at hor2; cases hor2
    · exact hne (hw1.symm.trans hw2)
  have cost_high_sum : (∑ v ∈ Finset.Ico M (2 * M), cost v) ≤ 2 * s := by
    have hbij : ∑ v ∈ Finset.Ico M (2 * M), cost v = ∑ w ∈ Finset.range M, (IncW w).card := by
      refine Finset.sum_bij (fun v _ => 2 * M - 1 - v) ?_ ?_ ?_ ?_
      · intro v hv
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hv
        exact Finset.mem_range.mpr (by omega)
      · intro v₁ hv₁ v₂ hv₂ heq
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hv₁
        obtain ⟨h3, h4⟩ := Finset.mem_Ico.mp hv₂
        omega
      · intro w hw
        have hwM : w < M := Finset.mem_range.mp hw
        refine ⟨2 * M - 1 - w, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro v hv
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hv
        have hnm : ¬ v < m := by omega
        have hnM : ¬ v < M := by omega
        dsimp [cost]
        rw [if_neg hnm, if_neg hnM, if_pos h2]
    rw [hbij, ← Finset.card_biUnion IncW_disjoint]
    have hsub : (Finset.range M).biUnion IncW ⊆ (Finset.range s) ×ˢ ({false, true} : Finset Bool) := by
      intro e he
      obtain ⟨w, _, hwe⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp hwe).1
    exact (Finset.card_le_card hsub).trans (by simp; omega)
  have cost_total : (∑ v ∈ Finset.range (2 * M), cost v) ≤ 3 * s := by
    have hsplit : Finset.range (2 * M) = Finset.range M ∪ Finset.Ico M (2 * M) := by
      ext v
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range M) (Finset.Ico M (2 * M)) := by
      refine Finset.disjoint_left.mpr ?_
      intro v h1 h2
      have := Finset.mem_range.mp h1
      have := (Finset.mem_Ico.mp h2).1
      omega
    rw [hsplit, Finset.sum_union hdisj]
    omega
  have expand_node (z : Fin N → Bool) (v : ℕ) (hv : v < 2 * M)
      (hbig : 2 ≤ (P v).card) (hz : H v z = false) :
      ∃ Kids : Finset ℕ, Kids ⊆ Finset.range v ∧ (∀ u ∈ Kids, H u z = false) ∧
        P v ⊆ Kids.biUnion P ∧ Kids.card ≤ 1 + cost v := by
    by_cases hvm : v < m
    · exfalso
      have hcard1 : (P v).card ≤ 1 := by
        apply Finset.card_le_one_iff.mpr
        intro a b ha hb
        have ha' : wire v (one a) zero = true := by
          have := (Finset.mem_filter.mp ha).2
          simpa [H, show v < M by omega] using this
        have hb' : wire v (one b) zero = true := by
          have := (Finset.mem_filter.mp hb).2
          simpa [H, show v < M by omega] using this
        by_cases hpt : v < N
        · have ea := wire_pt ⟨v, hpt⟩ (one a) zero
          have eb := wire_pt ⟨v, hpt⟩ (one b) zero
          change wire v (one a) zero = one a ⟨v, hpt⟩ at ea
          change wire v (one b) zero = one b ⟨v, hpt⟩ at eb
          rw [ea] at ha'
          rw [eb] at hb'
          exact (of_decide_eq_true ha').symm.trans (of_decide_eq_true hb')
        · let r : Fin N := ⟨v - N, by omega⟩
          have hr : N + r.val = v := by dsimp [r]; omega
          have ea := wire_ln r (one a) zero
          rw [hr] at ea
          rw [ea] at ha'
          cases ha'
      omega
    · by_cases hvM : v < M
      · let j : ℕ := v - m
        have hjs : j < s := by omega
        have hvj : m + j = v := by dsimp [j]; omega
        obtain ⟨_, _, hlt1, hlt2, _⟩ := gate_spec j hjs
        have hz' : wire (m + j) z zero = false := by
          have hH : H v z = wire v z zero := if_pos hvM
          rw [hH] at hz
          rwa [hvj]
        by_cases hor : isOr j = true
        · rw [wire_gate_eval j hjs z zero, if_pos hor] at hz'
          simp only [Bool.or_eq_false_iff] at hz'
          refine ⟨{inA j, inB j}, ?_, ?_, ?_, ?_⟩
          · intro u hu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            exact Finset.mem_range.mpr (by rcases hu with rfl | rfl <;> omega)
          · intro u hu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl
            · dsimp [H]; rw [if_pos (by omega)]; exact hz'.1
            · dsimp [H]; rw [if_pos (by omega)]; exact hz'.2
          · intro p hp
            have hp' : wire (m + j) (one p) zero = true := by
              have := (Finset.mem_filter.mp hp).2
              simpa [H, hvM, hvj] using this
            rw [wire_gate_eval j hjs (one p) zero, if_pos hor] at hp'
            simp only [Bool.or_eq_true] at hp'
            rcases hp' with hA | hB
            · exact Finset.mem_biUnion.mpr ⟨inA j, by simp,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [H]; rw [if_pos (by omega)]; exact hA⟩⟩
            · exact Finset.mem_biUnion.mpr ⟨inB j, by simp,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [H]; rw [if_pos (by omega)]; exact hB⟩⟩
          · have hc : cost v = 1 := by
              dsimp [cost]
              rw [if_neg hvm, if_pos hvM]
              change (if isOr j = true then 1 else 0) = 1
              rw [if_pos hor]
            rw [hc]
            exact Finset.card_le_two
        · rw [wire_gate_eval j hjs z zero, if_neg hor] at hz'
          simp only [Bool.and_eq_false_iff] at hz'
          have hpick : ∃ u, (u = inA j ∨ u = inB j) ∧ wire u z zero = false := by
            rcases hz' with hA | hB
            · exact ⟨inA j, Or.inl rfl, hA⟩
            · exact ⟨inB j, Or.inr rfl, hB⟩
          obtain ⟨u, huab, huz⟩ := hpick
          have hu_lt : u < v := by rcases huab with rfl | rfl <;> omega
          refine ⟨{u}, ?_, ?_, ?_, ?_⟩
          · intro t ht
            rw [Finset.mem_singleton.mp ht]
            exact Finset.mem_range.mpr hu_lt
          · intro t ht
            rw [Finset.mem_singleton.mp ht]
            dsimp [H]
            rw [if_pos (by omega)]
            exact huz
          · intro p hp
            have hp' : wire (m + j) (one p) zero = true := by
              have := (Finset.mem_filter.mp hp).2
              simpa [H, hvM, hvj] using this
            rw [wire_gate_eval j hjs (one p) zero, if_neg hor] at hp'
            simp only [Bool.and_eq_true] at hp'
            have hpu : wire u (one p) zero = true := by
              rcases huab with rfl | rfl
              · exact hp'.1
              · exact hp'.2
            exact Finset.mem_biUnion.mpr ⟨u, by simp,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [H]; rw [if_pos (by omega)]; exact hpu⟩⟩
          · simp
      · let w : ℕ := 2 * M - 1 - v
        have hwM : w < M := by omega
        have hTz : T w z = false := by
          dsimp [H] at hz
          rw [if_neg hvM] at hz
          exact hz
        have hw_ne_out : w ≠ C.output := by
          intro heq
          have h1 : T w z = true := (T_iff z w).mpr (Or.inl heq)
          rw [h1] at hTz
          cases hTz
        let pick (e : ℕ × Bool) : ℕ :=
          if isOr e.1 = true then idxT (m + e.1)
          else if wire (guard e.1) z zero = false then guard e.1
          else idxT (m + e.1)
        refine ⟨(IncW w).image pick, ?_, ?_, ?_, ?_⟩
        · intro u hu
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨hprod, hnot, hcase⟩ := Finset.mem_filter.mp he
          have hes : e.1 < s := Finset.mem_range.mp (Finset.mem_product.mp hprod).1
          obtain ⟨_, _, hlt1, hlt2, _⟩ := gate_spec e.1 hes
          dsimp [pick]
          split_ifs with h1 h2
          · have hltw : w < m + e.1 := by
              rcases hcase with ⟨_, ⟨_, hw1⟩ | ⟨_, hw1⟩⟩ | ⟨hand, _, _⟩
              · omega
              · omega
              · rw [h1] at hand; cases hand
            exact Finset.mem_range.mpr (by dsimp [idxT, w] at *; omega)
          · have hand : isOr e.1 = false := Bool.eq_false_iff.mpr h1
            obtain ⟨hltg, _, _, _⟩ := guard_spec e.1 hes hand hnot
            exact Finset.mem_range.mpr (by omega)
          · have hand : isOr e.1 = false := Bool.eq_false_iff.mpr h1
            obtain ⟨_, hltc, _, _⟩ := guard_spec e.1 hes hand hnot
            have hwc : carr e.1 = w := by
              rcases hcase with ⟨hor, _⟩ | ⟨_, _, hwc⟩
              · exact absurd hor h1
              · exact hwc
            exact Finset.mem_range.mpr (by dsimp [idxT, w] at *; omega)
        · intro u hu
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨hprod, hnot, hcase⟩ := Finset.mem_filter.mp he
          have hes : e.1 < s := Finset.mem_range.mp (Finset.mem_product.mp hprod).1
          dsimp [pick]
          split_ifs with h1 h2
          · rw [H_idxT (m + e.1) (by omega) z]
            rcases Bool.eq_false_or_eq_true (T (m + e.1) z) with hT1 | hT1
            · exfalso
              have hTw : T w z = true := by
                apply (T_iff z w).mpr
                right
                refine ⟨e.1, hes, hnot, hT1, Or.inl ⟨h1, ?_⟩⟩
                rcases hcase with ⟨_, ⟨_, hw1⟩ | ⟨_, hw1⟩⟩ | ⟨hand, _, _⟩
                · exact Or.inl hw1.symm
                · exact Or.inr hw1.symm
                · rw [h1] at hand; exact Bool.noConfusion hand
              rw [hTw] at hTz
              exact Bool.noConfusion hTz
            · exact hT1
          · have hand : isOr e.1 = false := Bool.eq_false_iff.mpr h1
            obtain ⟨hltg, _, _, _⟩ := guard_spec e.1 hes hand hnot
            dsimp [H]
            rw [if_pos (by omega)]
            exact h2
          · rw [H_idxT (m + e.1) (by omega) z]
            have hand : isOr e.1 = false := Bool.eq_false_iff.mpr h1
            have hgtrue : wire (guard e.1) z zero = true := Bool.eq_true_of_not_eq_false h2
            have hwc : carr e.1 = w := by
              rcases hcase with ⟨hor, _⟩ | ⟨_, _, hwc⟩
              · exact absurd hor h1
              · exact hwc
            rcases Bool.eq_false_or_eq_true (T (m + e.1) z) with hT1 | hT1
            · exfalso
              have hTw : T w z = true :=
                (T_iff z w).mpr (Or.inr ⟨e.1, hes, hnot, hT1, Or.inr ⟨hand, hwc.symm, hgtrue⟩⟩)
              rw [hTw] at hTz
              exact Bool.noConfusion hTz
            · exact hT1
        · intro p hp
          have hTp : T w (one p) = true := by
            have := (Finset.mem_filter.mp hp).2
            dsimp [H] at this
            rw [if_neg hvM] at this
            exact this
          rcases (T_iff (one p) w).mp hTp with heq | ⟨j, hjs, hnot, hTj, hbr⟩
          · exact absurd heq hw_ne_out
          · rcases hbr with ⟨hor, hwA | hwB⟩ | ⟨hand, hwC, hgp⟩
            · have he : (j, false) ∈ IncW w := by
                refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hjs, by simp⟩,
                  hnot, Or.inl ⟨hor, Or.inl ⟨rfl, hwA.symm⟩⟩⟩
              refine Finset.mem_biUnion.mpr ⟨pick (j, false), Finset.mem_image.mpr ⟨_, he, rfl⟩, ?_⟩
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              dsimp [pick]
              rw [if_pos hor, H_idxT (m + j) (by omega) (one p)]
              exact hTj
            · have he : (j, true) ∈ IncW w := by
                refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hjs, by simp⟩,
                  hnot, Or.inl ⟨hor, Or.inr ⟨rfl, hwB.symm⟩⟩⟩
              refine Finset.mem_biUnion.mpr ⟨pick (j, true), Finset.mem_image.mpr ⟨_, he, rfl⟩, ?_⟩
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              dsimp [pick]
              rw [if_pos hor, H_idxT (m + j) (by omega) (one p)]
              exact hTj
            · have he : (j, false) ∈ IncW w := by
                refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hjs, by simp⟩,
                  hnot, Or.inr ⟨hand, rfl, hwC.symm⟩⟩
              refine Finset.mem_biUnion.mpr ⟨pick (j, false), Finset.mem_image.mpr ⟨_, he, rfl⟩, ?_⟩
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              obtain ⟨hltg, _, _, _⟩ := guard_spec j hjs hand hnot
              dsimp [pick]
              rw [if_neg (by rw [hand]; decide)]
              split_ifs with hgz
              · dsimp [H]
                rw [if_pos (by omega)]
                exact hgp
              · rw [H_idxT (m + j) (by omega) (one p)]
                exact hTj
        · have hc : cost v = (IncW w).card := by
            dsimp [cost]
            rw [if_neg hvm, if_neg hvM, if_pos hv]
          rw [hc]
          exact Finset.card_image_le.trans (Nat.le_add_left _ _)
  have budget (z : Fin N → Bool) : ∀ n ≤ 2 * M, ∀ R : Finset ℕ,
      R ⊆ Finset.range n → (∀ v ∈ R, H v z = false) →
      (R.biUnion P).card ≤ R.card +
        ∑ v ∈ (Finset.range n).filter (fun v => 2 ≤ (P v).card ∧ H v z = false), cost v := by
    intro n
    induction n with
    | zero =>
      intro _ R hsub _
      have hR : R = ∅ := Finset.subset_empty.mp (by simpa using hsub)
      subst hR
      simp
    | succ n ih =>
      intro hn R hsub hRz
      let filt (k : ℕ) : Finset ℕ :=
        (Finset.range k).filter (fun v => 2 ≤ (P v).card ∧ H v z = false)
      have hmono_filt : filt n ⊆ filt (n + 1) := by
        intro v hv
        obtain ⟨hr, h2, hhz⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hr)), h2, hhz⟩
      have hsum_mono : (∑ v ∈ filt n, cost v) ≤ ∑ v ∈ filt (n + 1), cost v :=
        Finset.sum_le_sum_of_subset hmono_filt
      by_cases htop : n ∈ R
      · let R' := R.erase n
        have hR'sub : R' ⊆ Finset.range n := by
          intro v hv
          obtain ⟨hne, hvR⟩ := Finset.mem_erase.mp hv
          have hvlt := Finset.mem_range.mp (hsub hvR)
          exact Finset.mem_range.mpr (by omega)
        have hR'z : ∀ v ∈ R', H v z = false := fun v hv => hRz v (Finset.mem_erase.mp hv).2
        have hcardR' : R'.card + 1 = R.card := Finset.card_erase_add_one htop
        by_cases hbig : 2 ≤ (P n).card
        · obtain ⟨Kids, hKsub, hKz, hKcov, hKcard⟩ := expand_node z n (by omega) hbig (hRz n htop)
          let Rnew := Kids ∪ R'
          have hRnew_sub : Rnew ⊆ Finset.range n := Finset.union_subset hKsub hR'sub
          have hRnew_z : ∀ v ∈ Rnew, H v z = false := by
            intro v hv
            rcases Finset.mem_union.mp hv with h1 | h2
            · exact hKz v h1
            · exact hR'z v h2
          have hcov : R.biUnion P ⊆ Rnew.biUnion P := by
            intro p hp
            obtain ⟨v, hvR, hpv⟩ := Finset.mem_biUnion.mp hp
            by_cases hvn : v = n
            · subst hvn
              obtain ⟨u, huK, hpu⟩ := Finset.mem_biUnion.mp (hKcov hpv)
              exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_union_left _ huK, hpu⟩
            · exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hvn, hvR⟩), hpv⟩
          have hfilt_succ : filt (n + 1) = insert n (filt n) := by
            ext v
            simp only [filt, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
            constructor
            · rintro ⟨hlt, h2, hhz⟩
              by_cases hvn : v = n
              · exact Or.inl hvn
              · exact Or.inr ⟨by omega, h2, hhz⟩
            · rintro (hv | ⟨hlt, h2, hhz⟩)
              · rw [hv]
                exact ⟨Nat.lt_succ_self n, hbig, hRz n htop⟩
              · exact ⟨by omega, h2, hhz⟩
          have hnotmem : n ∉ filt n := by simp [filt]
          have hsum_succ : (∑ v ∈ filt (n + 1), cost v) = cost n + ∑ v ∈ filt n, cost v := by
            rw [hfilt_succ, Finset.sum_insert hnotmem]
          have hRnew_card : Rnew.card ≤ R.card + cost n := by
            have := Finset.card_union_le Kids R'
            dsimp only [Rnew]
            omega
          have hih := ih (by omega) Rnew hRnew_sub hRnew_z
          have hbi := Finset.card_le_card hcov
          change (R.biUnion P).card ≤ R.card + ∑ v ∈ filt (n + 1), cost v
          change (Rnew.biUnion P).card ≤ Rnew.card + ∑ v ∈ filt n, cost v at hih
          omega
        · have hih := ih (by omega) R' hR'sub hR'z
          have hins : R.biUnion P = P n ∪ R'.biUnion P := by
            rw [← Finset.insert_erase htop, Finset.biUnion_insert]
          have hbi : (R.biUnion P).card ≤ (P n).card + (R'.biUnion P).card := by
            rw [hins]
            exact Finset.card_union_le _ _
          change (R.biUnion P).card ≤ R.card + ∑ v ∈ filt (n + 1), cost v
          change (R'.biUnion P).card ≤ R'.card + ∑ v ∈ filt n, cost v at hih
          omega
      · have hRsub : R ⊆ Finset.range n := by
          intro v hv
          have hne : v ≠ n := fun heq => htop (heq ▸ hv)
          have hlt := Finset.mem_range.mp (hsub hv)
          exact Finset.mem_range.mpr (by omega)
        have hih := ih (by omega) R hRsub hRz
        change (R.biUnion P).card ≤ R.card + ∑ v ∈ filt (n + 1), cost v
        change (R.biUnion P).card ≤ R.card + ∑ v ∈ filt n, cost v at hih
        omega
  let zL (l : Fin N) : Fin N → Bool := fun p => decide (¬ I p l)
  have P_sub_line (l : Fin N) (v : ℕ) (hz : H v (zL l) = false) (p : Fin N) (hp : p ∈ P v) : I p l := by
    by_contra hno
    have hHp : H v (one p) = true := (Finset.mem_filter.mp hp).2
    have hHz : H v (zL l) = true := by
      apply H_mono v (one p) (zL l) _ hHp
      intro r hr
      have hrp : r = p := of_decide_eq_true hr
      subst hrp
      exact decide_eq_true hno
    rw [hHz] at hz
    cases hz
  let Charged (l : Fin N) : Finset ℕ :=
    (Finset.range (2 * M)).filter (fun v => 2 ≤ (P v).card ∧ H v (zL l) = false)
  have Charged_disjoint : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint Charged := by
    intro l₁ _ l₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    intro v h1 h2
    obtain ⟨_, hbig, hz1⟩ := Finset.mem_filter.mp h1
    obtain ⟨_, _, hz2⟩ := Finset.mem_filter.mp h2
    obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := Finset.one_lt_card.mp hbig
    have hl1 : I p₁ l₁ ∧ I p₂ l₁ := ⟨P_sub_line l₁ v hz1 p₁ hp₁, P_sub_line l₁ v hz1 p₂ hp₂⟩
    have hl2 : I p₁ l₂ ∧ I p₂ l₂ := ⟨P_sub_line l₂ v hz2 p₁ hp₁, P_sub_line l₂ v hz2 p₂ hp₂⟩
    exact hne ((huniq p₁ p₂ hpne).unique hl1 hl2)
  have sum_Charged_cost : (∑ l : Fin N, ∑ v ∈ Charged l, cost v) ≤ 3 * s := by
    rw [← Finset.sum_biUnion Charged_disjoint]
    have hsub : Finset.univ.biUnion Charged ⊆ Finset.range (2 * M) := by
      intro v hv
      obtain ⟨l, _, hvl⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_filter.mp hvl).1
    exact (Finset.sum_le_sum_of_subset hsub).trans cost_total
  let KA (l : Fin N) : Finset ℕ :=
    Lcross.filter (fun j => 2 ≤ (P (idxT (m + j))).card ∧ H (idxT (m + j)) (zL l) = false)
  have KA_disjoint : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint KA := by
    intro l₁ _ l₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    intro j h1 h2
    obtain ⟨hj, hbig, hz1⟩ := Finset.mem_filter.mp h1
    obtain ⟨_, _, hz2⟩ := Finset.mem_filter.mp h2
    obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := Finset.one_lt_card.mp hbig
    have hl1 : I p₁ l₁ ∧ I p₂ l₁ :=
      ⟨P_sub_line l₁ (idxT (m + j)) hz1 p₁ hp₁, P_sub_line l₁ (idxT (m + j)) hz1 p₂ hp₂⟩
    have hl2 : I p₁ l₂ ∧ I p₂ l₂ :=
      ⟨P_sub_line l₂ (idxT (m + j)) hz2 p₁ hp₁, P_sub_line l₂ (idxT (m + j)) hz2 p₂ hp₂⟩
    exact hne ((huniq p₁ p₂ hpne).unique hl1 hl2)
  have sum_KA_card : (∑ l : Fin N, (KA l).card) ≤ s := by
    rw [← Finset.card_biUnion KA_disjoint]
    have hsub : Finset.univ.biUnion KA ⊆ Finset.range s := by
      intro j hj
      obtain ⟨l, _, hjl⟩ := Finset.mem_biUnion.mp hj
      exact hLcross_sub_range (Finset.mem_filter.mp hjl).1
    exact (Finset.card_le_card hsub).trans (by simp)
  let RL (l : Fin N) : Finset ℕ :=
    insert (idxT (N + l.val)) ((KA l).image (fun j => idxT (m + j)))
  have T_line_false (l : Fin N) : T (N + l.val) (zL l) = false := by
    rcases Bool.eq_false_or_eq_true (T (N + l.val) (zL l)) with hTt | hTt
    · exfalso
      have hwl : wire (N + l.val) (zL l) (one l) = true := by
        rw [wire_ln l (zL l) (one l)]
        simp [one]
      have hout_t := T_sound' (N + l.val) (zL l) (one l) hTt hwl
      have hout_f := wire_out_line l
      rw [hout_t] at hout_f
      exact Bool.noConfusion hout_f
    · exact hTt
  have RL_budget (l : Fin N) : ((RL l).biUnion P).card ≤ (RL l).card + ∑ v ∈ Charged l, cost v := by
    apply budget (zL l) (2 * M) le_rfl (RL l)
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | himg
      · exact Finset.mem_range.mpr (by dsimp [idxT, M, m]; omega)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp himg
        have hjs : j < s := Finset.mem_range.mp (hLcross_sub_range (Finset.mem_filter.mp hj).1)
        exact Finset.mem_range.mpr (by dsimp [idxT, M, m]; omega)
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | himg
      · rw [H_idxT (N + l.val) (by dsimp [M, m]; omega) (zL l)]
        exact T_line_false l
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp himg
        exact (Finset.mem_filter.mp hj).2.2
  have sum_RL_card : (∑ l : Fin N, (RL l).card) ≤ N + s := by
    have h1 : ∀ l : Fin N, (RL l).card ≤ 1 + (KA l).card := by
      intro l
      have hc1 := Finset.card_insert_le (idxT (N + l.val)) ((KA l).image (fun j => idxT (m + j)))
      have hc2 : ((KA l).image (fun j => idxT (m + j))).card ≤ (KA l).card := Finset.card_image_le
      dsimp only [RL]
      omega
    calc (∑ l : Fin N, (RL l).card)
        ≤ ∑ l : Fin N, (1 + (KA l).card) := Finset.sum_le_sum (fun l _ => h1 l)
      _ = (∑ _l : Fin N, 1) + ∑ l : Fin N, (KA l).card := Finset.sum_add_distrib
      _ = N + ∑ l : Fin N, (KA l).card := by simp
      _ ≤ N + s := Nat.add_le_add_left sum_KA_card N
  let CoveredDA : Finset (Fin N × Fin N) :=
    Finset.univ.biUnion (fun l : Fin N => ((RL l).biUnion P).image (fun p => (p, l)))
  have CoveredDA_card : CoveredDA.card ≤ N + 4 * s := by
    calc CoveredDA.card
        ≤ ∑ l : Fin N, (((RL l).biUnion P).image (fun p => (p, l))).card := Finset.card_biUnion_le
      _ ≤ ∑ l : Fin N, ((RL l).biUnion P).card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ ≤ ∑ l : Fin N, ((RL l).card + ∑ v ∈ Charged l, cost v) := Finset.sum_le_sum (fun l _ => RL_budget l)
      _ = (∑ l : Fin N, (RL l).card) + ∑ l : Fin N, ∑ v ∈ Charged l, cost v := Finset.sum_add_distrib
      _ ≤ (N + s) + 3 * s := Nat.add_le_add sum_RL_card sum_Charged_cost
      _ = N + 4 * s := by omega
  let B : Finset ℕ := Lcross.filter (fun j => (P (idxT (m + j))).card = 1)
  let owner (j : ℕ) : Fin N :=
    if h : (P (idxT (m + j))).Nonempty then Classical.choose h else ⟨0, hNpos⟩
  have owner_mem (j : ℕ) (hj : j ∈ B) : owner j ∈ P (idxT (m + j)) := by
    have hcard : (P (idxT (m + j))).card = 1 := (Finset.mem_filter.mp hj).2
    have hne : (P (idxT (m + j))).Nonempty := Finset.card_pos.mp (by omega)
    dsimp [owner]
    rw [dite_eq_left hne]
    exact Classical.choose_spec hne
  have owner_unique (j : ℕ) (hj : j ∈ B) (p : Fin N) (hp : p ∈ P (idxT (m + j))) : owner j = p := by
    have hcard : (P (idxT (m + j))).card ≤ 1 := by
      have := (Finset.mem_filter.mp hj).2
      omega
    exact Finset.card_le_one_iff.mp hcard (owner_mem j hj) hp
  have B_sub_range : B ⊆ Finset.range C.size :=
    (Finset.filter_subset _ _).trans hLcross_sub_range
  have B_spec (j : ℕ) (hj : j ∈ B) :
      ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        ∀ w ∈ g.inputs, ∃ x : Fin N → Bool, wire w x (fun _ => false) ≠ wire w x (fun _ => true) :=
    hLcross_spec j (Finset.mem_filter.mp hj).1
  have B_sound (j : ℕ) (hj : j ∈ B) (y : Fin N → Bool)
      (hy : Fintype.card {l : Fin N // y l = true} ≤ q)
      (hno : ∀ l, y l = true → ¬ I (owner j) l) :
      wire (N + N + j) (one (owner j)) y = false := by
    have hjs : j < s := Finset.mem_range.mp (B_sub_range hj)
    have hmem := owner_mem j hj
    have hHp : H (idxT (m + j)) (one (owner j)) = true := (Finset.mem_filter.mp hmem).2
    rw [H_idxT (m + j) (by dsimp [M]; omega) (one (owner j))] at hHp
    by_contra hne
    have hwt : wire (m + j) (one (owner j)) y = true := Bool.eq_true_of_not_eq_false hne
    have hout_t := T_sound' (m + j) (one (owner j)) y hHp hwt
    have hout_f := wire_out_pt_avoid (owner j) y hy hno
    rw [hout_t] at hout_f
    cases hout_f
  have B_small : 100 * B.card < N * q :=
    (Nat.mul_le_mul_left 100 (Finset.card_le_card (Finset.filter_subset _ _))).trans_lt hLcross_small
  let AllInc : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  have AllInc_card : AllInc.card = N * q + N := by
    have hbi : AllInc = Finset.univ.biUnion (fun l : Fin N =>
        (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
      ext ⟨p, l⟩
      simp [AllInc]
    have hdisj : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
        (fun l : Fin N => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
      intro l₁ _ l₂ _ hne
      refine Finset.disjoint_left.mpr ?_
      intro e h1 h2
      obtain ⟨p₁, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨p₂, _, heq⟩ := Finset.mem_image.mp h2
      exact hne (Prod.mk.inj heq).2.symm
    rw [hbi, Finset.card_biUnion hdisj]
    have hterm : ∀ l : Fin N, ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card = q + 1 := by
      intro l
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
      rw [← Fintype.card_subtype]
      exact hdeg l
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  let CoveredB : Finset (Fin N × Fin N) := AllInc.filter (fun e =>
    ∃ j ∈ B, owner j = e.1 ∧ wire (m + j) (one e.1) (one e.2) = true)
  let CoveredC : Finset (Fin N × Fin N) := AllInc.filter (fun e =>
    ∃ j ∈ Lcross, wire (m + j) (one e.1) (one e.2) = true ∧
      wire (m + j) (fun p => decide (¬ I p e.2)) (one e.2) = false)
  have AllInc_cover : AllInc ⊆ CoveredDA ∪ (CoveredB ∪ CoveredC) := by
    rintro ⟨p, l⟩ he
    have hI : I p l := (Finset.mem_filter.mp he).2
    rcases T_complete p l hI with hdir | ⟨j, hjL, hTj, hwij⟩
    · apply Finset.mem_union_left
      refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Finset.mem_image.mpr ⟨p, ?_, rfl⟩⟩
      refine Finset.mem_biUnion.mpr ⟨idxT (N + l.val), Finset.mem_insert_self _ _, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [H_idxT (N + l.val) (by dsimp [M, m]; omega) (one p)]
      exact hdir
    · have hjs : j < s := Finset.mem_range.mp (hLcross_sub_range hjL)
      have hpP : p ∈ P (idxT (m + j)) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [H_idxT (m + j) (by dsimp [M]; omega) (one p)]
        exact hTj
      rcases Bool.eq_false_or_eq_true (T (m + j) (zL l)) with hTz | hTz
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        refine Finset.mem_filter.mpr ⟨he, j, hjL, hwij, ?_⟩
        rcases Bool.eq_false_or_eq_true (wire (m + j) (zL l) (one l)) with hwt | hwf
        · exfalso
          have hout_t := T_sound' (m + j) (zL l) (one l) hTz hwt
          have hout_f := wire_out_line l
          rw [hout_t] at hout_f
          exact Bool.noConfusion hout_f
        · exact hwf
      · by_cases hbig : 2 ≤ (P (idxT (m + j))).card
        · apply Finset.mem_union_left
          refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Finset.mem_image.mpr ⟨p, ?_, rfl⟩⟩
          have hjKA : j ∈ KA l := by
            refine Finset.mem_filter.mpr ⟨hjL, hbig, ?_⟩
            rw [H_idxT (m + j) (by dsimp [M]; omega) (zL l)]
            exact hTz
          refine Finset.mem_biUnion.mpr ⟨idxT (m + j),
            Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hjKA, rfl⟩), hpP⟩
        · apply Finset.mem_union_right
          apply Finset.mem_union_left
          have hposP : 1 ≤ (P (idxT (m + j))).card := Finset.card_pos.mpr ⟨p, hpP⟩
          have hjB : j ∈ B := Finset.mem_filter.mpr ⟨hjL, by omega⟩
          exact Finset.mem_filter.mpr ⟨he, j, hjB, owner_unique j hjB p hpP, hwij⟩
  have htotal_ineq : N * q ≤ 4 * s + CoveredB.card + CoveredC.card := by
    have h1 := Finset.card_le_card AllInc_cover
    have h2 := Finset.card_union_le CoveredDA (CoveredB ∪ CoveredC)
    have h3 := Finset.card_union_le CoveredB CoveredC
    rw [AllInc_card] at h1
    omega
  by_cases hdone : N * q ≤ 100 * s
  · exact hdone
  · have hlt : 100 * s < N * q := by omega
    have h96 : 96 * (N * q) ≤ 100 * CoveredB.card + 100 * CoveredC.card := by omega
    by_cases hBcase : 48 * (N * q) ≤ 100 * CoveredB.card
    · have hBncard : CoveredB.card = {e : Fin N × Fin N | I e.1 e.2 ∧
          ∃ j ∈ B, owner j = e.1 ∧ wire (N + N + j) (one e.1) (one e.2) = true}.ncard := by
        rw [← Set.ncard_coe_finset CoveredB]
        congr 1
        ext e
        simp [CoveredB, AllInc, m]
      rw [hBncard] at hBcase
      exact pointFocused q N I C hq200ge hN hdeg huniq hmono wire_out_inc hsound B owner
        B_sub_range B_spec B_sound B_small hBcase
    · have hCcase : 48 * (N * q) ≤ 100 * CoveredC.card := by omega
      have hCncard : CoveredC.card = {e : Fin N × Fin N | I e.1 e.2 ∧
          ∃ j ∈ Lcross, wire (N + N + j) (one e.1) (one e.2) = true ∧
            wire (N + N + j) (fun p => decide (¬ I p e.2)) (one e.2) = false}.ncard := by
        rw [← Set.ncard_coe_finset CoveredC]
        congr 1
        ext e
        simp [CoveredC, AllInc, m]
      rw [hCncard] at hCcase
      exact lineSeparating q N I C hq200ge hN hdeg huniq hmono wire_out_inc hsound Lcross
        hLcross_sub_range hLcross_spec hLcross_small hCcase
