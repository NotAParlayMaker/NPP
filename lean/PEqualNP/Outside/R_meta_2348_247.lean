import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2348_247
    (core : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false ∧ ∃ j < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x9.getD (PEqualNP.TopForm.opnd x1 j 0) false = false ∧ x9.getD (PEqualNP.TopForm.opnd x1 j 1) false = false ∧ x8 (PEqualNP.TopForm.opnd x1 j 0) = true ∧ x8 (PEqualNP.TopForm.opnd x1 j 1) = true) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  intro C hsize hAO hdistinct hfirst hcomp hlin
  have hbase (b : Bool) :
      C.eval (List.ofFn (fun i : Fin 14 => decide (i = if b = true then (0 : Fin 14) else 7))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨p,l,_,hp,hl⟩ := (hcomp _).mp h
    cases b
    · have hp' : (Fin.castAdd 7 p : Fin 14) = 7 := by simpa using hp
      have hv := congrArg Fin.val hp'
      simp [Fin.castAdd] at hv
      omega
    · have hl' : (Fin.natAdd 7 l : Fin 14) = 0 := by simpa using hl
      have hv := congrArg Fin.val hl'
      simp [Fin.natAdd] at hv <;> omega
  have hpair : C.eval (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) = true := by
    apply (hcomp _).mpr
    exact ⟨0, 0, Or.inl rfl, by decide, by decide⟩
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have stepWire_eq (w : List Bool) (g : Gate) :
      stepWire w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl
  let runWires (gs : List Gate) (init : List Bool) : List Bool := gs.foldl stepWire init
  have getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false =
        if i < w.length then w.getD i false
        else if i = w.length then b
        else false := by
    simp only [List.getD_eq_getElem?_getD]
    by_cases h1 : i < w.length
    · rw [ite_eq_left h1, List.getElem?_append_left h1]
    · rw [ite_eq_right h1]
      by_cases h2 : i = w.length
      · subst h2
        rw [ite_eq_left rfl, List.getElem?_append_right (Nat.le_refl _)]
        simp
      · rw [ite_eq_right h2, List.getElem?_eq_none]
        · rfl
        · simp only [List.length_append, List.length_singleton]
          omega
  
  have getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
      w.getD i false = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    rfl
  
  have runWires_len (gs : List Gate) (init : List Bool) :
      (runWires gs init).length = init.length + gs.length := by
    induction gs generalizing init with
    | nil => simp [runWires]
    | cons g gs ih =>
      change (runWires gs (stepWire init g)).length = init.length + (gs.length + 1)
      rw [ih, stepWire_eq, List.length_append, List.length_singleton]
      omega
  
  have runWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
      (hi : i < init.length) :
      (runWires gs init).getD i false = init.getD i false := by
    induction gs generalizing init with
    | nil => rfl
    | cons g gs ih =>
      change (runWires gs (stepWire init g)).getD i false = init.getD i false
      have hlt : i < (stepWire init g).length := by
        simp only [stepWire_eq, List.length_append, List.length_singleton]
        omega
      rw [ih (stepWire init g) hlt, stepWire_eq, getD_append_singleton, ite_eq_left hi]
  
  have runWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
      (hj : j < gs.length) :
      (runWires gs init).getD (init.length + j) false =
        (gs[j]).op.eval
          ((gs[j]).inputs.map fun i =>
            if i < init.length + j then (runWires gs init).getD i false else false) := by
    induction gs generalizing init j with
    | nil => simp at hj
    | cons g gs ih =>
      cases j with
      | zero =>
        change (runWires gs (stepWire init g)).getD (init.length + 0) false =
          g.op.eval (g.inputs.map fun i =>
            if i < init.length + 0 then (runWires gs (stepWire init g)).getD i false else false)
        have hlen : init.length < (stepWire init g).length := by
          simp only [stepWire_eq, List.length_append, List.length_singleton]
          omega
        rw [Nat.add_zero, runWires_getD_prefix gs (stepWire init g) init.length hlen]
        have hhead : (stepWire init g).getD init.length false =
            g.op.eval (g.inputs.map fun i => init.getD i false) := by
          rw [stepWire_eq, getD_append_singleton, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
        rw [hhead]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < init.length
        · rw [ite_eq_left hi]
          have hi' : i < (stepWire init g).length := by
            simp only [stepWire_eq, List.length_append, List.length_singleton]
            omega
          rw [runWires_getD_prefix gs (stepWire init g) i hi', stepWire_eq,
            getD_append_singleton, ite_eq_left hi]
        · rw [ite_eq_right hi, getD_of_ge init i (Nat.le_of_not_gt hi)]
      | succ k =>
        have hk : k < gs.length := by simpa using hj
        have hidx : init.length + (k + 1) = (stepWire init g).length + k := by
          simp only [stepWire_eq, List.length_append, List.length_singleton]
          omega
        change (runWires gs (stepWire init g)).getD (init.length + (k + 1)) false =
          (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
            if i < init.length + (k + 1) then (runWires gs (stepWire init g)).getD i false else false)
        rw [hidx]
        exact ih (stepWire init g) k hk
  
  let wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD w false
  
  have wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
      wireVal C x i = x ⟨i, hi⟩ := by
    unfold wireVal
    change (runWires C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
    rw [runWires_getD_prefix C.gates (List.ofFn x) i (by simp [hi])]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hi]
  
  have wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
      (hj : j < C.gates.length) :
      wireVal C x (n + j) =
        (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
          if i < n + j then wireVal C x i else false) := by
    unfold wireVal
    have h := runWires_getD_gate C.gates (List.ofFn x) j hj
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    rw [hlen] at h
    exact h
  
  have wireVal_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
      (hw : n + C.gates.length ≤ w) : wireVal C x w = false := by
    unfold wireVal
    apply getD_of_ge
    change (runWires C.gates (List.ofFn x)).length ≤ w
    rw [runWires_len, List.length_ofFn]
    exact hw
  have hgate (j : ℕ) (hj : j < C.gates.length) :
      gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  have hinputs (j : ℕ) (hj : j < C.gates.length) :
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    have hlen := hAO.2.2 C.gates[j] (List.getElem_mem hj)
    rw [← hgate j hj] at hlen
    generalize hxs : (gateAt C j).inputs = xs at hlen ⊢
    unfold opnd
    rw [hxs]
    cases xs with
    | nil => simp at hlen
    | cons a t =>
      cases t with
      | nil => simp at hlen
      | cons b t =>
        cases t with
        | nil => rfl
        | cons c t => simp at hlen
  have hread (j : ℕ) (hj : j < C.gates.length) (k : Fin 2) :
      opnd C j k < 14 + j := by
    apply hAO.2.1 j hj
    rw [hinputs j hj]
    have hk : k = 0 ∨ k = 1 := by
      have hk' : k.val = 0 ∨ k.val = 1 := by omega
      rcases hk' with hk' | hk'
      · left; apply Fin.ext; exact hk'
      · right; apply Fin.ext; exact hk'
    rcases hk with rfl | rfl <;> simp
  have hrec (x : Fin 14 → Bool) (j : ℕ) (hj : j < C.gates.length) :
      wireVal C x (14+j) = (gateAt C j).op.eval [wireVal C x (opnd C j 0), wireVal C x (opnd C j 1)] := by
    rw [wireVal_gate C x j hj, ← hgate j hj, hinputs j hj]
    simp [hread j hj 0, hread j hj 1]
  apply core C hsize hAO hdistinct hfirst hcomp
  intro b
  obtain ⟨d, hdin, hdgate, hdout⟩ := hlin b
  refine ⟨d, hdin, hdgate, hdout, ?_⟩
  let base := wireVal C (fun i : Fin 14 => decide (i = if b = true then (0 : Fin 14) else 7))
  let pair := wireVal C (fun i : Fin 14 => decide (i = 0 ∨ i = 7))
  change ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
    base (opnd C j 0) = false ∧ base (opnd C j 1) = false ∧
    d (opnd C j 0) = true ∧ d (opnd C j 1) = true
  apply Classical.byContradiction
  intro hn
  have invariant : ∀ w : ℕ, pair w = true → base w = true ∨ d w = true := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hp
      by_cases hw : w < 14
      · have h1 : pair w = decide ((⟨w,hw⟩ : Fin 14) = 0 ∨ (⟨w,hw⟩ : Fin 14) = 7) :=
          wireVal_input C _ w hw
        have h2 : base w = decide ((⟨w,hw⟩ : Fin 14) = if b = true then (0 : Fin 14) else 7) :=
          wireVal_input C _ w hw
        rw [h1] at hp
        rw [h2, hdin w hw]
        have hm : w = 0 ∨ w = 7 := by
          simp only [decide_eq_true_eq, Fin.ext_iff] at hp
          exact hp
        cases b
        · rcases hm with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl rfl
        · rcases hm with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
      · by_cases hw' : w < 14+C.gates.length
        · let j := w - 14
          have hj : j < C.gates.length := by dsimp [j]; omega
          have heq : w = 14+j := by dsimp [j]; omega
          have hpa : pair w = (gateAt C j).op.eval [pair (opnd C j 0), pair (opnd C j 1)] := by
            rw [heq]; exact hrec _ j hj
          have hba : base w = (gateAt C j).op.eval [base (opnd C j 0), base (opnd C j 1)] := by
            rw [heq]; exact hrec _ j hj
          have ha := ih (opnd C j 0) (by rw [heq]; exact hread j hj 0)
          have hb := ih (opnd C j 1) (by rw [heq]; exact hread j hj 1)
          have hder := hdgate j hj
          obtain hop | hop := hAO.1 C.gates[j] (List.getElem_mem hj)
          all_goals rw [← hgate j hj] at hop
          · rw [hop] at hpa hba
            have hpa' : pair (opnd C j 0) = true ∧ pair (opnd C j 1) = true := by
              rw [hpa] at hp
              simpa [GateOp.eval] using hp
            have ha' := ha hpa'.1
            have hb' := hb hpa'.2
            have hd : d w = (base (opnd C j 0) && d (opnd C j 1) || d (opnd C j 0) && base (opnd C j 1)) := by
              rw [heq]; exact hder.1 hop
            by_cases h0 : base (opnd C j 0) = true
            · rcases hb' with h1 | h1
              · left; simp [hba, GateOp.eval, h0, h1]
              · right; simp [hd, h0, h1]
            · rcases ha' with ha0 | ha1
              · exact False.elim (h0 ha0)
              · rcases hb' with hb0 | hb1
                · right; simp [hd, ha1, hb0]
                · have h00 : base (opnd C j 0) = false := Bool.eq_false_iff.mpr h0
                  by_cases h1 : base (opnd C j 1) = true
                  · right; simp [hd, ha1, h1]
                  · exact False.elim (hn ⟨j,hj,hop,h00,Bool.eq_false_iff.mpr h1,ha1,hb1⟩)
          · rw [hop] at hpa hba
            have hp' : pair (opnd C j 0) = true ∨ pair (opnd C j 1) = true := by
              rw [hpa] at hp
              simpa [GateOp.eval] using hp
            have hd : d w = (d (opnd C j 0) || d (opnd C j 1)) := by
              rw [heq]; exact hder.2 hop
            rcases hp' with hp' | hp'
            · rcases ha hp' with h | h
              · left; simp [hba, GateOp.eval, h]
              · right; simp [hd, h]
            · rcases hb hp' with h | h
              · left; simp [hba, GateOp.eval, h]
              · right; simp [hd, h]
        · have hh : pair w = false := wireVal_ge C _ w (by omega)
          rw [hh] at hp
          contradiction
  have h := invariant C.output hpair
  rcases h with h | h
  · change C.eval (List.ofFn (fun i : Fin 14 => decide (i = if b = true then (0 : Fin 14) else 7))) = true at h
    rw [hbase b] at h
    contradiction
  · rw [hdout] at h
    contradiction
