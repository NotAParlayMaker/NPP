import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2515_619
    (immediate : ∀ C : Circuit, FanInTwo C →
      (∃ i j : Fin C.gates.length, i < j ∧ i.val = 1 ∧
        (C.gates.get i).op = .not ∧ (C.gates.get j).op = .not ∧
        ∀ k : Fin C.gates.length, (C.gates.get k).op = .not → k = i ∨ k = j) →
      (∃ gs, C.gates = ⟨.or, [0,2]⟩ :: gs ∨ C.gates = ⟨.or, [2,0]⟩ :: gs) →
      (∀ v : ℕ, v = 0 ∨ v = 2 → ∃ g ∈ C.gates.drop 1,
        (g.op = .not ∧ g.inputs.head? = some v) ∨ (g.op ≠ .not ∧ v ∈ g.inputs)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 16 ≤ C.size)
    (later : ∀ C : Circuit, FanInTwo C →
      (∃ i j : Fin C.gates.length, i < j ∧ (i.val = 2 ∨ i.val = 3) ∧
        (C.gates.get i).op = .not ∧ (C.gates.get j).op = .not ∧
        ∀ k : Fin C.gates.length, (C.gates.get k).op = .not → k = i ∨ k = j) →
      (∃ gs, C.gates = ⟨.or, [0,2]⟩ :: gs ∨ C.gates = ⟨.or, [2,0]⟩ :: gs) →
      (∀ v : ℕ, v = 0 ∨ v = 2 → ∃ g ∈ C.gates.drop 1,
        (g.op = .not ∧ g.inputs.head? = some v) ∨ (g.op ≠ .not ∧ v ∈ g.inputs)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 ≤ (3 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan nots first computes


  let run (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have old_wire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi

  have first_wire (g : Gate) (gs : List Gate) (x : Fin 9 → Bool) :
      (Circuit.wires ⟨g :: gs, 0⟩ (List.ofFn x)).getD 9 false =
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
    change (run gs (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD 9 false = _
    rw [old_wire _ _ _ (by simp)]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

  have single_read (k i : ℕ) (hk : k < 9) :
      (List.ofFn (fun j : Fin 9 => decide (j.val = k))).getD i false = decide (i = k) := by
    by_cases hi : i < 9
    · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_ofFn]
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
      have hn : i ≠ k := by omega
      simp [hn]

  have false_read (i : ℕ) :
      (List.ofFn (fun _ : Fin 9 => false)).getD i false = false := by
    by_cases hi : i < 9
    · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_ofFn]
    · exact List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)

  have gate_or_shape (g : Gate)
      (legal : g.op = .and ∨ g.op = .or ∨ g.op = .not)
      (len : g.inputs.length ≤ 2)
      (computes : ∀ x : Fin 9 → Bool,
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2)) :
      g = ⟨.or, [0,2]⟩ ∨ g = ⟨.or, [2,0]⟩ := by
    have hz := computes (fun _ => false)
    have h0 := computes (fun j => decide (j.val = 0))
    have h2 := computes (fun j => decide (j.val = 2))
    simp only [false_read, Bool.or_self] at hz
    simp only [single_read 0 _ (by omega), Fin.val_zero, decide_true,
      Bool.true_or] at h0
    simp only [single_read 2 _ (by omega)] at h2
    norm_num at h2
    rcases g with ⟨op, ins⟩
    simp only at legal len hz h0 h2 ⊢
    rcases legal with rfl | rfl | rfl
    · cases ins with
      | nil => exact Bool.noConfusion hz
      | cons a ins =>
        cases ins with
        | nil =>
          change decide (a = 0) && true = true at h0
          change decide (a = 2) && true = true at h2
          simp at h0 h2
          omega
        | cons b ins =>
          cases ins with
          | nil =>
            change decide (a = 0) && (decide (b = 0) && true) = true at h0
            change decide (a = 2) && (decide (b = 2) && true) = true at h2
            simp at h0 h2
            omega
          | cons c rest => simp at len
    · cases ins with
      | nil => exact Bool.noConfusion h0
      | cons a ins =>
        cases ins with
        | nil =>
          change decide (a = 0) || false = true at h0
          change decide (a = 2) || false = true at h2
          simp at h0 h2
          omega
        | cons b ins =>
          cases ins with
          | nil =>
            change decide (a = 0) || (decide (b = 0) || false) = true at h0
            change decide (a = 2) || (decide (b = 2) || false) = true at h2
            simp at h0 h2
            rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2 <;>
              first | omega | (subst a; subst b; simp)
          | cons c rest => simp at len
    · change Bool.not ((ins.map (fun _ => false)).headD false) = false at hz
      cases ins <;> simp at hz

  have first_gate_shape (C : Circuit) (fan : FanInTwo C)
      (first : ∀ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) :
      ∃ gs, C.gates = ⟨.or, [0,2]⟩ :: gs ∨ C.gates = ⟨.or, [2,0]⟩ :: gs := by
    cases hgs : C.gates with
    | nil =>
      have h := first (fun _ => true)
      change (run C.gates (List.ofFn (fun _ : Fin 9 => true))).getD 9 false = true at h
      simp [run, hgs] at h
    | cons g gs =>
      have hg := fan g (by simp [hgs])
      have hcalc : ∀ x : Fin 9 → Bool,
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
        intro x
        have h := first x
        change (run C.gates (List.ofFn x)).getD 9 false = _ at h
        rw [hgs] at h
        rw [show (run (g :: gs) (List.ofFn x)).getD 9 false =
            g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) from first_wire g gs x] at h
        exact h
      obtain rfl | rfl := gate_or_shape g hg.1 hg.2 hcalc
      · exact ⟨gs, Or.inl rfl⟩
      · exact ⟨gs, Or.inr rfl⟩



  let Reads (g : Gate) (v : ℕ) : Prop :=
    (g.op = .not ∧ g.inputs.head? = some v) ∨ (g.op ≠ .not ∧ v ∈ g.inputs)

  let val (g : Gate) (w : List Bool) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  have val_agree (g : Gate) (v : ℕ) (w w' : List Bool)
      (no : ¬ Reads g v)
      (eq : ∀ i, i ≠ v → w.getD i false = w'.getD i false) : val g w = val g w' := by
    by_cases hn : g.op = .not
    · cases hh : g.inputs with
      | nil =>
        change g.op.eval (g.inputs.map _) = g.op.eval (g.inputs.map _)
        rw [hn, hh]
        rfl
      | cons a rest =>
        have ha : a ≠ v := by
          intro same
          exact no (Or.inl ⟨hn, by simp [hh, same]⟩)
        change g.op.eval (g.inputs.map _) = g.op.eval (g.inputs.map _)
        rw [hn, hh]
        change Bool.not (w.getD a false) = Bool.not (w'.getD a false)
        rw [eq a ha]
    · have he : g.inputs.map (fun i => w.getD i false) =
          g.inputs.map (fun i => w'.getD i false) := by
        apply List.map_congr_left
        intro i hi
        apply eq i
        intro same
        exact no (Or.inr ⟨hn, same ▸ hi⟩)
      exact congrArg g.op.eval he

  have run_agree (gs : List Gate) (v : ℕ) (w w' : List Bool)
      (len : w.length = w'.length)
      (eq : ∀ i, i ≠ v → w.getD i false = w'.getD i false)
      (no : ∀ g ∈ gs, ¬ Reads g v) :
      ∀ i, i ≠ v → (run gs w).getD i false = (run gs w').getD i false := by
    induction gs generalizing w w' with
    | nil => exact eq
    | cons g gs ih =>
      have he := val_agree g v w w' (no g (by simp)) eq
      change ∀ i, i ≠ v →
        (run gs (w ++ [val g w])).getD i false = (run gs (w' ++ [val g w'])).getD i false
      apply ih _ _ (by simp [len]) _ (fun h hh => no h (by simp [hh]))
      intro i hi
      by_cases hil : i < w.length
      · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]
        exact eq i hi
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len, he]

  have input_agree (a b : Fin 9 → Bool) (v : Fin 9)
      (h : ∀ i, i ≠ v → a i = b i) :
      ∀ i, i ≠ v.val → (List.ofFn a).getD i false = (List.ofFn b).getD i false := by
    intro i hi
    by_cases hlt : i < 9
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt),
        List.getD_eq_getElem _ _ (by simpa using hlt)]
      simp only [List.getElem_ofFn]
      exact h ⟨i,hlt⟩ (fun he => hi (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)]

  have reader_of_witness (C : Circuit) (F : (Fin 9 → Bool) → Bool) (v : Fin 9)
      (a b : Fin 9 → Bool)
      (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
      (computes : ∀ x, C.eval (List.ofFn x) = F x)
      (ha : F a = false) (hb : F b = true)
      (hs : F (fun i => decide (i.val = v.val)) = false)
      (same : ∀ i, i ≠ v → a i = b i)
      (firstSame : (a 0 || a 2) = (b 0 || b 2)) :
      ∃ g ∈ C.gates.drop 1, Reads g v.val := by
    by_contra absent
    have no : ∀ g ∈ C.gates.drop 1, ¬ Reads g v.val := by
      intro g hg hr
      exact absent ⟨g,hg,hr⟩
    have out : C.output ≠ v.val := by
      intro ho
      have hc := computes (fun i => decide (i.val = v.val))
      change (run C.gates (List.ofFn (fun i : Fin 9 => decide (i.val = v.val)))).getD C.output false = _ at hc
      rw [ho, old_wire _ _ _ (by simp), single_read _ _ v.isLt, hs] at hc
      simp at hc
    cases hgs : C.gates with
    | nil =>
      have h := first (fun _ => true)
      change (run C.gates (List.ofFn (fun _ : Fin 9 => true))).getD 9 false = true at h
      simp [run, hgs] at h
    | cons g gs =>
      have firstEq (x : Fin 9 → Bool) : val g (List.ofFn x) = (x 0 || x 2) := by
        have h := first x
        change (run C.gates (List.ofFn x)).getD 9 false = _ at h
        rw [hgs] at h
        exact (first_wire g gs x).symm.trans h
      have initial : ∀ i, i ≠ v.val →
          (List.ofFn a ++ [val g (List.ofFn a)]).getD i false =
          (List.ofFn b ++ [val g (List.ofFn b)]).getD i false := by
        intro i hi
        by_cases hil : i < 9
        · rw [List.getD_append _ _ _ _ (by simpa using hil),
            List.getD_append _ _ _ _ (by simpa using hil)]
          exact input_agree a b v same i hi
        · rw [List.getD_append_right _ _ _ _ (by simp; omega),
            List.getD_append_right _ _ _ _ (by simp; omega), firstEq, firstEq, firstSame]
          simp
      have both := run_agree gs v.val
        (List.ofFn a ++ [val g (List.ofFn a)])
        (List.ofFn b ++ [val g (List.ofFn b)]) (by simp) initial
        (fun q hq => no q (by simpa [hgs] using hq)) C.output out
      have hca := computes a
      have hcb := computes b
      change (run C.gates (List.ofFn a)).getD C.output false = _ at hca
      change (run C.gates (List.ofFn b)).getD C.output false = _ at hcb
      rw [hgs] at hca hcb
      change (run gs (List.ofFn a ++ [val g (List.ofFn a)])).getD C.output false = _ at hca
      change (run gs (List.ofFn b ++ [val g (List.ofFn b)])).getD C.output false = _ at hcb
      rw [both, hcb, ha, hb] at hca
      contradiction

  let target (x : Fin 9 → Bool) : Bool :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)

  have mandatory_readers (C : Circuit)
      (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
      (computes : ∀ x, C.eval (List.ofFn x) = target x) :
      ∀ v : ℕ, v = 0 ∨ v = 2 → ∃ g ∈ C.gates.drop 1, Reads g v := by
    intro v hv
    rcases hv with rfl | rfl
    · let a : Fin 9 → Bool := fun i => decide (i.val = 2 ∨ i.val = 4)
      let b : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 2 ∨ i.val = 4)
      apply reader_of_witness C target 0 a b first computes
      · decide
      · decide
      · decide
      · intro i hi
        simp [a,b,hi]
      · decide
    · let a : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 3)
      let b : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 2 ∨ i.val = 3)
      apply reader_of_witness C target 2 a b first computes
      · decide
      · decide
      · decide
      · intro i hi
        have hiv : i.val ≠ 2 := fun h => hi (Fin.ext h)
        simp [a,b,hiv]
      · decide

  have not_index_positive (C : Circuit)
      (shape : ∃ gs, C.gates = ⟨.or, [0,2]⟩ :: gs ∨
        C.gates = ⟨.or, [2,0]⟩ :: gs)
      (i : Fin C.gates.length) (hn : (C.gates.get i).op = .not) :
      0 < i.val := by
    by_contra h
    have iz : i.val = 0 := by omega
    obtain ⟨gs, hgs | hgs⟩ := shape
    · have eq : C.gates.get i = ⟨.or, [0,2]⟩ := by
        simp only [List.get_eq_getElem, iz, hgs, List.getElem_cons_zero]
      rw [eq] at hn
      contradiction
    · have eq : C.gates.get i = ⟨.or, [2,0]⟩ := by
        simp only [List.get_eq_getElem, iz, hgs, List.getElem_cons_zero]
      rw [eq] at hn
      contradiction

  have normalized := first_gate_shape C fan first
  have values : ∀ x, C.eval (List.ofFn x) = target x := by
    intro x
    have h := congrFun computes x
    change C.eval (List.ofFn x) = _ at h
    simpa only [target, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc] using h
  have repeated := mandatory_readers C first values
  have functionEq : circuitFun 9 C = target := by
    funext x
    exact values x
  obtain ⟨i,j,ij,early,ni,nj,others⟩ := nots
  have positive := not_index_positive C normalized i ni
  by_cases atOne : i.val = 1
  · exact immediate C fan ⟨i,j,ij,atOne,ni,nj,others⟩ normalized repeated functionEq
  · exact later C fan ⟨i,j,ij,by omega,ni,nj,others⟩ normalized repeated functionEq
