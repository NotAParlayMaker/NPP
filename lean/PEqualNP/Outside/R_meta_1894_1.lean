import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1894_1
    (singleton : ∀ (C : Circuit), Monotone2 C → C.size ≤ 124 →
    (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
        x u = true ∧ x v = true) →
    ∀ Z : Finset (Fin 42), Z.card ≤ 1 → (∀ p ∈ Z, p.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) →
      ∀ (i : ℕ) (g : Gate),
      C.gates[i]? = some g → g.op = GateOp.and →
      (C.wires (List.ofFn fun p => decide (p ∈ Z))).getD (42+i) false = false)
    (pair : ∀ (C : Circuit), Monotone2 C → C.size ≤ 124 →
    (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∧
        x u = true ∧ x v = true) →
    (∀ Z : Finset (Fin 42), Z.card ≤ 1 → (∀ p ∈ Z, p.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) →
      ∀ (i : ℕ) (g : Gate),
      C.gates[i]? = some g → g.op = GateOp.and →
      (C.wires (List.ofFn fun p => decide (p ∈ Z))).getD (42+i) false = false) →
    ∀ Z : Finset (Fin 42), Z.card = 2 →
    (∀ p ∈ Z, p.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) →
    ∀ (i : ℕ) (g : Gate), C.gates[i]? = some g → g.op = GateOp.and →
    (C.wires (List.ofFn fun p => decide (p ∈ Z))).getD (42+i) false = false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∃ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x6 : Fin (42 : ℕ)) => Decidable.decide (↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x4) Bool.false = Bool.true) → ∃ (x5 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by

  classical
  let run (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

  have run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
      run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
    rfl

  have run_length (gs : List Gate) (x : List Bool) :
      (run gs x).length = x.length + gs.length := by
    induction gs generalizing x with
    | nil => simp [run]
    | cons g gs ih => rw [run_cons, ih]; simp; omega

  have run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
      (run gs x).getD w false = x.getD w false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

  have run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
      run gs x = run (gs.drop j) (run (gs.take j) x) := by
    simpa only [run, List.foldl_append] using
      congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

  let value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD w false

  have input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
      value C x p = x p := by
    change (run C.gates (List.ofFn x)).getD p false = x p
    have hp : (p : ℕ) < (List.ofFn x).length := by simp
    rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
    simp

  have gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
      (hn : n ≤ w) (hw : w < n + C.size) :
      let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
      value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
    let j := w - n
    have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
    let g := C.gates[j]
    let earlier := run (C.gates.take j) (List.ofFn x)
    have plen : earlier.length = w := by
      simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
    have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
      rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
    have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
      by_cases hr : r < w
      · rw [ite_eq_left hr]
        change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
        rw [split]
        exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
      · rw [ite_eq_right hr]
        exact List.getD_eq_default _ _ (by omega)
    change (run C.gates (List.ofFn x)).getD w false =
      g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
    rw (occs := [1]) [split]
    rw (occs := [1]) [run_cons]
    rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
    simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

  have sparse :
      ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ Y : Finset (Fin n),
        (∃ (i : ℕ) (g : Gate), C.gates[i]? = some g ∧ g.op = GateOp.and ∧
          (C.wires (List.ofFn fun p => decide (p ∈ Y))).getD (n+i) false = true) →
        ∃ Z : Finset (Fin n), Z ⊆ Y ∧ Z.card ≤ 2 ∧
          ∃ (i : ℕ) (g : Gate), C.gates[i]? = some g ∧ g.op = GateOp.and ∧
            (C.wires (List.ofFn fun p => decide (p ∈ Z))).getD (n+i) false = true := by
    classical
    intro n C mono Y hot
    let y : Fin n → Bool := fun p => decide (p ∈ Y)
    let P (i : ℕ) := ∃ (g : Gate), C.gates[i]? = some g ∧
      g.op = GateOp.and ∧ value C y (n+i) = true
    have existsP : ∃ i, P i := hot
    let j := Nat.find existsP
    have earlier (i : ℕ) (lt : i < j) : ¬ P i := Nat.find_min existsP lt
    obtain ⟨g, hget, hand, hon⟩ := (show P j from Nat.find_spec existsP)
    have valid : j < C.gates.length := by
      by_contra! h
      rw [List.getElem?_eq_none h] at hget
      contradiction
    have gEq : C.gates[j] = g := Option.some.inj ((List.getElem?_eq_getElem valid).symm.trans hget)
    obtain ⟨_, binary⟩ := mono g (gEq ▸ List.getElem_mem valid)
    let read (x : Fin n → Bool) (w r : ℕ) :=
      if r < w then value C x r else false
    have evalGate (x : Fin n → Bool) (i : ℕ) (ilt : i < C.gates.length) :
        value C x (n+i) = C.gates[i].op.eval (C.gates[i].inputs.map (read x (n+i))) := by
      simpa only [Nat.add_sub_cancel_left] using
        (gate_value C x (n+i) (by omega) (by exact Nat.add_lt_add_left ilt n))
    have prefixTrace (w : ℕ) (lt : w < n+j) (on : value C y w = true) :
        ∃ p ∈ Y, ∀ x : Fin n → Bool, x p = true → value C x w = true := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases hinput : w < n
        · let p : Fin n := ⟨w,hinput⟩
          have hp : p ∈ Y := by
            change value C y p = true at on
            simpa [input_value,y] using on
          exact ⟨p,hp,fun x hx => (input_value C x p).trans hx⟩
        let i := w-n
        have iw : n+i=w := by omega
        have ilt : i<j := by omega
        have iok := ilt.trans valid
        have types := (mono _ (List.getElem_mem iok)).1
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at types
        have op : C.gates[i].op = GateOp.or := by
          rcases types with a | b
          · exact (earlier i ilt ⟨C.gates[i], List.getElem?_eq_getElem iok, a, iw ▸ on⟩).elim
          · exact b
        have on' : (C.gates[i].inputs.map (read y w)).any id = true := by
          have h := evalGate y i iok
          rw [iw,op,GateOp.eval] at h
          exact h.symm.trans on
        obtain ⟨b, bmem, rtrue⟩ := List.any_eq_true.mp on'
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp bmem
        have rw' : r < w := by
          by_contra! h
          simp [read, Nat.not_lt.mpr h] at rtrue
        have ry : value C y r=true := by simpa [read,rw'] using rtrue
        obtain ⟨p,hp,hprop⟩ := ih r rw' (rw'.trans lt) ry
        refine ⟨p,hp,fun x hx => ?_⟩
        have eval := evalGate x i iok
        rw [iw,op,GateOp.eval] at eval
        exact eval.trans (List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨r,hr,rfl⟩,
          by simpa [read,rw'] using hprop x hx⟩)
    have andTrue (x : Fin n → Bool) : value C x (n+j) = true ↔
        ∀ r ∈ g.inputs, read x (n+j) r = true := by
      rw [evalGate x j valid, gEq, hand, GateOp.eval]
      simp [List.all_eq_true]
    let Parents := g.inputs.toFinset
    have chooseInput (r : { i // i ∈ Parents }) :
        ∃ p ∈ Y, ∀ x : Fin n → Bool, x p = true → read x (n+j) r = true := by
      have on := (andTrue y).mp hon r (List.mem_toFinset.mp r.property)
      have lt : r.val < n+j := by
        by_contra! h
        simp [read, Nat.not_lt.mpr h] at on
      obtain ⟨p,hp,hprop⟩ := prefixTrace r lt (by simpa [read,lt] using on)
      exact ⟨p,hp,fun x hx => by simpa [read,lt] using hprop x hx⟩
    choose point properties using chooseInput
    let Z := Finset.univ.image point
    have sub : Z ⊆ Y := by
      intro p hp
      obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hp
      exact (properties r).1
    have sz : Z.card ≤ 2 := by
      apply Finset.card_image_le.trans
      simpa [Parents] using (List.toFinset_card_le g.inputs).trans binary
    refine ⟨Z,sub,sz,j,g,hget,hand,(andTrue _).mpr ?_⟩
    intro r hr
    let rr : { i // i ∈ Parents } := ⟨r,List.mem_toFinset.mpr hr⟩
    exact (properties rr).2 _ (by simp [Z])
  intro C mono size hot
  by_contra! correct
  let Y := (Finset.univ : Finset (Fin 42)).filter
    (fun p => p.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))
  have yEq : (fun p => decide (p ∈ Y)) =
      fun p : Fin 42 => decide (p.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) := by
    funext p
    simp [Y]
  have hY : ∃ (i : ℕ) (g : Gate), C.gates[i]? = some g ∧ g.op = GateOp.and ∧
      (C.wires (List.ofFn fun p => decide (p ∈ Y))).getD (42+i) false = true := by
    rw [yEq]
    exact hot
  obtain ⟨Z, sub, card, i, g, get, op, on⟩ := sparse 42 C mono Y hY
  have singletonCold := singleton C mono size correct
  have onY : ∀ p ∈ Z, p.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ) := by
    intro p hp
    exact (Finset.mem_filter.mp (sub hp)).2
  by_cases single : Z.card ≤ 1
  · exact Bool.noConfusion (on.symm.trans (singletonCold Z single onY i g get op))
  · exact Bool.noConfusion (on.symm.trans (pair C mono size correct singletonCold Z (by omega) onY i g get op))
