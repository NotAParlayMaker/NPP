import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1356

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem prefixValue (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem inputValue {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    Circuit.eval ⟨gs, p.val⟩ (List.ofFn x) = x p := by
  change (gs.foldl step (List.ofFn x)).getD p.val false = _
  rw [prefixValue _ _ _ (by simp)]
  simp

private def Off (skip : ℕ → Prop) (r : Bool → Bool → Prop)
    (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, ¬ skip i → r (w.getD i false) (w'.getD i false)

private theorem offSnoc {skip r w w' a b} (h : Off skip r w w') (hab : r a b) :
    Off skip r (w ++ [a]) (w' ++ [b]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  by_cases il : i < w.length
  · rw [List.getD_append _ _ _ _ il, List.getD_append _ _ _ _ (by rw [← h.1]; exact il)]
    exact h.2 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by rw [← h.1]; omega), ← h.1]
    cases d : i - w.length with
    | zero => simpa using hab
    | succ j =>
      have h0 := h.2 i hi
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by rw [← h.1]; omega)] at h0
      simpa using h0

private theorem offFold {skip r} (gs : List Gate)
    (preserve : ∀ g ∈ gs, ∀ w w', Off skip r w w' →
      r (g.op.eval (g.inputs.map fun i => w.getD i false))
         (g.op.eval (g.inputs.map fun i => w'.getD i false))) :
    ∀ w w', Off skip r w w' → Off skip r (gs.foldl step w) (gs.foldl step w') := by
  induction gs with
  | nil => exact fun _ _ h => h
  | cons g gs ih =>
    intro w w' h
    change Off skip r (gs.foldl step (step w g)) (gs.foldl step (step w' g))
    exact ih (fun g' hm => preserve g' (List.mem_cons_of_mem _ hm)) _ _
      (offSnoc h (preserve g List.mem_cons_self w w' h))

private theorem offInput {n : ℕ} {skip r} {x y : Fin n → Bool}
    (h : ∀ i : Fin n, ¬ skip i.val → r (x i) (y i)) (r00 : r false false) :
    Off skip r (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun j hj => ?_⟩
  by_cases jl : j < n
  · simpa [jl] using h ⟨j, jl⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact r00

private def Binary (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

private theorem binaryMono {skip w w'} (g : Gate) (hg : Binary g)
    (safe : ∀ j ∈ g.inputs, ¬ skip j) (h : Off skip (fun a b => a = true → b = true) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hl b hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact h.2 j (safe j hj) (hl _ ⟨j, hj, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
    exact ⟨_, ⟨j, hj, rfl⟩, h.2 j (safe j hj) hb⟩

private theorem binaryEq {skip w w'} (g : Gate)
    (safe : ∀ j ∈ g.inputs, ¬ skip j) (h : Off skip Eq w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
    g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  exact congrArg g.op.eval (List.map_congr_left fun j hj => h.2 j (safe j hj))

private theorem mem_take_index {l : List Gate} {a : Gate} {k : ℕ} (ha : a ∈ l.take k) :
    ∃ i : Fin l.length, i.val < k ∧ l.get i = a := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hi
  have il : i < l.length := lt_of_lt_of_le hlt (by simp)
  have ik : i < k := lt_of_lt_of_le hlt (by simp)
  refine ⟨⟨i, il⟩, ik, ?_⟩
  change l[i] = a
  rw [← List.getElem_take]
  exact heq

private theorem outputNotInput {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ o : Fin m, 2 ≤ (S o).card) (gs : List Gate) (out : Fin m → ℕ)
    (correct : ∀ (o : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) :
    ∀ o : Fin m, n ≤ out o := by
  intro o
  by_contra! h
  let p : Fin n := ⟨out o,h⟩
  have hex : ∃ q ∈ S o, q ≠ p := by
    by_contra! hall
    have le : S o ⊆ {p} := by intro q hq; simpa using hall q hq
    have := Finset.card_le_card le
    simp at this
    have := hcard o
    omega
  obtain ⟨q, hq, qp⟩ := hex
  let x : Fin n → Bool := fun i => decide (i = q)
  have l : Circuit.eval ⟨gs,out o⟩ (List.ofFn x) = false := by
    change Circuit.eval ⟨gs,p.val⟩ (List.ofFn x) = false
    rw [inputValue]
    simp [x, qp.symm]
  rw [correct] at l
  exact (of_decide_eq_false l) ⟨q, hq, by simp [x]⟩

end PEqualNP.Outside.L_meta_1356

theorem PEqualNP.Outside.L_meta_1356 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i9 : Fin m, 2 ≤ (S i9).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ (p : Fin n) (i0 : Fin m), p ∈ S i0 → ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a).inputs := by
  classical
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1356 in
  intro n m S hcard gates out ops correct ι hι p i0 hp
  by_contra hno
  let x : Fin n → Bool := fun i => decide (i = p)
  let y : Fin n → Bool := fun _ => false
  let skip : ℕ → Prop := fun j => j = p.val
  let rel : Bool → Bool → Prop := fun l r => l = true → r = true
  let q : Fin gates.length := ι 0
  let before : List Gate := gates.take q.val
  let g0 : Gate := gates.get q
  let after : List Gate := gates.drop (q.val + 1)
  let w : List Bool := before.foldl step (List.ofFn x)
  let w' : List Bool := before.foldl step (List.ofFn y)
  have opsGet (a : Fin gates.length) :
      ((gates.get a).op = GateOp.and ∨ (gates.get a).op = GateOp.or ∨ (gates.get a).op = GateOp.not) ∧
      (gates.get a).inputs.length ≤ 2 :=
    ops (gates.get a) (List.get_mem gates a)
  have noRead (a : Fin gates.length) (hbin : Binary (gates.get a)) :
      p.val ∉ (gates.get a).inputs := by
    intro hread
    exact hno ⟨a, hbin, hread⟩
  have binaryNe (a : Fin gates.length) (ha : a ≠ q) : Binary (gates.get a) := by
    rcases (opsGet a).1 with ho | ho | ho
    · exact Or.inl ho
    · exact Or.inr ho
    · exfalso
      have e : a = q := by
        obtain ⟨r, hr⟩ := hι a ho
        calc
          a = ι r := hr.symm
          _ = ι 0 := by rw [Subsingleton.elim r 0]
          _ = q := rfl
      exact ha e
  have safeBinary (a : Fin gates.length) (hbin : Binary (gates.get a)) :
      ∀ j ∈ (gates.get a).inputs, ¬ skip j := by
    intro j hj hs
    have hj' : j = p.val := hs
    exact noRead a hbin (hj' ▸ hj)
  have initial : Off skip Eq (List.ofFn x) (List.ofFn y) := by
    apply offInput
    · intro i hi
      have ip : i ≠ p := fun e => hi (congrArg Fin.val e)
      simp [x, y, ip]
    · rfl
  have preserveBefore : ∀ g ∈ before, ∀ v v', Off skip Eq v v' →
      g.op.eval (g.inputs.map fun i => v.getD i false) =
      g.op.eval (g.inputs.map fun i => v'.getD i false) := by
    intro g hg v v' hv
    obtain ⟨i, ik, hi⟩ := mem_take_index hg
    have ine : i ≠ q := by
      intro e
      have : i.val = q.val := congrArg Fin.val e
      omega
    have hbin : Binary g := by rw [← hi]; exact binaryNe i ine
    have safe : ∀ j ∈ g.inputs, ¬ skip j := by
      intro j hj hs
      have hj' : j = p.val := hs
      have hnot : p.val ∉ (gates.get i).inputs := noRead i (binaryNe i ine)
      apply hnot
      rw [hi]
      rw [← hj']
      exact hj
    exact binaryEq g safe hv
  have wEq : Off skip Eq w w' := by
    change Off skip Eq (before.foldl step (List.ofFn x)) (before.foldl step (List.ofFn y))
    exact offFold before preserveBefore (List.ofFn x) (List.ofFn y) initial
  have eqImpRel : Off skip Eq w w' → Off skip rel w w' := by
    intro h
    refine ⟨h.1, fun i hi => ?_⟩
    intro hw
    have : w.getD i false = w'.getD i false := h.2 i hi
    rw [← this]
    exact hw
  have hd : rel
      (g0.op.eval (g0.inputs.map fun i => w.getD i false))
      (g0.op.eval (g0.inputs.map fun i => w'.getD i false)) := by
    rcases (opsGet q).1 with ho | ho | ho
    · exact binaryMono g0 (Or.inl ho) (safeBinary q (Or.inl ho)) (eqImpRel wEq)
    · exact binaryMono g0 (Or.inr ho) (safeBinary q (Or.inr ho)) (eqImpRel wEq)
    · cases hg0 : g0.inputs with
      | nil => rw [ho]; simp [rel, GateOp.eval]
      | cons j js =>
        by_cases hj : j = p.val
        · have hwp : w.getD p.val false = true := by
            rw [prefixValue before (List.ofFn x) p.val (by simp)]
            simp [x]
          rw [ho]
          simp [rel, GateOp.eval, hj]
          intro h
          rw [← List.getD] at h
          rw [hwp] at h
          cases h
        · have hns : ¬ skip j := by
            intro hs
            exact hj (by simpa [skip] using hs)
          have heqj : w.getD j false = w'.getD j false := wEq.2 j hns
          rw [ho]
          simp [rel, GateOp.eval]
          intro h
          rw [← List.getD] at h
          rw [heqj] at h
          rw [List.getD] at h
          exact h
  have afterG0 : Off skip rel (step w g0) (step w' g0) :=
    offSnoc (eqImpRel wEq) hd
  have preserveAfter : ∀ g ∈ after, ∀ v v', Off skip rel v v' →
      rel (g.op.eval (g.inputs.map fun i => v.getD i false))
           (g.op.eval (g.inputs.map fun i => v'.getD i false)) := by
    intro g hg v v' hv
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hj
    have hdrop : j < gates.length - (q.val + 1) := by simpa [after, List.length_drop] using hlt
    have qlt : q.val < gates.length := q.isLt
    have hfull : q.val + 1 + j < gates.length := by omega
    let i : Fin gates.length := ⟨q.val + 1 + j, hfull⟩
    have heqi : gates.get i = g := by
      change gates[q.val + 1 + j] = g
      rw [← List.getElem_drop]
      exact heq
    have ine : i ≠ q := by
      intro e
      have : q.val + 1 + j = q.val := congrArg Fin.val e
      omega
    have hbin : Binary g := by rw [← heqi]; exact binaryNe i ine
    have safe : ∀ k ∈ g.inputs, ¬ skip k := by
      intro k hk hs
      have hk' : k = p.val := hs
      have hnot : p.val ∉ (gates.get i).inputs := noRead i (binaryNe i ine)
      apply hnot
      rw [heqi]
      rw [← hk']
      exact hk
    exact binaryMono g hbin safe hv
  have result : Off skip rel (after.foldl step (step w g0)) (after.foldl step (step w' g0)) :=
    offFold after preserveAfter (step w g0) (step w' g0) afterG0
  have dropDecomp : gates.drop q.val = g0 :: after := by
    rw [List.cons_get_drop_succ]
  have gateDecomp : gates = before ++ g0 :: after := by
    rw [← List.take_append_drop q.val gates, dropDecomp]
  have wxeq : gates.foldl step (List.ofFn x) = after.foldl step (step w g0) := by
    rw [gateDecomp, List.foldl_append]
    rfl
  have wyeq : gates.foldl step (List.ofFn y) = after.foldl step (step w' g0) := by
    rw [gateDecomp, List.foldl_append]
    rfl
  have fullResult : Off skip rel (gates.foldl step (List.ofFn x)) (gates.foldl step (List.ofFn y)) := by
    rw [wxeq, wyeq]
    exact result
  have outGE : n ≤ out i0 := outputNotInput S hcard gates out correct i0
  have hns : ¬ skip (out i0) := by
    intro hs
    have ho : out i0 = p.val := hs
    have : out i0 < n := ho.symm ▸ p.isLt
    omega
  have comparison : rel (Circuit.eval ⟨gates, out i0⟩ (List.ofFn x))
      (Circuit.eval ⟨gates, out i0⟩ (List.ofFn y)) := by
    change rel ((gates.foldl step (List.ofFn x)).getD (out i0) false)
      ((gates.foldl step (List.ofFn y)).getD (out i0) false)
    exact fullResult.2 (out i0) hns
  rw [correct, correct] at comparison
  have hx : (∃ v ∈ S i0, x v = true) := ⟨p, hp, by simp [x]⟩
  simp [rel, hx, y] at comparison
