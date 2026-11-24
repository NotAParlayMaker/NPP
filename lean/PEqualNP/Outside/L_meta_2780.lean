import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection

namespace PEqualNP.Outside.L_meta_2780

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma keep (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma gate_value (gs : List Gate) (w : List Bool) (j : Nat) (g : Gate)
    (someGate : gs[j]? = some g) (back : ∀ i ∈ g.inputs, i < w.length + j) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at someGate
  | cons a gs ih =>
    cases j with
    | zero =>
      have eq : a = g := by simpa using someGate
      subst a
      simp only [List.foldl_cons, Nat.add_zero]
      rw [keep gs (step w g) w.length (by simp [step])]
      have eqMap : (g.inputs.map fun i => (gs.foldl step (step w g)).getD i false) =
          g.inputs.map (fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i hi
        have h := back i hi
        simp only [Nat.add_zero] at h
        rw [keep gs (step w g) i (by simp [step]; omega)]
        simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
      rw [eqMap]
      simp [step, List.getD_eq_getElem?_getD]
    | succ j =>
      have idx : (step w a).length + j = w.length + (j+1) := by
        simp [step]
        omega
      rw [List.foldl_cons, ← idx]
      exact ih _ _ (by simpa using someGate) (by simpa only [idx] using back)

def ordered (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i, u.getD i false ≤ v.getD i false

lemma ordered_append {u v u' v' : List Bool} (a : ordered u v) (b : ordered u' v') :
    ordered (u ++ u') (v ++ v') := by
  refine ⟨by simp [a.1,b.1], ?_⟩
  intro i
  by_cases h : i < u.length
  · have hv : i < v.length := a.1 ▸ h
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left h,
      List.getElem?_append_left hv] using a.2 i
  · have hu : u.length ≤ i := by omega
    have hv : v.length ≤ i := a.1 ▸ hu
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_right hu,
      List.getElem?_append_right hv, a.1] using b.2 (i - v.length)

lemma step_mono {u v : List Bool} (h : ordered u v) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) (two : g.inputs.length = 2) :
    ordered (step u g) (step v g) := by
  obtain ⟨a,b,ab⟩ := List.length_eq_two.mp two
  apply ordered_append h
  refine ⟨rfl, ?_⟩
  intro i
  cases i with
  | zero =>
    rw [ab]
    have ha := h.2 a
    have hb := h.2 b
    simp only [List.getD_eq_getElem?_getD] at ha hb
    rcases op with op | op <;>
      simp [op, GateOp.eval] <;>
      generalize u[a]?.getD false = ua at ha ⊢ <;>
      generalize u[b]?.getD false = ub at hb ⊢ <;>
      generalize v[a]?.getD false = va at ha ⊢ <;>
      generalize v[b]?.getD false = vb at hb ⊢ <;>
      cases ua <;> cases ub <;> cases va <;> cases vb <;> simp_all
  | succ i => simp

lemma wire_mono (n : Nat) (C : Circuit) (ao : IsAO2 n C)
    {u v : List Bool} (h : ordered u v) (i : Nat) :
    wireValue C u i ≤ wireValue C v i := by
  have all (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (twos : ∀ g ∈ gs, g.inputs.length = 2) (u v : List Bool) (h : ordered u v) :
      ordered (gs.foldl step u) (gs.foldl step v) := by
    induction gs generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      simp only [List.foldl_cons]
      exact ih (fun d md => ops d (List.mem_cons_of_mem g md))
        (fun d md => twos d (List.mem_cons_of_mem g md)) _ _
        (step_mono h g (ops g List.mem_cons_self) (twos g List.mem_cons_self))
  exact (all C.gates ao.1 ao.2.2 u v h).2 i


lemma fn_order {n : Nat} {x y : Fin n → Bool} (h : ∀ i, x i ≤ y i) :
    ordered (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, hi] using h ⟨i,hi⟩
  · simp [List.getD_eq_getElem?_getD, hi]

def bits {n : Nat} (X : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ X)

lemma low_order {n : Nat} (X : Finset (Fin n)) :
    ordered (List.replicate n false) (List.ofFn (bits X)) := by
  rw [← List.ofFn_const]
  exact fn_order (fun _ => Bool.false_le _)

lemma high_order {n : Nat} (X : Finset (Fin n)) :
    ordered (List.ofFn (bits X)) (List.replicate n true) := by
  rw [← List.ofFn_const]
  exact fn_order (fun _ => Bool.le_true _)

lemma purePoint {n : Nat} {C : Circuit} (ao : IsAO2 (n+n) C) (i : Nat)
    (same : ∀ x : Fin n → Bool,
      wireValue C (List.ofFn x ++ List.replicate n false) i =
      wireValue C (List.ofFn x ++ List.replicate n true) i)
    (X Y : Finset (Fin n)) :
    wireValue C (incidenceInput X Y) i =
      wireValue C (List.ofFn (bits X) ++ List.replicate n false) i := by
  have lo := wire_mono _ C ao
    (ordered_append (fn_order (x := bits X) (fun _ => le_rfl)) (low_order Y)) i
  have hi := wire_mono _ C ao
    (ordered_append (fn_order (x := bits X) (fun _ => le_rfl)) (high_order Y)) i
  rw [← same (bits X)] at hi
  exact le_antisymm hi lo

lemma pureLine {n : Nat} {C : Circuit} (ao : IsAO2 (n+n) C) (i : Nat)
    (same : ∀ x : Fin n → Bool,
      wireValue C (List.replicate n false ++ List.ofFn x) i =
      wireValue C (List.replicate n true ++ List.ofFn x) i)
    (X Y : Finset (Fin n)) :
    wireValue C (incidenceInput X Y) i =
      wireValue C (List.replicate n false ++ List.ofFn (bits Y)) i := by
  have lo := wire_mono _ C ao
    (ordered_append (low_order X) (fn_order (x := bits Y) (fun _ => le_rfl))) i
  have hi := wire_mono _ C ao
    (ordered_append (high_order X) (fn_order (x := bits Y) (fun _ => le_rfl))) i
  rw [← same (bits Y)] at hi
  exact le_antisymm hi lo

lemma zero_wire {n : Nat} (C : Circuit) (ao : IsAO2 n C) (i : Nat) :
    wireValue C (List.replicate n false) i = false := by
  have allZero (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (twos : ∀ g ∈ gs, g.inputs.length = 2) (w : List Bool)
      (zero : ∀ i, w.getD i false = false) :
      ∀ i, (gs.foldl step w).getD i false = false := by
    induction gs generalizing w with
    | nil => exact zero
    | cons g gs ih =>
      obtain ⟨a,b,ab⟩ := List.length_eq_two.mp (twos g List.mem_cons_self)
      simp only [List.getD_eq_getElem?_getD] at zero
      have gateZero : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
        rw [ab]
        rcases ops g List.mem_cons_self with hop | hop <;> simp [hop, GateOp.eval, zero]
      apply ih (fun d hd => ops d (List.mem_cons_of_mem g hd))
        (fun d hd => twos d (List.mem_cons_of_mem g hd))
      intro j
      change (w ++ [_]).getD j false = false
      rw [gateZero]
      by_cases hj : j < w.length
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hj] using zero j
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        cases j - w.length <;> rfl
  apply allZero C.gates ao.1 ao.2.2
  intro j
  by_cases hj : j < n <;> simp [List.getD_eq_getElem?_getD, hj]

end PEqualNP.Outside.L_meta_2780

open PEqualNP.Outside.L_meta_2780

theorem PEqualNP.Outside.L_meta_2780 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.false) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.true) x4) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.false ++ List.ofFn x6) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.true ++ List.ofFn x6) x4); ∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x2 + x2) x3 → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 → x1 x2 x3 x7 → x6 ∈ x4) → ∀ x7 < x3.size, x7 ∉ x4 → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : Finset (Fin x2) → Bool) (x12 : Finset (Fin x2) → Bool), ∀ (x13 x14 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x3 (PEqualNP.GenericRejection.incidenceInput x13 x14) (x2 + x2 + x7) = (x11 x13 && x12 x14) := by
  classical
  dsimp only
  intro n C U ao cover j hj outside hop
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
  have hlen : j < C.gates.length := hj
  have ge : g = C.gates[j] := List.getD_eq_getElem _ _ hlen
  have someGate : C.gates[j]? = some g := by rw [ge, List.getElem?_eq_getElem hlen]
  have mem : g ∈ C.gates := ge ▸ List.getElem_mem (l := C.gates) (n := j) hlen
  have noPoint : ¬ ∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
      wireValue C (List.ofFn x ++ List.replicate n false) w ≠
        wireValue C (List.ofFn x ++ List.replicate n true) w := by
    intro h
    exact outside (cover j g someGate ⟨hop, Or.inl h⟩)
  have noLine : ¬ ∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
      wireValue C (List.replicate n false ++ List.ofFn x) w ≠
        wireValue C (List.replicate n true ++ List.ofFn x) w := by
    intro h
    exact outside (cover j g someGate ⟨hop, Or.inr h⟩)
  push Not at noPoint noLine
  obtain ⟨p, hp, point⟩ := noPoint
  obtain ⟨l, hl, line⟩ := noLine
  have value (X Y : Finset (Fin n)) :
      wireValue C (incidenceInput X Y) (n+n+j) =
        g.op.eval (g.inputs.map fun i => wireValue C (incidenceInput X Y) i) := by
    have len : (incidenceInput X Y).length = n+n := by simp [incidenceInput]
    have back : ∀ i ∈ g.inputs, i < (incidenceInput X Y).length + j := by
      intro i hi
      rw [len]
      exact ao.2.1 j hlen i hi
    have val := gate_value C.gates (incidenceInput X Y) j g someGate back
    rw [len] at val
    exact val
  let P (X : Finset (Fin n)) := wireValue C (List.ofFn (bits X) ++ List.replicate n false) p
  let L (Y : Finset (Fin n)) := wireValue C (List.replicate n false ++ List.ofFn (bits Y)) l
  have hpure (X Y : Finset (Fin n)) : wireValue C (incidenceInput X Y) p = P X :=
    purePoint ao p point X Y
  have lpure (X Y : Finset (Fin n)) : wireValue C (incidenceInput X Y) l = L Y :=
    pureLine ao l line X Y
  obtain ⟨a,b,ab⟩ := List.length_eq_two.mp (ao.2.2 g mem)
  by_cases e : p = l
  · have z : wireValue C (incidenceInput (∅ : Finset (Fin n)) (∅ : Finset (Fin n))) p = false := by
      simp only [incidenceInput, Finset.notMem_empty, decide_false, List.ofFn_const, ← List.replicate_add]
      exact zero_wire C ao p
    have pzero (X Y : Finset (Fin n)) : wireValue C (incidenceInput X Y) p = false := by
      rw [hpure X Y, ← hpure X ∅, e, lpure X ∅, ← lpure ∅ ∅, ← e]
      exact z
    refine ⟨fun _ => false, fun _ => false, ?_⟩
    intro X Y
    rw [value, show g.op = GateOp.and from hop, ab]
    have pside : p = a ∨ p = b := by simpa [ab] using hp
    rcases pside with rfl | rfl <;> simp [GateOp.eval, pzero]
  · refine ⟨P,L,?_⟩
    intro X Y
    rw [value, show g.op = GateOp.and from hop, ab]
    have pside : p = a ∨ p = b := by simpa [ab] using hp
    have lside : l = a ∨ l = b := by simpa [ab] using hl
    rcases pside with rfl | rfl <;> rcases lside with rfl | rfl
    · exact (e rfl).elim
    · simp [GateOp.eval, hpure, lpure]
    · simp [GateOp.eval, hpure, lpure, Bool.and_comm]
    · exact (e rfl).elim
