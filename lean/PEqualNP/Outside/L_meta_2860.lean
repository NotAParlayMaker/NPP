import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2860

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

-- With every gate reading earlier wires, the guard in `val_gate` can be dropped.
lemma val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hR : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hR j hj i hi)]

lemma eval_and2 (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by
  simp [GateOp.eval]

lemma eval_or2 (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by
  simp [GateOp.eval]

lemma gateAt_set (C : Circuit) (i j : ℕ) (g : Gate) (hi : i < C.gates.length) :
    gateAt ⟨C.gates.set i g, C.output⟩ j = if j = i then g else gateAt C j := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

lemma main (n : ℕ) (C : Circuit) (m u v z a b : ℕ) (hR : ReadsBack n C)
    (hm : m < C.gates.length) (hnu : n ≤ u) (huv : u < v) (hvm : v < n + m)
    (hmop : (gateAt C m).op = GateOp.and) (hmin : (gateAt C m).inputs = [u, v])
    (huop : (gateAt C (u - n)).op = GateOp.or) (huin : (gateAt C (u - n)).inputs = [z, a])
    (hvop : (gateAt C (v - n)).op = GateOp.or) (hvin : (gateAt C (v - n)).inputs = [z, b])
    (hread : ∀ j < C.gates.length, j ≠ m → v ∉ (gateAt C j).inputs) (hout : C.output ≠ v) :
    ReadsBack n (⟨(C.gates.set (v - n) ⟨GateOp.and, [a, b]⟩).set m ⟨GateOp.or, [z, v]⟩,
        C.output⟩ : Circuit) ∧
      (⟨(C.gates.set (v - n) ⟨GateOp.and, [a, b]⟩).set m ⟨GateOp.or, [z, v]⟩,
        C.output⟩ : Circuit).size = C.size ∧
      ∀ x : Fin n → Bool,
        (⟨(C.gates.set (v - n) ⟨GateOp.and, [a, b]⟩).set m ⟨GateOp.or, [z, v]⟩,
          C.output⟩ : Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  -- names for the pieces
  set C1 : Circuit := ⟨C.gates.set (v - n) ⟨GateOp.and, [a, b]⟩, C.output⟩ with hC1
  set C2 : Circuit := ⟨(C.gates.set (v - n) ⟨GateOp.and, [a, b]⟩).set m ⟨GateOp.or, [z, v]⟩,
    C.output⟩ with hC2
  have hvi : v - n < C.gates.length := by omega
  have hui : u - n < C.gates.length := by omega
  have hvm' : v - n ≠ m := by omega
  have hl1 : C1.gates.length = C.gates.length := by simp [hC1]
  have hl2 : C2.gates.length = C.gates.length := by simp [hC2]
  -- the gates of the new circuit
  have hg2 : ∀ j, gateAt C2 j =
      if j = m then ⟨GateOp.or, [z, v]⟩ else
        if j = v - n then ⟨GateOp.and, [a, b]⟩ else gateAt C j := by
    intro j
    have e2 : C2 = ⟨C1.gates.set m ⟨GateOp.or, [z, v]⟩, C1.output⟩ := rfl
    rw [e2, gateAt_set C1 m j _ (by rw [hl1]; exact hm)]
    by_cases hjm : j = m
    · rw [if_pos hjm, if_pos hjm]
    · rw [if_neg hjm, if_neg hjm]
      exact gateAt_set C (v - n) j _ hvi
  -- the operands sit below their readers
  have hu_eq : n + (u - n) = u := by omega
  have hv_eq : n + (v - n) = v := by omega
  have hz : z < u := by
    have := hR (u - n) hui z (by rw [huin]; simp); omega
  have ha : a < u := by
    have := hR (u - n) hui a (by rw [huin]; simp); omega
  have hb : b < v := by
    have := hR (v - n) hvi b (by rw [hvin]; simp); omega
  have hR2 : ReadsBack n C2 := by
    intro j hj i hi
    rw [hl2] at hj
    rw [hg2 j] at hi
    by_cases hjm : j = m
    · rw [if_pos hjm] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · rw [if_neg hjm] at hi
      by_cases hjv : j = v - n
      · rw [if_pos hjv] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · rw [if_neg hjv] at hi
        exact hR j hj i hi
  refine ⟨hR2, by simp [Circuit.size, hC2], ?_⟩
  intro x
  have hx : (List.ofFn x).length = n := by simp
  -- the wire values of the two circuits
  have key : ∀ k, (k ≠ v → val C2 (List.ofFn x) k = val C (List.ofFn x) k) ∧
      (k = v → val C2 (List.ofFn x) k =
        (val C (List.ofFn x) a && val C (List.ofFn x) b)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      have same : ∀ i < k, i ≠ v → val C2 (List.ofFn x) i = val C (List.ofFn x) i :=
        fun i hi hiv => (ih i hi).1 hiv
      by_cases hkn : k < n
      · have e1 := val_input (C := C2) hx hkn
        have e2 := val_input (C := C) hx hkn
        refine ⟨fun _ => by rw [e1, e2], fun hk => by omega⟩
      · by_cases hklen : n + C.gates.length ≤ k
        · have e1 := val_ge (C := C2) (u := k) hx (by rw [hl2]; exact hklen)
          have e2 := val_ge (C := C) (u := k) hx hklen
          refine ⟨fun _ => by rw [e1, e2], fun hk => by omega⟩
        · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
          have hj : j < C.gates.length := by omega
          have hj2 : j < C2.gates.length := by rw [hl2]; exact hj
          have v2 := val_gate_rb hx hR2 hj2
          have v1 := val_gate_rb hx hR hj
          rw [hg2 j] at v2
          by_cases hjm : j = m
          · subst hjm
            rw [if_pos rfl, eval_or2] at v2
            rw [hmop, hmin, eval_and2] at v1
            have hu1 := val_gate_rb hx hR hui
            rw [huop, huin, eval_or2, hu_eq] at hu1
            have hv1 := val_gate_rb hx hR hvi
            rw [hvop, hvin, eval_or2, hv_eq] at hv1
            have ez := same z (by omega) (by omega)
            have ev := (ih v (by omega)).2 rfl
            refine ⟨fun _ => ?_, fun hk => by omega⟩
            rw [v2, v1, ez, ev, hu1, hv1]
            cases val C (List.ofFn x) z <;> cases val C (List.ofFn x) a <;>
              cases val C (List.ofFn x) b <;> rfl
          · rw [if_neg hjm] at v2
            by_cases hjv : j = v - n
            · subst hjv
              rw [if_pos rfl, eval_and2] at v2
              have ea := same a (by omega) (by omega)
              have eb := same b (by omega) (by omega)
              refine ⟨fun hk => by omega, fun _ => ?_⟩
              rw [v2, ea, eb]
            · rw [if_neg hjv] at v2
              refine ⟨fun _ => ?_, fun hk => by omega⟩
              rw [v2, v1]
              congr 1
              apply List.map_congr_left
              intro i hi
              have hlt : i < n + j := hR j hj i hi
              have hiv : i ≠ v := by
                rintro rfl
                exact hread j hj hjm hi
              exact same i hlt hiv
  rw [eval_eq_val, eval_eq_val]
  have ho : C2.output = C.output := rfl
  rw [ho]
  exact (key C.output).1 hout

end PEqualNP.Outside.L_meta_2860

theorem PEqualNP.Outside.L_meta_2860 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m u v z a b : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → n ≤ u → u < v → v < n + m → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs = [u, v] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).inputs = [z, a] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).inputs = [z, b] → (∀ j < C.gates.length, j ≠ m → v ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) → C.output ≠ v → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m u v z a b hR hm hnu huv hvm hmop hmin huop huin hvop hvin hread hout
  exact PEqualNP.Outside.L_meta_2860.main n C m u v z a b hR hm hnu huv hvm hmop hmin huop huin
    hvop hvin hread hout
