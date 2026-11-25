import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7577

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def remapW (p q : Equiv.Perm (Fin 13)) (w : Nat) : Nat :=
  if h1 : w < 13 then (p ⟨w, h1⟩).val
  else if h2 : w < 26 then 13 + (q ⟨w - 13, by omega⟩).val
  else w

def remapGate (p q : Equiv.Perm (Fin 13)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapW p q)⟩

def circStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma remapW_lt26 (p q : Equiv.Perm (Fin 13)) (w : Nat) (hw : w < 26) :
    remapW p q w < 26 := by
  unfold remapW
  split_ifs with h1 _
  · have := (p ⟨w, h1⟩).isLt; omega
  · have := (q ⟨w - 13, by omega⟩).isLt; omega

lemma remapW_ge26 (p q : Equiv.Perm (Fin 13)) (w : Nat) (hw : 26 ≤ w) :
    remapW p q w = w := by
  unfold remapW
  have h1 : ¬ (w < 13) := by omega
  have h2 : ¬ (w < 26) := by omega
  simp [h1, h2]

lemma remapW_lt_add (p q : Equiv.Perm (Fin 13)) (k w : Nat) (hw : w < 26 + k) :
    remapW p q w < 26 + k := by
  by_cases h : w < 26
  · have := remapW_lt26 p q w h; omega
  · rw [remapW_ge26 p q w (by omega)]; exact hw

lemma gateAt_map (p q : Equiv.Perm (Fin 13)) (C : Circuit) (k : Nat) :
    gateAt ⟨C.gates.map (remapGate p q), remapW p q C.output⟩ k =
      if k < C.gates.length then remapGate p q (gateAt C k) else ⟨.or, []⟩ := by
  unfold gateAt
  by_cases hk : k < C.gates.length
  · simp only [hk, ite_true, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
  · simp only [hk, ite_false, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt hk), Option.map_none, Option.getD_none]

lemma gateAt_op_eq (p q : Equiv.Perm (Fin 13)) (C : Circuit) (k : Nat) :
    (gateAt ⟨C.gates.map (remapGate p q), remapW p q C.output⟩ k).op = (gateAt C k).op := by
  rw [gateAt_map]
  split_ifs with hk
  · rfl
  · unfold gateAt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hk)]

lemma foldl_remap (p q : Equiv.Perm (Fin 13)) (gs : List Gate) (a b : List Bool)
    (hlen : a.length = b.length) (h26 : 26 ≤ a.length)
    (hmatch : ∀ w, b.getD (remapW p q w) false = a.getD w false) :
    ∀ w, ((gs.map (remapGate p q)).foldl circStep b).getD (remapW p q w) false =
      (gs.foldl circStep a).getD w false := by
  induction gs generalizing a b with
  | nil => exact hmatch
  | cons g tl ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hval : (remapGate p q g).op.eval ((remapGate p q g).inputs.map fun i => b.getD i false) =
        g.op.eval (g.inputs.map fun i => a.getD i false) := by
      simp only [remapGate, List.map_map, Function.comp_def, hmatch]
    apply ih (circStep a g) (circStep b (remapGate p q g))
    · simp [circStep, hlen]
    · simp [circStep]; omega
    · intro w
      unfold circStep
      rw [hval]
      by_cases hw : w < a.length
      · have hrw : remapW p q w < b.length := by
          have := remapW_lt_add p q (a.length - 26) w (by omega)
          omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hrw,
            List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
        exact hmatch w
      · by_cases heq : w = a.length
        · subst heq
          have hrw : remapW p q a.length = b.length := by
            rw [remapW_ge26 p q a.length h26, hlen]
          rw [hrw, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
          simp
        · have hgt : a.length < w := by omega
          have hrw : b.length < remapW p q w := by
            rw [remapW_ge26 p q w (by omega)]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]

lemma main :
    have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) =>
      (List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) ++
      List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2);
    have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ∃ x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).inputs,
        (26 : ℕ) ≤ x4 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x4 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and;
    ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Equiv.Perm (Fin (13 : ℕ))),
      PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 →
      ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ → ℕ),
        x8.size = x3.size ∧ PEqualNP.MetaComplexity.Monotone2 x8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x8 ∧
        (∀ x10 < (26 : ℕ) + x3.size, x9 x10 < (26 : ℕ) + x8.size) ∧
        (∀ (x10 : ℕ), x2 x3 x10 → x2 x8 x10) ∧
        ∀ (x10 : ℕ) (x11 x12 : Finset (Fin (13 : ℕ))),
          (x8.wires (x1 x11 x12)).getD (x9 x10) Bool.false =
            (x3.wires (x1 (Finset.image (⇑(Equiv.symm x4)) x11) (Finset.image (⇑(Equiv.symm x5)) x12))).getD x10 Bool.false := by
  intro x1 x2 x3 x4 x5 hmono hrb
  let x8 : Circuit := ⟨x3.gates.map (remapGate x4 x5), remapW x4 x5 x3.output⟩
  refine ⟨x8, remapW x4 x5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [x8, Circuit.size]
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    simpa [remapGate] using hmono g0 hg0
  · intro k hk u hu
    have hk' : k < x3.gates.length := by simpa [x8] using hk
    rw [gateAt_map, if_pos hk'] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact remapW_lt_add x4 x5 k v (hrb k hk' v hv)
  · intro w hw
    have hsz : x8.size = x3.size := by simp [x8, Circuit.size]
    rw [hsz]
    exact remapW_lt_add x4 x5 x3.size w hw
  · intro k ⟨hop, u, hu, h26, huop⟩
    have hk : k < x3.gates.length := by
      by_contra h
      have hgate : gateAt x3 k = ⟨.or, []⟩ := by
        unfold gateAt; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]
      rw [hgate] at hop; cases hop
    refine ⟨?_, u, ?_, h26, ?_⟩
    · rw [gateAt_op_eq]; exact hop
    · rw [gateAt_map, if_pos hk]
      refine List.mem_map.mpr ⟨u, hu, remapW_ge26 x4 x5 u h26⟩
    · rw [gateAt_op_eq]; exact huop
  · intro w A B
    let b := x1 A B
    let a := x1 (Finset.image x4.symm A) (Finset.image x5.symm B)
    have hinit : ∀ u, b.getD (remapW x4 x5 u) false = a.getD u false := by
      intro u
      by_cases h1 : u < 13
      · have hru : remapW x4 x5 u = (x4 ⟨u, h1⟩).val := by simp [remapW, h1]
        rw [hru]
        have hlt1 : (x4 ⟨u, h1⟩).val < 13 := (x4 ⟨u, h1⟩).isLt
        have hl1 : (List.ofFn fun x3 : Fin 13 => decide (x3 ∈ A)).length = 13 := List.length_ofFn
        have hl2 : (List.ofFn fun x3 : Fin 13 => decide (x3 ∈ Finset.image x4.symm A)).length = 13 := List.length_ofFn
        unfold b a x1
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        rw [List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hlt1, dif_pos h1]
        simp only [Option.getD_some, decide_eq_decide]
        constructor
        · intro hmem
          exact Finset.mem_image.mpr ⟨x4 ⟨u, h1⟩, hmem, by simp⟩
        · intro hmem
          obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp hmem
          have : x4 ⟨u, h1⟩ = y := by rw [← hyu]; simp
          simpa [this] using hy
      · by_cases h2 : u < 26
        · have hru : remapW x4 x5 u = 13 + (x5 ⟨u - 13, by omega⟩).val := by simp [remapW, h1, h2]
          rw [hru]
          have hlt2 : (x5 ⟨u - 13, by omega⟩).val < 13 := (x5 ⟨u - 13, by omega⟩).isLt
          have hl1 : (List.ofFn fun x3 : Fin 13 => decide (x3 ∈ A)).length = 13 := List.length_ofFn
          have hl2 : (List.ofFn fun x3 : Fin 13 => decide (x3 ∈ Finset.image x4.symm A)).length = 13 := List.length_ofFn
          unfold b a x1
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
              hl1, hl2, Nat.add_sub_cancel_left]
          rw [List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hlt2, dif_pos (show u - 13 < 13 by omega)]
          simp only [Option.getD_some, decide_eq_decide]
          constructor
          · intro hmem
            exact Finset.mem_image.mpr ⟨x5 ⟨u - 13, by omega⟩, hmem, by simp⟩
          · intro hmem
            obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp hmem
            have : x5 ⟨u - 13, by omega⟩ = y := by rw [← hyu]; simp
            simpa [this] using hy
        · have hru : remapW x4 x5 u = u := remapW_ge26 x4 x5 u (by omega)
          rw [hru]
          have hlen_a : a.length = 26 := by simp [a, x1]
          have hlen_b : b.length = 26 := by simp [b, x1]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact foldl_remap x4 x5 x3.gates a b (by simp [a, b, x1]) (by simp [a, x1]) hinit w

end PEqualNP.Outside.L_meta_7577

theorem PEqualNP.Outside.L_meta_7577 :
    have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) ++ List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2); have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).inputs, (26 : ℕ) ≤ x4 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x4 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Equiv.Perm (Fin (13 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ → ℕ), x8.size = x3.size ∧ PEqualNP.MetaComplexity.Monotone2 x8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x8 ∧ (∀ x10 < (26 : ℕ) + x3.size, x9 x10 < (26 : ℕ) + x8.size) ∧ (∀ (x10 : ℕ), x2 x3 x10 → x2 x8 x10) ∧ ∀ (x10 : ℕ) (x11 x12 : Finset (Fin (13 : ℕ))), (x8.wires (x1 x11 x12)).getD (x9 x10) Bool.false = (x3.wires (x1 (Finset.image (⇑(Equiv.symm x4)) x11) (Finset.image (⇑(Equiv.symm x5)) x12))).getD x10 Bool.false :=
  PEqualNP.Outside.L_meta_7577.main
