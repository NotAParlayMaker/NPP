import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK

-- Delete line 1 and its four points {1, 2, 4, 10}, keeping point 0 and line 0 inside AG(2, 3).
-- A 19-gate four-star boundary circuit plus one OR gate preserves IsAO2, Nodup, and lineSingle on (0, 13).
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4877_427
    (glue :
      let inp := (List.finRange 26).filter (fun i => i.val ∉ ([1, 2, 4, 10, 14] : List ℕ))
      let hit := fun (x : Fin 26 → Bool) => decide (∃ p ∈ ({1, 2, 4, 10} : Finset (Fin 13)), ∃ l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
      ∀ B : Circuit, IsAO2 21 B → (∀ g ∈ B.gates, g.inputs.Nodup) → B.output < 21 + B.size →
        ∃ C : Circuit, C.size ≤ B.size + 20 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
          (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = (B.eval (inp.map x) || hit x)) ∧
          ∀ s : Bool,
            lineSingle C 26 (fun i => decide (i = if s then 0 else 13)) 0 13 =
            lineSingle B 21 (fun i => decide (i = if s then 0 else 9)) 0 9)
    (gateParts :
      ∀ (x1 x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x2 < x1 → x3 < x1 → x2 ≠ x3 → PEqualNP.TopForm.IsAO2 x1 x4 →
          have x9 : List (Bool × Bool) := PEqualNP.ReadK.linearParts x4 (fun (x9 : ℕ) => Decidable.decide (x9 = x2)) (List.map (fun (x9 : ℕ) => x9 == x2 || x9 == x3) (List.range x1));
          have x10 : ℕ → Bool := fun (x10 : ℕ) => (x9.getD x10 (Bool.false, Bool.false)).2;
          have x11 : List Bool := x4.wires (List.ofFn fun (x11 : Fin x1) => Decidable.decide (↑x11 = x3));
          ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ),
            x4.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] →
              (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x10 (x1 + x12) = (x11.getD x14 Bool.false && x10 x15 || x10 x14 && x11.getD x15 Bool.false)) ∧
              (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10 (x1 + x12) = (x10 x14 || x10 x15)))
    (affine44 :
      let z := fun (x : Fin 13 → Bool) (j : Fin 13) => !(x j || x (j + 1) || x (j + 3) || x (j + 9))
      let inp := (List.finRange 26).filter (fun i => i.val ∉ ([1, 2, 4, 10, 14] : List ℕ))
      let one := fun (p i : Fin 13) => decide (i = p)
      ∃ B : Circuit, B.size ≤ 44 ∧ IsAO2 21 B ∧ (∀ g ∈ B.gates, g.inputs.Nodup) ∧
        B.output < 21 + B.size ∧
        (∀ p l : Fin 13, p ∉ ({1, 2, 4, 10} : Finset (Fin 13)) → z (one p) l = false →
          B.eval (inp.map (Fin.addCases (one p) (one l))) = true) ∧
        (∀ y : Fin 13 → Bool, (List.ofFn y).count true ≤ 3 →
          B.eval (inp.map (Fin.addCases y (z y))) = false ∧
          B.eval (inp.map (Fin.addCases (fun p => !(y p || y (p - 1) || y (p - 3) || y (p - 9))) y)) = false) ∧
        ∀ s : Bool, lineSingle B 21 (fun i => decide (i = if s then 0 else 9)) 0 9 = false) :
    have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧       (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧         (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧           (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧             ∀ (x5 : Bool),               ∃ (x6 : ℕ → Bool),                 (∀ x7 < (26 : ℕ), x6 x7 = Decidable.decide (x7 = if x5 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ),                       x4.gates[x7]? = Option.some x8 →                         x8.inputs = [x9, x10] →                           have x13 : List Bool := x4.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ((26 : ℕ) + x7) = (x13.getD x9 Bool.false && x6 x10 || x6 x9 && x13.getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 ((26 : ℕ) + x7) = (x6 x9 || x6 x10))) ∧                     x6 x4.output = Bool.false := by
  dsimp only at glue affine44 ⊢
  obtain ⟨B, hBsz, hBao, hBnd, hBout, hBpos, hBneg, hBsing⟩ := affine44
  obtain ⟨C, hCsz, hCao, hCnd, hCeval, hCsing⟩ := glue B hBao hBnd hBout
  let z : (Fin 13 → Bool) → Fin 13 → Bool := fun x j => !(x j || x (j + 1) || x (j + 3) || x (j + 9))
  let inp : List (Fin 26) := (List.finRange 26).filter (fun i => i.val ∉ ([1, 2, 4, 10, 14] : List ℕ))
  let hit : (Fin 26 → Bool) → Bool := fun x => decide (∃ p ∈ ({1, 2, 4, 10} : Finset (Fin 13)), ∃ l : Fin 13,
    (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  refine ⟨C, by omega, hCao, hCnd, ?_, ?_, ?_⟩
  · intro p l hinc
    change C.eval (List.ofFn (Fin.addCases (fun i => decide (i = p)) (fun i => decide (i = l)))) = true
    rw [hCeval, Bool.or_eq_true]
    by_cases hp : p ∈ ({1, 2, 4, 10} : Finset (Fin 13))
    · right
      apply decide_eq_true
      refine ⟨p, hp, l, ?_, ?_, ?_⟩
      · change (!(decide (l = p) || decide (l + 1 = p) || decide (l + 3 = p) || decide (l + 9 = p))) = false at hinc
        simp only [Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq] at hinc
        rcases hinc with ((h | h) | h) | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inr (Or.inr (Or.inl h.symm))
        · exact Or.inr (Or.inr (Or.inr h.symm))
      · simp [Fin.addCases]
      · simp [Fin.addCases]
    · left
      exact hBpos p l hp hinc
  · intro y hy
    obtain ⟨hneg1, hneg2⟩ := hBneg y hy
    constructor
    · change C.eval (List.ofFn (fun i => Fin.addCases y (z y) i)) = false
      rw [hCeval]
      have hh : hit (fun i => Fin.addCases y (z y) i) = false := by
        apply decide_eq_false
        rintro ⟨p, _, l, hpl, hpy, hly⟩
        simp only [Fin.addCases_left, Fin.addCases_right] at hpy hly
        change (!(y l || y (l + 1) || y (l + 3) || y (l + 9))) = true at hly
        rcases hpl with rfl | rfl | rfl | rfl <;> simp [hpy] at hly
      rw [hneg1]
      change (false || hit (fun i => Fin.addCases y (z y) i)) = false
      rw [hh]; rfl
    · let y' : Fin 13 → Bool := fun p => !(y p || y (p - 1) || y (p - 3) || y (p - 9))
      change C.eval (List.ofFn (fun i => Fin.addCases y' y i)) = false
      rw [hCeval]
      have hh : hit (fun i => Fin.addCases y' y i) = false := by
        apply decide_eq_false
        rintro ⟨p, _, l, hpl, hpy, hly⟩
        simp only [Fin.addCases_left, Fin.addCases_right] at hpy hly
        change (!(y p || y (p - 1) || y (p - 3) || y (p - 9))) = true at hpy
        rcases hpl with rfl | rfl | rfl | rfl <;> simp [hly] at hpy
      rw [hneg2]
      change (false || hit (fun i => Fin.addCases y' y i)) = false
      rw [hh]; rfl
  · intro s
    let mark : ℕ → Bool := fun i => decide (i = if s = true then 0 else 13)
    let bits : List Bool := (List.range 26).map fun i => i == 0 || i == 13
    let parts : List (Bool × Bool) := linearParts C mark bits
    let initial : List (Bool × Bool) := bits.zipIdx.map fun p => if mark p.2 then (false, p.1) else (p.1, false)
    have hprefix : initial <+: parts := by
      have keepsPrefix (value : List (Bool × Bool) → Gate → Bool × Bool)
          (gs : List Gate) (w : List (Bool × Bool)) :
          w <+: gs.foldl (fun v g => v ++ [value v g]) w := by
        induction gs generalizing w with
        | nil => exact ⟨[], by simp⟩
        | cons g gs ih => exact List.IsPrefix.trans ⟨[value w g], rfl⟩ (ih _)
      exact keepsPrefix _ C.gates initial
    have hcomm : ((List.range 26).map fun i => i == 13 || i == 0) = bits := by
      dsimp only [bits]
      apply List.map_congr_left
      intro i _
      exact Bool.or_comm _ _
    refine ⟨fun i => (parts.getD i (false, false)).2, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨tail, ht⟩ := hprefix
      have hlen : i < initial.length := by simpa [initial, bits] using hi
      change (parts.getD i (false, false)).2 = mark i
      rw [← ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
      have initOK (j : Fin 26) :
          ((initial[j.val]?).getD (false, false)).2 = mark j.val := by
        revert j
        cases s <;> decide
      exact initOK ⟨i, hi⟩
    · cases s
      · have hgp := gateParts 26 13 0 C (by decide) (by decide) (by decide) hCao
        simpa only [parts, mark, hcomm, Bool.false_eq_true, ite_false] using hgp
      · have hgp := gateParts 26 0 13 C (by decide) (by decide) (by decide) hCao
        simpa only [parts, mark, bits, ite_true] using hgp
    · exact (hCsing s).trans (hBsing s)
