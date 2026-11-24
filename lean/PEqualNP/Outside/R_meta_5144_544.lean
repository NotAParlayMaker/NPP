import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

-- Reduce Petersen-minus-vertex with first gate OR(x0, x2) and second gate AND(x_i, x_j)
-- across the 21 orbit representatives under (0 2)(3 5)(4 7), then split NOT-free vs NOT-compiled.
theorem PEqualNP.Outside.R_meta_5144_544
    (hCompile : ∀ C : Circuit, FanInTwo C → ∃ (B : BinaryCircuit) (p : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) ∧
      B.size + notCount C ≤ C.size ∧
      ∀ w : List Bool, w.length = 11 → (B.eval (w ++ [false]) != p) = C.eval w)
    (hSigned : ∀ p ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 13, 14, 16, 18, 34, 35, 36, 37, 38, 46, 47, 48, 68] : List ℕ),
      ∀ (B : BinaryCircuit) (pol : Bool),
        (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
        B.size ≤ 12 →
        ∃ x : Fin 9 → Bool,
          (B.eval (List.ofFn x ++ [x 0 || x 2, x (Fin.ofNat 9 (p / 10)) && x (Fin.ofNat 9 (p % 10)), false]) != pol) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
             x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
             x 6 && x 8 || x 8 && x 5))
    (hMono : ∀ p ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 13, 14, 16, 18, 34, 35, 36, 37, 38, 46, 47, 48, 68] : List ℕ),
      ∀ C : Circuit, Monotone2 C →
        (∀ m ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ),
          C.eval (List.ofFn (fun k : Fin 9 => m.testBit k.val) ++ [m.testBit 0 || m.testBit 2, m.testBit (p / 10) && m.testBit (p % 10)]) = true) →
        (∀ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ),
          C.eval (List.ofFn (fun k : Fin 9 => m.testBit k.val) ++ [m.testBit 0 || m.testBit 2, m.testBit (p / 10) && m.testBit (p % 10)]) = false) →
        14 ≤ C.size) :
    ∀ (x1 x2 : Fin (9 : ℕ)),   x1 < x2 →     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ))];             x4.eval (x8 ++ [x7 x1 && x7 x2]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  classical
  let orbits : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 13, 14, 16, 18, 34, 35, 36, 37, 38, 46, 47, 48, 68]
  let target : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let row : Fin 9 → Fin 9 → (Fin 9 → Bool) → List Bool := fun i j x =>
    List.ofFn x ++ [x 0 || x 2, x i && x j]
  let sig : Fin 9 → Fin 9 := fun k => ([2, 1, 0, 5, 7, 3, 6, 4, 8] : List (Fin 9)).getD k.val 0
  let renWire : ℕ → ℕ := fun w => if h : w < 9 then (sig ⟨w, h⟩).val else w
  let renGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map renWire⟩
  let renCircuit : Circuit → Circuit := fun C => ⟨C.gates.map renGate, renWire C.output⟩
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hFinDiv : ∀ p ∈ orbits, (Fin.ofNat 9 (p / 10)).val = p / 10 ∧ (Fin.ofNat 9 (p % 10)).val = p % 10 := by
    decide
  have hSig0 : sig 0 = 2 := by decide
  have hSig2 : sig 2 = 0 := by decide
  have hOrb : ∀ (i j : Fin 9), i < j →
      (10 * i.val + j.val ∈ orbits) ∨
      (10 * (min (sig i) (sig j)).val + (max (sig i) (sig j)).val ∈ orbits) := by
    intro i j hij
    revert hij
    fin_cases i <;> fin_cases j <;> decide
  have hTargetBool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
      (a2 && a1 || a1 && a0 || a0 && a5 || a5 && a7 || a7 && a2 || a2 && a3 ||
       a1 && a6 || a0 && a4 || a5 && a8 || a3 && a4 || a6 && a8 || a8 && a3) =
      (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 ||
       a1 && a6 || a2 && a7 || a3 && a8 || a5 && a7 || a6 && a8 || a8 && a5) := by
    decide +kernel
  have hTargetSig : ∀ x : Fin 9 → Bool, target (fun k => x (sig k)) = target x := by
    intro x
    change (x (sig 0) && x (sig 1) || x (sig 1) && x (sig 2) || x (sig 2) && x (sig 3) ||
      x (sig 3) && x (sig 4) || x (sig 4) && x (sig 0) || x (sig 0) && x (sig 5) ||
      x (sig 1) && x (sig 6) || x (sig 2) && x (sig 7) || x (sig 3) && x (sig 8) ||
      x (sig 5) && x (sig 7) || x (sig 6) && x (sig 8) || x (sig 8) && x (sig 5)) = _
    have hs1 : sig 1 = 1 := by decide
    have hs3 : sig 3 = 5 := by decide
    have hs4 : sig 4 = 7 := by decide
    have hs5 : sig 5 = 3 := by decide
    have hs6 : sig 6 = 6 := by decide
    have hs7 : sig 7 = 4 := by decide
    have hs8 : sig 8 = 8 := by decide
    rw [hSig0, hs1, hSig2, hs3, hs4, hs5, hs6, hs7, hs8]
    exact hTargetBool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  have hEvalRen : ∀ (gs : List Gate) (u v : List Bool), u.length = v.length → 11 ≤ u.length →
      (∀ k : ℕ, u.getD (renWire k) false = v.getD k false) →
      ∀ k : ℕ, ((gs.map renGate).foldl step u).getD (renWire k) false = (gs.foldl step v).getD k false := by
    intro gs
    induction gs with
    | nil => intro u v _ _ h k; exact h k
    | cons g gs ih =>
      intro u v hlen hlen11 hagree k
      simp only [List.map_cons, List.foldl_cons]
      have hOut : g.op.eval ((renGate g).inputs.map fun i => u.getD i false) =
          g.op.eval (g.inputs.map fun i => v.getD i false) := by
        dsimp only [renGate]
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => hagree i)
      apply ih (step u (renGate g)) (step v g)
      · simp [step, hlen]
      · simp [step]; omega
      · intro m
        dsimp only [step]
        rw [hOut]
        by_cases hm9 : m < 9
        · have hrm : renWire m < 9 := by
            dsimp only [renWire]
            rw [dite_eq_left hm9]
            exact (sig ⟨m, hm9⟩).isLt
          have h1 : renWire m < u.length := Nat.lt_of_lt_of_le hrm (by omega)
          have h2 : m < v.length := Nat.lt_of_lt_of_le hm9 (by omega)
          rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
          exact hagree m
        · have hrm : renWire m = m := by dsimp only [renWire]; exact dite_eq_right hm9
          by_cases hmu : m < u.length
          · have hmv : m < v.length := hlen ▸ hmu
            have hrmu : renWire m < u.length := by rw [hrm]; exact hmu
            rw [List.getD_append _ _ _ _ hrmu, List.getD_append _ _ _ _ hmv]
            exact hagree m
          · by_cases hmeq : m = u.length
            · have hmveq : m = v.length := hlen ▸ hmeq
              conv_lhs => rw [hrm, hmeq, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
              conv_rhs => rw [hmveq, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
            · have h1 : (u ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).length ≤ renWire m := by
                rw [hrm]; simp; omega
              have h2 : (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).length ≤ m := by simp; omega
              rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
  intro x1 x2 hlt C hfan hsz
  by_contra hno
  have hCcorrect : ∀ x : Fin 9 → Bool, C.eval (row x1 x2 x) = target x := by
    intro x
    exact not_ne_iff.mp fun hne => hno ⟨x, by
      simpa only [row, target, List.append_assoc, List.cons_append, List.nil_append] using hne⟩
  have hRed : ∃ (p : ℕ) (D : Circuit), p ∈ orbits ∧ FanInTwo D ∧ D.size ≤ 13 ∧
      ∀ y : Fin 9 → Bool, D.eval (row (Fin.ofNat 9 (p / 10)) (Fin.ofNat 9 (p % 10)) y) = target y := by
    rcases hOrb x1 x2 hlt with h1 | h2
    · refine ⟨10 * x1.val + x2.val, C, h1, hfan, hsz, fun y => ?_⟩
      have hx1 : Fin.ofNat 9 ((10 * x1.val + x2.val) / 10) = x1 := by
        ext; have h2lt : x2.val < 9 := x2.isLt; have h1lt : x1.val < 9 := x1.isLt
        change ((10 * x1.val + x2.val) / 10) % 9 = x1.val; omega
      have hx2 : Fin.ofNat 9 ((10 * x1.val + x2.val) % 10) = x2 := by
        ext; have h2lt : x2.val < 9 := x2.isLt; change ((10 * x1.val + x2.val) % 10) % 9 = x2.val; omega
      rw [hx1, hx2]
      exact hCcorrect y
    · refine ⟨10 * (min (sig x1) (sig x2)).val + (max (sig x1) (sig x2)).val, renCircuit C, h2, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
        have hf := hfan g0 hg0
        exact ⟨hf.1, by simpa only [renGate, List.length_map] using hf.2⟩
      · change C.gates.length ≤ 13 at hsz
        change (C.gates.map renGate).length ≤ 13
        simpa only [List.length_map] using hsz
      · intro y
        let p := 10 * (min (sig x1) (sig x2)).val + (max (sig x1) (sig x2)).val
        let p1 := Fin.ofNat 9 (p / 10)
        let p2 := Fin.ofNat 9 (p % 10)
        have hp1 : p1 = min (sig x1) (sig x2) := by
          ext; have hm1 := (min (sig x1) (sig x2)).isLt; have hm2 := (max (sig x1) (sig x2)).isLt
          change (p / 10) % 9 = _; dsimp only [p]; omega
        have hp2 : p2 = max (sig x1) (sig x2) := by
          ext; have hm1 := (min (sig x1) (sig x2)).isLt; have hm2 := (max (sig x1) (sig x2)).isLt
          change (p % 10) % 9 = _; dsimp only [p]; omega
        have hand : (y p1 && y p2) = (y (sig x1) && y (sig x2)) := by
          rw [hp1, hp2]
          by_cases hle : sig x1 ≤ sig x2
          · rw [min_eq_left hle, max_eq_right hle]
          · have hlt' : sig x2 ≤ sig x1 := le_of_not_ge hle
            rw [min_eq_right hlt', max_eq_left hlt', Bool.and_comm]
        have hagree : ∀ k : ℕ, (row p1 p2 y).getD (renWire k) false =
            (row x1 x2 (fun t => y (sig t))).getD k false := by
          intro k
          have hofFn (z : Fin 9 → Bool) (m : ℕ) (hm : m < 9) :
              (List.ofFn z).getD m false = z ⟨m, hm⟩ := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            simp only [hm, ↓reduceDIte, Option.getD_some]
          by_cases hk9 : k < 9
          · have hrm : (sig ⟨k, hk9⟩).val < 9 := (sig ⟨k, hk9⟩).isLt
            dsimp only [renWire, row]
            rw [dite_eq_left hk9, List.getD_append _ _ _ _ (by simp [hrm]), hofFn y _ hrm,
                List.getD_append _ _ _ _ (by simp [hk9]), hofFn _ k hk9]
          · have hrm : renWire k = k := by dsimp only [renWire]; exact dite_eq_right hk9
            rw [hrm]
            by_cases hk9eq : k = 9
            · subst hk9eq
              dsimp only [row]
              rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
              simp [hSig0, hSig2, Bool.or_comm]
            · by_cases hk10eq : k = 10
              · subst hk10eq
                dsimp only [row]
                rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
                simpa [List.length_ofFn] using hand
              · have hlen1 : (row p1 p2 y).length ≤ k := by simp [row]; omega
                have hlen2 : (row x1 x2 (fun t => y (sig t))).length ≤ k := by simp [row]; omega
                rw [List.getD_eq_default _ _ hlen1, List.getD_eq_default _ _ hlen2]
        have hEval := hEvalRen C.gates (row p1 p2 y) (row x1 x2 (fun t => y (sig t)))
          (by simp [row]) (by simp [row]) hagree C.output
        have hDval : (renCircuit C).eval (row p1 p2 y) = C.eval (row x1 x2 (fun t => y (sig t))) := by
          exact hEval
        rw [hDval, hCcorrect (fun t => y (sig t)), hTargetSig y]
  obtain ⟨p, D, hp, hDfan, hDsz, hDeq⟩ := hRed
  by_cases hzero : notCount D = 0
  · have hDmono : Monotone2 D := by
      intro g hg
      have hf := hDfan g hg
      rcases hf.1 with h1 | h2 | h3
      · exact ⟨Or.inl h1, hf.2⟩
      · exact ⟨Or.inr h2, hf.2⟩
      · exfalso
        unfold notCount at hzero
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hzero
        have hne := hzero g hg
        rw [h3] at hne
        exact hne rfl
    have hpos : ∀ m ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ),
        D.eval (List.ofFn (fun k : Fin 9 => m.testBit k.val) ++ [m.testBit 0 || m.testBit 2, m.testBit (p / 10) && m.testBit (p % 10)]) = true := by
      intro m hm
      have hsub := hDeq (fun k : Fin 9 => m.testBit k.val)
      have hdiv := hFinDiv p hp
      change D.eval (List.ofFn (fun k : Fin 9 => m.testBit k.val) ++ [m.testBit 0 || m.testBit 2, m.testBit (Fin.ofNat 9 (p / 10)).val && m.testBit (Fin.ofNat 9 (p % 10)).val]) = _ at hsub
      rw [hdiv.1, hdiv.2] at hsub
      rw [hsub]
      have htests : ∀ m ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ),
          target (fun k : Fin 9 => m.testBit k.val) = true := by decide +kernel
      exact htests m hm
    have hneg : ∀ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ),
        D.eval (List.ofFn (fun k : Fin 9 => m.testBit k.val) ++ [m.testBit 0 || m.testBit 2, m.testBit (p / 10) && m.testBit (p % 10)]) = false := by
      intro m hm
      have hsub := hDeq (fun k : Fin 9 => m.testBit k.val)
      have hdiv := hFinDiv p hp
      change D.eval (List.ofFn (fun k : Fin 9 => m.testBit k.val) ++ [m.testBit 0 || m.testBit 2, m.testBit (Fin.ofNat 9 (p / 10)).val && m.testBit (Fin.ofNat 9 (p % 10)).val]) = _ at hsub
      rw [hdiv.1, hdiv.2] at hsub
      rw [hsub]
      have htests : ∀ m ∈ ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ),
          target (fun k : Fin 9 => m.testBit k.val) = false := by decide +kernel
      exact htests m hm
    have h14 := hMono p hp D hDmono hpos hneg
    omega
  · obtain ⟨B, pol, hsig, hcost, hreplay⟩ := hCompile D hDfan
    have hBsz : B.size ≤ 12 := by omega
    obtain ⟨x, hxne⟩ := hSigned p hp B pol hsig hBsz
    have h1 := hreplay (row (Fin.ofNat 9 (p / 10)) (Fin.ofNat 9 (p % 10)) x) (by simp [row])
    rw [hDeq x] at h1
    change (B.eval (row (Fin.ofNat 9 (p / 10)) (Fin.ofNat 9 (p % 10)) x ++ [false]) != pol) ≠ target x at hxne
    exact hxne h1
