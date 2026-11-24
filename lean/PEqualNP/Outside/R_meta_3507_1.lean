import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3507_1
    (many_nots :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
        13 ≤ C.size - PEqualNP.NotBracket.notCount C)
    (orb_deg3 :
      ∀ p ∈ ([(1, 2), (2, 3)] : List (Fin 9 × Fin 9)),
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          PEqualNP.NotBracket.notCount C ≤ 2 →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) =
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
          False)
    (orb_deg2 :
      ∀ p ∈ ([(1, 6), (2, 7)] : List (Fin 9 × Fin 9)),
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          PEqualNP.NotBracket.notCount C ≤ 2 →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x p.1 || x p.2]) =
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
          False) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → ↑x1 * (10 : ℕ) + ↑x2 ∈ [(12 : ℕ), (21 : ℕ), (23 : ℕ), (32 : ℕ), (16 : ℕ), (61 : ℕ), (27 : ℕ), (72 : ℕ), (38 : ℕ), (83 : ℕ), (57 : ℕ), (75 : ℕ), (68 : ℕ), (86 : ℕ), (58 : ℕ), (85 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x12 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)), x12 x1 || x12 x2]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) → False := by
  classical
  intro a b C _ _ _ _ _ hcode hfan hsz heq
  let edge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  let mapGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
  have ofFn_getD (x : Fin 9 → Bool) (k : ℕ) (hk : k < 9) :
      (List.ofFn x).getD k false = x ⟨k, hk⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hk, ↓reduceDIte, Option.getD_some]
  -- Bound notCount C ≤ 2 via many_nots
  have hnot_le2 : PEqualNP.NotBracket.notCount C ≤ 2 := by
    let g0 : Gate := ⟨.or, [0, 4]⟩
    let g1 : Gate := ⟨.or, [a.val, b.val]⟩
    let full : Circuit := ⟨g0 :: g1 :: C.gates, C.output⟩
    have hfull_fan : FanInTwo full := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg1
      · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
      · rcases List.mem_cons.mp hg1 with rfl | hg2
        · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
        · exact hfan g hg2
    have hfull_eval : ∀ x : Fin 9 → Bool, full.eval (List.ofFn x) = edge x := by
      intro x
      let x7 := List.ofFn x ++ [x 0 || x 4]
      have hs0 : step (List.ofFn x) g0 = x7 := by
        change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false]] = x7
        rw [ofFn_getD x 0 (by omega), ofFn_getD x 4 (by omega)]
        change List.ofFn x ++ [(x 0 || (x 4 || false))] = x7
        rw [Bool.or_false]
      have hs1 : step x7 g1 = List.ofFn x ++ [x 0 || x 4, x a || x b] := by
        change x7 ++ [GateOp.or.eval [x7.getD a.val false, x7.getD b.val false]] = _
        have ha : x7.getD a.val false = x a := by
          rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact a.isLt), ofFn_getD x a.val a.isLt]
        have hb : x7.getD b.val false = x b := by
          rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact b.isLt), ofFn_getD x b.val b.isLt]
        rw [ha, hb]
        change (List.ofFn x ++ [x 0 || x 4]) ++ [(x a || (x b || false))] = List.ofFn x ++ [x 0 || x 4, x a || x b]
        rw [Bool.or_false, List.append_assoc]
        rfl
      change ((g0 :: g1 :: C.gates).foldl step (List.ofFn x)).getD C.output false = edge x
      rw [List.foldl_cons, hs0, List.foldl_cons, hs1]
      exact heq x
    have h13 := many_nots full hfull_fan hfull_eval
    have hfsz : full.size = 2 + C.size := by
      change (g0 :: g1 :: C.gates).length = 2 + C.gates.length
      simp only [List.length_cons]; omega
    have hfnot : PEqualNP.NotBracket.notCount full = PEqualNP.NotBracket.notCount C := by
      unfold PEqualNP.NotBracket.notCount
      rfl
    rw [hfsz, hfnot] at h13
    omega
  -- Involution r = (1 5)(2 8)(6 7) fixing 0, 3, 4 (hence fixing x 0 || x 4)
  let rL : List ℕ := [0, 5, 8, 3, 4, 1, 7, 6, 2]
  have hr_lt (i : Fin 9) : rL.getD i.val 0 < 9 := by fin_cases i <;> decide
  let rf (i : Fin 9) : Fin 9 := ⟨rL.getD i.val 0, hr_lt i⟩
  let fR (k : ℕ) : ℕ := if k < 9 then rL.getD k 0 else k
  let Cr : Circuit := ⟨C.gates.map (mapGate fR), fR C.output⟩
  have hCr_fan : FanInTwo Cr := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen0⟩ := hfan g0 hg0
    exact ⟨hop, by simp only [mapGate, List.length_map]; exact hlen0⟩
  have hCr_sz : Cr.size ≤ 13 := by
    change (C.gates.map (mapGate fR)).length ≤ 13
    rw [List.length_map]; exact hsz
  have hCr_not : PEqualNP.NotBracket.notCount Cr ≤ 2 := by
    have hEq : PEqualNP.NotBracket.notCount Cr = PEqualNP.NotBracket.notCount C := by
      unfold PEqualNP.NotBracket.notCount
      dsimp only [Cr]
      rw [List.filter_map, List.length_map]
      rfl
    rw [hEq]; exact hnot_le2
  have hinv_bool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
      (a0 && a5 || a5 && a8 || a8 && a3 || a3 && a4 || a4 && a0 || a0 && a1 ||
       a5 && a7 || a8 && a6 || a3 && a2 || a1 && a6 || a7 && a2 || a2 && a1) =
      (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 ||
       a1 && a6 || a2 && a7 || a3 && a8 || a5 && a7 || a6 && a8 || a8 && a5) := by decide
  have hedge_r (x : Fin 9 → Bool) : edge (fun i => x (rf i)) = edge x :=
    hinv_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  have rewire_r : ∀ (gs : List Gate) (u v : List Bool),
      u.length = v.length → 11 ≤ u.length →
      (∀ k, k < u.length → v.getD (fR k) false = u.getD k false) →
      ∀ k, ((gs.map (mapGate fR)).foldl step v).getD (fR k) false = (gs.foldl step u).getD k false := by
    intro gs
    induction gs with
    | nil =>
      intro u v hlen _ hagree k
      change v.getD (fR k) false = u.getD k false
      by_cases hk : k < u.length
      · exact hagree k hk
      · have hfk : fR k = k := by simp only [fR, show ¬ (k < 9) by omega, ↓reduceIte]
        rw [hfk, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    | cons g gs ih =>
      intro u v hlen h11 hagree k
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hall : ∀ j, v.getD (fR j) false = u.getD j false := by
        intro j
        by_cases hj : j < u.length
        · exact hagree j hj
        · have hfj : fR j = j := by simp only [fR, show ¬ (j < 9) by omega, ↓reduceIte]
          rw [hfj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      have hbit : (mapGate fR g).op.eval ((mapGate fR g).inputs.map fun j => v.getD j false) =
                  g.op.eval (g.inputs.map fun j => u.getD j false) := by
        change g.op.eval ((g.inputs.map fR).map fun j => v.getD j false) = _
        rw [List.map_map]
        congr 1
        exact List.map_congr_left fun j _ => hall j
      have hstep_v : step v (mapGate fR g) = v ++ [g.op.eval (g.inputs.map fun j => u.getD j false)] := by
        change v ++ [(mapGate fR g).op.eval ((mapGate fR g).inputs.map fun j => v.getD j false)] = _
        rw [hbit]
      apply ih (step u g) (step v (mapGate fR g))
      · change (u ++ [_]).length = (v ++ [_]).length; simp only [List.length_append, List.length_singleton]; omega
      · change 11 ≤ (u ++ [_]).length; simp only [List.length_append, List.length_singleton]; omega
      · intro j hj
        rw [hstep_v]
        change (v ++ [g.op.eval (g.inputs.map fun t => u.getD t false)]).getD (fR j) false =
               (u ++ [g.op.eval (g.inputs.map fun t => u.getD t false)]).getD j false
        have hulen : (step u g).length = u.length + 1 := by
          change (u ++ [_]).length = u.length + 1; simp only [List.length_append, List.length_singleton]
        by_cases hlast : j = u.length
        · subst hlast
          have hfj : fR u.length = v.length := by simp only [fR, show ¬ (u.length < 9) by omega, ↓reduceIte]; omega
          rw [hfj, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
              List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        · have hjlt : j < u.length := by omega
          have hfjlt : fR j < v.length := by
            by_cases hj9 : j < 9
            · have hfj : fR j = rL.getD j 0 := by simp only [fR, hj9, ↓reduceIte]
              have hlt := hr_lt ⟨j, hj9⟩
              change rL.getD j 0 < 9 at hlt
              omega
            · have hfj : fR j = j := by simp only [fR, hj9, ↓reduceIte]
              omega
          rw [List.getD_append _ _ _ _ hfjlt, List.getD_append _ _ _ _ hjlt]
          exact hagree j hjlt
  have heq_r : ∀ x : Fin 9 → Bool,
      Cr.eval (List.ofFn x ++ [x 0 || x 4, x (rf a) || x (rf b)]) = edge x := by
    intro x
    let xr : Fin 9 → Bool := fun i => x (rf i)
    let u0 : List Bool := List.ofFn xr ++ [xr 0 || xr 4, xr a || xr b]
    let v0 : List Bool := List.ofFn x ++ [x 0 || x 4, x (rf a) || x (rf b)]
    have hrew : Cr.eval v0 = C.eval u0 := by
      change ((C.gates.map (mapGate fR)).foldl step v0).getD (fR C.output) false =
             (C.gates.foldl step u0).getD C.output false
      exact rewire_r C.gates u0 v0
        (by simp only [u0, v0, List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
        (by simp only [u0, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)
        (fun k hk => by
          have hk11 : k < 11 := by
            simp only [u0, List.length_append, List.length_ofFn, List.length_cons, List.length_nil] at hk; omega
          by_cases hk9 : k < 9
          · have hfk : fR k = rL.getD k 0 := by simp only [fR, hk9, ↓reduceIte]
            have hlt9 : rL.getD k 0 < 9 := hr_lt ⟨k, hk9⟩
            have hlhs : v0.getD (fR k) false = x ⟨rL.getD k 0, hlt9⟩ := by
              rw [hfk, List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hlt9),
                  ofFn_getD x (rL.getD k 0) hlt9]
            have hrhs : u0.getD k false = xr ⟨k, hk9⟩ := by
              rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hk9),
                  ofFn_getD xr k hk9]
            rw [hlhs, hrhs]
          · by_cases hk9e : k = 9
            · subst hk9e
              have hf9 : fR 9 = 9 := rfl
              rw [hf9]
              have hlhs : v0.getD 9 false = (x 0 || x 4) := by
                rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
                simp only [List.length_ofFn, Nat.sub_self]; rfl
              have hrhs : u0.getD 9 false = (xr 0 || xr 4) := by
                rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
                simp only [List.length_ofFn, Nat.sub_self]; rfl
              rw [hlhs, hrhs]; rfl
            · have hk10 : k = 10 := by omega
              subst hk10
              have hf10 : fR 10 = 10 := rfl
              rw [hf10]
              have hlhs : v0.getD 10 false = (x (rf a) || x (rf b)) := by
                rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
                simp only [List.length_ofFn]; rfl
              have hrhs : u0.getD 10 false = (xr a || xr b) := by
                rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
                simp only [List.length_ofFn]; rfl
              rw [hlhs, hrhs])
        C.output
    exact (hrew.trans (heq xr)).trans (hedge_r x)
  -- Dispatch all 16 codes to the 4 canonical orbits
  have heq_comm : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 4, x b || x a]) = edge x := by
    intro x; rw [Bool.or_comm (x b) (x a)]; exact heq x
  have heq_r_comm : ∀ x : Fin 9 → Bool,
      Cr.eval (List.ofFn x ++ [x 0 || x 4, x (rf b) || x (rf a)]) = edge x := by
    intro x; rw [Bool.or_comm (x (rf b)) (x (rf a))]; exact heq_r x
  have hcode_dec : ∀ i j : Fin 9,
      i.val * 10 + j.val ∈ ([12, 21, 23, 32, 16, 61, 27, 72, 38, 83, 57, 75, 68, 86, 58, 85] : List ℕ) →
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      (i = 1 ∧ j = 6) ∨ (i = 6 ∧ j = 1) ∨
      (i = 2 ∧ j = 7) ∨ (i = 7 ∧ j = 2) ∨
      (i = 3 ∧ j = 8) ∨ (i = 8 ∧ j = 3) ∨
      (i = 5 ∧ j = 7) ∨ (i = 7 ∧ j = 5) ∨
      (i = 6 ∧ j = 8) ∨ (i = 8 ∧ j = 6) ∨
      (i = 5 ∧ j = 8) ∨ (i = 8 ∧ j = 5) := by decide
  have hcases := hcode_dec a b hcode
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact orb_deg3 (1, 2) (by decide) C hfan hsz hnot_le2 heq
  · exact orb_deg3 (1, 2) (by decide) C hfan hsz hnot_le2 heq_comm
  · exact orb_deg3 (2, 3) (by decide) C hfan hsz hnot_le2 heq
  · exact orb_deg3 (2, 3) (by decide) C hfan hsz hnot_le2 heq_comm
  · exact orb_deg2 (1, 6) (by decide) C hfan hsz hnot_le2 heq
  · exact orb_deg2 (1, 6) (by decide) C hfan hsz hnot_le2 heq_comm
  · exact orb_deg2 (2, 7) (by decide) C hfan hsz hnot_le2 heq
  · exact orb_deg2 (2, 7) (by decide) C hfan hsz hnot_le2 heq_comm
  · exact orb_deg3 (2, 3) (by decide) Cr hCr_fan hCr_sz hCr_not heq_r_comm
  · exact orb_deg3 (2, 3) (by decide) Cr hCr_fan hCr_sz hCr_not heq_r
  · exact orb_deg2 (1, 6) (by decide) Cr hCr_fan hCr_sz hCr_not heq_r
  · exact orb_deg2 (1, 6) (by decide) Cr hCr_fan hCr_sz hCr_not heq_r_comm
  · exact orb_deg2 (2, 7) (by decide) Cr hCr_fan hCr_sz hCr_not heq_r_comm
  · exact orb_deg2 (2, 7) (by decide) Cr hCr_fan hCr_sz hCr_not heq_r
  · exact orb_deg3 (1, 2) (by decide) Cr hCr_fan hCr_sz hCr_not heq_r
  · exact orb_deg3 (1, 2) (by decide) Cr hCr_fan hCr_sz hCr_not heq_r_comm
