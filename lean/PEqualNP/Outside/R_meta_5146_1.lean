import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The extra wire is x j AND (x 0 OR x 2). For j = 0 or j = 2 it copies an input wire, and the
-- circuit with the gate OR(x 0, x 2) in front has at most 14 gates (no14). Otherwise the two
-- front gates give a circuit for the edge function, so many_nots leaves at most two NOT gates.
-- The automorphism (0 2)(3 5)(4 7) fixes x 0 OR x 2 and takes j = 5, 7 to j = 3, 4.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5146_1
    (no14 :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 14 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (many_nots :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
        13 ≤ C.size - PEqualNP.NotBracket.notCount C)
    (core :
      ∀ j ∈ ([1, 3, 4, 6, 8] : List (Fin 9)),
        ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          PEqualNP.NotBracket.notCount C ≤ 2 →
          ∃ x : Fin 9 → Bool,
            C.eval (List.ofFn x ++ [x 0 || x 2, x j && (x 0 || x 2)]) ≠
              (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
                x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
                x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (13 : ℕ) →       ∃ (x5 : Fin (9 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ))];         x2.eval (x6 ++ [x5 x1 && (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))]) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  classical
  have ofFn_getD {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
      (List.ofFn x).getD k false = x ⟨k, hk⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hk, ↓reduceDIte, Option.getD_some]
  have hget_lt (x : Fin 9 → Bool) (i : Fin 9) :
      (List.ofFn x ++ [x 0 || x 2]).getD i.val false = x i := by
    rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact i.isLt),
        ofFn_getD x i.val i.isLt]
  have hget9 (x : Fin 9 → Bool) :
      (List.ofFn x ++ [x 0 || x 2]).getD 9 false = (x 0 || x 2) := by
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn, Nat.sub_self]; rfl
  have hjcases : ∀ i : Fin 9, i = 0 ∨ i = 2 ∨ i ∈ ([1, 3, 4, 6, 8] : List (Fin 9)) ∨ i = 5 ∨ i = 7 := by
    decide
  intro j C hfan hsz
  by_contra hno
  let edge (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have heq : ∀ x : Fin 9 → Bool,
      let x7 : List Bool := List.ofFn x ++ [x 0 || x 2]
      C.eval (x7 ++ [x j && (x 0 || x 2)]) = edge x := by
    intro x
    by_contra hne
    exact hno ⟨x, hne⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  let mapGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
  have hfan_map (f : ℕ → ℕ) (gs : List Gate) (o : ℕ)
      (h : FanInTwo ⟨gs, o⟩) : FanInTwo ⟨gs.map (mapGate f), o⟩ := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen0⟩ := h g0 hg0
    exact ⟨hop, by simp only [mapGate, List.length_map]; exact hlen0⟩
  have hnot_map (f : ℕ → ℕ) (gs : List Gate) (o₁ o₂ : ℕ) :
      PEqualNP.NotBracket.notCount ⟨gs.map (mapGate f), o₁⟩ =
      PEqualNP.NotBracket.notCount ⟨gs, o₂⟩ := by
    unfold PEqualNP.NotBracket.notCount
    dsimp only
    rw [List.filter_map, List.length_map]
    rfl
  have rewire (m n L : ℕ) (f : ℕ → ℕ)
      (hf_hi : ∀ k, m ≤ k → f k = k - m + n)
      (hf_lo : ∀ k, k < m → f k < n ∨ n + L ≤ f k) :
      ∀ (gs : List Gate) (i : ℕ) (u v : List Bool),
        u.length = m + i → v.length = n + i → i + gs.length ≤ L →
        (∀ k, k < u.length → v.getD (f k) false = u.getD k false) →
        ∀ k, ((gs.map (mapGate f)).foldl step v).getD (f k) false = (gs.foldl step u).getD k false := by
    intro gs
    induction gs with
    | nil =>
      intro i u v hu hv _ hagree k
      change v.getD (f k) false = u.getD k false
      by_cases hk : k < u.length
      · exact hagree k hk
      · have hmk : m ≤ k := by omega
        have hfk : v.length ≤ f k := by rw [hf_hi k hmk]; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hfk, List.getElem?_eq_none (Nat.le_of_not_lt hk)]
    | cons g gs ih =>
      intro i u v hu hv hbound hagree k
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hall : ∀ j, v.getD (f j) false = u.getD j false := by
        intro j
        by_cases hj : j < u.length
        · exact hagree j hj
        · have hmj : m ≤ j := by omega
          have hfj : v.length ≤ f j := by rw [hf_hi j hmj]; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none hfj, List.getElem?_eq_none (Nat.le_of_not_lt hj)]
      have hbit : (mapGate f g).op.eval ((mapGate f g).inputs.map fun j => v.getD j false) =
                  g.op.eval (g.inputs.map fun j => u.getD j false) := by
        change g.op.eval ((g.inputs.map f).map fun j => v.getD j false) = _
        rw [List.map_map]
        congr 1
        exact List.map_congr_left fun j _ => hall j
      have hstep_v : step v (mapGate f g) = v ++ [g.op.eval (g.inputs.map fun j => u.getD j false)] := by
        change v ++ [(mapGate f g).op.eval ((mapGate f g).inputs.map fun j => v.getD j false)] = _
        rw [hbit]
      apply ih (i + 1) (step u g) (step v (mapGate f g))
      · change (u ++ [_]).length = m + (i + 1); simp only [List.length_append, List.length_singleton]; omega
      · change (v ++ [_]).length = n + (i + 1); simp only [List.length_append, List.length_singleton]; omega
      · simp only [List.length_cons] at hbound; omega
      · intro j hj
        rw [hstep_v]
        change (v ++ [g.op.eval (g.inputs.map fun t => u.getD t false)]).getD (f j) false =
               (u ++ [g.op.eval (g.inputs.map fun t => u.getD t false)]).getD j false
        have hulen : (step u g).length = m + i + 1 := by
          change (u ++ [_]).length = m + i + 1; simp only [List.length_append, List.length_singleton]; omega
        by_cases hlast : j = m + i
        · subst hlast
          have hfj : f (m + i) = v.length := by rw [hf_hi (m + i) (Nat.le_add_right m i)]; omega
          rw [hfj, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
              ← hu, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        · have hjlt : j < u.length := by omega
          rw [List.getD_append _ _ _ _ hjlt]
          by_cases hjm : j < m
          · rcases hf_lo j hjm with hsmall | hbig
            · rw [List.getD_append _ _ _ _ (by omega)]
              exact hagree j hjlt
            · have hle1 : (v ++ [g.op.eval (g.inputs.map fun t => u.getD t false)]).length ≤ f j := by
                simp only [List.length_append, List.length_cons, List.length_nil] at hbound ⊢; omega
              have hle2 : v.length ≤ f j := by
                simp only [List.length_cons] at hbound; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle1]
              have hprev : v.getD (f j) false = false := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle2]; rfl
              rw [← hagree j hjlt, hprev]; rfl
          · have hfj : f j < v.length := by rw [hf_hi j (Nat.le_of_not_lt hjm)]; omega
            rw [List.getD_append _ _ _ _ hfj]
            exact hagree j hjlt
  have eval_rewire (m n : ℕ) (f : ℕ → ℕ)
      (hf_hi : ∀ k, m ≤ k → f k = k - m + n)
      (hf_lo : ∀ k, k < m → f k < n ∨ n + C.size ≤ f k)
      (u0 v0 : List Bool) (hu0 : u0.length = m) (hv0 : v0.length = n)
      (hagree0 : ∀ k, k < m → v0.getD (f k) false = u0.getD k false) :
      (Circuit.mk (C.gates.map (mapGate f)) (f C.output)).eval v0 = C.eval u0 := by
    change ((C.gates.map (mapGate f)).foldl step v0).getD (f C.output) false =
           (C.gates.foldl step u0).getD C.output false
    exact rewire m n C.size f hf_hi hf_lo C.gates 0 u0 v0 (by omega) (by omega)
      (by change 0 + C.gates.length ≤ C.gates.length; omega)
      (fun k hk => hagree0 k (by omega)) C.output
  -- Close the step when wire 10 always equals wire r, for some r below 10.
  have close_redundant (r : ℕ) (hr : r < 10)
      (hval : ∀ x : Fin 9 → Bool,
        (x j && (x 0 || x 2)) = (List.ofFn x ++ [x 0 || x 2]).getD r false) : False := by
    let f (k : ℕ) : ℕ := if k < 10 then k else if k = 10 then r else k - 11 + 10
    let g0 : Gate := ⟨.or, [0, 2]⟩
    let D : Circuit := ⟨g0 :: C.gates.map (mapGate f), f C.output⟩
    have hD_fan : FanInTwo D := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact ⟨Or.inr (Or.inl rfl), by decide⟩
      · exact hfan_map f C.gates (f C.output) hfan g hg'
    have hD_sz : D.size ≤ 14 := by
      change (g0 :: C.gates.map (mapGate f)).length ≤ 14
      simp only [List.length_cons, List.length_map]
      change C.gates.length ≤ 13 at hsz
      omega
    obtain ⟨x, hx⟩ := no14 D hD_fan hD_sz
    apply hx
    let x7 : List Bool := List.ofFn x ++ [x 0 || x 2]
    have hlen7 : x7.length = 10 := by
      simp only [x7, List.length_append, List.length_ofFn, List.length_singleton]
    have hstep0 : step (List.ofFn x) g0 = x7 := by
      change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false]] = x7
      rw [ofFn_getD x 0 (by omega), ofFn_getD x 2 (by omega)]
      change List.ofFn x ++ [(x 0 || (x 2 || false))] = x7
      rw [Bool.or_false]
    have hDeval : D.eval (List.ofFn x) = (Circuit.mk (C.gates.map (mapGate f)) (f C.output)).eval x7 := by
      change ((g0 :: C.gates.map (mapGate f)).foldl step (List.ofFn x)).getD (f C.output) false = _
      rw [List.foldl_cons, hstep0]
      rfl
    rw [hDeval]
    have hrew := eval_rewire 11 10 f
      (fun k hk => by simp only [f, show ¬ (k < 10) by omega, show ¬ (k = 10) by omega, ↓reduceIte])
      (fun k hk => by
        by_cases h10 : k < 10
        · left; simp only [f, h10, ↓reduceIte]
        · have hk10 : k = 10 := by omega
          subst hk10
          have hf10 : f 10 = r := rfl
          rw [hf10]
          exact Or.inl hr)
      (x7 ++ [x j && (x 0 || x 2)]) x7
      (by simp only [List.length_append, hlen7, List.length_singleton])
      hlen7
      (fun k hk => by
        by_cases h10 : k < 10
        · have hfk : f k = k := by simp only [f, h10, ↓reduceIte]
          have hrhs : (x7 ++ [x j && (x 0 || x 2)]).getD k false = x7.getD k false :=
            List.getD_append _ _ _ _ (by omega)
          rw [hfk, hrhs]
        · have hk10 : k = 10 := by omega
          subst hk10
          have hf10 : f 10 = r := rfl
          have hrhs : (x7 ++ [x j && (x 0 || x 2)]).getD 10 false = (x j && (x 0 || x 2)) := by
            rw [List.getD_append_right _ _ _ _ (by omega), hlen7, Nat.sub_self]; rfl
          rw [hf10, hrhs]
          exact (hval x).symm)
    rw [hrew]
    exact heq x
  -- The two front gates and C form a circuit for the edge function: at most two NOT gates.
  have hnot_le2 : PEqualNP.NotBracket.notCount C ≤ 2 := by
    let g0 : Gate := ⟨.or, [0, 2]⟩
    let g1 : Gate := ⟨.and, [j.val, 9]⟩
    let full : Circuit := ⟨g0 :: g1 :: C.gates, C.output⟩
    have hfull_fan : FanInTwo full := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg1
      · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
      · rcases List.mem_cons.mp hg1 with rfl | hg2
        · exact ⟨Or.inl rfl, Nat.le_refl 2⟩
        · exact hfan g hg2
    have hfull_eval : ∀ x : Fin 9 → Bool, full.eval (List.ofFn x) = edge x := by
      intro x
      have hs0 : step (List.ofFn x) g0 = List.ofFn x ++ [x 0 || x 2] := by
        change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false]] = _
        rw [ofFn_getD x 0 (by omega), ofFn_getD x 2 (by omega)]
        change List.ofFn x ++ [(x 0 || (x 2 || false))] = _
        rw [Bool.or_false]
      have hs1 : step (List.ofFn x ++ [x 0 || x 2]) g1 =
          (List.ofFn x ++ [x 0 || x 2]) ++ [x j && (x 0 || x 2)] := by
        change (List.ofFn x ++ [x 0 || x 2]) ++
            [GateOp.and.eval [(List.ofFn x ++ [x 0 || x 2]).getD j.val false,
              (List.ofFn x ++ [x 0 || x 2]).getD 9 false]] = _
        rw [hget_lt x j, hget9 x]
        change (List.ofFn x ++ [x 0 || x 2]) ++ [(x j && ((x 0 || x 2) && true))] = _
        rw [Bool.and_true]
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
    have hsz' : C.size ≤ 13 := hsz
    rw [hfsz, hfnot] at h13
    omega
  -- j in {5, 7}: relabel the inputs by the automorphism (0 2)(3 5)(4 7).
  have hsig_bool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
      (a2 && a1 || a1 && a0 || a0 && a5 || a5 && a7 || a7 && a2 || a2 && a3 ||
       a1 && a6 || a0 && a4 || a5 && a8 || a3 && a4 || a6 && a8 || a8 && a3) =
      (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 ||
       a1 && a6 || a2 && a7 || a3 && a8 || a5 && a7 || a6 && a8 || a8 && a5) := by decide
  let sigL : List ℕ := [2, 1, 0, 5, 7, 3, 6, 4, 8]
  have hsig_lt (i : Fin 9) : sigL.getD i.val 0 < 9 := by
    fin_cases i <;> decide
  let sig (i : Fin 9) : Fin 9 := ⟨sigL.getD i.val 0, hsig_lt i⟩
  let fSig (k : ℕ) : ℕ := if k < 9 then sigL.getD k 0 else k
  let Csig : Circuit := ⟨C.gates.map (mapGate fSig), fSig C.output⟩
  have hCsig_fan : FanInTwo Csig := hfan_map fSig C.gates (fSig C.output) hfan
  have hCsig_sz : Csig.size ≤ 13 := by
    change (C.gates.map (mapGate fSig)).length ≤ 13
    rw [List.length_map]; exact hsz
  have hCsig_not : PEqualNP.NotBracket.notCount Csig ≤ 2 := by
    rw [hnot_map fSig C.gates (fSig C.output) C.output]; exact hnot_le2
  have hedge_sig (x : Fin 9 → Bool) : edge (fun i => x (sig i)) = edge x :=
    hsig_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  have eval_sig (w2 : (Fin 9 → Bool) → Bool)
      (hw2 : ∀ x : Fin 9 → Bool,
        (x (sig j) && (x (sig 0) || x (sig 2))) = w2 x)
      (x : Fin 9 → Bool) :
      Csig.eval (List.ofFn x ++ [x 0 || x 2, w2 x]) = edge x := by
    let xs : Fin 9 → Bool := fun i => x (sig i)
    let x7s : List Bool := List.ofFn xs ++ [xs 0 || xs 2]
    have hlen7s : x7s.length = 10 := by
      simp only [x7s, List.length_append, List.length_ofFn, List.length_singleton]
    have hrew := eval_rewire 11 11 fSig
      (fun k hk => by simp only [fSig, show ¬ (k < 9) by omega, ↓reduceIte]; omega)
      (fun k hk => by
        left
        by_cases hk9 : k < 9
        · have hfk : fSig k = sigL.getD k 0 := by simp only [fSig, hk9, ↓reduceIte]
          have hlt := hsig_lt ⟨k, hk9⟩
          change sigL.getD k 0 < 9 at hlt
          omega
        · have hfk : fSig k = k := by simp only [fSig, hk9, ↓reduceIte]
          omega)
      (x7s ++ [xs j && (xs 0 || xs 2)])
      (List.ofFn x ++ [x 0 || x 2, w2 x])
      (by simp only [List.length_append, hlen7s, List.length_singleton])
      (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
      (fun k hk => by
        by_cases hk9 : k < 9
        · have hfk : fSig k = sigL.getD k 0 := by simp only [fSig, hk9, ↓reduceIte]
          have hlt9 : sigL.getD k 0 < 9 := hsig_lt ⟨k, hk9⟩
          have hlhs : (List.ofFn x ++ [x 0 || x 2, w2 x]).getD (fSig k) false = x ⟨sigL.getD k 0, hlt9⟩ := by
            rw [hfk, List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hlt9),
                ofFn_getD x (sigL.getD k 0) hlt9]
          have hrhs : (x7s ++ [xs j && (xs 0 || xs 2)]).getD k false = xs ⟨k, hk9⟩ := by
            rw [List.getD_append _ _ _ _ (by omega),
                List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hk9),
                ofFn_getD xs k hk9]
          rw [hlhs, hrhs]
        · by_cases hk9e : k = 9
          · subst hk9e
            have hf9 : fSig 9 = 9 := rfl
            have hlhs : (List.ofFn x ++ [x 0 || x 2, w2 x]).getD 9 false = (x 0 || x 2) := by
              rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
              simp only [List.length_ofFn, Nat.sub_self]; rfl
            have hrhs : (x7s ++ [xs j && (xs 0 || xs 2)]).getD 9 false = (xs 0 || xs 2) := by
              rw [List.getD_append _ _ _ _ (by omega), hget9 xs]
            rw [hf9, hlhs, hrhs]
            change (x 0 || x 2) = (x 2 || x 0)
            exact Bool.or_comm (x 0) (x 2)
          · have hk10 : k = 10 := by omega
            subst hk10
            have hf10 : fSig 10 = 10 := rfl
            have hlhs : (List.ofFn x ++ [x 0 || x 2, w2 x]).getD 10 false = w2 x := by
              rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
              simp only [List.length_ofFn]; rfl
            have hrhs : (x7s ++ [xs j && (xs 0 || xs 2)]).getD 10 false =
                (xs j && (xs 0 || xs 2)) := by
              rw [List.getD_append_right _ _ _ _ (by omega), hlen7s, Nat.sub_self]; rfl
            rw [hf10, hlhs, hrhs]
            exact (hw2 x).symm)
    rw [show Csig.eval (List.ofFn x ++ [x 0 || x 2, w2 x]) =
             (Circuit.mk (C.gates.map (mapGate fSig)) (fSig C.output)).eval (List.ofFn x ++ [x 0 || x 2, w2 x]) from rfl,
        hrew, heq xs, hedge_sig x]
  rcases hjcases j with hj0 | hj2 | hjc | hj5 | hj7
  · exact close_redundant (0 : Fin 9).val (by decide) (fun x => by
      rw [hget_lt x 0, hj0]; cases x 0 <;> cases x 2 <;> rfl)
  · exact close_redundant (2 : Fin 9).val (by decide) (fun x => by
      rw [hget_lt x 2, hj2]; cases x 0 <;> cases x 2 <;> rfl)
  · obtain ⟨x, hx⟩ := core j hjc C hfan hsz hnot_le2
    have h := heq x
    dsimp only at h
    rw [List.append_assoc] at h
    exact hx h
  · obtain ⟨x, hx⟩ := core 3 (by decide) Csig hCsig_fan hCsig_sz hCsig_not
    exact hx (eval_sig (fun z => z 3 && (z 0 || z 2)) (fun z => by
      rw [hj5]
      change (z 3 && (z 2 || z 0)) = (z 3 && (z 0 || z 2))
      rw [Bool.or_comm (z 2) (z 0)]) x)
  · obtain ⟨x, hx⟩ := core 4 (by decide) Csig hCsig_fan hCsig_sz hCsig_not
    exact hx (eval_sig (fun z => z 4 && (z 0 || z 2)) (fun z => by
      rw [hj7]
      change (z 4 && (z 2 || z 0)) = (z 4 && (z 0 || z 2))
      rw [Bool.or_comm (z 2) (z 0)]) x)
