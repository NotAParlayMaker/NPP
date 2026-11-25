import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3646_427
    (normalize : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      0 < s → (∀ r ∈ rows, r < 2 ^ n) → PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      ∃ k < PEqualNP.Defs.LratEncoding.enc2CubeCount n s,
        PEqualNP.Defs.LratEncoding.FormulaSat
          (PEqualNP.Defs.LratEncoding.enc2 n s g rows ++ PEqualNP.Defs.LratEncoding.enc2Cube n s k))
    (lastAnd : ∀ k : ℕ, k < (24 : ℕ) →
      ¬PEqualNP.Defs.LratEncoding.FormulaSat
        (PEqualNP.Defs.LratEncoding.enc2 (10 : ℕ) (14 : ℕ)
          (fun (x3 : ℕ) => [(515 : ℕ), (6 : ℕ), (12 : ℕ), (529 : ℕ), (536 : ℕ), (545 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].contains x3)
          [(24 : ℕ), (3 : ℕ), (515 : ℕ), (6 : ℕ), (12 : ℕ), (529 : ℕ), (536 : ℕ), (545 : ℕ), (42 : ℕ), (562 : ℕ), (66 : ℕ), (581 : ℕ), (104 : ℕ), (628 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (713 : ℕ), (720 : ℕ), (773 : ℕ), (264 : ℕ), (788 : ℕ), (288 : ℕ), (320 : ℕ), (897 : ℕ), (914 : ℕ)] ++
          PEqualNP.Defs.LratEncoding.enc2Cube (10 : ℕ) (14 : ℕ) k))
    (lastOr : ∀ k : ℕ, (24 : ℕ) ≤ k → k < (48 : ℕ) →
      ¬PEqualNP.Defs.LratEncoding.FormulaSat
        (PEqualNP.Defs.LratEncoding.enc2 (10 : ℕ) (14 : ℕ)
          (fun (x3 : ℕ) => [(515 : ℕ), (6 : ℕ), (12 : ℕ), (529 : ℕ), (536 : ℕ), (545 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].contains x3)
          [(24 : ℕ), (3 : ℕ), (515 : ℕ), (6 : ℕ), (12 : ℕ), (529 : ℕ), (536 : ℕ), (545 : ℕ), (42 : ℕ), (562 : ℕ), (66 : ℕ), (581 : ℕ), (104 : ℕ), (628 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (713 : ℕ), (720 : ℕ), (773 : ℕ), (264 : ℕ), (788 : ℕ), (288 : ℕ), (320 : ℕ), (897 : ℕ), (914 : ℕ)] ++
          PEqualNP.Defs.LratEncoding.enc2Cube (10 : ℕ) (14 : ℕ) k)) :
    ∀ x1 ∈ [(3 : ℕ), (33 : ℕ)], ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => [(515 : ℕ), (6 : ℕ), (12 : ℕ), (529 : ℕ), (536 : ℕ), (545 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].contains x3) [(24 : ℕ), x1, (515 : ℕ), (6 : ℕ), (12 : ℕ), (529 : ℕ), (536 : ℕ), (545 : ℕ), (42 : ℕ), (562 : ℕ), (66 : ℕ), (581 : ℕ), (104 : ℕ), (628 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (713 : ℕ), (720 : ℕ), (773 : ℕ), (264 : ℕ), (788 : ℕ), (288 : ℕ), (320 : ℕ), (897 : ℕ), (914 : ℕ)]) := by
  classical
  let gFun : ℕ → Bool := fun x3 =>
    [(515 : ℕ), 6, 12, 529, 536, 545, 66, 132, 160, 264, 288, 320].contains x3
  let baseRows : List ℕ :=
    [515, 6, 12, 529, 536, 545, 42, 562, 66, 581, 104, 628, 132, 138, 160, 713, 720, 773,
      264, 788, 288, 320, 897, 914]
  let rows3 : List ℕ := 24 :: 3 :: baseRows
  let rows33 : List ℕ := 24 :: 33 :: baseRows
  have litP : ∀ (a : ℕ → Bool) (v : ℕ), litVal a (P v) = a (v + 1) := by
    intro a v
    unfold litVal P
    have h1 : (2 * v + 2) / 2 = v + 1 := by omega
    have h2 : (2 * v + 2) % 2 = 0 := by omega
    rw [h1, h2]
    cases a (v + 1) <;> rfl
  have litQ : ∀ (a : ℕ → Bool) (v : ℕ), litVal a (Q v) = !(a (v + 1)) := by
    intro a v
    unfold litVal Q
    have h1 : (2 * v + 3) / 2 = v + 1 := by omega
    have h2 : (2 * v + 3) % 2 = 1 := by omega
    rw [h1, h2]
    cases a (v + 1) <;> rfl
  have litL : ∀ (a : ℕ → Bool) (v : ℕ) (b : Bool), litVal a (L v b) = (a (v + 1) == b) := by
    intro a v b
    unfold L
    cases b
    · simp only [Bool.false_eq_true, ite_false, litQ]; cases a (v + 1) <;> rfl
    · simp only [ite_true, litP]; cases a (v + 1) <;> rfl
  have stepLen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp; omega
  have getDLt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
        w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi
  -- Decode any satisfying assignment of enc 10 14 gFun rows into a Monotone2 circuit of size 14
  have decodeEnc : ∀ (rows : List ℕ), FormulaSat (enc 10 14 gFun rows) →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 14 ∧
        ∀ r ∈ rows, C.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = gFun r := by
    intro rows ⟨a, ha⟩
    have hOpMem : ∀ j < 14, ClauseSat a [P (ix 10 14 0 j 0), P (ix 10 14 0 j 1), P (ix 10 14 0 j 2)] := by
      intro j hj
      apply ha
      unfold enc fOp
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩))))))))))
    have hSrcAloMem : ∀ e ∈ ([1, 2] : List ℕ), ∀ j < 14,
        ClauseSat a ((List.range (10 + j + 1)).map fun k => P (ix 10 14 e j k)) := by
      intro e he j hj
      apply ha
      unfold enc fSrcAlo
      simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨e, he, j, hj, rfl⟩))))))))))
    have hSrcEqMem : ∀ e ∈ ([1, 2] : List ℕ), ∀ j < 14, ∀ r ∈ rows, ∀ k < 10 + j + 1,
        ∀ c ∈ srcEq 10 14 e j k r, ClauseSat a c := by
      intro e he j hj r hr k hk c hc
      apply ha
      unfold enc fSrcEq
      simp only [List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨e, he, j, hj, r, hr, k, hk, hc⟩)))))))))
    have hGateMem : ∀ j < 14, ∀ r ∈ rows, ∀ c ∈ gateCl 10 14 j r, ClauseSat a c := by
      intro j hj r hr c hc
      apply ha
      unfold enc fGate
      simp only [List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, r, hr, hc⟩))))))))
    have hOutAloMem : ClauseSat a ((List.range 25).map fun k => P (ix 10 14 6 0 k)) := by
      apply ha
      unfold enc fOutAlo
      simp only [List.mem_append, List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr trivial)))))))
    have hOutEqMem : ∀ r ∈ rows, ∀ k < 25, ∀ c ∈ outEq 10 14 gFun k r, ClauseSat a c := by
      intro r hr k hk c hc
      apply ha
      unfold enc fOutEq
      simp only [List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, hr, k, hk, hc⟩))))))
    have hSrcPick : ∀ e ∈ ([1, 2] : List ℕ), ∀ j < 14,
        ∃ k < 10 + j + 1, a (ix 10 14 e j k + 1) = true := by
      intro e he j hj
      obtain ⟨l, hl, hlv⟩ := hSrcAloMem e he j hj
      simp only [List.mem_map, List.mem_range] at hl
      obtain ⟨k, hk, rfl⟩ := hl
      rw [litP] at hlv
      exact ⟨k, hk, hlv⟩
    let s1 (j : ℕ) : ℕ := if hj : j < 14 then (hSrcPick 1 (by simp) j hj).choose else 0
    let s2 (j : ℕ) : ℕ := if hj : j < 14 then (hSrcPick 2 (by simp) j hj).choose else 0
    have hs1Spec : ∀ j < 14, s1 j < 10 + j + 1 ∧ a (ix 10 14 1 j (s1 j) + 1) = true := by
      intro j hj
      simp only [s1, hj, dite_true]
      exact (hSrcPick 1 (by simp) j hj).choose_spec
    have hs2Spec : ∀ j < 14, s2 j < 10 + j + 1 ∧ a (ix 10 14 2 j (s2 j) + 1) = true := by
      intro j hj
      simp only [s2, hj, dite_true]
      exact (hSrcPick 2 (by simp) j hj).choose_spec
    let mkGate (j : ℕ) : Gate :=
      if a (ix 10 14 0 j 0 + 1) then ⟨GateOp.and, [s1 j, s2 j]⟩
      else if a (ix 10 14 0 j 1 + 1) then ⟨GateOp.or, [s1 j, s2 j]⟩
      else ⟨GateOp.and, []⟩
    have hOutPick : ∃ k < 25, a (ix 10 14 6 0 k + 1) = true := by
      obtain ⟨l, hl, hlv⟩ := hOutAloMem
      simp only [List.mem_map, List.mem_range] at hl
      obtain ⟨k, hk, rfl⟩ := hl
      rw [litP] at hlv
      exact ⟨k, hk, hlv⟩
    obtain ⟨outK, houtKlt, houtKval⟩ := hOutPick
    let gs : List Gate := (List.range 14).map mkGate
    let C : Circuit := ⟨gs, outK⟩
    have hMono : Monotone2 C := by
      intro g hg
      simp only [C, gs, List.mem_map, List.mem_range] at hg
      obtain ⟨j, _, rfl⟩ := hg
      dsimp only [mkGate]
      split_ifs <;> exact ⟨by simp, by simp⟩
    have hSz : C.size ≤ 14 := by
      change gs.length ≤ 14
      simp [gs]
    have hWires : ∀ r ∈ rows, ∀ m ≤ 14, ∀ j < m,
        (((List.range m).map mkGate).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn fun i : Fin 10 => r.testBit i.val)).getD (10 + j) false =
          a (ix 10 14 3 j r + 1) := by
      intro r hr m
      induction m with
      | zero => intro _ j hj; omega
      | succ m ih =>
        intro hm j hj
        have htake : (List.range (m + 1)).map mkGate = (List.range m).map mkGate ++ [mkGate m] := by
          rw [List.range_succ, List.map_append]; rfl
        rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
        let wPrev := ((List.range m).map mkGate).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn fun i : Fin 10 => r.testBit i.val)
        have hwPrevLen : wPrev.length = 10 + m := by
          dsimp only [wPrev]
          rw [stepLen, List.length_ofFn, List.length_map, List.length_range]
        by_cases hjm : j < m
        · change (wPrev ++ [(mkGate m).op.eval ((mkGate m).inputs.map fun i => wPrev.getD i false)]).getD (10 + j) false = _
          rw [List.getD_append _ _ _ _ (by omega)]
          exact ih (by omega) j hjm
        · have hjeq : j = m := by omega
          subst hjeq
          have hidx : (wPrev ++ [(mkGate j).op.eval ((mkGate j).inputs.map fun i => wPrev.getD i false)]).getD (10 + j) false =
              (mkGate j).op.eval ((mkGate j).inputs.map fun i => wPrev.getD i false) := by
            rw [← hwPrevLen]; simp
          change (wPrev ++ [(mkGate j).op.eval ((mkGate j).inputs.map fun i => wPrev.getD i false)]).getD (10 + j) false = _
          rw [hidx]
          have hSrcVal : ∀ e ∈ ([1, 2] : List ℕ), ∀ k < 10 + j + 1,
              a (ix 10 14 e j k + 1) = true →
              wPrev.getD k false = a (ix 10 14 (e + 3) j r + 1) := by
            intro e he k hk hae
            by_cases hk10 : k < 10
            · have hcl := hSrcEqMem e he j (by omega) r hr k hk
                [Q (ix 10 14 e j k), L (ix 10 14 (e + 3) j r) (r.testBit k)] (by unfold srcEq; simp [hk10])
              obtain ⟨l, hl, hlv⟩ := hcl
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl
              · rw [litQ, hae] at hlv; cases hlv
              · rw [litL] at hlv
                have hw : wPrev.getD k false = r.testBit k := by
                  rw [getDLt _ _ k (by simp; omega)]
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk10, dite_true, Option.getD_some]
                rw [hw]
                exact (beq_iff_eq.mp hlv).symm
            · by_cases hkj : k < 10 + j
              · have hcl1 := hSrcEqMem e he j (by omega) r hr k hk
                  [Q (ix 10 14 e j k), Q (ix 10 14 (e + 3) j r), P (ix 10 14 3 (k - 10) r)]
                  (by unfold srcEq; simp [hk10, hkj])
                have hcl2 := hSrcEqMem e he j (by omega) r hr k hk
                  [Q (ix 10 14 e j k), P (ix 10 14 (e + 3) j r), Q (ix 10 14 3 (k - 10) r)]
                  (by unfold srcEq; simp [hk10, hkj])
                have hw : wPrev.getD k false = a (ix 10 14 3 (k - 10) r + 1) := by
                  have hih := ih (by omega) (k - 10) (by omega)
                  have hek : 10 + (k - 10) = k := by omega
                  rwa [hek] at hih
                rw [hw]
                obtain ⟨l1, hl1, hlv1⟩ := hcl1
                obtain ⟨l2, hl2, hlv2⟩ := hcl2
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1 hl2
                rcases hl1 with rfl | rfl | rfl
                · rw [litQ, hae] at hlv1; cases hlv1
                · rcases hl2 with rfl | rfl | rfl
                  · rw [litQ, hae] at hlv2; cases hlv2
                  · rw [litQ] at hlv1; rw [litP] at hlv2; rw [hlv2] at hlv1; cases hlv1
                  · rw [litQ] at hlv1 hlv2
                    cases hx : a (ix 10 14 3 (k - 10) r + 1) <;> cases hy : a (ix 10 14 (e + 3) j r + 1) <;>
                      simp_all
                · rcases hl2 with rfl | rfl | rfl
                  · rw [litQ, hae] at hlv2; cases hlv2
                  · rw [litP] at hlv1 hlv2; rw [hlv1, hlv2]
                  · rw [litP] at hlv1; rw [litQ] at hlv2; rw [hlv1] at hlv2; cases hlv2
              · have hcl := hSrcEqMem e he j (by omega) r hr k hk
                  [Q (ix 10 14 e j k), Q (ix 10 14 (e + 3) j r)]
                  (by unfold srcEq; simp [hk10, hkj])
                obtain ⟨l, hl, hlv⟩ := hcl
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                rcases hl with rfl | rfl
                · rw [litQ, hae] at hlv; cases hlv
                · rw [litQ] at hlv
                  have hw : wPrev.getD k false = false := List.getD_eq_default _ _ (by omega)
                  rw [hw]
                  cases hy : a (ix 10 14 (e + 3) j r + 1) <;> simp_all
          have hs1v : wPrev.getD (s1 j) false = a (ix 10 14 4 j r + 1) :=
            hSrcVal 1 (by simp) (s1 j) (hs1Spec j (by omega)).1 (hs1Spec j (by omega)).2
          have hs2v : wPrev.getD (s2 j) false = a (ix 10 14 5 j r + 1) :=
            hSrcVal 2 (by simp) (s2 j) (hs2Spec j (by omega)).1 (hs2Spec j (by omega)).2
          dsimp only [mkGate]
          by_cases hop0 : a (ix 10 14 0 j 0 + 1) = true
          · rw [ite_eq_left hop0]
            change (wPrev.getD (s1 j) false && (wPrev.getD (s2 j) false && true)) = a (ix 10 14 3 j r + 1)
            rw [Bool.and_true, hs1v, hs2v]
            have hc1 := hGateMem j (by omega) r hr [Q (ix 10 14 0 j 0), Q (ix 10 14 3 j r), P (ix 10 14 4 j r)] (by unfold gateCl; simp)
            have hc2 := hGateMem j (by omega) r hr [Q (ix 10 14 0 j 0), Q (ix 10 14 3 j r), P (ix 10 14 5 j r)] (by unfold gateCl; simp)
            have hc3 := hGateMem j (by omega) r hr [Q (ix 10 14 0 j 0), P (ix 10 14 3 j r), Q (ix 10 14 4 j r), Q (ix 10 14 5 j r)] (by unfold gateCl; simp)
            cases h3 : a (ix 10 14 3 j r + 1) <;> cases h4 : a (ix 10 14 4 j r + 1) <;> cases h5 : a (ix 10 14 5 j r + 1) <;> try rfl
            · obtain ⟨l, hl, hlv⟩ := hc3
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl | rfl <;> simp [litP, litQ, hop0, h3, h4, h5] at hlv
            · obtain ⟨l, hl, hlv⟩ := hc1
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl <;> simp [litP, litQ, hop0, h3, h4] at hlv
            · obtain ⟨l, hl, hlv⟩ := hc1
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl <;> simp [litP, litQ, hop0, h3, h4] at hlv
            · obtain ⟨l, hl, hlv⟩ := hc2
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl <;> simp [litP, litQ, hop0, h3, h5] at hlv
          · rw [ite_eq_right hop0]
            by_cases hop1 : a (ix 10 14 0 j 1 + 1) = true
            · rw [ite_eq_left hop1]
              change (wPrev.getD (s1 j) false || (wPrev.getD (s2 j) false || false)) = a (ix 10 14 3 j r + 1)
              rw [Bool.or_false, hs1v, hs2v]
              have hc1 := hGateMem j (by omega) r hr [Q (ix 10 14 0 j 1), P (ix 10 14 3 j r), Q (ix 10 14 4 j r)] (by unfold gateCl; simp)
              have hc2 := hGateMem j (by omega) r hr [Q (ix 10 14 0 j 1), P (ix 10 14 3 j r), Q (ix 10 14 5 j r)] (by unfold gateCl; simp)
              have hc3 := hGateMem j (by omega) r hr [Q (ix 10 14 0 j 1), Q (ix 10 14 3 j r), P (ix 10 14 4 j r), P (ix 10 14 5 j r)] (by unfold gateCl; simp)
              cases h3 : a (ix 10 14 3 j r + 1) <;> cases h4 : a (ix 10 14 4 j r + 1) <;> cases h5 : a (ix 10 14 5 j r + 1) <;> try rfl
              · obtain ⟨l, hl, hlv⟩ := hc2
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                rcases hl with rfl | rfl | rfl <;> simp [litP, litQ, hop1, h3, h5] at hlv
              · obtain ⟨l, hl, hlv⟩ := hc1
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                rcases hl with rfl | rfl | rfl <;> simp [litP, litQ, hop1, h3, h4] at hlv
              · obtain ⟨l, hl, hlv⟩ := hc1
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                rcases hl with rfl | rfl | rfl <;> simp [litP, litQ, hop1, h3, h4] at hlv
              · obtain ⟨l, hl, hlv⟩ := hc3
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                rcases hl with rfl | rfl | rfl | rfl <;> simp [litP, litQ, hop1, h3, h4, h5] at hlv
            · rw [ite_eq_right hop1]
              change true = a (ix 10 14 3 j r + 1)
              have hop2 : a (ix 10 14 0 j 2 + 1) = true := by
                obtain ⟨l, hl, hlv⟩ := hOpMem j (by omega)
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                rcases hl with rfl | rfl | rfl
                · rw [litP] at hlv; exact absurd hlv hop0
                · rw [litP] at hlv; exact absurd hlv hop1
                · rw [litP] at hlv; exact hlv
              have hc := hGateMem j (by omega) r hr [Q (ix 10 14 0 j 2), P (ix 10 14 3 j r)] (by unfold gateCl; simp)
              obtain ⟨l, hl, hlv⟩ := hc
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl
              · rw [litQ, hop2] at hlv; cases hlv
              · rw [litP] at hlv; exact hlv.symm
    refine ⟨C, hMono, hSz, ?_⟩
    intro r hr
    by_cases h10 : outK < 10
    · have hw : C.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = r.testBit outK := by
        unfold Circuit.eval Circuit.wires
        rw [getDLt _ _ outK (by simp; omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h10, dite_true, Option.getD_some]
      rw [hw]
      by_contra hne
      have hcl := hOutEqMem r hr outK houtKlt [Q (ix 10 14 6 0 outK)] (by unfold outEq; simp [h10, hne])
      obtain ⟨l, hl, hlv⟩ := hcl
      simp only [List.mem_singleton] at hl
      rw [hl, litQ, houtKval] at hlv
      cases hlv
    · by_cases h24 : outK < 24
      · have hw : C.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = a (ix 10 14 3 (outK - 10) r + 1) := by
          unfold Circuit.eval Circuit.wires
          have h14 := hWires r hr 14 le_rfl (outK - 10) (by omega)
          have hek : 10 + (outK - 10) = outK := by omega
          rwa [hek] at h14
        rw [hw]
        have hcl := hOutEqMem r hr outK houtKlt [Q (ix 10 14 6 0 outK), L (ix 10 14 3 (outK - 10) r) (gFun r)]
          (by unfold outEq; simp [h10, h24])
        obtain ⟨l, hl, hlv⟩ := hcl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · rw [litQ, houtKval] at hlv; cases hlv
        · rw [litL] at hlv; exact beq_iff_eq.mp hlv
      · have hw : C.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = false := by
          unfold Circuit.eval Circuit.wires
          exact List.getD_eq_default _ _ (by dsimp only [C, gs]; rw [stepLen]; simp; omega)
        rw [hw]
        cases hg : gFun r with
        | false => rfl
        | true =>
          have hcl := hOutEqMem r hr outK houtKlt [Q (ix 10 14 6 0 outK)]
            (by unfold outEq; simp [h10, h24, hg])
          obtain ⟨l, hl, hlv⟩ := hcl
          simp only [List.mem_singleton] at hl
          rw [hl, litQ, houtKval] at hlv
          cases hlv
  -- Eliminate all padding cubes 48 <= k < 72 directly
  have noPadCube : ∀ k : ℕ, 48 ≤ k → k < 72 →
      ¬FormulaSat (enc2 10 14 gFun rows3 ++ enc2Cube 10 14 k) := by
    intro k hk1 hk2 ⟨a, ha⟩
    have haEnc : ∀ c ∈ enc 10 14 gFun rows3, ClauseSat a c := by
      intro c hc
      apply ha
      unfold enc2
      simp only [List.mem_append]
      exact Or.inl (Or.inl hc)
    have hdiv : k / (10 + 14) = 2 := by omega
    have hop13 : a (ix 10 14 0 13 2 + 1) = true := by
      have hcl : ClauseSat a [P (ix 10 14 0 13 2)] := by
        apply ha
        unfold enc2Cube
        simp only [List.mem_append, hdiv, List.mem_cons]
        exact Or.inr (Or.inr (Or.inl trivial))
      obtain ⟨l, hl, hlv⟩ := hcl
      simp only [List.mem_singleton] at hl
      rw [hl, litP] at hlv
      exact hlv
    have hPadMem : ∀ j < 14, ∀ c ∈
        [[Q (ix 10 14 7 j 0), P (ix 10 14 0 j 2)], [Q (ix 10 14 7 j 0), P (ix 10 14 1 j (10 + j))],
         [Q (ix 10 14 7 j 0), P (ix 10 14 2 j (10 + j))], [P (ix 10 14 7 j 0), Q (ix 10 14 0 j 2)],
         [P (ix 10 14 7 j 0), Q (ix 10 14 1 j (10 + j))], [P (ix 10 14 7 j 0), Q (ix 10 14 2 j (10 + j))]],
        ClauseSat a c := by
      intro j hj c hc
      apply haEnc
      unfold enc fPad
      simp only [List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, hc⟩))))
    have hPreMem : ∀ j < 13, ClauseSat a [Q (ix 10 14 7 (j + 1) 0), P (ix 10 14 7 j 0)] := by
      intro j hj
      apply haEnc
      unfold enc fPre
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩)))
    have hpad13 : a (ix 10 14 7 13 0 + 1) = true := by
      obtain ⟨l, hl, hlv⟩ := hPadMem 13 (by omega) [P (ix 10 14 7 13 0), Q (ix 10 14 0 13 2)] (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · rw [litP] at hlv; exact hlv
      · rw [litQ, hop13] at hlv; cases hlv
    have hpadAll : ∀ d ≤ 13, a (ix 10 14 7 (13 - d) 0 + 1) = true := by
      intro d
      induction d with
      | zero => intro _; exact hpad13
      | succ d ih =>
        intro hd
        have hnext : a (ix 10 14 7 ((13 - (d + 1)) + 1) 0 + 1) = true := by
          have heq : (13 - (d + 1)) + 1 = 13 - d := by omega
          rw [heq]; exact ih (by omega)
        obtain ⟨l, hl, hlv⟩ := hPreMem (13 - (d + 1)) (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · rw [litQ, hnext] at hlv; cases hlv
        · rw [litP] at hlv; exact hlv
    have hGate24True : ∀ j < 14, a (ix 10 14 3 j 24 + 1) = true := by
      intro j hj
      have hpadj : a (ix 10 14 7 j 0 + 1) = true := by
        have heq : j = 13 - (13 - j) := by omega
        rw [heq]; exact hpadAll (13 - j) (by omega)
      have hop2j : a (ix 10 14 0 j 2 + 1) = true := by
        obtain ⟨l, hl, hlv⟩ := hPadMem j hj [Q (ix 10 14 7 j 0), P (ix 10 14 0 j 2)] (by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · rw [litQ, hpadj] at hlv; cases hlv
        · rw [litP] at hlv; exact hlv
      have hcl : ClauseSat a [Q (ix 10 14 0 j 2), P (ix 10 14 3 j 24)] := by
        apply haEnc
        unfold enc fGate
        simp only [List.mem_append, List.mem_flatMap, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, 24, by simp [rows3], by unfold gateCl; simp⟩))))))))
      obtain ⟨l, hl, hlv⟩ := hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · rw [litQ, hop2j] at hlv; cases hlv
      · rw [litP] at hlv; exact hlv
    have hOutAlo : ClauseSat a ((List.range 25).map fun k => P (ix 10 14 6 0 k)) := by
      apply haEnc
      unfold enc fOutAlo
      simp only [List.mem_append, List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr trivial)))))))
    have hOutEq : ∀ r ∈ rows3, ∀ out < 25, ∀ c ∈ outEq 10 14 gFun out r, ClauseSat a c := by
      intro r hr out hout c hc
      apply haEnc
      unfold enc fOutEq
      simp only [List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, hr, out, hout, hc⟩))))))
    obtain ⟨l, hl, hlv⟩ := hOutAlo
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨out, hout, rfl⟩ := hl
    rw [litP] at hlv
    by_cases h10 : out < 10
    · have hkill : ∀ r ∈ rows3, r.testBit out ≠ gFun r → False := by
        intro r hr hne
        obtain ⟨l', hl', hlv'⟩ := hOutEq r hr out hout [Q (ix 10 14 6 0 out)] (by unfold outEq; simp [h10, hne])
        simp only [List.mem_singleton] at hl'
        rw [hl', litQ, hlv] at hlv'
        cases hlv'
      interval_cases out
      · exact hkill 6 (by decide) (by decide)
      · exact hkill 12 (by decide) (by decide)
      · exact hkill 515 (by decide) (by decide)
      · exact hkill 515 (by decide) (by decide)
      · exact hkill 515 (by decide) (by decide)
      · exact hkill 515 (by decide) (by decide)
      · exact hkill 515 (by decide) (by decide)
      · exact hkill 515 (by decide) (by decide)
      · exact hkill 515 (by decide) (by decide)
      · exact hkill 6 (by decide) (by decide)
    · by_cases h24 : out < 24
      · have hg24 : gFun 24 = false := by decide
        obtain ⟨l', hl', hlv'⟩ := hOutEq 24 (by decide) out hout
          [Q (ix 10 14 6 0 out), Q (ix 10 14 3 (out - 10) 24)]
          (by unfold outEq L; simp [h10, h24, hg24])
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
        rcases hl' with rfl | rfl
        · rw [litQ, hlv] at hlv'; cases hlv'
        · rw [litQ, hGate24True (out - 10) (by omega)] at hlv'; cases hlv'
      · have hg515 : gFun 515 = true := by decide
        obtain ⟨l', hl', hlv'⟩ := hOutEq 515 (by decide) out hout
          [Q (ix 10 14 6 0 out)] (by unfold outEq; simp [h10, h24, hg515])
        simp only [List.mem_singleton] at hl'
        rw [hl', litQ, hlv] at hlv'
        cases hlv'
  -- Reject any Monotone2 circuit of size <= 14 matching gFun on rows3
  have killRows3 : ∀ C : Circuit, Monotone2 C → C.size ≤ 14 →
      (∀ r ∈ rows3, C.eval (List.ofFn fun i : Fin 10 => r.testBit i.val) = gFun r) → False := by
    intro C hMono hSz hMatch
    have hBound : ∀ r ∈ rows3, r < 2 ^ 10 := by decide +kernel
    obtain ⟨k, hk, hSat⟩ := normalize 10 14 gFun rows3 C (by omega) hBound hMono hSz hMatch
    have hk72 : k < 72 := hk
    by_cases h24 : k < 24
    · exact lastAnd k h24 hSat
    · by_cases h48 : k < 48
      · exact lastOr k (by omega) h48 hSat
      · exact noPadCube k (by omega) hk72 hSat
  -- Main proof for x1 in [3, 33]
  intro x1 hx1 hSat
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
  rcases hx1 with rfl | rfl
  · obtain ⟨C, hMono, hSz, hMatch⟩ := decodeEnc rows3 hSat
    exact killRows3 C hMono hSz hMatch
  · obtain ⟨C, hMono, hSz, hMatch⟩ := decodeEnc rows33 hSat
    let sigma : Fin 10 → Fin 10 := ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9]
    let mapW (i : ℕ) : ℕ := if h : i < 10 then (sigma ⟨i, h⟩).val else i
    let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map mapW⟩
    let C' : Circuit := ⟨C.gates.map mapG, mapW C.output⟩
    have hMono' : Monotone2 C' := by
      intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have horig := hMono g0 hg0
      exact ⟨horig.1, by simpa [mapG] using horig.2⟩
    have hSz' : C'.size ≤ 14 := by
      change (C.gates.map mapG).length ≤ 14
      rw [List.length_map]
      exact hSz
    have hSim : ∀ (gs : List Gate) (u1 u2 : List Bool),
        u1.length = u2.length → 10 ≤ u1.length →
        (∀ i, u1.getD i false = u2.getD (mapW i) false) →
        ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) u1).getD i false =
          ((gs.map mapG).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) u2).getD (mapW i) false := by
      intro gs
      induction gs with
      | nil => intro u1 u2 _ _ h i; exact h i
      | cons g rest ih =>
        intro u1 u2 hl h10 h
        have hgv : g.op.eval (g.inputs.map fun j => u1.getD j false) =
            (mapG g).op.eval ((mapG g).inputs.map fun j => u2.getD j false) := by
          simp only [mapG, List.map_map]
          congr 1
          apply List.map_congr_left
          intro j _
          exact h j
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        refine ih _ _ (by simp [hl]) (by simp; omega) ?_
        intro i
        rw [hgv]
        by_cases hil : i = u1.length
        · have hmw : mapW i = u2.length := by
            simp only [mapW, show ¬ i < 10 by omega, dite_false]; omega
          rw [hmw, hil]; simp
        · have hmw : mapW i ≠ u2.length := by
            by_cases hlt : i < 10
            · simp only [mapW, hlt, dite_true]
              have : (sigma ⟨i, hlt⟩).val < 10 := (sigma ⟨i, hlt⟩).isLt
              omega
            · simp only [mapW, hlt, dite_false]; omega
          have hs1 : ∀ v : Bool, (u1 ++ [v]).getD i false = u1.getD i false := by
            intro v
            by_cases hlt : i < u1.length
            · exact List.getD_append _ _ _ _ hlt
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
          have hs2 : ∀ v : Bool, (u2 ++ [v]).getD (mapW i) false = u2.getD (mapW i) false := by
            intro v
            by_cases hlt : mapW i < u2.length
            · exact List.getD_append _ _ _ _ hlt
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
          rw [hs1, hs2, h i]
    let permRow (r : ℕ) : ℕ :=
      (List.range 10).foldl (fun acc j =>
        if r.testBit (sigma (Fin.ofNat 10 j)).val then acc + 2 ^ j else acc) 0
    have hPermOk : ∀ r ∈ rows3, permRow r ∈ rows33 ∧ gFun (permRow r) = gFun r ∧
        ∀ j : Fin 10, (permRow r).testBit j.val = r.testBit (sigma j).val := by
      have chk : rows3.all (fun r => decide (permRow r ∈ rows33 ∧ gFun (permRow r) = gFun r ∧
          ∀ j : Fin 10, (permRow r).testBit j.val = r.testBit (sigma j).val)) = true := by
        decide +kernel
      exact fun r hr => of_decide_eq_true (List.all_eq_true.mp chk r hr)
    refine killRows3 C' hMono' hSz' ?_
    intro r hr
    obtain ⟨hmem33, hgEq, hbits⟩ := hPermOk r hr
    have hbase : ∀ i, (List.ofFn fun j : Fin 10 => (permRow r).testBit j.val).getD i false =
        (List.ofFn fun j : Fin 10 => r.testBit j.val).getD (mapW i) false := by
      intro i
      by_cases hlt : i < 10
      · have hlt2 : (sigma ⟨i, hlt⟩).val < 10 := (sigma ⟨i, hlt⟩).isLt
        simp only [mapW, hlt, dite_true, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt2,
          Option.getD_some]
        exact hbits ⟨i, hlt⟩
      · simp only [mapW, hlt, dite_false]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hev := hSim C.gates
      (List.ofFn fun j : Fin 10 => (permRow r).testBit j.val)
      (List.ofFn fun j : Fin 10 => r.testBit j.val)
      (by simp) (by simp) hbase C.output
    unfold Circuit.eval Circuit.wires
    dsimp only [C']
    rw [← hev]
    exact (hMatch (permRow r) hmem33).trans hgEq
