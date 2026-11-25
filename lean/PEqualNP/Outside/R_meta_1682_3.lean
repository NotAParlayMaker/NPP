import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1682_3 :
    (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ 63 ∧
        26 ≤ C.output ∧
        (∃ h : C.output - 26 < C.gates.length,
          (C.gates.get ⟨C.output - 26, h⟩).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (∀ p w : Fin 13, (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) →
          PEqualNP.MetaComplexity.circuitFun (13 + 13) C
            (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13),
          (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13,
            (∀ pp ∈ P, ¬ (pp = w2 ∨ pp = w2 + 1 ∨ pp = w2 + 3 ∨ pp = w2 + 9)) ∧
            (v = w2 ∨ v = w2 + 1 ∨ v = w2 + 3 ∨ v = w2 + 9)) →
          ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (p3 = w3 ∨ p3 = w3 + 1 ∨ p3 = w3 + 3 ∨ p3 = w3 + 9)) ∧
          ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13,
            (∀ pp ∈ P, ¬ (pp = w4 ∨ pp = w4 + 1 ∨ pp = w4 + 3 ∨ pp = w4 + 9)) →
            (v4 = w4 ∨ v4 = w4 + 1 ∨ v4 = w4 + 3 ∨ v4 = w4 + 9)) →
          PEqualNP.MetaComplexity.circuitFun (13 + 13) C
            (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
              (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
                (∀ pp ∈ P, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9))))) = false))) →
    (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ 63 ∧
        26 ≤ C.output ∧
        (∃ h : C.output - 26 < C.gates.length,
          (C.gates.get ⟨C.output - 26, h⟩).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        (∀ p w : Fin 13, (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) →
          PEqualNP.MetaComplexity.circuitFun (13 + 13) C
            (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13),
          (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13,
            (∀ pp ∈ P, ¬ (pp = w2 ∨ pp = w2 + 1 ∨ pp = w2 + 3 ∨ pp = w2 + 9)) ∧
            (v = w2 ∨ v = w2 + 1 ∨ v = w2 + 3 ∨ v = w2 + 9)) →
          ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (p3 = w3 ∨ p3 = w3 + 1 ∨ p3 = w3 + 3 ∨ p3 = w3 + 9)) ∧
          ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13,
            (∀ pp ∈ P, ¬ (pp = w4 ∨ pp = w4 + 1 ∨ pp = w4 + 3 ∨ pp = w4 + 9)) →
            (v4 = w4 ∨ v4 = w4 + 1 ∨ v4 = w4 + 3 ∨ v4 = w4 + 9)) →
          PEqualNP.MetaComplexity.circuitFun (13 + 13) C
            (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
              (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
                (∀ pp ∈ P, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9))))) = false))) →
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  intro hOutOr hOutAnd
  rintro ⟨C, hmono, hsize, hpos, hneg⟩
  have hwireLen :
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (gs.foldl (fun acc g =>
          acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w).length =
          w.length + gs.length := by
    intro gs
    induction gs with
    | nil =>
        intro w
        simp
    | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp [List.length_append]
        omega
  have hwireIn :
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
        i < w.length →
          (gs.foldl (fun acc g =>
            acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w).getD i false =
            w.getD i false := by
    intro gs
    induction gs with
    | nil =>
        intro w i _
        rfl
    | cons g gs ih =>
        intro w i hi
        have hlen : i < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
          simp [List.length_append]
          omega
        rw [List.foldl_cons, ih _ i hlen]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have houtLt : C.output < 26 + C.size := by
    by_contra hge
    push Not at hge
    have h00 := hpos 0 0 ⟨0, by decide, by decide⟩
    change (C.gates.foldl (fun acc g =>
      acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)])
      (List.ofFn (fun k : Fin (13 + 13) =>
        decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13))))).getD C.output false = true at h00
    have hlen :
        (C.gates.foldl (fun acc g =>
          acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)])
          (List.ofFn (fun k : Fin (13 + 13) =>
            decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13))))).length ≤ C.output := by
      rw [hwireLen, List.length_ofFn]
      change 26 + C.gates.length ≤ C.output at hge
      omega
    rw [List.getD_eq_default _ _ hlen] at h00
    exact Bool.noConfusion h00
  have houtGe : 26 ≤ C.output := by
    by_contra hlt
    push Not at hlt
    let Pshift : Fin 13 → Finset (Fin 13) := fun c => {c, 1 + c, 2 + c, 6 + c}
    have hshift : ∀ a b dd c : Fin 13, a + c = (b + c) + dd ↔ a = b + dd := by
      intro a b dd c
      rw [add_right_comm b c dd]
      exact add_right_cancel_iff
    have hmiss : ∀ (c k : Fin 13), (k = 7 ∨ k = 8 ∨ k = 9) →
        ∀ pp ∈ Pshift c, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = (k + c) + dd) := by
      rintro c k hk pp hpp ⟨dd, hdd, heq⟩
      simp only [Pshift, Finset.mem_insert, Finset.mem_singleton] at hpp hdd
      have h0 : ∃ a : Fin 13, (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 6) ∧ pp = a + c := by
        rcases hpp with rfl | rfl | rfl | rfl
        · exact ⟨0, Or.inl rfl, (zero_add _).symm⟩
        · exact ⟨1, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨2, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
        · exact ⟨6, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
      rcases h0 with ⟨a, ha, rfl⟩
      rw [hshift] at heq
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl <;>
        rcases hdd with rfl | rfl | rfl | rfl <;>
        exact absurd heq (by decide)
    have hgen1 : ∀ c : Fin 13, ∀ v : Fin 13, v ∉ Pshift c → ∃ w2 : Fin 13,
        (∀ pp ∈ Pshift c, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧
        (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd) := by
      intro c v hv
      have hvc : (v - c) + c = v := sub_add_cancel v c
      generalize hd : v - c = d at hvc
      fin_cases d
      · exact absurd (by change (0 : Fin 13) + c = v at hvc; rw [← hvc, zero_add]; exact Finset.mem_insert_self _ _) hv
      · exact absurd (by change (1 : Fin 13) + c = v at hvc; rw [← hvc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hv
      · exact absurd (by change (2 : Fin 13) + c = v at hvc; rw [← hvc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) hv
      · exact ⟨7 + c, hmiss c 7 (Or.inl rfl), 9, by decide, by rw [← hvc, hshift]; decide⟩
      · exact ⟨8 + c, hmiss c 8 (Or.inr (Or.inl rfl)), 9, by decide, by rw [← hvc, hshift]; decide⟩
      · exact ⟨9 + c, hmiss c 9 (Or.inr (Or.inr rfl)), 9, by decide, by rw [← hvc, hshift]; decide⟩
      · exact absurd (by change (6 : Fin 13) + c = v at hvc; rw [← hvc]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))) hv
      · exact ⟨7 + c, hmiss c 7 (Or.inl rfl), 0, by decide, by rw [← hvc, hshift]; decide⟩
      · exact ⟨7 + c, hmiss c 7 (Or.inl rfl), 1, by decide, by rw [← hvc, hshift]; decide⟩
      · exact ⟨8 + c, hmiss c 8 (Or.inr (Or.inl rfl)), 1, by decide, by rw [← hvc, hshift]; decide⟩
      · exact ⟨7 + c, hmiss c 7 (Or.inl rfl), 3, by decide, by rw [← hvc, hshift]; decide⟩
      · exact ⟨8 + c, hmiss c 8 (Or.inr (Or.inl rfl)), 3, by decide, by rw [← hvc, hshift]; decide⟩
      · exact ⟨9 + c, hmiss c 9 (Or.inr (Or.inr rfl)), 3, by decide, by rw [← hvc, hshift]; decide⟩
    have hgen2 : ∀ c : Fin 13,
        ¬ (∃ w3 : Fin 13, ∀ p3 ∈ Pshift c, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) := by
      rintro c ⟨w3, hw3⟩
      obtain ⟨d0, hd0, h0⟩ := hw3 c (by simp [Pshift])
      obtain ⟨d1, hd1, h1⟩ := hw3 (1 + c) (by simp [Pshift])
      obtain ⟨d2, hd2, h2⟩ := hw3 (2 + c) (by simp [Pshift])
      have h10 : 1 + d0 = d1 := by
        apply add_left_cancel (a := w3)
        calc
          w3 + (1 + d0) = 1 + (w3 + d0) := add_left_comm w3 1 d0
          _ = 1 + c := by rw [← h0]
          _ = w3 + d1 := h1
      have h20 : 2 + d0 = d2 := by
        apply add_left_cancel (a := w3)
        calc
          w3 + (2 + d0) = 2 + (w3 + d0) := add_left_comm w3 2 d0
          _ = 2 + c := by rw [← h0]
          _ = w3 + d2 := h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd0
      rcases hd0 with rfl | rfl | rfl | rfl
      · rw [← h20] at hd2; exact absurd hd2 (by decide)
      · rw [← h10] at hd1; exact absurd hd1 (by decide)
      · rw [← h10] at hd1; exact absurd hd1 (by decide)
      · rw [← h10] at hd1; exact absurd hd1 (by decide)
    have hgen3 : ∀ c : Fin 13,
        ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13,
          (∀ pp ∈ Pshift c, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) →
          (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) := by
      rintro c ⟨v4, hv4⟩
      obtain ⟨d7, hd7, h7⟩ := hv4 (7 + c) (hmiss c 7 (Or.inl rfl))
      obtain ⟨d8, hd8, h8⟩ := hv4 (8 + c) (hmiss c 8 (Or.inr (Or.inl rfl)))
      obtain ⟨d9, hd9, h9⟩ := hv4 (9 + c) (hmiss c 9 (Or.inr (Or.inr rfl)))
      have h89 : 1 + d9 = d8 := by
        apply add_left_cancel (a := 8 + c)
        calc
          (8 + c) + (1 + d9) = ((8 + 1) + c) + d9 := by abel
          _ = (9 + c) + d9 := by rfl
          _ = v4 := h9.symm
          _ = (8 + c) + d8 := h8
      have h79 : 2 + d9 = d7 := by
        apply add_left_cancel (a := 7 + c)
        calc
          (7 + c) + (2 + d9) = ((7 + 2) + c) + d9 := by abel
          _ = (9 + c) + d9 := by rfl
          _ = v4 := h9.symm
          _ = (7 + c) + d7 := h7
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd9
      rcases hd9 with rfl | rfl | rfl | rfl
      · rw [← h79] at hd7; exact absurd hd7 (by decide)
      · rw [← h89] at hd8; exact absurd hd8 (by decide)
      · rw [← h89] at hd8; exact absurd hd8 (by decide)
      · rw [← h89] at hd8; exact absurd hd8 (by decide)
    have hpIn : ∀ c : Fin 13, c ∈ Pshift c := fun c => Finset.mem_insert_self _ _
    by_cases hk : C.output < 13
    · let c : Fin 13 := ⟨C.output, hk⟩
      have hf := hneg (Pshift c) (hgen1 c) ⟨hgen2 c, hgen3 c⟩
      let x : Fin (13 + 13) → Bool := fun kk =>
        decide ((∃ pp ∈ Pshift c, kk = Fin.castAdd 13 pp) ∨
          (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
            (∀ pp ∈ Pshift c, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))
      change (C.gates.foldl (fun acc g =>
        acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) (List.ofFn x)).getD C.output false = false at hf
      have hlen : C.output < (List.ofFn x).length := by simp [hlt]
      rw [hwireIn C.gates (List.ofFn x) C.output hlen] at hf
      have hof : (List.ofFn x).getD C.output false = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_ofFn]
        simp only [x, decide_eq_true_eq]
        exact Or.inl ⟨c, hpIn c, rfl⟩
      rw [hof] at hf
      exact Bool.noConfusion hf
    · let w : Fin 13 := ⟨C.output - 13, by omega⟩
      let c : Fin 13 := w - 7
      have hwc : 7 + c = w := by rw [add_comm]; exact sub_add_cancel w 7
      have hf := hneg (Pshift c) (hgen1 c) ⟨hgen2 c, hgen3 c⟩
      let x : Fin (13 + 13) → Bool := fun kk =>
        decide ((∃ pp ∈ Pshift c, kk = Fin.castAdd 13 pp) ∨
          (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
            (∀ pp ∈ Pshift c, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))
      change (C.gates.foldl (fun acc g =>
        acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) (List.ofFn x)).getD C.output false = false at hf
      have hlen : C.output < (List.ofFn x).length := by simp [hlt]
      rw [hwireIn C.gates (List.ofFn x) C.output hlen] at hf
      have hof : (List.ofFn x).getD C.output false = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_ofFn]
        simp only [x, decide_eq_true_eq]
        refine Or.inr ⟨w, ?_, ?_⟩
        · apply Fin.ext
          simp [w]
          omega
        · rw [← hwc]
          exact hmiss c 7 (Or.inl rfl)
      rw [hof] at hf
      exact Bool.noConfusion hf
  have hltg : C.output - 26 < C.gates.length := by
    change C.output < 26 + C.gates.length at houtLt
    omega
  have hm :
      ∀ g ∈ C.gates,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := hmono
  have hop :
      C.gates[C.output - 26].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        C.gates[C.output - 26].op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm _ (List.getElem_mem hltg)).1
  have key : ∀ a b : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + dd) ↔
      (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) := by
    intro a b
    simp
  simp only [key] at hpos hneg
  rcases hop with hand | hor
  · exact hOutAnd ⟨C, hmono, hsize, houtGe, ⟨hltg, by simpa using hand⟩, hpos, hneg⟩
  · exact hOutOr ⟨C, hmono, hsize, houtGe, ⟨hltg, by simpa using hor⟩, hpos, hneg⟩
