import Mathlib
import PEqualNP.Defs

-- Classify the tests as arcs of three or four points, solve the gate table on those tests,
-- and read the table as a circuit.
theorem PEqualNP.Outside.R_meta_1681_1
    (classify : let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ P : Finset (Fin 13),
        (∀ v : Fin 13, v ∉ P → ∃ w : Fin 13, (∀ p ∈ P, p - w ∉ D) ∧ v - w ∈ D) →
        (∀ w : Fin 13, ∃ p ∈ P, p - w ∉ D) →
        (∀ v : Fin 13, ∃ w : Fin 13, (∀ p ∈ P, p - w ∉ D) ∧ v - w ∉ D) →
        (P.card = 3 ∨ P.card = 4) ∧
          ∀ w : Fin 13, (P.filter fun p => p - w ∈ D).card ≤ 2)
    (table : let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∃ (op : Fin 63 → Bool) (a b : Fin 63 → ℕ) (out : ℕ), out < 26 + 63 ∧
        (∀ j : Fin 63, a j < b j ∧ b j < 26 + j.val) ∧
        (∀ p w : Fin 13, p - w ∈ D → ∃ v : ℕ → Bool,
          (∀ i : Fin 13, v i.val = decide (i = p) ∧ v (13 + i.val) = decide (i = w)) ∧
          (∀ j : Fin 63, v (26 + j.val) =
            if op j then v (a j) && v (b j) else v (a j) || v (b j)) ∧
          v out = true) ∧
        (∀ P : Finset (Fin 13), (P.card = 3 ∨ P.card = 4) →
          (∀ w : Fin 13, (P.filter fun p => p - w ∈ D).card ≤ 2) → ∃ v : ℕ → Bool,
          (∀ i : Fin 13, v i.val = decide (i ∈ P) ∧
            v (13 + i.val) = decide (∀ p ∈ P, p - i ∉ D)) ∧
          (∀ j : Fin 63, v (26 + j.val) =
            if op j then v (a j) && v (b j) else v (a j) || v (b j)) ∧
          v out = false))
    (sound : ∀ (n s : ℕ) (op : Fin s → Bool) (a b : Fin s → ℕ) (out : ℕ)
      (x : Fin n → Bool) (v : ℕ → Bool), out < n + s →
      (∀ j : Fin s, a j < n + j.val ∧ b j < n + j.val) →
      (∀ i : Fin n, v i.val = x i) →
      (∀ j : Fin s, v (n + j.val) =
        if op j then v (a j) && v (b j) else v (a j) || v (b j)) →
      PEqualNP.MetaComplexity.circuitFun n
        ⟨List.ofFn fun j : Fin s => ⟨if op j then PEqualNP.CircuitLowerBounds.GateOp.and
          else PEqualNP.CircuitLowerBounds.GateOp.or, [a j, b j]⟩, out⟩ x = v out) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  obtain ⟨op, a, b, out, hout, hreads, hpos, hneg⟩ := table
  have inc (p w : Fin 13) :
      (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d) ↔
        p - w ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    constructor
    · rintro ⟨d, hd, he⟩
      have hs : p - w = d := sub_eq_iff_eq_add.2 (he.trans (add_comm _ _))
      rwa [hs]
    · intro h
      exact ⟨p - w, h, (sub_add_cancel p w).symm.trans (add_comm _ _)⟩
  have cross (i j : Fin 13) : Fin.castAdd 13 i ≠ Fin.natAdd 13 j := by
    intro h
    have d := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at d
    omega
  have rb (j : Fin 63) : a j < 13 + 13 + j.val ∧ b j < 13 + 13 + j.val :=
    ⟨(hreads j).1.trans (hreads j).2, (hreads j).2⟩
  refine ⟨⟨List.ofFn fun j : Fin 63 => ⟨if op j then PEqualNP.CircuitLowerBounds.GateOp.and
      else PEqualNP.CircuitLowerBounds.GateOp.or, [a j, b j]⟩, out⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    refine ⟨?_, le_refl 2⟩
    cases op j <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro p w hpw
    obtain ⟨v, hv, hgate, hv1⟩ := hpos p w ((inc p w).1 hpw)
    refine (sound (13 + 13) 63 op a b out _ v hout rb ?_ hgate).trans hv1
    intro i
    refine Fin.addCases (fun q => ?_) (fun q => ?_) i
    · rw [Fin.val_castAdd, (hv q).1]
      apply decide_eq_decide.mpr
      exact ⟨fun h => Or.inl (congrArg _ h), fun h => h.elim
        (fun e => Fin.castAdd_injective 13 13 e) (fun e => (cross _ _ e).elim)⟩
    · rw [Fin.val_natAdd, (hv q).2]
      apply decide_eq_decide.mpr
      exact ⟨fun h => Or.inr (congrArg _ h), fun h => h.elim
        (fun e => (cross _ _ e.symm).elim) (fun e => Fin.natAdd_injective 13 13 e)⟩
  · intro P closed generic
    have hmiss (w : Fin 13) :
        (∀ p ∈ P, ¬ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d) ↔
          ∀ p ∈ P, p - w ∉ ({0, 1, 3, 9} : Finset (Fin 13)) :=
      forall₂_congr fun p _ => not_congr (inc p w)
    obtain ⟨hcard, harc⟩ := classify P
      (fun v hv => by
        obtain ⟨w, hw, hvw⟩ := closed v hv
        exact ⟨w, (hmiss w).1 hw, (inc v w).1 hvw⟩)
      (fun w => by
        by_contra hno
        push_neg at hno
        exact generic.1 ⟨w, fun p hp => (inc p w).2 (hno p hp)⟩)
      (fun v => by
        by_contra hno
        push_neg at hno
        exact generic.2 ⟨v, fun w hw => (inc v w).2 (hno w ((hmiss w).1 hw))⟩)
    obtain ⟨v, hv, hgate, hv0⟩ := hneg P hcard harc
    refine (sound (13 + 13) 63 op a b out _ v hout rb ?_ hgate).trans hv0
    intro i
    refine Fin.addCases (fun q => ?_) (fun q => ?_) i
    · rw [Fin.val_castAdd, (hv q).1]
      apply decide_eq_decide.mpr
      constructor
      · exact fun h => Or.inl ⟨q, h, rfl⟩
      · rintro (⟨p, hp, e⟩ | ⟨w, e, _⟩)
        · exact (Fin.castAdd_injective 13 13 e) ▸ hp
        · exact (cross _ _ e).elim
    · rw [Fin.val_natAdd, (hv q).2]
      apply decide_eq_decide.mpr
      constructor
      · exact fun h => Or.inr ⟨q, rfl, (hmiss q).2 h⟩
      · rintro (⟨p, _, e⟩ | ⟨w, e, hw⟩)
        · exact (cross _ _ e.symm).elim
        · have hq : q = w := Fin.natAdd_injective 13 13 e
          exact (hmiss q).1 (hq ▸ hw)
