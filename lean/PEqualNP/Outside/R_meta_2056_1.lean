import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Order-3 Frobenius automorphism (x |-> 3*x mod 13) of PG(2,3) partitions the 13 points into
-- the fixed point 0 and three orbits of the 4-point slice {1, 2, 4, 7}. Finding an 18-gate
-- monotone circuit for the 4-point slice and gluing three rotated copies with point 0 yields
-- a 61-gate (<= 63) circuit for PG(2,3).
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2056_1
    (hSlice :
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ D.size ≤ 18 ∧ D.output < 26 + D.size ∧
        ∀ s t : Finset (Fin 13), D.eval (List.ofFn (vec s t)) = true ↔
          ∃ p ∈ s, p.val ∈ ([1, 2, 4, 7] : List ℕ) ∧ ∃ l ∈ t, near p l)
    (hGlue :
      let perm := fun (k : ℕ) (x : Fin 26 → Bool) (i : Fin 26) =>
        if i.val < 13 then x (Fin.ofNat 26 ((k * i.val) % 13))
        else x (Fin.ofNat 26 (13 + (k * (i.val - 13)) % 13))
      ∀ D : Circuit, Monotone2 D → ReadsBack 26 D → D.output < 26 + D.size →
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 3 * D.size + 7 ∧
          ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
            D.eval (List.ofFn (perm 1 x)) = true ∨
            D.eval (List.ofFn (perm 3 x)) = true ∨
            D.eval (List.ofFn (perm 9 x)) = true ∨
            (x 0 = true ∧ (x 13 = true ∨ x 14 = true ∨ x 16 = true ∨ x 22 = true))) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  let near : Fin 13 → Fin 13 → Prop := fun p l => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let vec : Finset (Fin 13) → Finset (Fin 13) → Fin 26 → Bool := fun s t i =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off : Finset (Fin 13) → Finset (Fin 13) := fun s =>
    Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, ¬ near p l
  let perm : ℕ → (Fin 26 → Bool) → Fin 26 → Bool := fun k x i =>
    if i.val < 13 then x (Fin.ofNat 26 ((k * i.val) % 13))
    else x (Fin.ofNat 26 (13 + (k * (i.val - 13)) % 13))
  have hNearInv : ∀ k ∈ ([1, 3, 9] : List ℕ), ∀ p l : Fin 13,
      near p l ↔ near (Fin.ofNat 13 (k * p.val)) (Fin.ofNat 13 (k * l.val)) := by
    dsimp only [near]; decide
  have hOrbits : ∀ p : Fin 13, p = 0 ∨
      ∃ k ∈ ([1, 3, 9] : List ℕ), ∃ q : Fin 13, q.val ∈ ([1, 2, 4, 7] : List ℕ) ∧
        Fin.ofNat 13 (k * q.val) = p := by decide
  have hSurj : ∀ k ∈ ([1, 3, 9] : List ℕ), ∀ l : Fin 13,
      ∃ l' : Fin 13, Fin.ofNat 13 (k * l'.val) = l := by decide
  have hZeroNear : ∀ l : Fin 13, near 0 l ↔ (l = 0 ∨ l = 1 ∨ l = 3 ∨ l = 9) := by
    dsimp only [near]; decide
  have hPermVec : ∀ (k : ℕ) (s t : Finset (Fin 13)),
      perm k (vec s t) = vec (Finset.univ.filter fun p : Fin 13 => Fin.ofNat 13 (k * p.val) ∈ s)
        (Finset.univ.filter fun l : Fin 13 => Fin.ofNat 13 (k * l.val) ∈ t) := by
    intro k s t
    funext i
    dsimp only [perm, vec]
    by_cases hi : i.val < 13
    · rw [if_pos hi, if_pos hi]
      have hlt : (Fin.ofNat 26 ((k * i.val) % 13)).val < 13 := by
        change ((k * i.val) % 13) % 26 < 13
        have h1 : (k * i.val) % 13 < 13 := Nat.mod_lt _ (by decide)
        omega
      rw [if_pos hlt]
      congr 1
      have heq : Fin.ofNat 13 (Fin.ofNat 26 ((k * i.val) % 13)).val =
          Fin.ofNat 13 (k * (Fin.ofNat 13 i.val).val) := by
        apply Fin.ext
        change (((k * i.val) % 13) % 26) % 13 = (k * (i.val % 13)) % 13
        have h1 : (k * i.val) % 13 < 13 := Nat.mod_lt _ (by decide)
        rw [Nat.mod_eq_of_lt (by omega : (k * i.val) % 13 < 26), Nat.mod_eq_of_lt hi, Nat.mod_mod]
      rw [Finset.mem_filter]
      exact propext ⟨fun h => ⟨Finset.mem_univ _, by rw [← heq]; exact h⟩, fun h => by rw [heq]; exact h.2⟩
    · rw [if_neg hi, if_neg hi]
      have hge : ¬ (Fin.ofNat 26 (13 + (k * (i.val - 13)) % 13)).val < 13 := by
        change ¬ (13 + (k * (i.val - 13)) % 13) % 26 < 13
        have h1 : (k * (i.val - 13)) % 13 < 13 := Nat.mod_lt _ (by decide)
        rw [Nat.mod_eq_of_lt (by omega : 13 + (k * (i.val - 13)) % 13 < 26)]
        omega
      rw [if_neg hge]
      congr 1
      have heq : Fin.ofNat 13 (Fin.ofNat 26 (13 + (k * (i.val - 13)) % 13)).val =
          Fin.ofNat 13 (k * (Fin.ofNat 13 i.val).val) := by
        apply Fin.ext
        change ((13 + (k * (i.val - 13)) % 13) % 26) % 13 = (k * (i.val % 13)) % 13
        have h1 : (k * (i.val - 13)) % 13 < 13 := Nat.mod_lt _ (by decide)
        have h2 : i.val % 13 = i.val - 13 := by have := i.isLt; omega
        rw [h2, Nat.mod_eq_of_lt (by omega : 13 + (k * (i.val - 13)) % 13 < 26)]
        omega
      rw [Finset.mem_filter]
      exact propext ⟨fun h => ⟨Finset.mem_univ _, by rw [← heq]; exact h⟩, fun h => by rw [heq]; exact h.2⟩
  obtain ⟨D, hDmono, hDrb, hDsz, hDout, hDeval⟩ := hSlice
  obtain ⟨C, hCmono, hCsz, hCeval⟩ := hGlue D hDmono hDrb hDout
  have hC63 : C.size ≤ 63 := by omega
  have hAll : ∀ s t : Finset (Fin 13), C.eval (List.ofFn (vec s t)) = true ↔
      ∃ p ∈ s, ∃ l ∈ t, near p l := by
    intro s t
    rw [hCeval (vec s t)]
    have hK : ∀ k ∈ ([1, 3, 9] : List ℕ),
        D.eval (List.ofFn (perm k (vec s t))) = true ↔
          ∃ q : Fin 13, Fin.ofNat 13 (k * q.val) ∈ s ∧ q.val ∈ ([1, 2, 4, 7] : List ℕ) ∧
            ∃ l ∈ t, near (Fin.ofNat 13 (k * q.val)) l := by
      intro k hk
      rw [hPermVec k s t, hDeval]
      constructor
      · rintro ⟨q, hqs, hq4, l', hl't, hnl⟩
        have hqs' : Fin.ofNat 13 (k * q.val) ∈ s := (Finset.mem_filter.mp hqs).2
        have hl't' : Fin.ofNat 13 (k * l'.val) ∈ t := (Finset.mem_filter.mp hl't).2
        exact ⟨q, hqs', hq4, Fin.ofNat 13 (k * l'.val), hl't', (hNearInv k hk q l').mp hnl⟩
      · rintro ⟨q, hqs, hq4, l, hlt, hnl⟩
        obtain ⟨l', hl'eq⟩ := hSurj k hk l
        refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hqs⟩, hq4,
          l', Finset.mem_filter.mpr ⟨Finset.mem_univ l', by rw [hl'eq]; exact hlt⟩, ?_⟩
        exact (hNearInv k hk q l').mpr (by rw [hl'eq]; exact hnl)
    have hZero : (vec s t 0 = true ∧ (vec s t 13 = true ∨ vec s t 14 = true ∨ vec s t 16 = true ∨ vec s t 22 = true)) ↔
        (0 : Fin 13) ∈ s ∧ ∃ l ∈ t, near 0 l := by
      have hv0 : vec s t 0 = true ↔ (0 : Fin 13) ∈ s := by dsimp only [vec]; simp
      have hv13 : vec s t 13 = true ↔ (0 : Fin 13) ∈ t := by dsimp only [vec]; simp
      have hv14 : vec s t 14 = true ↔ (1 : Fin 13) ∈ t := by dsimp only [vec]; simp
      have hv16 : vec s t 16 = true ↔ (3 : Fin 13) ∈ t := by dsimp only [vec]; simp
      have hv22 : vec s t 22 = true ↔ (9 : Fin 13) ∈ t := by dsimp only [vec]; simp
      rw [hv0, hv13, hv14, hv16, hv22]
      constructor
      · rintro ⟨h0s, h0 | h1 | h3 | h9⟩
        · exact ⟨h0s, 0, h0, (hZeroNear 0).mpr (Or.inl rfl)⟩
        · exact ⟨h0s, 1, h1, (hZeroNear 1).mpr (Or.inr (Or.inl rfl))⟩
        · exact ⟨h0s, 3, h3, (hZeroNear 3).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact ⟨h0s, 9, h9, (hZeroNear 9).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩
      · rintro ⟨h0s, l, hlt, hnl⟩
        refine ⟨h0s, ?_⟩
        rcases (hZeroNear l).mp hnl with rfl | rfl | rfl | rfl
        · exact Or.inl hlt
        · exact Or.inr (Or.inl hlt)
        · exact Or.inr (Or.inr (Or.inl hlt))
        · exact Or.inr (Or.inr (Or.inr hlt))
    rw [hK 1 (by decide), hK 3 (by decide), hK 9 (by decide), hZero]
    constructor
    · rintro (⟨q, hqs, _, l, hlt, hnl⟩ | ⟨q, hqs, _, l, hlt, hnl⟩ | ⟨q, hqs, _, l, hlt, hnl⟩ | ⟨h0s, l, hlt, hnl⟩)
      · exact ⟨_, hqs, l, hlt, hnl⟩
      · exact ⟨_, hqs, l, hlt, hnl⟩
      · exact ⟨_, hqs, l, hlt, hnl⟩
      · exact ⟨0, h0s, l, hlt, hnl⟩
    · rintro ⟨p, hps, l, hlt, hnl⟩
      rcases hOrbits p with rfl | ⟨k, hk, q, hq4, hqeq⟩
      · exact Or.inr (Or.inr (Or.inr ⟨hps, l, hlt, hnl⟩))
      · rcases List.mem_cons.mp hk with rfl | hk'
        · exact Or.inl ⟨q, by rw [hqeq]; exact hps, hq4, l, hlt, by rw [hqeq]; exact hnl⟩
        · rcases List.mem_cons.mp hk' with rfl | hk''
          · exact Or.inr (Or.inl ⟨q, by rw [hqeq]; exact hps, hq4, l, hlt, by rw [hqeq]; exact hnl⟩)
          · rcases List.mem_cons.mp hk'' with rfl | hnil
            · exact Or.inr (Or.inr (Or.inl ⟨q, by rw [hqeq]; exact hps, hq4, l, hlt, by rw [hqeq]; exact hnl⟩))
            · cases hnil
  refine ⟨C, hCmono, hC63, ?_⟩
  change (∀ p l : Fin 13, near p l → C.eval (List.ofFn (vec {p} {l})) = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 →
      C.eval (List.ofFn (vec s (off s))) = false ∧ C.eval (List.ofFn (vec (off s) s)) = false
  constructor
  · intro p l h
    exact (hAll {p} {l}).mpr ⟨p, Finset.mem_singleton_self p, l, Finset.mem_singleton_self l, h⟩
  · intro s _
    constructor
    · rw [Bool.eq_false_iff]
      intro h
      obtain ⟨p, hp, l, hl, hnl⟩ := (hAll s (off s)).mp h
      exact (Finset.mem_filter.mp hl).2 p hp hnl
    · rw [Bool.eq_false_iff]
      intro h
      obtain ⟨p, hp, l, hl, hnl⟩ := (hAll (off s) s).mp h
      apply (Finset.mem_filter.mp hp).2 l hl
      dsimp only [near] at hnl ⊢
      rw [Nat.add_comm]
      exact hnl
