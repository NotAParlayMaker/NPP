import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.R_meta_1477_581
    (hNormalize : ∀ C : Circuit, Monotone2 C → ∃ D : Circuit,
      Monotone2 D ∧ NestedCover.ReadsBack 42 D ∧ D.size ≤ C.size ∧
      ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (hBound :
      let diff : Finset (Fin 21) := {0, 1, 4, 14, 16}
      ∀ C : Circuit, Monotone2 C → NestedCover.ReadsBack 42 C →
        (∀ p l : Fin 21, p - l ∈ diff →
          C.eval (List.ofFn fun i : Fin 42 =>
            decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l)) = true) →
        (∀ Q : Finset (Fin 21), Q.card = 6 →
          (∀ l : Fin 21, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2) →
          C.eval (List.ofFn (Fin.addCases (fun p => decide (p ∈ Q))
            (fun l => decide (∀ p ∈ Q, p - l ∉ diff)))) = false) →
        125 ≤ C.size) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  intro h
  obtain ⟨C, hMono, hSize, hEval⟩ := h
  obtain ⟨D, hDMono, hBack, hDSize, hSame⟩ := hNormalize C hMono
  let diff : Finset (Fin 21) := {0, 1, 4, 14, 16}
  let edges : List (ℕ × ℕ) := ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ))
  have hTable : edges = (List.finRange 21).flatMap (fun p =>
      ((List.finRange 21).filter fun l => decide (p - l ∈ diff)).map fun l => (p.val, 21+l.val)) := by
    decide +kernel
  have hInc : ∀ p l : Fin 21,
      ((Fin.castAdd 21 p).val, (Fin.natAdd 21 l).val) ∈ edges ↔ p - l ∈ diff := by
    intro p l
    rw [hTable, List.mem_flatMap]
    constructor
    · rintro ⟨p', _, hMem⟩
      obtain ⟨l', hKeep, hPair⟩ := List.mem_map.mp hMem
      have hp : p' = p := Fin.ext (congrArg Prod.fst hPair)
      have hl : l' = l := by
        apply Fin.ext
        have hIdx := congrArg Prod.snd hPair
        change 21 + l'.val = 21 + l.val at hIdx
        omega
      subst p'
      subst l'
      exact of_decide_eq_true (List.mem_filter.mp hKeep).2
    · intro h
      exact ⟨p, by simp, List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨by simp, decide_eq_true h⟩, rfl⟩⟩
  have hBipart : ∀ u v : Fin 42, (u.val, v.val) ∈ edges → u.val < 21 ∧ 21 ≤ v.val := by
    have hAll : edges.all (fun e => decide (e.1 < 21 ∧ 21 ≤ e.2)) = true := by decide +kernel
    intro u v h
    exact of_decide_eq_true (List.all_eq_true.mp hAll _ h)
  have hPositive : ∀ p l : Fin 21, p - l ∈ diff →
      D.eval (List.ofFn fun i : Fin 42 =>
        decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l)) = true := by
    intro p l hp
    rw [hSame]
    exact (hEval _).mpr ⟨Fin.castAdd 21 p, Fin.natAdd 21 l, (hInc p l).mpr hp, by simp, by simp⟩
  have hLower : 125 ≤ D.size := by
    apply hBound D hDMono hBack hPositive
    intro Q _ _
    rw [hSame]
    by_contra hf
    obtain ⟨u, v, huv, hu, hv⟩ := (hEval _).mp (Bool.eq_true_of_not_eq_false hf)
    obtain ⟨hu21, hv21⟩ := hBipart u v huv
    let p : Fin 21 := ⟨u.val, hu21⟩
    let l : Fin 21 := ⟨v.val - 21, by omega⟩
    have hp : u = Fin.castAdd 21 p := Fin.ext rfl
    have hl : v = Fin.natAdd 21 l := by
      apply Fin.ext
      change v.val = 21 + (v.val - 21)
      omega
    have hpl : p - l ∈ diff := (hInc p l).mp (by simpa only [hp, hl] using huv)
    have hIn : p ∈ Q := by simpa only [hp, Fin.addCases_left, decide_eq_true_eq] using hu
    have hMiss : ∀ r ∈ Q, r - l ∉ diff := by
      simpa only [hl, Fin.addCases_right, decide_eq_true_eq] using hv
    exact hMiss p hIn hpl
  exact (Nat.not_succ_le_self 124) (hLower.trans (hDSize.trans hSize))
