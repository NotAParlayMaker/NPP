import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_1780_2
    (hbase : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1) → PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true)) → N * q ≤ 32 * C.size + 3 * N + (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))).length)
    (hnorm : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∃ D : Circuit,
      IsMinimalMonoCircuit n D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧
      circuitFun n D = circuitFun n C ∧
      ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
        circuitFun n D x = true → circuitFun n D y = true)
    (hlocal : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l')) →
      IsMinimalMonoCircuit (N+N) D → ReadsBack (N+N) D →
      (∀ z, circuitFun (N+N) D z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ∀ (S : List (ℕ × ℕ)) (G : Finset (Fin D.size)),
        S.Sublist (doubleReread D (N+N) (fun w => decide (N ≤ w))
          ((List.finRange N).flatMap fun p => ((List.finRange N).filter fun l => decide (I p l)).map fun l => (p.val,N+l.val))) →
        S ≠ [] → (∀ e ∈ S, ∀ k : Fin D.size, isJoin D (N+N) (N+N+k) e.1 e.2 = true → k ∈ G) →
        ∃ (j : Fin D.size) (B : Finset (Fin D.size)), B ⊆ G ∧ j ∈ B ∧
          (∀ k ∈ B, k = j ∨ InCone (N+N) D k j) ∧
          (∃ e ∈ S, isJoin D (N+N) (N+N+j) e.1 e.2 = true) ∧
          (S.filter (fun e => B.toList.any (fun k => isJoin D (N+N) (N+N+k) e.1 e.2))).length ≤ 66 * B.card) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq hN hcard hlines hm hacc hsound
  classical
  obtain ⟨D,hmin,hback,hsize,hfun,hmono⟩ := hnorm (N+N) C hm
  have exactD : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
    intro z
    by_cases ex : ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
    · rw [decide_eq_true ex]
      obtain ⟨p,l,he,hp,hl⟩ := ex
      apply hmono (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) z
      · intro i hi
        obtain rfl | rfl := of_decide_eq_true hi
        · exact hp
        · exact hl
      · rw [hfun]
        exact hacc p l he
    · rw [decide_eq_false ex,hfun]
      exact hsound z ex
  have girth : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l') := by
    rintro p p' l l' hp hl ⟨a,b,c,d⟩
    exact hl ((hlines p p' hp).unique ⟨a,b⟩ ⟨c,d⟩)
  have ao : AndOrFanInTwo D := ⟨fun g hg => (hmin.1 g hg).1, fun g hg => (hmin.1 g hg).2⟩
  let E := doubleReread D (N+N) (fun w => decide (N≤w))
      ((List.finRange N).flatMap fun p => ((List.finRange N).filter fun l => decide (I p l)).map fun l => (p.val,N+l.val))
  have base : N*q ≤ 32*D.size+3*N+E.length :=
    hbase q N I D (by omega) hN hcard hlines ao hback exactD
  let J (k : Fin D.size) (e : ℕ × ℕ) := isJoin D (N+N) (N+N+k) e.1 e.2
  have bound : ∀ (n : ℕ) (G : Finset (Fin D.size)), G.card = n →
      ∀ S : List (ℕ×ℕ), S.Sublist E →
      (∀ e ∈ S, ∀ k, J k e = true → k ∈ G) → S.length ≤ 66*n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro G count S sub avail
      by_cases empty : S = []
      · simp [empty]
      obtain ⟨j,B,within,hj,_,_,charge⟩ := hlocal N I D girth hmin hback exactD S G sub empty avail
      let hit (e : ℕ×ℕ) := B.toList.any (fun k => J k e)
      change (S.filter hit).length ≤ 66 * B.card at charge
      have card := Finset.card_le_card within
      have pos := Finset.card_pos.mpr ⟨j,hj⟩
      have dif := Finset.card_sdiff_of_subset within
      have restBound := ih (G \ B).card (by omega) (G \ B) rfl
          (S.filter (fun e => !hit e)) ((List.filter_sublist).trans sub) (by
        intro e he k hk
        obtain ⟨ins,miss⟩ := List.mem_filter.mp he
        refine Finset.mem_sdiff.mpr ⟨avail e ins k hk,?_⟩
        intro ink
        have got : hit e = true :=
          List.any_eq_true.mpr ⟨k,Finset.mem_toList.mpr ink,hk⟩
        simp [got] at miss)
      have partition : (S.filter hit).length + (S.filter (fun e => !hit e)).length = S.length :=
        (S.length_eq_length_filter_add hit).symm
      omega
  have allBound := bound _ Finset.univ rfl E (List.Sublist.refl E) (by simp)
  have remain : E.length ≤ 66*D.size := by simpa using allBound
  have scale : N * 199 ≤ N*q := Nat.mul_le_mul_left N hq
  omega
