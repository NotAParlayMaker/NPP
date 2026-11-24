import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Every active point or line wire is essential: the accepted pair and the rejected singleton
-- differ only there. Fan-in two circuits have at most size+1 essential inputs (support).
-- In a C4-free accepted set with all degrees above 44, a nonempty set has at least
-- 1 + 45*44 = 1981 active points and as many active lines (count).
-- So a nonempty accepted set forces at least 3961 gates, and only that case is left (core).
theorem PEqualNP.Outside.R_meta_4453_1
    (support : ∀ (n : ℕ) (C : Circuit) (A : Finset (Fin n)),
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      (∀ i ∈ A, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) →
      A.card ≤ C.size + 1)
    (count : ∀ (N : ℕ) (E : Finset (Fin N × Fin N)),
      (∀ p r l m : Fin N, p ≠ r → l ≠ m →
        ¬ ((p,l) ∈ E ∧ (r,l) ∈ E ∧ (p,m) ∈ E ∧ (r,m) ∈ E)) →
      (∀ e ∈ E, 44 < (E.filter fun f => f.1 = e.1).card ∧
        44 < (E.filter fun f => f.2 = e.2).card) →
      E.Nonempty →
      1981 ≤ (E.image Prod.fst).card ∧ 1981 ≤ (E.image Prod.snd).card)
    (core : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      131 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      IsAO2 (N+N) C →
      (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N+N) C x = false) →
      let E := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧
        circuitFun (N+N) C (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true
      (∀ v : Fin (N+N), let d := (E.filter fun e => v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2).card
         d = 0 ∨ 44 < d) →
      3961 ≤ C.size → E.card ≤ 44*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (131 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : Finset (Fin x2 × Fin x2) := {x12 : Fin x2 × Fin x2 | x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true};               (∀ (x13 : Fin (x2 + x2)),                   have x14 : ℕ := {x14 ∈ x12 | x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2}.card;                   x14 = (0 : ℕ) ∨ (44 : ℕ) < x14) →                 x12.card ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hN deg uniq ao sound E hdeg
  have apart : ∀ p l : Fin N, Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have h' := congrArg Fin.val h
    change p.val = N + l.val at h'
    omega
  have natInj : ∀ a b : Fin N, Fin.natAdd N a = Fin.natAdd N b → a = b := by
    intro a b h
    apply Fin.ext
    have h' := congrArg Fin.val h
    change N + a.val = N + b.val at h'
    omega
  have memE : ∀ e, e ∈ E ↔ I e.1 e.2 ∧ circuitFun (N+N) C
      (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true := by
    intro e
    simp [E]
  by_cases hE : E.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hE]
    simp
  refine core q N I C hq hN deg uniq ao sound hdeg ?_
  -- soundness on singletons
  have offPoint : ∀ p : Fin N, circuitFun (N+N) C (fun i => decide (i = Fin.castAdd N p)) = false := by
    intro p
    apply sound
    · have h0 : Fintype.card {l : Fin N //
          (fun i => decide (i = Fin.castAdd N p)) (Fin.natAdd N l) = true} = 0 :=
        Fintype.card_eq_zero_iff.mpr ⟨fun ⟨l, hl⟩ => apart p l (of_decide_eq_true hl).symm⟩
      exact (le_of_eq h0).trans (Nat.zero_le q)
    · rintro ⟨r, l, _, _, bad⟩
      exact apart p l (of_decide_eq_true bad).symm
  have offLine : ∀ l : Fin N, circuitFun (N+N) C (fun i => decide (i = Fin.natAdd N l)) = false := by
    intro l
    apply sound
    · rw [Fintype.card_subtype]
      have sub : (Finset.univ.filter fun k : Fin N => decide (Fin.natAdd N k = Fin.natAdd N l) = true)
          ⊆ {l} := by
        intro k hk
        exact Finset.mem_singleton.mpr
          (natInj _ _ (of_decide_eq_true (Finset.mem_filter.mp hk).2))
      have h := Finset.card_le_card sub
      simp only [Finset.card_singleton] at h
      exact h.trans (by omega)
    · rintro ⟨p, k, _, bad, _⟩
      exact apart p l (of_decide_eq_true bad)
  -- C4-freeness
  have c4 : ∀ p r l m : Fin N, p ≠ r → l ≠ m →
      ¬ ((p,l) ∈ E ∧ (r,l) ∈ E ∧ (p,m) ∈ E ∧ (r,m) ∈ E) := by
    rintro p r l m hpr hlm ⟨h1, h2, h3, h4⟩
    obtain ⟨k, _, hk⟩ := uniq p r hpr
    have e1 := hk l ⟨((memE _).mp h1).1, ((memE _).mp h2).1⟩
    have e2 := hk m ⟨((memE _).mp h3).1, ((memE _).mp h4).1⟩
    exact hlm (e1.trans e2.symm)
  -- degrees
  have degP : ∀ e ∈ E, 44 < (E.filter fun f => f.1 = e.1).card := by
    intro e he
    have hset : (E.filter fun f => Fin.castAdd N e.1 = Fin.castAdd N f.1 ∨
        Fin.castAdd N e.1 = Fin.natAdd N f.2) = E.filter fun f => f.1 = e.1 := by
      apply Finset.filter_congr
      intro f _
      constructor
      · rintro (h | h)
        · exact (Fin.castAdd_injective N N h).symm
        · exact absurd h (apart _ _)
      · intro h
        exact Or.inl (by rw [h])
    rcases hdeg (Fin.castAdd N e.1) with h | h
    · exfalso
      have : e ∈ E.filter fun f => f.1 = e.1 := Finset.mem_filter.mpr ⟨he, rfl⟩
      rw [← hset] at this
      rw [Finset.card_eq_zero] at h
      rw [h] at this
      exact Finset.notMem_empty _ this
    · rwa [hset] at h
  have degL : ∀ e ∈ E, 44 < (E.filter fun f => f.2 = e.2).card := by
    intro e he
    have hset : (E.filter fun f => Fin.natAdd N e.2 = Fin.castAdd N f.1 ∨
        Fin.natAdd N e.2 = Fin.natAdd N f.2) = E.filter fun f => f.2 = e.2 := by
      apply Finset.filter_congr
      intro f _
      constructor
      · rintro (h | h)
        · exact absurd h.symm (apart _ _)
        · exact (natInj _ _ h).symm
      · intro h
        exact Or.inr (by rw [h])
    rcases hdeg (Fin.natAdd N e.2) with h | h
    · exfalso
      have : e ∈ E.filter fun f => f.2 = e.2 := Finset.mem_filter.mpr ⟨he, rfl⟩
      rw [← hset] at this
      rw [Finset.card_eq_zero] at h
      rw [h] at this
      exact Finset.notMem_empty _ this
    · rwa [hset] at h
  obtain ⟨cP, cL⟩ := count N E c4 (fun e he => ⟨degP e he, degL e he⟩) hE
  -- essential active wires
  let A : Finset (Fin (N+N)) :=
    (E.image Prod.fst).image (Fin.castAdd N) ∪ (E.image Prod.snd).image (Fin.natAdd N)
  have hdisj : Disjoint ((E.image Prod.fst).image (Fin.castAdd N))
      ((E.image Prod.snd).image (Fin.natAdd N)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hb
    exact apart p l hl.symm
  have hA : A.card = (E.image Prod.fst).card + (E.image Prod.snd).card := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (Fin.castAdd_injective N N),
      Finset.card_image_of_injective _ (fun a b h => natInj a b h)]
  have ess : ∀ i ∈ A, ∃ x y : Fin (N+N) → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun (N+N) C x ≠ circuitFun (N+N) C y := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      refine ⟨fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2),
        fun i => decide (i = Fin.natAdd N e.2), ?_, ?_⟩
      · intro j hj
        simp only [hj, false_or]
      · rw [((memE e).mp he).2, offLine]
        decide
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
      refine ⟨fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2),
        fun i => decide (i = Fin.castAdd N e.1), ?_, ?_⟩
      · intro j hj
        simp only [hj, or_false]
      · rw [((memE e).mp he).2, offPoint]
        decide
  have hs := support (N+N) C A (fun g hg => (ao.2.2 g hg).le) ess
  omega
