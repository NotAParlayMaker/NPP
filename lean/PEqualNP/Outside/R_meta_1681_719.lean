import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_1681_719
    (hRealize :
      ∀ (T : Finset (Fin 26 → Bool)) (W : List (Finset (Fin 26 → Bool))) (o : ℕ),
        let V (j : ℕ) := (List.ofFn fun i : Fin 26 => T.filter (fun x => x i)) ++ W.take j
        (∀ j < W.length, let A := fun i => (V j).getD i ∅
          ∃ a b : ℕ, W.getD j ∅ = A a ∪ A b ∨ W.getD j ∅ = A a ∩ A b) →
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ W.length ∧
          ∀ x ∈ T, circuitFun 26 C x = decide (x ∈ (V W.length).getD o ∅))
    (hSearch :
      let S := singerLines3
      let X (P L : Finset (Fin 13)) (i : Fin 26) : Bool :=
        Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L)) i
      ∃ (T : Finset (Fin 26 → Bool)) (W : List (Finset (Fin 26 → Bool))) (o : ℕ),
        let V (j : ℕ) := (List.ofFn fun i : Fin 26 => T.filter (fun x => x i)) ++ W.take j
        let Z := (V W.length).getD o ∅
        W.length ≤ 63 ∧
        (∀ j < W.length, let A := fun i => (V j).getD i ∅
          ∃ a b : ℕ, W.getD j ∅ = A a ∪ A b ∨ W.getD j ∅ = A a ∩ A b) ∧
        (∀ p l, p ∈ S l → X {p} {l} ∈ T ∧ X {p} {l} ∈ Z) ∧
        ∀ P : Finset (Fin 13), let L := missLines S P
          (∀ p ∉ P, ∃ l ∈ L, p ∈ S l) →
          (∀ l, ¬ P ⊆ S l) →
          (∀ p, ∃ l ∈ L, p ∉ S l) →
          X P L ∈ T ∧ X P L ∉ Z) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  classical
  obtain ⟨T, W, o, hSize, hTrace, hPositive, hNegative⟩ := hSearch
  obtain ⟨C, hMono, hSmall, hValues⟩ := hRealize T W o hTrace
  let S := singerLines3
  have inc (p l : Fin 13) :
      p ∈ S l ↔ (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d) := by
    exact (by decide +kernel : ∀ p l : Fin 13,
      p ∈ singerLines3 l ↔ (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d)) p l
  have memMiss (P : Finset (Fin 13)) (l : Fin 13) :
      l ∈ missLines S P ↔ ∀ p ∈ P, p ∉ S l := by
    change l ∈ Finset.univ.filter (fun k => Disjoint (S k) P) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
    constructor
    · exact fun h p hp hs => h hs hp
    · exact fun h p hs hp => h p hp hs
  have cross (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro h
    have he := congrArg Fin.val h
    change p.val = 13 + l.val at he
    have hp := p.isLt
    omega
  refine ⟨C, hMono, hSmall.trans hSize, ?_, ?_⟩
  · intro p l hp
    obtain ⟨hRow, hOne⟩ := hPositive p l ((inc p l).mpr hp)
    have hX : (fun i : Fin 26 => Fin.addCases (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13))))
          (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))) i) =
        (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) := by
      funext i
      refine Fin.addCases (m := 13) (n := 13) (fun a => ?_) (fun b => ?_) i
      · rw [Fin.addCases_left]
        apply decide_eq_decide.mpr
        simp only [Finset.mem_singleton, cross a l, or_false]
        exact ⟨congrArg (Fin.castAdd 13), Fin.castAdd_inj.mp⟩
      · rw [Fin.addCases_right]
        apply decide_eq_decide.mpr
        have hinj : Fin.natAdd 13 b = Fin.natAdd 13 l ↔ b = l := by simp [Fin.ext_iff]
        simp only [Finset.mem_singleton, Ne.symm (cross p b), false_or, hinj]
    have h := hValues _ hRow
    rw [decide_eq_true hOne] at h
    change circuitFun 26 C (fun i => Fin.addCases (fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13))))
      (fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))) i) = true at h
    rw [hX] at h
    exact h
  · intro P hClosed hGen
    let L := missLines S P
    have hClosed' : ∀ p ∉ P, ∃ l ∈ L, p ∈ S l := by
      intro p hp
      obtain ⟨l, hl, hInc⟩ := hClosed p hp
      exact ⟨l, (memMiss P l).mpr (fun w hw h => hl w hw ((inc w l).mp h)), (inc p l).mpr hInc⟩
    have hPoints : ∀ l, ¬ P ⊆ S l := by
      intro l hsub
      exact hGen.1 ⟨l, fun p hp => (inc p l).mp (hsub hp)⟩
    have hLines : ∀ p, ∃ l ∈ L, p ∉ S l := by
      intro p
      by_contra hn
      apply hGen.2
      refine ⟨p, fun l hl => (inc p l).mp ?_⟩
      by_contra hNot
      exact hn ⟨l, (memMiss P l).mpr (fun w hw h => hl w hw ((inc w l).mp h)), hNot⟩
    obtain ⟨hRow, hZero⟩ := hNegative P hClosed' hPoints hLines
    have h := hValues _ hRow
    rw [decide_eq_false hZero] at h
    have hX :
      (fun i : Fin 26 => Fin.addCases (fun p : Fin 13 => decide (p ∈ P))
        (fun l : Fin 13 => decide (l ∈ L)) i) =
        (fun i : Fin 26 => decide
          ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
            (∃ l : Fin 13, i = Fin.natAdd 13 l ∧
              ∀ p ∈ P, ¬ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l+d))) := by
      funext i
      refine Fin.addCases (m := 13) (n := 13) (fun a => ?_) (fun b => ?_) i
      · rw [Fin.addCases_left]
        apply decide_eq_decide.mpr
        constructor
        · intro ha
          exact Or.inl ⟨a, ha, rfl⟩
        · rintro (⟨p, hp, he⟩ | ⟨l, he, _⟩)
          · exact (Fin.castAdd_inj.mp he) ▸ hp
          · exact (cross _ _ he).elim
      · rw [Fin.addCases_right]
        apply decide_eq_decide.mpr
        constructor
        · intro hb
          refine Or.inr ⟨b, rfl, fun p hp he => ?_⟩
          exact (memMiss P b).mp hb p hp ((inc p b).mpr he)
        · rintro (⟨p, _, he⟩ | ⟨l, he, hl⟩)
          · exact (cross _ _ he.symm).elim
          · have hb : b = l := by
              apply Fin.ext
              have e := congrArg Fin.val he
              change 13 + b.val = 13 + l.val at e
              omega
            subst l
            exact (memMiss P b).mpr (fun p hp hi => hl p hp ((inc p b).mp hi))
    change circuitFun 26 C (fun i => Fin.addCases (fun p : Fin 13 => decide (p ∈ P))
      (fun l : Fin 13 => decide (l ∈ L)) i) = false at h
    rw [hX] at h
    exact h
