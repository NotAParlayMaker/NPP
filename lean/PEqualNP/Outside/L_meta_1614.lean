import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1614 : (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N) → ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (@Finset.filter (Fin N × Fin N) (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false ∧ ∃ jt : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jt) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jt) false = true ∧ ∃ ut : Fin N, ¬ I e2.1 ut ∧ ((∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa jt) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true) ∨ (∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb jt) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))) (Classical.decPred _) Finset.univ).card ≤ 192 * (Ckt.size + (Jn + Jn)) + 8 * N := by
  intro hpiv N Jn I _ Ckt fa fb fr hc4 hmon hdeg _
  classical
  let fg : Fin (Jn + Jn) → ℕ := fun k =>
    if hk : k.val < Jn then fa ⟨k.val, hk⟩ else fb ⟨k.val - Jn, by omega⟩
  let Wl : Fin (Jn + Jn) → Finset (Fin N) := fun k =>
    Finset.univ.filter fun u : Fin N =>
      ∀ zz : Fin (N + N) → Bool,
        (∀ pz : Fin N, I pz u → zz (Fin.castAdd N pz) = false) →
        (Ckt.wires (List.ofFn zz)).getD (fg k) false = true →
        ∃ pa lb : Fin N, I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true
  have hdeg' : ∀ jd : Fin (Jn + Jn),
      (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2 := by
    intro jd
    dsimp [fg]
    split_ifs with hlt
    · exact (hdeg ⟨jd.val, hlt⟩).1
    · exact (hdeg ⟨jd.val - Jn, by omega⟩).2
  have hsound' : ∀ (jb : Fin (Jn + Jn)) (zz : Fin (N + N) → Bool),
      (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) →
      (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true →
      ∃ pa lb : Fin N, I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true := by
    intro jb zz ⟨uz, huz, hzero⟩ htrue
    have hmem := (Finset.mem_filter.mp huz).2
    exact hmem zz hzero htrue
  have hbound := hpiv N (Jn + Jn) I Ckt fg Wl hc4 hmon hdeg' hsound'
  refine le_trans (Finset.card_le_card ?_) hbound
  intro e2 he2
  have he2' := (@Finset.mem_filter _ _ (Classical.decPred _) _ _).mp he2
  rw [Finset.mem_filter]
  refine ⟨he2'.1, he2'.2.1, ?_⟩
  obtain ⟨_, _, ⟨jc, hfa, hfb⟩, hforall⟩ := he2'.2
  obtain ⟨_, _, jt, hfajt, hfbjt, ut, hnotI, hsound⟩ := hforall jc hfa hfb
  rcases hsound with hsound_a | hsound_b
  · let k : Fin (Jn + Jn) := ⟨jt.val, by omega⟩
    have hfgk : fg k = fa jt := by
      dsimp [fg, k]
      split_ifs with h
      · rfl
      · exact absurd jt.isLt h
    refine ⟨k, ⟨ut, ?_, hnotI⟩, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ ut, ?_⟩
      rw [hfgk]
      exact hsound_a
    · rw [hfgk]
      exact hfajt
  · let k : Fin (Jn + Jn) := ⟨Jn + jt.val, by omega⟩
    have hfgk : fg k = fb jt := by
      dsimp [fg, k]
      split_ifs with h
      · omega
      · congr 1
        ext
        simp
    refine ⟨k, ⟨ut, ?_, hnotI⟩, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ ut, ?_⟩
      rw [hfgk]
      exact hsound_b
    · rw [hfgk]
      exact hfbjt
