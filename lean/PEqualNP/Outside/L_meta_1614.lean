import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1614 : (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N) → ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (@Finset.filter (Fin N × Fin N) (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false ∧ ∃ jt : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jt) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jt) false = true ∧ ∃ ut : Fin N, ¬ I e2.1 ut ∧ ((∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa jt) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true) ∨ (∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb jt) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))) (Classical.decPred _) Finset.univ).card ≤ 192 * (Ckt.size + (Jn + Jn)) + 8 * N := by
  intro hH N Jn I decI Ckt fa fb fr hC4 hM2 hdeg _hsound
  let fg : Fin (Jn + Jn) → ℕ := fun k =>
    if hk : k.val < Jn then fa ⟨k.val, hk⟩ else fb ⟨k.val - Jn, by omega⟩
  let Wl : Fin (Jn + Jn) → Finset (Fin N) := fun k =>
    @Finset.filter (Fin N) (fun u : Fin N =>
      ∀ zz : Fin (N + N) → Bool,
        (∀ pz : Fin N, I pz u → zz (Fin.castAdd N pz) = false) →
        (Ckt.wires (List.ofFn zz)).getD (fg k) false = true →
        ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true)
      (Classical.decPred _) Finset.univ
  have hfg_l : ∀ j : Fin Jn, fg ⟨j.val, by omega⟩ = fa j := by
    intro j
    simp [fg, j.isLt]
  have hfg_r : ∀ j : Fin Jn, fg ⟨Jn + j.val, by omega⟩ = fb j := by
    intro j
    have hnot : ¬ (Jn + j.val < Jn) := by omega
    simp [fg, hnot]
  have hdeg' : ∀ jd : Fin (Jn + Jn),
      (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2 := by
    intro jd
    dsimp only [fg]
    split_ifs with h
    · exact (hdeg ⟨jd.val, h⟩).1
    · exact (hdeg ⟨jd.val - Jn, by omega⟩).2
  have hsound' : ∀ (jb : Fin (Jn + Jn)) (zz : Fin (N + N) → Bool),
      (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) →
      (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true →
      ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true := by
    intro jb zz ⟨uz, huz, hzero⟩ hfire
    have huz' : uz ∈ Finset.univ ∧ ∀ zz' : Fin (N + N) → Bool,
        (∀ pz : Fin N, I pz uz → zz' (Fin.castAdd N pz) = false) →
        (Ckt.wires (List.ofFn zz')).getD (fg jb) false = true →
        ∃ (pa lb : Fin N), I pa lb ∧ zz' (Fin.castAdd N pa) = true ∧ zz' (Fin.natAdd N lb) = true := by
      simpa [Wl] using huz
    exact huz'.2 zz hzero hfire
  have hbound := @hH N (Jn + Jn) I decI Ckt fg Wl hC4 hM2 hdeg' hsound'
  refine le_trans (Finset.card_le_card ?_) hbound
  intro e2 he2
  rw [@Finset.mem_filter] at he2
  rw [@Finset.mem_filter]
  rcases he2 with ⟨_, hI, _hfr, ⟨jc, hfa_jc, hfb_jc⟩, hall⟩
  rcases hall jc hfa_jc hfb_jc with ⟨_, _, jt, hfa_jt, hfb_jt, ut, hnotI, hsab⟩
  refine ⟨Finset.mem_univ _, hI, ?_⟩
  rcases hsab with hsa | hsb
  · refine ⟨⟨jt.val, by omega⟩, ⟨ut, ?_, hnotI⟩, ?_⟩
    · simp only [Wl, @Finset.mem_filter, Finset.mem_univ, true_and]
      intro zz hzero hfire
      rw [hfg_l jt] at hfire
      exact hsa zz hzero hfire
    · rw [hfg_l jt]
      exact hfa_jt
  · refine ⟨⟨Jn + jt.val, by omega⟩, ⟨ut, ?_, hnotI⟩, ?_⟩
    · simp only [Wl, @Finset.mem_filter, Finset.mem_univ, true_and]
      intro zz hzero hfire
      rw [hfg_r jt] at hfire
      exact hsb zz hzero hfire
    · rw [hfg_r jt]
      exact hfb_jt
