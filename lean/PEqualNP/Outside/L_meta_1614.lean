import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1614 : (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N) → ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (@Finset.filter (Fin N × Fin N) (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false ∧ ∃ jt : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jt) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jt) false = true ∧ ∃ ut : Fin N, ¬ I e2.1 ut ∧ ((∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa jt) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true) ∨ (∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb jt) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))) (Classical.decPred _) Finset.univ).card ≤ 192 * (Ckt.size + (Jn + Jn)) + 8 * N := by
  intro H N Jn I _ Ckt fa fb fr hI hMono hdeg hSound
  classical
  set fg : Fin (Jn + Jn) → ℕ := Fin.addCases (motive := fun _ => ℕ) fa fb with hfg
  set Wl : Fin (Jn + Jn) → Finset (Fin N) :=
    Fin.addCases (motive := fun _ => Finset (Fin N))
      (fun j => Finset.univ.filter (fun ut => ∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa j) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true))
      (fun j => Finset.univ.filter (fun ut => ∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb j) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))
      with hWl
  have hcard :=
    H N (Jn + Jn) I Ckt fg Wl hI hMono
      (by
        intro jd
        refine Fin.addCases (fun j => ?_) (fun j => ?_) jd
        · simp only [hfg, Fin.addCases_left]
          exact (hdeg j).1
        · simp only [hfg, Fin.addCases_right]
          exact (hdeg j).2)
      (by
        intro jb
        refine Fin.addCases (fun j => ?_) (fun j => ?_) jb
        · intro zz hz hw
          simp only [hWl, Fin.addCases_left, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          obtain ⟨uz, huz, hf⟩ := hz
          simp only [hfg, Fin.addCases_left] at hw
          exact huz zz hf hw
        · intro zz hz hw
          simp only [hWl, Fin.addCases_right, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          obtain ⟨uz, huz, hf⟩ := hz
          simp only [hfg, Fin.addCases_right] at hw
          exact huz zz hf hw)
  refine le_trans (Finset.card_le_card ?_) hcard
  intro e2 he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  obtain ⟨hiI, _hfr, hex, hall⟩ := he
  obtain ⟨jc, hca, hcb⟩ := hex
  obtain ⟨_, _, jt, hja, hjb, ut, hut, hdisj⟩ := hall jc hca hcb
  refine ⟨hiI, ?_⟩
  rcases hdisj with hs | hs
  · refine ⟨Fin.castAdd Jn jt, ⟨ut, ?_, hut⟩, ?_⟩
    · simp only [hWl, Fin.addCases_left, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs
    · simp only [hfg, Fin.addCases_left]
      exact hja
  · refine ⟨Fin.natAdd Jn jt, ⟨ut, ?_, hut⟩, ?_⟩
    · simp only [hWl, Fin.addCases_right, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs
    · simp only [hfg, Fin.addCases_right]
      exact hjb
