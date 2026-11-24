import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1614 : (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N) → ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (@Finset.filter (Fin N × Fin N) (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false ∧ ∃ jt : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jt) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jt) false = true ∧ ∃ ut : Fin N, ¬ I e2.1 ut ∧ ((∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa jt) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true) ∨ (∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb jt) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))) (Classical.decPred _) Finset.univ).card ≤ 192 * (Ckt.size + (Jn + Jn)) + 8 * N := by
  classical
  intro hcount N Jn I _ Ckt fa fb fr hrect hmono hdegree _
  let fg : Fin (Jn + Jn) → ℕ := Fin.addCases fa fb
  let Sound : ℕ → Fin N → Prop := fun f u =>
    ∀ z : Fin (N + N) → Bool,
      (∀ p : Fin N, I p u → z (Fin.castAdd N p) = false) →
      (Ckt.wires (List.ofFn z)).getD f false = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true
  let Wl : Fin (Jn + Jn) → Finset (Fin N) :=
    fun j => Finset.univ.filter (Sound (fg j))
  have hdeg : ∀ j : Fin (Jn + Jn),
      (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg j) 0 ≤ 2 := by
    intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [fg, Fin.addCases_left] using (hdegree k).1
    · simpa only [fg, Fin.addCases_right] using (hdegree k).2
  have hsound : ∀ (j : Fin (Jn + Jn)) (z : Fin (N + N) → Bool),
      (∃ u ∈ Wl j, ∀ p : Fin N, I p u → z (Fin.castAdd N p) = false) →
      (Ckt.wires (List.ofFn z)).getD (fg j) false = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true := by
    intro j z hz hf
    obtain ⟨u, hu, hzero⟩ := hz
    have hs : Sound (fg j) u := (Finset.mem_filter.mp hu).2
    exact hs z hzero hf
  have hbound := hcount N (Jn + Jn) I Ckt fg Wl hrect hmono hdeg hsound
  apply (Finset.card_le_card ?_).trans hbound
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨hI, _, ⟨j, hja, hjb⟩, hall⟩ := he
  obtain ⟨_, _, k, hka, hkb, u, hnot, hs⟩ := hall j hja hjb
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, hI, ?_⟩
  rcases hs with hsa | hsb
  · refine ⟨Fin.castAdd Jn k, ⟨u, ?_, hnot⟩, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ u, ?_⟩
      simpa only [fg, Fin.addCases_left, Sound] using hsa
    · simpa only [fg, Fin.addCases_left] using hka
  · refine ⟨Fin.natAdd Jn k, ⟨u, ?_, hnot⟩, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ u, ?_⟩
      simpa only [fg, Fin.addCases_right, Sound] using hsb
    · simpa only [fg, Fin.addCases_right] using hkb
