import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1614 : (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N) → ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (@Finset.filter (Fin N × Fin N) (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false ∧ ∃ jt : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jt) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jt) false = true ∧ ∃ ut : Fin N, ¬ I e2.1 ut ∧ ((∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa jt) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true) ∨ (∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb jt) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))) (Classical.decPred _) Finset.univ).card ≤ 192 * (Ckt.size + (Jn + Jn)) + 8 * N := by
  intro bound N Jn I instI Ckt fa fb fr hrect hmono hdegrees _hcover
  classical
  let Sound (g : ℕ) (u : Fin N) : Prop :=
    ∀ z : Fin (N + N) → Bool,
      (∀ p : Fin N, I p u → z (Fin.castAdd N p) = false) →
      (Ckt.wires (List.ofFn z)).getD g false = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
  let fg : Fin (Jn + Jn) → ℕ := Fin.addCases fa fb
  let Wl (j : Fin (Jn + Jn)) : Finset (Fin N) :=
    Finset.univ.filter (Sound (fg j))
  have hdeg (j : Fin (Jn + Jn)) :
      (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg j) 0 ≤ 2 := by
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [fg, Fin.addCases_left] using (hdegrees k).1
    · simpa only [fg, Fin.addCases_right] using (hdegrees k).2
  have hsound (j : Fin (Jn + Jn)) (z : Fin (N + N) → Bool)
      (hz : ∃ u ∈ Wl j, ∀ p : Fin N, I p u → z (Fin.castAdd N p) = false)
      (hw : (Ckt.wires (List.ofFn z)).getD (fg j) false = true) :
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    obtain ⟨u, hu, hzero⟩ := hz
    exact (Finset.mem_filter.mp hu).2 z hzero hw
  have hcount := bound N (Jn + Jn) I Ckt fg Wl hrect hmono hdeg hsound
  refine le_trans (Finset.card_le_card ?_) hcount
  intro e he
  have ht := ((@Finset.mem_filter _ _ (Classical.decPred _) _ _).mp he).2
  obtain ⟨k, hka, hkb⟩ := ht.2.2.1
  obtain ⟨j, hfa, hfb, u, hmiss, hs⟩ := (ht.2.2.2 k hka hkb).2.2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.1, ?_⟩
  have hw (j' : Fin (Jn + Jn)) (h : Sound (fg j') u)
      (hf : (Ckt.wires (List.ofFn (fun vq : Fin (N + N) =>
        if vq = Fin.castAdd N e.1 then true else
        if vq = Fin.natAdd N e.2 then true else false))).getD (fg j') false = true) :
      ∃ jc : Fin (Jn + Jn), (∃ uc ∈ Wl jc, ¬ I e.1 uc) ∧
        (Ckt.wires (List.ofFn (fun vq : Fin (N + N) =>
          if vq = Fin.castAdd N e.1 then true else
          if vq = Fin.natAdd N e.2 then true else false))).getD (fg jc) false = true :=
    ⟨j', ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hmiss⟩, hf⟩
  rcases hs with ha | hb
  · exact hw (Fin.castAdd Jn j) (by simpa only [fg, Fin.addCases_left] using ha) (by simpa only [fg, Fin.addCases_left] using hfa)
  · exact hw (Fin.natAdd Jn j) (by simpa only [fg, Fin.addCases_right] using hb) (by simpa only [fg, Fin.addCases_right] using hfb)
