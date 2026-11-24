import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1614

open PEqualNP.CircuitLowerBounds

private def soundOff {n : ℕ} (I : Fin n → Fin n → Prop) (C : Circuit)
    (w : ℕ) (u : Fin n) : Prop :=
  ∀ x : Fin (n + n) → Bool, (∀ p : Fin n, I p u → x (Fin.castAdd n p) = false) →
    (C.wires (List.ofFn x)).getD w false = true →
    ∃ p l : Fin n, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true

end PEqualNP.Outside.L_meta_1614

open PEqualNP.Outside.L_meta_1614 in
theorem PEqualNP.Outside.L_meta_1614 : (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N) → ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (@Finset.filter (Fin N × Fin N) (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false ∧ ∃ jt : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jt) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jt) false = true ∧ ∃ ut : Fin N, ¬ I e2.1 ut ∧ ((∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa jt) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true) ∨ (∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb jt) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))) (Classical.decPred _) Finset.univ).card ≤ 192 * (Ckt.size + (Jn + Jn)) + 8 * N := by
  intro count N Jn I _ Ckt fa fb fr noRectangle monotone degrees covered
  classical
  let fg : Fin (Jn + Jn) → ℕ := Fin.addCases fa fb
  -- Include every line off which this wire is sound.
  let Wl : Fin (Jn + Jn) → Finset (Fin N) :=
    fun j => Finset.univ.filter (soundOff I Ckt (fg j))
  have hdegree : ∀ j : Fin (Jn + Jn),
      (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg j) 0 ≤ 2 := by
    intro j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · simpa only [fg, Fin.addCases_left] using (degrees a).1
    · simpa only [fg, Fin.addCases_right] using (degrees b).2
  have hsound (j : Fin (Jn + Jn)) (x : Fin (N + N) → Bool)
      (h : ∃ u ∈ Wl j, ∀ p : Fin N, I p u → x (Fin.castAdd N p) = false)
      (hw : (Ckt.wires (List.ofFn x)).getD (fg j) false = true) :
      ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
    obtain ⟨u, hu, hx⟩ := h
    exact (Finset.mem_filter.mp hu).2 x hx hw
  refine le_trans (Finset.card_le_card ?_) (count N (Jn + Jn) I Ckt fg Wl
    noRectangle monotone hdegree hsound)
  intro e he
  obtain ⟨_, hi, _, ⟨j, hja, hjb⟩, hall⟩ := (@Finset.mem_filter _ _ (Classical.decPred _) _ _).mp he
  obtain ⟨_, _, t, hta, htb, u, hmiss, hside⟩ := hall j hja hjb
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_⟩
  rcases hside with hleft | hright
  · refine ⟨Fin.castAdd Jn t, ⟨u, ?_, hmiss⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [soundOff, fg, Fin.addCases_left] using hleft⟩
    · simpa only [fg, Fin.addCases_left] using hta
  · refine ⟨Fin.natAdd Jn t, ⟨u, ?_, hmiss⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [soundOff, fg, Fin.addCases_right] using hright⟩
    · simpa only [fg, Fin.addCases_right] using htb
