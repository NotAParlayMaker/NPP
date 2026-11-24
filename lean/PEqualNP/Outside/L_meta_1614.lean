import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1614 : (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N) → ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (@Finset.filter (Fin N × Fin N) (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false ∧ ∃ jt : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jt) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jt) false = true ∧ ∃ ut : Fin N, ¬ I e2.1 ut ∧ ((∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa jt) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true) ∨ (∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb jt) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))) (Classical.decPred _) Finset.univ).card ≤ 192 * (Ckt.size + (Jn + Jn)) + 8 * N := by
  intro H N Jn I instI Ckt fa fb fr h4 hmono hdeg hpair
  obtain ⟨fg, hfgl, hfgr⟩ : ∃ fg : Fin (Jn + Jn) → ℕ,
      (∀ j : Fin Jn, fg (Fin.castAdd Jn j) = fa j) ∧ (∀ j : Fin Jn, fg (Fin.natAdd Jn j) = fb j) :=
    ⟨Fin.append fa fb, fun j => Fin.append_left fa fb j, fun j => Fin.append_right fa fb j⟩
  obtain ⟨Wl, hWl⟩ : ∃ Wl : Fin (Jn + Jn) → Finset (Fin N), ∀ (j : Fin (Jn + Jn)) (u : Fin N),
      u ∈ Wl j ↔ (∀ zz : Fin (N + N) → Bool, (∀ pz : Fin N, I pz u → zz (Fin.castAdd N pz) = false) →
        (Ckt.wires (List.ofFn zz)).getD (fg j) false = true →
        ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) := by
    classical
    exact ⟨fun j => Finset.univ.filter (fun u => ∀ zz : Fin (N + N) → Bool,
        (∀ pz : Fin N, I pz u → zz (Fin.castAdd N pz) = false) →
        (Ckt.wires (List.ofFn zz)).getD (fg j) false = true →
        ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true),
      fun j u => ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩⟩
  have hd : ∀ jd : Fin (Jn + Jn),
      (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2 := by
    intro jd
    induction jd using Fin.addCases with
    | left j => rw [hfgl j]; exact (hdeg j).1
    | right j => rw [hfgr j]; exact (hdeg j).2
  have key := @H N (Jn + Jn) I instI Ckt fg Wl h4 hmono hd
    (fun jb zz hex hw => by
      obtain ⟨uz, huz, hz⟩ := hex
      exact (hWl jb uz).mp huz zz hz hw)
  refine le_trans (Finset.card_le_card ?_) key
  intro e he
  obtain ⟨-, hI, -, ⟨jc, hA, hB⟩, hall⟩ := (@Finset.mem_filter _ _ (Classical.decPred _) _ _).mp he
  obtain ⟨-, -, jt, hAt, hBt, ut, hut, hs⟩ := hall jc hA hB
  rcases hs with hs | hs
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, Fin.castAdd Jn jt, ⟨ut, (hWl _ ut).mpr ?_, hut⟩, ?_⟩
    · rw [hfgl jt]; exact hs
    · rw [hfgl jt]; exact hAt
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, Fin.natAdd Jn jt, ⟨ut, (hWl _ ut).mpr ?_, hut⟩, ?_⟩
    · rw [hfgr jt]; exact hs
    · rw [hfgr jt]; exact hBt
