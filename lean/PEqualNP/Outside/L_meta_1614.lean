import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_1614 : (∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : Fin Jn → ℕ) (Wl : Fin Jn → Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fg jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (∃ uz ∈ Wl jb, ∀ pz : Fin N, I pz uz → zz (Fin.castAdd N pz) = false) → (Ckt.wires (List.ofFn zz)).getD (fg jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ ∃ jc : Fin Jn, (∃ uc ∈ Wl jc, ¬ I e2.1 uc) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fg jc) false = true)).card ≤ 192 * (Ckt.size + Jn) + 8 * N) → ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (@Finset.filter (Fin N × Fin N) (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false ∧ ∃ jt : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jt) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jt) false = true ∧ ∃ ut : Fin N, ¬ I e2.1 ut ∧ ((∀ za : Fin (N + N) → Bool, (∀ pa : Fin N, I pa ut → za (Fin.castAdd N pa) = false) → (Ckt.wires (List.ofFn za)).getD (fa jt) false = true → ∃ (qa ma : Fin N), I qa ma ∧ za (Fin.castAdd N qa) = true ∧ za (Fin.natAdd N ma) = true) ∨ (∀ zb : Fin (N + N) → Bool, (∀ pb : Fin N, I pb ut → zb (Fin.castAdd N pb) = false) → (Ckt.wires (List.ofFn zb)).getD (fb jt) false = true → ∃ (qb mb : Fin N), I qb mb ∧ zb (Fin.castAdd N qb) = true ∧ zb (Fin.natAdd N mb) = true))) (Classical.decPred _) Finset.univ).card ≤ 192 * (Ckt.size + (Jn + Jn)) + 8 * N := by

  classical
  intro count N J I _ C a b r free mono degree _sound
  let f : Fin (J+J) → ℕ := Fin.addCases a b
  let pivot (i : Fin (J+J)) (u : Fin N) : Prop := ∀ z : Fin (N+N) → Bool,
    (∀ p : Fin N, I p u → z (Fin.castAdd N p) = false) →
    (C.wires (List.ofFn z)).getD (f i) false = true →
    ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
  let W := fun i => Finset.univ.filter (pivot i)
  have fd (i : Fin (J+J)) : (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD (f i) 0 ≤ 2 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [f,Fin.addCases_left] using (degree j).1
    · simpa only [f,Fin.addCases_right] using (degree j).2
  have hit := count N (J+J) I C f W free mono fd (by
    intro i z ex fire
    obtain ⟨u,mem,miss⟩ := ex
    exact (Finset.mem_filter.mp mem).2 z miss fire)
  refine le_trans (Finset.card_le_card ?_) hit
  intro e he
  obtain ⟨inc,_,⟨j,aj,bj⟩,all⟩ := ((@Finset.mem_filter _ _ (Classical.decPred _) _ _).mp he).2
  obtain ⟨_,_,t,at',bt,u,off,pa|pb⟩ := all j aj bj
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,inc,Fin.castAdd J t,⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,off⟩,?_⟩
    · simpa only [pivot,f,Fin.addCases_left] using pa
    · simpa only [f,Fin.addCases_left] using at'
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,inc,Fin.natAdd J t,⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,off⟩,?_⟩
    · simpa only [pivot,f,Fin.addCases_right] using pb
    · simpa only [f,Fin.addCases_right] using bt
