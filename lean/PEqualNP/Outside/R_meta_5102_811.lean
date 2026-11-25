import Mathlib.Data.List.GetD

-- Compile a word-by-word construction on the Heawood boundary rows
-- into the program expected by the desk. The finite search uses one first
-- word per orbit under symmetries of the seeded bank and discards words
-- whose errors contain those of a word already available.
theorem PEqualNP.Outside.R_meta_5102_811
    (compile :
    let legal := fun (w : List Nat) (v : Nat) =>
      ∃ a ∈ w, ∃ b ∈ w, v = a &&& b ∨ v = a ||| b
    let step := fun (d : Nat) (w : List Nat) (g : Bool × Nat × Nat) =>
      w ++ [if g.1 = true then w.getD g.2.1 d ||| w.getD g.2.2 d
             else w.getD g.2.1 d &&& w.getD g.2.2 d]
    ∀ (bank xs : List Nat), (∀ i : Fin xs.length, legal (bank ++ xs.take i.val) (xs.get i)) →
      ∃ p : List (Bool × Nat × Nat), p.length = xs.length ∧
        p.foldl (step (bank.headD 0)) bank = bank ++ xs)
    (search :
    let legal := fun (w : List Nat) (v : Nat) =>
      ∃ a ∈ w, ∃ b ∈ w, v = a &&& b ∨ v = a ||| b
    let bank : List Nat := [917681504273, 14878052356, 31886295704066, 257731462272, 42884715528480, 82789891049544, 248671168364547, 198670308868108, 158476001083504, 238332533539200, 176488259259904, 212188564320256, 280375465312256, 271282175737871, 280357743624591]
    let target : Nat := 262143
    ∃ xs : List Nat, xs.length ≤ 22 ∧
      (∃ first ∈ ([1, 16, 32, 128, 272596145284, 927693901845, 32803808125459, 43142443058592, 158482008182900, 158596264232176, 159393682587761, 176745990721152, 194218182053488, 198679179821180, 198685186920460, 198721861977228, 198967232331805, 229789638094960, 238334157590916, 238470001852912, 238590265001344, 271282448367743, 271287314092047, 271299360195727, 275888812327299, 280357747819007, 280358285021583, 280374928082319] : List Nat), xs.head? = some first) ∧
      target ∈ bank ++ xs ∧
      ∀ i : Fin xs.length,
        legal (bank ++ xs.take i.val) (xs.get i) ∧
        ∀ a ∈ bank ++ xs.take i.val, (a ^^^ target) &&& (xs.get i ^^^ target) ≠ (a ^^^ target)) :
    have x1 : List ℕ → List (Bool × ℕ × ℕ) → ℕ → ℕ := fun (x1 : List ℕ) (x2 : List (Bool × ℕ × ℕ)) (x3 : ℕ) =>   have x4 : ℕ := x1.headD (0 : ℕ);   (List.foldl         (fun (x5 : List ℕ) (x6 : Bool × ℕ × ℕ) =>           have x7 : ℕ → ℕ := fun (x7 : ℕ) => x5.getD x7 x4;           x5 ++ [if x6.1 = Bool.true then x7 x6.2.1 ||| x7 x6.2.2 else x7 x6.2.1 &&& x7 x6.2.2])         x1 x2).getD     x3 x4; have x2 : List ℕ := [(917681504273 : ℕ), (14878052356 : ℕ), (31886295704066 : ℕ), (257731462272 : ℕ), (42884715528480 : ℕ), (82789891049544 : ℕ), (248671168364547 : ℕ), (198670308868108 : ℕ), (158476001083504 : ℕ), (238332533539200 : ℕ), (176488259259904 : ℕ), (212188564320256 : ℕ), (280375465312256 : ℕ), (271282175737871 : ℕ), (280357743624591 : ℕ)]; ∃ (x3 : List (Bool × ℕ × ℕ)), x3.length ≤ (22 : ℕ) ∧ ∃ (x4 : ℕ), x1 x2 x3 x4 = (262143 : ℕ) := by
  let step := fun (d : Nat) (w : List Nat) (g : Bool × Nat × Nat) =>
      w ++ [if g.1 = true then w.getD g.2.1 d ||| w.getD g.2.2 d
             else w.getD g.2.1 d &&& w.getD g.2.2 d]
  let bank : List Nat := [917681504273, 14878052356, 31886295704066, 257731462272, 42884715528480, 82789891049544, 248671168364547, 198670308868108, 158476001083504, 238332533539200, 176488259259904, 212188564320256, 280375465312256, 271282175737871, 280357743624591]
  obtain ⟨xs, size, _, output, gates⟩ := search
  obtain ⟨p, cost, tape⟩ := compile bank xs (fun i => (gates i).1)
  have outputInTape : (262143 : Nat) ∈ bank ++ xs := output
  obtain ⟨out, bound, hit⟩ := List.getElem_of_mem outputInTape
  have costBound : p.length ≤ 22 := by
    rw [cost]
    exact size
  refine ⟨p, costBound, out, ?_⟩
  change (p.foldl (step (bank.headD 0)) bank).getD out (bank.headD 0) = 262143
  rw [tape, List.getD_eq_getElem (bank ++ xs) (bank.headD 0) bound]
  exact hit
