import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Record each distinct binary truth table once and charge shared complements by source.
-- A Petersen automorphism moves the first two source vertices into the first three inputs.
-- Its first binary truth table therefore repeats every eight rows of the full 1024-row table.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_4727_1
    (compress : ∀ (w : ℕ) (raw : List (BitVec w)) (C : Circuit) (t : BitVec w),
    FanInTwo C → (∀ r : Fin w, C.eval (raw.map (fun p => p.getLsbD r)) = t.getLsbD r) →
    ∃ (S : Finset (BitVec w)) (ls : List (BitVec w)),
      S.card ≤ PEqualNP.NotBracket.notCount C ∧ ls.length + PEqualNP.NotBracket.notCount C ≤ C.size ∧
      let live := fun (B : List (BitVec w)) (p : BitVec w) =>
        p ∈ B ∨ ∃ q ∈ B, q ∈ S ∧ p = ~~~q
      let seed := (0 : BitVec w) :: ~~~0 :: raw
      (∀ i : Fin ls.length, let B := seed ++ ls.take i.val
        let p := ls[i.val]
        p ∉ B ∧ ∃ a b, live B a ∧ live B b ∧ a.toNat < b.toNat ∧ p ≠ a ∧ p ≠ b ∧
          (p = a &&& b ∨ p = a ||| b)) ∧ live (seed ++ ls) t)
    (normalize : let V := fun (S : Finset (BitVec 1024)) (ls : List (BitVec 1024)) =>
      let live := fun (B : List (BitVec 1024)) (p : BitVec 1024) =>
        p ∈ B ∨ ∃ q ∈ B, q ∈ S ∧ p = ~~~q
      let seed := (0 : BitVec 1024) :: ~~~0 :: (List.ofFn (fun i : Fin 10 => BitVec.ofNat 1024 (((2^1024-1)/(2^(2^i.val)+1))*2^(2^i.val))))
      (∀ i : Fin ls.length, let B := seed ++ ls.take i.val
        let p := ls[i.val]
        p ∉ B ∧ ∃ a b, live B a ∧ live B b ∧ a.toNat < b.toNat ∧ p ≠ a ∧ p ≠ b ∧
          (p = a &&& b ∨ p = a ||| b)) ∧ live (seed ++ ls) 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
    ∀ (S : Finset (BitVec 1024)) (ls : List (BitVec 1024)), V S ls →
      ∃ (T : Finset (BitVec 1024)) (ps : List (BitVec 1024)), T.card ≤ S.card ∧
        ps.length=ls.length ∧ V T ps ∧ (∀ r : Fin 1024, (ps.headD (0 : BitVec 1024)).getLsbD r = (ps.headD 0).getLsbD (r.val%8)))
    (exclude : ∀ (S : Finset (BitVec 1024)) (ls : List (BitVec 1024)),
    S.card ≤ 4 → ls.length ≤ 18 → ls.length + S.card ≤ 19 → (∀ r : Fin 1024, (ls.headD (0 : BitVec 1024)).getLsbD r = (ls.headD 0).getLsbD (r.val%8)) → ¬ (
      let live := fun (B : List (BitVec 1024)) (p : BitVec 1024) =>
        p ∈ B ∨ ∃ q ∈ B, q ∈ S ∧ p = ~~~q
      let seed := (0 : BitVec 1024) :: ~~~0 :: (List.ofFn (fun i : Fin 10 => BitVec.ofNat 1024 (((2^1024-1)/(2^(2^i.val)+1))*2^(2^i.val))))
      (∀ i : Fin ls.length, let B := seed ++ ls.take i.val
        let p := ls[i.val]
        p ∉ B ∧ ∃ a b, live B a ∧ live B b ∧ a.toNat < b.toNat ∧ p ≠ a ∧ p ≠ b ∧
          (p = a &&& b ∨ p = a ||| b)) ∧ live (seed ++ ls) 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8)) :
  have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (19 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x2 → PEqualNP.NotBracket.notCount x2 ≤ (4 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7 := by
  classical
  dsimp only
  intro C fan small one four correct
  let raw := List.ofFn (fun i : Fin 10 => BitVec.ofNat 1024 (((2^1024-1)/(2^(2^i.val)+1))*2^(2^i.val)))
  let tgt : BitVec 1024 := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
  have columns : ∀ (i : Fin 10) (r : Fin 1024),
      (raw[i.val]'(by simp [raw])).getLsbD r = r.val.testBit i.val := by decide
  have answers : ∀ r : Fin 1024, tgt.getLsbD r =
      ((fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) (fun i => r.val.testBit i.val)) := by decide
  have computes (r : Fin 1024) : C.eval (raw.map (fun p => p.getLsbD r)) = tgt.getLsbD r := by
    have eq : raw.map (fun p => p.getLsbD r) = List.ofFn (fun i : Fin 10 => r.val.testBit i.val) := by
      apply List.ext_getElem
      · simp [raw]
      · intro j hj hk
        have h : j < 10 := by simpa using hk
        simpa only [List.getElem_map,List.getElem_ofFn] using columns ⟨j,h⟩ r
    rw [eq,answers]
    exact correct _
  obtain ⟨S,ls,paid,len,form⟩ := compress 1024 raw C tgt fan computes
  obtain ⟨T,ps,card,lenEq,transformed,periodic⟩ := normalize S ls form
  exact exclude T ps (by omega) (by omega) (by omega) periodic transformed
