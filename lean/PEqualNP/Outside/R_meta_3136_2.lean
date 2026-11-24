import Mathlib.Data.List.GetD
import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- Each bit is one of the 512 input rows. The search uses sorted source pairs, a single complement budget, and a fixed AND output. Source 23 is zero and source 24 is one. -/
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3136_2
    (normalize : ∀ gs : List Gate, gs.length = 13 → FanInTwo (⟨gs, 0⟩ : Circuit) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      ∃ ps : List (Fin 3 × Fin 25 × Fin 25), ps.length = 13 ∧
        ps.countP (fun p => decide (p.1.val = 2)) ≤ 1 ∧
        (∀ p ∈ ps, p.1.val < 2 → p.2.1 ≤ p.2.2) ∧
        ∀ u : List Bool, u.length = 10 →
          ps.foldl (fun (w : List (Bool)) (p : Fin 3 × Fin 25 × Fin 25) =>
        let rd := fun (i : Fin 25) => if i.val = 24 then true else w.getD i.val false
        let a := rd p.2.1
        let b := rd p.2.2
        w ++ [if p.1.val = 0 then a && b else if p.1.val = 1 then a || b else !a]) u = (⟨gs, 0⟩ : Circuit).wires u)
    (obstruction : ∀ ps : List (Fin 3 × Fin 25 × Fin 25), ps.length = 13 →
      ps.countP (fun p => decide (p.1.val = 2)) ≤ 1 →
      (∀ p ∈ ps, p.1.val < 2 → p.2.1 ≤ p.2.2) →
      let ws := ps.foldl (fun (w : List (BitVec 512)) (p : Fin 3 × Fin 25 × Fin 25) =>
        let rd := fun (i : Fin 25) => if i.val = 24 then (BitVec.allOnes 512) else w.getD i.val (0 : BitVec 512)
        let a := rd p.2.1
        let b := rd p.2.2
        w ++ [if p.1.val = 0 then a &&& b else if p.1.val = 1 then a ||| b else ~~~a]) (let col := (fun (j : ℕ) => let t : ℕ := 2 ^ (2 ^ j); BitVec.ofNat 512 (((2 ^ 512 - 1) / (t + 1)) * t)); (List.range 9).map col ++ [col 0 ||| col 3])
      ∀ a b : Fin 25, (ws.getD a.val 0 &&& ws.getD b.val 0) ≠ (0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : BitVec 512)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro gs a b len fan neg ha hb
  classical
  obtain ⟨ps, plen, pn, psort, hsim⟩ := normalize gs len fan neg
  let bs := fun (w : List (Bool)) (p : Fin 3 × Fin 25 × Fin 25) =>
        let rd := fun (i : Fin 25) => if i.val = 24 then true else w.getD i.val false
        let a := rd p.2.1
        let b := rd p.2.2
        w ++ [if p.1.val = 0 then a && b else if p.1.val = 1 then a || b else !a]
  let vs := fun (w : List (BitVec 512)) (p : Fin 3 × Fin 25 × Fin 25) =>
        let rd := fun (i : Fin 25) => if i.val = 24 then (BitVec.allOnes 512) else w.getD i.val (0 : BitVec 512)
        let a := rd p.2.1
        let b := rd p.2.2
        w ++ [if p.1.val = 0 then a &&& b else if p.1.val = 1 then a ||| b else ~~~a]
  let cols : List (BitVec 512) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 512), (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 512), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 512), (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 512), (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 512), (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : BitVec 512), (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 : BitVec 512), (0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000 : BitVec 512), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 : BitVec 512), (0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa : BitVec 512)]
  let target : BitVec 512 := (0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : BitVec 512)
  let aa : Fin 25 := ⟨a, by omega⟩
  let bb : Fin 25 := ⟨b, by omega⟩
  have hbad := obstruction ps plen pn psort aa bb
  apply Classical.byContradiction
  intro hno
  push_neg at hno
  apply hbad
  change ((ps.foldl vs cols).getD a 0 &&& (ps.foldl vs cols).getD b 0) = target
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let bit := fun (v : BitVec 512) => v.getLsbD i
  have get (w : List (BitVec 512)) (j : ℕ) :
      bit (w.getD j 0) = (w.map bit).getD j false := by
    have bz : bit 0 = false := BitVec.getLsbD_zero
    rw [← bz]
    exact (List.getD_map w 0 (n := j) bit).symm
  have push (w : List (BitVec 512)) (p : Fin 3 × Fin 25 × Fin 25) :
      (vs w p).map bit = bs (w.map bit) p := by
    dsimp only [vs, bs]
    rw [List.map_append, List.map_cons, List.map_nil]
    congr 2
    have read (j : Fin 25) :
        bit (if j.val = 24 then BitVec.allOnes 512 else w.getD j.val 0) =
        (if j.val = 24 then true else (w.map bit).getD j.val false) := by
      by_cases h : j.val = 24
      · simp only [h, ite_true, bit, BitVec.getLsbD_allOnes, hi, decide_true]
      · simpa [h] using get w j.val
    by_cases h : p.1.val = 0
    · simp only [h, ite_true]
      change (_ &&& _ : BitVec 512).getLsbD i = _
      rw [BitVec.getLsbD_and]
      exact congrArg₂ (· && ·) (read _) (read _)
    · by_cases h' : p.1.val = 1
      · simp only [h, ite_false, h', ite_true]
        change (_ ||| _ : BitVec 512).getLsbD i = _
        rw [BitVec.getLsbD_or]
        exact congrArg₂ (· || ·) (read _) (read _)
      · simp only [h, ite_false, h']
        change (~~~_ : BitVec 512).getLsbD i = _
        rw [BitVec.getLsbD_not]
        simp only [hi, decide_true, Bool.true_and]
        exact congrArg Bool.not (read _)
  have sim (qs : List (Fin 3 × Fin 25 × Fin 25)) (u : List (BitVec 512)) :
      (qs.foldl vs u).map bit = qs.foldl bs (u.map bit) := by
    induction qs generalizing u with
    | nil => rfl
    | cons p qs ih => simpa only [List.foldl_cons, ih, push]
  let x (j : Fin 9) : Bool := i.testBit j.val
  let inputs := List.ofFn x ++ [x 0 || x 3]
  have init : cols.map bit = inputs := by
    exact (show ∀ r : Fin 512, cols.map (fun w => w.getLsbD r.val) =
      List.ofFn (fun j : Fin 9 => r.val.testBit j.val) ++ [r.val.testBit 0 || r.val.testBit 3] from by
      decide +kernel) ⟨i, hi⟩
  have proj : (ps.foldl vs cols).map bit = (⟨gs,0⟩ : Circuit).wires inputs := by
    rw [sim, init]
    exact hsim inputs (by simp [inputs])
  have tgt : target.getLsbD i = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    exact (show ∀ r : Fin 512, target.getLsbD r.val = (r.val.testBit 0 && r.val.testBit 1 || r.val.testBit 1 && r.val.testBit 2 || r.val.testBit 2 && r.val.testBit 3 || r.val.testBit 3 && r.val.testBit 4 || r.val.testBit 4 && r.val.testBit 0 || r.val.testBit 0 && r.val.testBit 5 || r.val.testBit 1 && r.val.testBit 6 || r.val.testBit 2 && r.val.testBit 7 || r.val.testBit 3 && r.val.testBit 8 || r.val.testBit 5 && r.val.testBit 7 || r.val.testBit 6 && r.val.testBit 8 || r.val.testBit 8 && r.val.testBit 5) from by decide +kernel) ⟨i, hi⟩
  rw [BitVec.getLsbD_and, tgt]
  change (bit ((ps.foldl vs cols).getD a 0) && bit ((ps.foldl vs cols).getD b 0)) = _
  rw [get, get, proj]
  exact Classical.not_not.mp (hno x)
