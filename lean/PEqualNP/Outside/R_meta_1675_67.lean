import Mathlib
import PEqualNP.Defs
theorem PEqualNP.Outside.R_meta_1675_67
  (normalize : let G : BitVec 512 := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8; let B : List (BitVec 512) := (List.range 9).map fun i => BitVec.ofNat 512 (((2^512-1)/(2^(2^i)+1)) * 2^(2^i));
    let w := B ++ [B.getD 0 0 ||| B.getD 3 0];
    let R := ((List.range 270).filter (Nat.testBit 1185712011494028706952314624697188026918248785336673961850684158045538241742897747)).map fun n =>
      let a := w.getD (n / 10 % 10) 0; let b := w.getD (n % 10) 0;
      if n<10 then ~~~b else if n<200 then a &&& b else a ||| b;
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 3)) →
      (∀ i : Fin 512, C.eval (B.map (fun a => a.getLsbD i.val)) = (G : BitVec 512).getLsbD i.val) → ∃ v ∈ R, ∃ p : List (Bool × BitVec 512), p.length=13 ∧ p.countP Prod.fst ≤ 1 ∧
      (∀ i : Fin p.length, let A := w ++ v :: (p.take i.val).map Prod.snd; let s := p.get i;
        if s.1 then ∃ a ∈ A, s.2 = ~~~a else ∃ a ∈ A, ∃ b ∈ A, s.2=a&&&b ∨ s.2=a|||b) ∧
      G ∈ p.map Prod.snd)
  (exclude : let G : BitVec 512 := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8; let B : List (BitVec 512) := (List.range 9).map fun i => BitVec.ofNat 512 (((2^512-1)/(2^(2^i)+1)) * 2^(2^i));
    let w := B ++ [B.getD 0 0 ||| B.getD 3 0];
    let R := ((List.range 270).filter (Nat.testBit 1185712011494028706952314624697188026918248785336673961850684158045538241742897747)).map fun n =>
      let a := w.getD (n / 10 % 10) 0; let b := w.getD (n % 10) 0;
      if n<10 then ~~~b else if n<200 then a &&& b else a ||| b;
    ¬ (∃ v ∈ R, ∃ p : List (Bool × BitVec 512), p.length=13 ∧ p.countP Prod.fst ≤ 1 ∧
      (∀ i : Fin p.length, let A := w ++ v :: (p.take i.val).map Prod.snd; let s := p.get i;
        if s.1 then ∃ a ∈ A, s.2 = ~~~a else ∃ a ∈ A, ∃ b ∈ A, s.2=a&&&b ∨ s.2=a|||b) ∧
      G ∈ p.map Prod.snd)) : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  dsimp only at normalize exclude
  intro C fan first correct
  by_contra! cap
  apply exclude (normalize C fan (by omega) first ?_)
  intro i
  let B : List (BitVec 512) := (List.range 9).map fun j => BitVec.ofNat 512 (((2^512-1)/(2^(2^j)+1))*2^(2^j))
  let x : Fin 9 → Bool := fun j => (B.getD j.val 0).getLsbD i.val
  have values : List.ofFn x = B.map (fun a => a.getLsbD i.val) := by
    change (List.ofFn fun j : Fin 9 => (B.getD j.val 0).getLsbD i.val) = _
    have base : List.ofFn (fun j : Fin 9 => B.getD j.val 0) = B := rfl
    conv_rhs => rw [←base,List.map_ofFn]
    rfl
  change C.eval (B.map _) = _
  rw [←values]
  apply (congrFun correct x).trans
  revert i
  decide +kernel
