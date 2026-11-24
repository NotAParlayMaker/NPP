import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3077_801
  (packed : ∀ (k : Fin 9) (gs : List (Fin 3 × Fin 26 × Fin 26)), gs.length ≤ 13 →
    (∀ i < 9, ∃ g ∈ gs, g.2.1.val = i ∨ g.2.2.val = i) →
    let pack : (Fin 512 → Bool) → BitVec 512 := fun (f : Fin 512 → Bool) =>
      (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
    let bit : ℕ → ℕ → Bool := Nat.testBit
    let inp := fun (i : Fin 9) => pack (fun m => bit m.val i.val)
    let first := inp 0 ||| inp 4
    let target := pack (fun m => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => bit m.val (Fin.ofNat 9 (e / 10)).val && bit m.val (Fin.ofNat 9 (e % 10)).val))
    let rd := fun (s : List (BitVec 512)) (w : Fin 26) =>
      if w.val = 25 then BitVec.allOnes 512 else s.getD w.val 0
    target ∉ gs.foldl (fun (s : List (BitVec 512)) (g : Fin 3 × Fin 26 × Fin 26) =>
      s ++ [if g.1.val = 0 then rd s g.2.1 &&& rd s g.2.2 else
        if g.1.val = 1 then rd s g.2.1 ||| rd s g.2.2 else ~~~(rd s g.2.1)]) (List.ofFn inp ++ [first, first ||| inp k]))
  (projection : ∀ (gs : List (Fin 3 × Fin 26 × Fin 26)) (s : List (BitVec 512)) (n : Fin 512),
    let rd := fun (s : List (BitVec 512)) (w : Fin 26) =>
      if w.val = 25 then BitVec.allOnes 512 else s.getD w.val 0
    let rb := fun (s : List Bool) (w : Fin 26) =>
      if w.val = 25 then true else s.getD w.val false
    (gs.foldl (fun (s : List (BitVec 512)) (g : Fin 3 × Fin 26 × Fin 26) =>
      s ++ [if g.1.val = 0 then rd s g.2.1 &&& rd s g.2.2 else
        if g.1.val = 1 then rd s g.2.1 ||| rd s g.2.2 else ~~~(rd s g.2.1)]) s).map (fun t => t.getLsbD n.val) =
      gs.foldl (fun (s : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
      s ++ [if g.1.val = 0 then rb s g.2.1 && rb s g.2.2 else
        if g.1.val = 1 then rb s g.2.1 || rb s g.2.2 else !(rb s g.2.1)]) (s.map fun t => t.getLsbD n.val)) :
  ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b out gs hlen hab ha hb cover
  let pack : (Fin 512 → Bool) → BitVec 512 := fun f =>
    (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
  have pack_bit (f : Fin 512 → Bool) (n : Fin 512) : (pack f).getLsbD n.val = f n := by
    simp only [pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, n.isLt, dite_true, Option.getD_some]
  let bits (n : Fin 512) (i : Fin 9) := n.val.testBit i.val
  let inp (i : Fin 9) := pack (fun n => bits n i)
  let first := inp 0 ||| inp 4
  let graph (m : Fin 512) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => m.val.testBit (Fin.ofNat 9 (e / 10)).val && m.val.testBit (Fin.ofNat 9 (e % 10)).val)
  let target := pack graph
  let other := if a.val = 9 then b else a
  let k : Fin 9 := if hk : other.val < 9 then ⟨other.val,hk⟩ else 0
  let seed := List.ofFn inp ++ [first, first ||| inp k]
  let rd := fun (s : List (BitVec 512)) (w : Fin 26) =>
      if w.val = 25 then BitVec.allOnes 512 else s.getD w.val 0
  let rb := fun (s : List Bool) (w : Fin 26) =>
      if w.val = 25 then true else s.getD w.val false
  let sw := fun (s : List (BitVec 512)) (g : Fin 3 × Fin 26 × Fin 26) =>
      s ++ [if g.1.val = 0 then rd s g.2.1 &&& rd s g.2.2 else
        if g.1.val = 1 then rd s g.2.1 ||| rd s g.2.2 else ~~~(rd s g.2.1)]
  let sb := fun (s : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
      s ++ [if g.1.val = 0 then rb s g.2.1 && rb s g.2.2 else
        if g.1.val = 1 then rb s g.2.1 || rb s g.2.2 else !(rb s g.2.1)]
  let res := gs.foldl sw seed
  have excluded : target ∉ res := packed k gs hlen cover
  let base (n : Fin 512) := List.ofFn (bits n) ++ [bits n 0 || bits n 4]
  have readFirst (w : Fin 26) (hw : w.val = 9) (n : Fin 512) :
      rb (base n) w = (bits n 0 || bits n 4) := by
    simp [rb, base, hw, List.getD_eq_getElem?_getD]
  have norm (n : Fin 512) : ((bits n 0 || bits n 4) || rb (base n) other) =
      ((bits n 0 || bits n 4) || bits n k) := by
    have hne : other.val ≠ 25 := by unfold other; split <;> assumption
    by_cases hk : other.val < 9
    · simp only [rb, hne, ite_false, base, k, hk, dite_true, ite_true, List.getD_eq_getElem?_getD,
        List.getElem?_append, List.length_ofFn, List.getElem?_ofFn, Option.getD_some]
    · by_cases h9 : other.val = 9
      · rw [readFirst other h9 n]
        simp only [k, hk, dite_false]
        cases bits n 0 <;> cases bits n 4 <;> decide
      · have hge : 10 ≤ other.val := by omega
        have hnone : (base n)[other.val]? = none := List.getElem?_eq_none (by simp [base]; omega)
        simp only [rb, hne, ite_false, List.getD_eq_getElem?_getD, hnone, Option.getD_none, k, hk, dite_false]
        cases bits n 0 <;> cases bits n 4 <;> decide
  have seed_bit (n : Fin 512) :
      seed.map (fun t => t.getLsbD n.val) = sb (base n) ((1 : Fin 3),a,b) := by
    have mapin : (List.ofFn inp).map (fun t => t.getLsbD n.val) = List.ofFn (bits n) := by
      rw [List.map_ofFn]
      exact congrArg List.ofFn (funext fun i => pack_bit _ n)
    have hb0 (i : Fin 9) : (inp i).getLsbD n.val = bits n i := pack_bit _ _
    have hfirst : first.getLsbD n.val = (bits n 0 || bits n 4) := by
      rw [BitVec.getLsbD_or, hb0, hb0]
    simp only [seed, List.map_append, mapin, List.map_cons, List.map_nil,
      BitVec.getLsbD_or, hfirst, hb0]
    change List.ofFn (bits n) ++ [bits n 0 || bits n 4, (bits n 0 || bits n 4) || bits n k] =
      (List.ofFn (bits n) ++ [bits n 0 || bits n 4]) ++ [rb (base n) a || rb (base n) b]
    rw [List.append_assoc]
    congr 3
    by_cases h9 : a.val = 9
    · rw [readFirst a h9 n]
      simpa only [other, h9, ite_true] using (norm n).symm
    · have hb9 : b.val = 9 := hab.resolve_left h9
      rw [readFirst b hb9 n, Bool.or_comm (rb _ a)]
      simpa only [other, h9, ite_false] using (norm n).symm
  by_contra! same
  have eq : res.getD out.val 0 = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let n : Fin 512 := ⟨m,hm⟩
    have sim := projection gs seed n
    change res.map (fun t => t.getLsbD n.val) = gs.foldl sb (seed.map (fun t => t.getLsbD n.val)) at sim
    rw [seed_bit] at sim
    have atOut := congrArg (fun l : List Bool => l.getD out.val false) sim
    have hread : (res.getD out.val 0).getLsbD n.val = (res.map (fun t => t.getLsbD n.val)).getD out.val false := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases res[out.val]? <;> simp
    change (res.getD out.val 0).getLsbD n.val = (pack graph).getLsbD n.val
    rw [pack_bit, hread, atOut]
    exact Decidable.of_not_not (same m hm)
  have nonzero : target ≠ 0 := by
    intro zero
    have wrong := congrArg (fun t : BitVec 512 => t.getLsbD 3) zero
    have z : (0 : BitVec 512).getLsbD 3 = false := BitVec.getLsbD_zero
    exact (by decide : graph 3 ≠ false) (((pack_bit graph 3).symm.trans wrong).trans z)
  rw [List.getD_eq_getElem?_getD] at eq
  cases found : res[out.val]? with
  | none => simp [found] at eq; exact nonzero eq.symm
  | some word =>
    have isTarget : word = target := by simpa [found] using eq
    exact excluded (isTarget ▸ List.mem_of_getElem? found)
