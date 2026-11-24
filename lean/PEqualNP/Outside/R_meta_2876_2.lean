import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The 58 boundary assignments occupy consecutive 14-bit fields, with the 21 edges first.
-- Input columns occupy 58-bit fields. Each anchor uses two 6-bit row indices.
theorem PEqualNP.Outside.R_meta_2876_2
    (compile : ∀ (n k : Nat) (inputs : List Nat) (gates : List (Bool × Nat × Nat)), inputs.length=n →
  ∃ C : Circuit, Monotone2 C ∧ C.size=gates.length ∧ ∀ (r : Fin k) (j : Nat),
    (C.wires (List.ofFn (fun v : Fin n => (inputs.getD v.val 0).testBit r.val))).getD j false =
      ((gates.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => w ++ [
    if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]) inputs).getD j 0).testBit r.val)
    (boundary : let row := fun i : Nat => (27100321562855002520517520580012742248824378795708664412127748656491125098734460563633593280333336662142036550621417671358586257697027368867971489186403052057072961283871061193322549110396220698310063367192158989181571413407477755618014925963393 : Nat) >>> (14*i) &&& 16383
  let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List Nat).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
  ∀ x : Fin 14 → Bool, (Minimal P x → ∃ i : Fin 21, x = fun v => (row i.val).testBit v.val) ∧
    (Maximal (fun z => ¬ P z) x → ∃ i : Fin 37, x = fun v => (row (21+i.val)).testBit v.val))
    (search : let inputs := (List.range 14).map (fun v => (27305519102644583149665226792277652155481711537918085168871095508135184176334603431239330874229324051701409612879344006668756009334260402552987786561760844676127080938240233073956043201016893889908026053332369881365537826095879983719911885111303 : Nat) >>> (58*v) &&& (2^58-1))
  ∃ (gs : List (Bool × Nat × Nat)) (a b j : Nat) (d : Bool),
    gs.length ≤ 25 ∧ 14 ≤ a ∧ a < b ∧ b < 14+gs.length ∧ j < (if d then 13 else 3) ∧
    let T := ((if d then 44790134296925272217719866519270602146899383701 else 16107700416) : Nat) >>> (12*j)
    let w := gs.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => w ++ [
    if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]) inputs
    let A := w.getD a 0
    let B := w.getD b 0
    let i := T &&& 63
    let h := (T >>> 6) &&& 63
    (if d then A &&& B else A ||| B) = 2097151 ∧
      A.testBit i ≠ B.testBit i ∧ A.testBit i = B.testBit h ∧ B.testBit i = A.testBit h) : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (25 : ℕ) ∧       (14 : ℕ) ≤ x4 ∧         x4 < x5 ∧           x5 < (14 : ℕ) + x2.size ∧             (x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 ∈ [((129 : ℕ), (130 : ℕ)), ((129 : ℕ), (260 : ℕ)), ((129 : ℕ), (544 : ℕ))] ∨ x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6 ∈ [((127 : ℕ), (244 : ℕ)), ((127 : ℕ), (432 : ℕ)), ((127 : ℕ), (3716 : ℕ)), ((127 : ℕ), (16256 : ℕ)), ((244 : ℕ), (314 : ℕ)), ((244 : ℕ), (432 : ℕ)), ((244 : ℕ), (792 : ℕ)), ((244 : ℕ), (1290 : ℕ)), ((244 : ℕ), (3716 : ℕ)), ((244 : ℕ), (7426 : ℕ)), ((432 : ℕ), (660 : ℕ)), ((432 : ℕ), (1220 : ℕ)), ((432 : ℕ), (1548 : ℕ))]) ∧               have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;               have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;               have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;               have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];               x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false := by
  letI : DecidableEq GateOp := NestedCover.gateOpDecEq
  let row := fun i : Nat => (27100321562855002520517520580012742248824378795708664412127748656491125098734460563633593280333336662142036550621417671358586257697027368867971489186403052057072961283871061193322549110396220698310063367192158989181571413407477755618014925963393 : Nat) >>> (14*i) &&& 16383
  let inputs := (List.range 14).map (fun v => (27305519102644583149665226792277652155481711537918085168871095508135184176334603431239330874229324051701409612879344006668756009334260402552987786561760844676127080938240233073956043201016893889908026053332369881365537826095879983719911885111303 : Nat) >>> (58*v) &&& (2^58-1))
  let entry (d : Bool) (j : Nat) := ((if d then 44790134296925272217719866519270602146899383701 else 16107700416) : Nat) >>> (12*j)
  let lo (d : Bool) (j : Nat) := entry d j &&& 63
  let hi (d : Bool) (j : Nat) := (entry d j >>> 6) &&& 63
  let op (d : Bool) : GateOp := if d then .and else .or
  have tables : ∀ (d : Bool) (j : Fin (if d then 13 else 3)),
      lo d j < 58 ∧ hi d j < 58 ∧
      ((op d = .or ∧ (row (lo d j), row (hi d j)) ∈ ([(129,130),(129,260),(129,544)] : List (Nat × Nat))) ∨
       (op d = .and ∧ (row (lo d j), row (hi d j)) ∈ ([(127,244),(127,432),(127,3716),(127,16256),(244,314),(244,432),(244,792),(244,1290),(244,3716),(244,7426),(432,660),(432,1220),(432,1548)] : List (Nat × Nat)))) := by decide
  have transpose : ∀ (r : Fin 58) (v : Fin 14), (inputs.getD v.val 0).testBit r.val = (row r.val).testBit v.val := by decide
  have ones : ∀ r : Fin 58, (2097151 : Nat).testBit r.val = decide (r.val < 21) := by decide
  have combine (d : Bool) (A B : Nat) (r : Nat) : (op d).eval [A.testBit r,B.testBit r] =
      (if d then A &&& B else A ||| B).testBit r := by
    cases d <;> simp [op, GateOp.eval,Nat.testBit_and,Nat.testBit_or]
  obtain ⟨gs,a,b,j,d,limit,ha,hab,hb,hj,truth,swap,ex,ey⟩ := search
  let w := gs.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => w ++ [
    if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]) inputs
  let i : Fin 58 := ⟨lo d j,(tables d ⟨j,hj⟩).1⟩
  let h : Fin 58 := ⟨hi d j,(tables d ⟨j,hj⟩).2.1⟩
  obtain ⟨C,mono,size,reads⟩ := compile 14 58 inputs gs (by decide)
  let X (r : Fin 58) (v : Fin 14) := (row r.val).testBit v.val
  have ev (r : Fin 58) (g : Nat) : (C.wires (List.ofFn (X r))).getD g false = (w.getD g 0).testBit r.val := by
    have e := reads r g
    have same : (fun v : Fin 14 => (inputs.getD v.val 0).testBit r.val) = X r := funext (transpose r)
    rw [same] at e
    exact e
  have both (r : Fin 58) : (op d).eval [(C.wires (List.ofFn (X r))).getD a false,(C.wires (List.ofFn (X r))).getD b false] = decide (r.val < 21) := by
    rw [ev,ev,combine]
    change (if d then w.getD a 0 &&& w.getD b 0 else w.getD a 0 ||| w.getD b 0).testBit r.val = _
    rw [show (if d then w.getD a 0 &&& w.getD b 0 else w.getD a 0 ||| w.getD b 0) = 2097151 from truth,ones]
  refine ⟨C,op d,a,b,(row i.val,row h.val),mono,by omega,ha,hab,by omega,(tables d ⟨j,hj⟩).2.2,?_,?_,?_,?_,?_⟩
  · change (C.wires (List.ofFn (X i))).getD a false ≠ (C.wires (List.ofFn (X i))).getD b false
    rw [ev,ev]; exact swap
  · change (C.wires (List.ofFn (X i))).getD a false = (C.wires (List.ofFn (X h))).getD b false
    rw [ev,ev]; exact ex
  · change (C.wires (List.ofFn (X i))).getD b false = (C.wires (List.ofFn (X h))).getD a false
    rw [ev,ev]; exact ey
  · intro x minimal
    obtain ⟨r,hx⟩ := (boundary x).1 minimal
    let t : Fin 58 := ⟨r.val,by omega⟩
    change x = X t at hx
    subst x
    right
    exact (both t).trans (decide_eq_true r.isLt)
  · intro x maximal
    obtain ⟨r,hx⟩ := (boundary x).2 maximal
    let t : Fin 58 := ⟨21+r.val,by omega⟩
    change x = X t at hx
    subst x
    right
    exact (both t).trans (decide_eq_false (by dsimp [t]; omega))
