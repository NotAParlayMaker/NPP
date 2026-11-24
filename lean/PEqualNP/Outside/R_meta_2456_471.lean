import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- A certificate chooses the initial complemented input and thirteen gates over 25 wire indices.
-- The final output is wire 23. Index 24 supplies false for an absent or forward input.
set_option maxHeartbeats 1200000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2456_471
    (search : ∃ (p : Fin 11) (P : List (Fin 3 × Fin 25 × Fin 25)), p.val ∈ ([0,2,4,5,10] : List ℕ) ∧ P.length = 13 ∧ ∀ m : Fin 1024, let r : ℕ := m.val; let x := fun i : Fin 10 => r.testBit i.val; (let w := List.ofFn x; (P.foldl (fun (w : List Bool) (g : (Fin 3 × Fin 25 × Fin 25)) => let u := w.getD g.2.1.val false; let v := w.getD g.2.2.val false; w ++ [if g.1.val = 0 then u && v else if g.1.val = 1 then u || v else !u]) (w ++ [!(w.getD p.val false)])).getD 23 false) = ([5,12,10,17,48,96,66,129,384,768,514] : List ℕ).any (fun k => (r &&& k) == k))
    (compile : ∀ (p : Fin 11) (P : List (Fin 3 × Fin 25 × Fin 25)), P.length = 13 → ∃ C : Circuit, FanInTwo C ∧ C.size = 14 ∧ (∃ g : Gate, C.gates.head? = some g ∧ g.op = GateOp.not) ∧ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = (let w := List.ofFn x; (P.foldl (fun (w : List Bool) (g : (Fin 3 × Fin 25 × Fin 25)) => let u := w.getD g.2.1.val false; let v := w.getD g.2.2.val false; w ++ [if g.1.val = 0 then u && v else if g.1.val = 1 then u || v else !u]) (w ++ [!(w.getD p.val false)])).getD 23 false)) : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (14 : ℕ) ∧ (∀ (x2 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x2) = [((0 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ)))].any fun (x3 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x2 x3.1 && x2 x3.2) ∧ ∃ (x2 : PEqualNP.CircuitLowerBounds.Gate), x1.gates.head? = Option.some x2 ∧ x2.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
  obtain ⟨p,P,_,len,sol⟩ := search
  obtain ⟨C,fan,size,head,reads⟩ := compile p P len
  refine ⟨C,fan,by omega,?_,head⟩
  intro x
  let s : BitVec 10 := (BitVec.ofBoolListLE (List.ofFn x)).cast (by simp)
  let m : Fin 1024 := ⟨s.toNat,s.isLt⟩
  have bits (i : Fin 10) : m.val.testBit i.val = x i := by
    change s.getLsbD i.val = x i
    simp only [s,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have same : (fun i : Fin 10 => m.val.testBit i.val) = x := funext bits
  have compares (a b : Fin 10) :
      ((m.val &&& (2^a.val ||| 2^b.val)) == (2^a.val ||| 2^b.val)) = (x a && x b) := by
    let k := 2^a.val ||| 2^b.val
    apply Bool.eq_iff_iff.mpr
    change (m.val &&& k == k) = true ↔ (x a && x b) = true
    rw [beq_iff_eq,Bool.and_eq_true]
    constructor
    · intro h
      have h₁ := congrArg (fun n : ℕ => n.testBit a.val) h
      have h₂ := congrArg (fun n : ℕ => n.testBit b.val) h
      change (m.val &&& k).testBit a.val = k.testBit a.val at h₁
      change (m.val &&& k).testBit b.val = k.testBit b.val at h₂
      simpa [k,Nat.testBit_and,Nat.testBit_two_pow,bits] using And.intro h₁ h₂
    · rintro ⟨ha,hb⟩
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases ha' : a.val = i
      · subst i; simp [k,Nat.testBit_two_pow,bits,ha]
      by_cases hb' : b.val = i
      · subst i; simp [k,Nat.testBit_two_pow,bits,hb]
      · simp [k,ha',hb']
  let edges : List (Fin 10 × Fin 10) := [(0,2),(2,3),(3,1),(0,4),(4,5),(5,6),(6,1),(0,7),(7,8),(8,9),(9,1)]
  let encode (e : Fin 10 × Fin 10) := 2^e.1.val ||| 2^e.2.val
  have nums : edges.map encode = ([5,12,10,17,48,96,66,129,384,768,514] : List ℕ) := by rfl
  have lab : ([5,12,10,17,48,96,66,129,384,768,514] : List ℕ).any (fun k => (m.val &&& k) == k) =
      edges.any (fun e => x e.1 && x e.2) := by
    rw [← nums,List.any_map]
    have point : (fun e : Fin 10 × Fin 10 => (m.val &&& encode e) == encode e) =
        (fun e => x e.1 && x e.2) := funext (fun e => compares e.1 e.2)
    exact congrArg (fun f => edges.any f) point
  have h := sol m
  dsimp only at h
  rw [same] at h
  exact (reads x).trans (h.trans lab)
