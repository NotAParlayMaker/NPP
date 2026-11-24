import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Setting any degree-two vertex to false produces the graph studied in L-meta-2036.
-- Three readers would reduce the restricted circuit to twelve gates.
-- Without a direct OR reader, a constant also propagates past the direct readers.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3436_714
    (pin : ∀ (D : Circuit) (i : Fin 9) (w : Fin 9 → Option (Fin 8)),
      FanInTwo D → w i = none →
      (∃ x y : Fin 9 → Bool, (∀ j, j ≠ i → x j = y j) ∧ circuitFun 9 D x ≠ circuitFun 9 D y) →
      (let f := fun x : Fin 8 → Bool => circuitFun 9 D (fun j => (w j).elim false x)
       (∃ x y, f x ≠ f y) →
       ∃ E : Circuit, FanInTwo E ∧ E.size + (D.gates.countP (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains i.val) +
        (if D.gates.any (fun g => g.op.eval [true,false] && g.inputs.contains i.val) then 0 else 1)) ≤ D.size
         ∧ ∀ x, circuitFun 8 E x = f x))
    (small : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12)
    (sparse : ∀ D : Circuit, FanInTwo D → D.size ≤ 15 →
      (∃ a b : Fin 11, (([691324052062,42949682180] : List ℕ).getD
        ((11*a.val+b.val)/40) 0).testBit ((11*a.val+b.val)%40) = true ∧
        D.gates.take 2 = [⟨GateOp.not,[0]⟩,⟨GateOp.or,[a.val,b.val]⟩]) →
      (∀ v ∈ ([4,6,7] : List ℕ), D.gates.countP (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains v) +
        (if D.gates.any (fun g => g.op.eval [true,false] && g.inputs.contains v) then 0 else 1) ≤ 2) →
      ∃ k : BitVec 9, D.eval (List.ofFn (fun i : Fin 9 => k.getLsbD i.val)) ≠
        ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun t => k.getLsbD (t/9) && k.getLsbD (t%9))) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (11 : ℕ) * ↑x1 + ↑x2 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (31 : ℕ), (37 : ℕ), (39 : ℕ), (42 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)] →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  classical
  intro a b C allowed fan size
  let D : Circuit := ⟨⟨GateOp.not,[0]⟩ :: ⟨GateOp.or,[a.val,b.val]⟩ :: C.gates,C.output⟩
  let es : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let G := fun x : Fin 9 → Bool => es.any (fun e => x e.1 && x e.2)
  let H := fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  have dsize : D.size ≤ 15 := by change C.gates.length + 1 + 1 ≤ 15; exact Nat.add_le_add_right size 2
  have dfan : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inr rfl),by decide⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl),le_rfl⟩
    exact fan _ hg
  have evaluate (x : Fin 9 → Bool) :
      circuitFun 9 D x = (let u := List.ofFn x ++ [!x 0]
        C.eval (u ++ [u.getD a.val false || u.getD b.val false])) := by
    have first : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
    let u := List.ofFn x ++ [!((List.ofFn x).getD 0 false)]
    change C.eval (u ++ [u.getD a.val false || (u.getD b.val false || false)]) = _
    simp only [u,first,Bool.or_false]
  by_contra! allRows
  have computes (x : Fin 9 → Bool) : circuitFun 9 D x = G x := by
    let z := (BitVec.ofBoolListLE (List.ofFn x)).cast List.length_ofFn
    have same : (fun i : Fin 9 => z.getLsbD i.val) = x := by
      funext i
      simp only [z,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [i.isLt]
    have h := Classical.not_not.mp (allRows z)
    change (let y := fun i : Fin 9 => z.getLsbD i.val
            let u := List.ofFn y ++ [!y 0]
            C.eval (u ++ [u.getD a.val false || u.getD b.val false]) = G y) at h
    dsimp only at h
    rw [← evaluate] at h
    rwa [same] at h
  let v : Fin 3 → Fin 9 := ![4,6,7]
  let neighbor : Fin 3 → Fin 9 := ![0,1,2]
  let wire : Fin 3 → Fin 9 → Option (Fin 8) :=
    ![![some 0,some 1,some 2,some 3,none,some 4,some 5,some 6,some 7],
       ![some 1,some 0,some 4,some 7,some 5,some 2,none,some 6,some 3],
       ![some 1,some 2,some 3,some 7,some 5,some 0,some 6,none,some 4]]
  have ident (t : Fin 3) (x : Fin 8 → Bool) :
      G (fun j => (wire t j).elim false x) = H x := by
    fin_cases t <;> simp [G,es,wire,H,List.any_cons] <;> ac_rfl
  have bounded (t : Fin 3) :
      D.gates.countP (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains (v t).val) +
        (if D.gates.any (fun g => g.op.eval [true,false] && g.inputs.contains (v t).val) then 0 else 1) ≤ 2 := by
    let lo := fun j : Fin 9 => decide (j = neighbor t)
    let hi := fun j : Fin 9 => decide (j = neighbor t ∨ j = v t)
    have only (j : Fin 9) (ne : j ≠ v t) : lo j = hi j := by simp [lo,hi,ne]
    have changeBit : G lo ≠ G hi := by
      fin_cases t <;> decide
    have disabled : wire t (v t) = none := by fin_cases t <;> decide
    have nonconst : ∃ x y : Fin 8 → Bool,
        circuitFun 9 D (fun j => (wire t j).elim false x) ≠
        circuitFun 9 D (fun j => (wire t j).elim false y) := by
      refine ⟨fun _ => false,fun _ => true,?_⟩
      rw [computes,computes,ident,ident]
      decide
    obtain ⟨E,hE,save,output⟩ := pin D (v t) (wire t) dfan disabled
      ⟨lo,hi,only,by simpa only [computes] using changeBit⟩ nonconst
    by_contra! large
    apply small
    refine ⟨E,hE,by omega,?_⟩
    intro x
    exact (output x).trans ((computes _).trans (ident t x))
  have boundAll (n : ℕ) (hn : n ∈ ([4,6,7] : List ℕ)) :
      D.gates.countP (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains n) +
        (if D.gates.any (fun g => g.op.eval [true,false] && g.inputs.contains n) then 0 else 1) ≤ 2 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact bounded 0
    · exact bounded 1
    · exact bounded 2
  have membership : ∀ i j : Fin 11, 11*i.val + j.val ∈
      ([1,2,3,4,6,9,13,14,15,16,17,18,19,20,25,26,28,29,30,31,37,39,42,50,53,73,75] : List ℕ) →
      (([691324052062,42949682180] : List ℕ).getD ((11*i.val+j.val)/40) 0).testBit ((11*i.val+j.val)%40) = true := by decide
  obtain ⟨k,hk⟩ := sparse D dfan dsize ⟨a,b,membership a b allowed,rfl⟩ boundAll
  exact hk (computes (fun i => k.getLsbD i.val))
