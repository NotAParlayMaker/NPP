import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3079_770
    (h3509 : ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → ↑x1 * (10 : ℕ) + ↑x2 ∉ [(12 : ℕ), (21 : ℕ), (23 : ℕ), (32 : ℕ), (16 : ℕ), (61 : ℕ), (27 : ℕ), (72 : ℕ), (38 : ℕ), (83 : ℕ), (57 : ℕ), (75 : ℕ), (68 : ℕ), (86 : ℕ), (58 : ℕ), (85 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x12 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)), x12 x1 || x12 x2]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) → False)
    (h3590 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 < x3 →       ¬(x2 = (0 : Fin (10 : ℕ)) ∧ x3 = (4 : Fin (10 : ℕ))) →         ¬((x2 = (0 : Fin (10 : ℕ)) ∨ x2 = (4 : Fin (10 : ℕ))) ∧ x3 = (9 : Fin (10 : ℕ))) →           (∀ (x8 : Fin (9 : ℕ) → Bool),               have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];               x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) →             (14 : ℕ) ≤ x1.size) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2 ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨ (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b o gs budget hn ha hb _
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let join (x : Fin 9 → Bool) (i j : Nat) :=
    (seed x).getD i false || (seed x).getD j false
  let full (x : Fin 9 → Bool) (i j : Nat) := seed x ++ [join x i j]
  have lens (x) : (seed x).length = 10 := by simp [seed]
  have lenf (x i j) : (full x i j).length = 11 := by simp [full,lens]
  have left (w s : List Bool) (i : Nat) (hi : i < w.length) :
      (w ++ s).getD i false = w.getD i false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
    simp [List.getD_eq_getElem?_getD]
  have bad (w : List Bool) (i : Nat) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]
  let Good (i j : Nat) := ∃ (p q : Fin 10) (t : Nat), p < q ∧ ¬(p = 0 ∧ q = 4) ∧
    ¬((p = 0 ∨ p = 4) ∧ q = 9) ∧ (t < 11 ∨ t = 26) ∧
    ∀ x, (full x p.val q.val).getD t false = join x i j
  have sorted (i j : Nat) (ij : i ≤ j) (_ : i ≠ 9) (nj : j ≠ 9) : Good i j := by
    by_cases big : 10 ≤ j
    · by_cases small : i < 10
      · refine ⟨0,1,i,by decide,by decide,by decide,Or.inl (by omega),?_⟩
        intro x
        simp only [full,join,left (seed x) _ i (by rw [lens]; exact small),
          bad (seed x) j (by rw [lens]; exact big),Bool.or_false]
      · refine ⟨0,1,26,by decide,by decide,by decide,Or.inr rfl,?_⟩
        intro x
        rw [bad _ _ (by rw [lenf]; decide)]
        simp only [join,bad (seed x) i (by rw [lens]; omega),bad (seed x) j (by rw [lens]; omega),Bool.or_false]
    · by_cases eq : i = j
      · subst j
        refine ⟨0,1,i,by decide,by decide,by decide,Or.inl (by omega),?_⟩
        intro x
        simp only [full,join,left (seed x) _ i (by rw [lens]; omega),Bool.or_self]
      by_cases pair : i = 0 ∧ j = 4
      · obtain ⟨rfl,rfl⟩ := pair
        refine ⟨0,1,9,by decide,by decide,by decide,Or.inl (by decide),?_⟩
        intro x
        rfl
      refine ⟨⟨i,by omega⟩,⟨j,by omega⟩,10,show i < j by omega,?_,?_,Or.inl (by decide),?_⟩
      · rintro ⟨e,f⟩
        exact pair ⟨congrArg Fin.val e,congrArg Fin.val f⟩
      · rintro ⟨_,f⟩
        exact nj (congrArg Fin.val f)
      intro x
      simpa only [full,lens] using last (seed x) (join x i j)
  have norm : Good a.val b.val := by
    by_cases h : a.val ≤ b.val
    · exact sorted _ _ h hn.1 hn.2
    · obtain ⟨p,q,t,h₁,h₂,h₃,ht,hs⟩ := sorted _ _ (by omega : b.val ≤ a.val) hn.2 hn.1
      exact ⟨p,q,t,h₁,h₂,h₃,ht,fun x => (hs x).trans (Bool.or_comm _ _)⟩
  obtain ⟨p,q,t,hp,hq,h9,ht,hs⟩ := norm
  let wire (i : Nat) := if i = 10 then t else i
  let raw (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :=
    let rd (j : Fin 26) := if j.val = 25 then true else w.getD j.val false
    if g.1.val = 0 then rd g.2.1 && rd g.2.2 else
      if g.1.val = 1 then rd g.2.1 || rd g.2.2 else !rd g.2.1
  let comp (g : Fin 3 × Fin 26 × Fin 26) : Gate :=
    let i := g.2.1.val
    let j := g.2.2.val
    if g.1.val = 0 then
      ⟨.and, (if i = 25 then [] else [wire i]) ++ (if j = 25 then [] else [wire j])⟩
    else if g.1.val = 1 then
      if i = 25 ∨ j = 25 then ⟨.and,[]⟩ else ⟨.or,[wire i,wire j]⟩
    else if i = 25 then ⟨.or,[]⟩ else ⟨.not,[wire i]⟩
  let C : Circuit := ⟨gs.map comp,wire o.val⟩
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hg
    dsimp only [comp]
    split_ifs <;> simp
  let val (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map (fun i => w.getD i false))
  have evAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evNot (l : List Bool) : GateOp.not.eval l = !l.headD false := rfl
  have step (u v : List Bool) (eqv : ∀ i, v.getD (wire i) false = u.getD i false)
      (g : Fin 3 × Fin 26 × Fin 26) : val v (comp g) = raw u g := by
    clear h3509 h3590
    dsimp only [raw,comp]
    split_ifs <;> simp_all [val]
  by_contra! no
  suffices correct : ∀ x, C.eval (full x p.val q.val) =
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
       List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) by
    by_cases splitCase : ∃ i j : Fin 9, i.val = p.val ∧ j.val = q.val ∧
        i ≠ 0 ∧ i ≠ 4 ∧ j ≠ 0 ∧ j ≠ 4 ∧ i ≠ j ∧
        i.val * 10 + j.val ∉ ([12,21,23,32,16,61,27,72,38,83,57,75,68,86,58,85] : List Nat)
    · obtain ⟨i,j,ip,jq,ni,mi,nj,mj,ij,nonEdge⟩ := splitCase
      apply h3509 i j C ni mi nj mj ij nonEdge fan (by change (gs.map comp).length ≤ 13; rw [List.length_map]; exact budget)
      intro x
      have readI (v : Fin 9) : (seed x).getD v.val false = x v := by
        rw [show seed x = List.ofFn x ++ [x 0 || x 4] from rfl]
        rw [left _ _ _ (by rw [List.length_ofFn]; exact v.isLt)]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left v.isLt,Option.getD_some]
      have hval := correct x
      rw [← ip,← jq] at hval
      simp only [full,join,readI,seed,List.append_assoc,List.cons_append,List.nil_append] at hval
      simpa only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using hval
    have h := h3590 C p q fan hp hq h9 correct
    change 14 ≤ (gs.map comp).length at h
    rw [List.length_map] at h
    omega
  intro x
  let U := full x a.val b.val
  let V := full x p.val q.val
  have readEq (s : List Bool) (ss : s.length ≤ 13) (i : Nat) :
      (V ++ s).getD (wire i) false = (U ++ s).getD i false := by
    by_cases e : i = 10
    · subst i
      simp only [wire,ite_true,left U s 10 (by simp [U,lenf])]
      have ru : U.getD 10 false = join x a.val b.val := by
        simpa only [U,full,lens] using last (seed x) (join x a.val b.val)
      rw [ru,← hs x]
      rcases ht with h | rfl
      · exact left _ _ _ (by simpa [V,lenf] using h)
      · rw [bad _ _ (by simp [V,lenf]; omega),bad _ _ (by simp [lenf])]
    simp only [wire,e,ite_false]
    by_cases hi : i < 10
    · rw [left V s i (by change i < (full x _ _).length; rw [lenf]; omega),
          left U s i (by change i < (full x _ _).length; rw [lenf]; omega)]
      simp only [V,U,full,left (seed x) _ i (by rw [lens]; exact hi)]
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right
          (show V.length ≤ i by rw [show V.length = 11 from lenf ..]; omega),
          List.getElem?_append_right (show U.length ≤ i by rw [show U.length = 11 from lenf ..]; omega),
          U,V,lenf]
  have run (l : List (Fin 3 × Fin 26 × Fin 26)) (s : List Bool)
      (hl : l.length + s.length ≤ 13) :
      (((l.map comp).foldl (fun w g => w ++ [val w g]) (V ++ s))).getD (wire o.val) false =
      (l.foldl (fun w g => w ++ [raw w g]) (U ++ s)).getD o.val false := by
    induction l generalizing s with
    | nil => exact readEq s (by simpa using hl) _
    | cons g l ih =>
      simp only [List.map_cons,List.foldl_cons]
      rw [step _ _ (readEq s (by simp at hl; omega)),List.append_assoc,List.append_assoc]
      apply ih
      simp at hl ⊢
      omega
  have sim : C.eval V = (gs.foldl (fun w g => w ++ [raw w g]) U).getD o.val false := by
    have hrun := run gs [] (by simpa using budget)
    simp only [List.append_nil] at hrun
    exact hrun
  rw [sim]
  let bits := BitVec.ofBoolListLE (List.ofFn x)
  have bound : bits.toNat < 512 := by simpa [bits] using bits.isLt
  have rep : (fun j : Fin 9 => bits.toNat.testBit j.val) = x := by
    funext j
    change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD j.val = _
    rw [BitVec.getLsbD_ofBoolListLE]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some]
  have same := Classical.not_not.mp (no bits.toNat bound)
  let edge (y : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
          (fun e => y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10)))
  change (gs.foldl (fun w g => w ++ [raw w g])
    (seed (fun j => bits.toNat.testBit j.val) ++
    [raw (seed (fun j => bits.toNat.testBit j.val)) (1,a,b)])).getD o.val false =
      edge (fun j => bits.toNat.testBit j.val) at same
  rw [rep] at same
  have start : raw (seed x) (1,a,b) = join x a.val b.val := by simp [raw,join,ha,hb]
  rw [start] at same
  exact same.trans (by rfl)
