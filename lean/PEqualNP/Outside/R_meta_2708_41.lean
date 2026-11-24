import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The Heawood graph has 37 maximal independent sets. Its 336 symmetries and an exchange of
-- the two output wires put the two opposite negative witnesses into thirteen representative pairs.
-- Vertices v0 through v13 are numbered 0 through 13, as in the parent edge list.
-- The 37 maximal independent sets are in increasing order of their characteristic vectors
-- read with vertex 0 as the least significant entry. The 13 pairs index this list from zero.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_2708_41
  (boundary :
    let v0 : ℕ := 0
    let v1 : ℕ := 1
    let v2 : ℕ := 2
    let v3 : ℕ := 3
    let v4 : ℕ := 4
    let v5 : ℕ := 5
    let v6 : ℕ := 6
    let v7 : ℕ := 7
    let v8 : ℕ := 8
    let v9 : ℕ := 9
    let v10 : ℕ := 10
    let v11 : ℕ := 11
    let v12 : ℕ := 12
    let v13 : ℕ := 13
    ∀ (C : Circuit) (a : ℕ), Monotone2 C →
      let es : List (ℕ × ℕ) := [(v0, v7), (v0, v8), (v0, v10), (v1, v7), (v1, v9), (v1, v13), (v2, v8), (v2, v12), (v2, v13), (v3, v7), (v3, v11), (v3, v12), (v4, v10), (v4, v11), (v4, v13), (v5, v9), (v5, v10), (v5, v12), (v6, v8), (v6, v9), (v6, v11)]
      let val := fun x : Fin 14 → Bool => (C.wires (List.ofFn x)).getD a false
      ∀ x : Fin 14 → Bool, (¬ ∃ v w : Fin 14, (v.val,w.val) ∈ es ∧ x v = true ∧ x w = true) → val x = true → ∃ h : Fin 37,
             val (fun i => ((([
                 [v0, v1, v2, v3, v4, v5, v6], [v2, v4, v5, v6, v7], [v1, v3, v4, v5, v8], [v4, v5, v7, v8],
                 [v0, v2, v3, v4, v9], [v2, v4, v7, v9], [v3, v4, v8, v9], [v1, v2, v3, v6, v10],
                 [v2, v6, v7, v10], [v1, v3, v8, v10]] ++ [
                 [v2, v3, v9, v10], [v0, v1, v2, v5, v11], [v2, v5, v7, v11], [v1, v5, v8, v11],
                 [v0, v2, v9, v11], [v1, v2, v10, v11], [v2, v7, v9, v10, v11], [v0, v1, v4, v6, v12],
                 [v4, v6, v7, v12], [v1, v4, v8, v12]] ++ [
                 [v0, v4, v9, v12], [v4, v7, v8, v9, v12], [v1, v6, v10, v12], [v0, v1, v11, v12],
                 [v1, v8, v10, v11, v12], [v0, v3, v5, v6, v13], [v5, v6, v7, v13], [v3, v5, v8, v13],
                 [v0, v3, v9, v13], [v3, v6, v10, v13]] ++ [
                 [v3, v8, v9, v10, v13], [v0, v5, v11, v13], [v5, v7, v8, v11, v13], [v0, v6, v12, v13],
                 [v6, v7, v10, v12, v13], [v0, v9, v11, v12, v13], [v7, v8, v9, v10, v11, v12, v13]]) : List (List ℕ)).getD h.val []).contains i.val) = true)
  (geometry :
    ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : ℕ, [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] = List.range 14 →
      let row (r : List ℕ) (v : Fin 14) := r.contains v.val
      let M := (([
          [v0, v1, v2, v3, v4, v5, v6], [v2, v4, v5, v6, v7], [v1, v3, v4, v5, v8], [v4, v5, v7, v8],
          [v0, v2, v3, v4, v9], [v2, v4, v7, v9], [v3, v4, v8, v9], [v1, v2, v3, v6, v10],
          [v2, v6, v7, v10], [v1, v3, v8, v10]] ++ [
          [v2, v3, v9, v10], [v0, v1, v2, v5, v11], [v2, v5, v7, v11], [v1, v5, v8, v11],
          [v0, v2, v9, v11], [v1, v2, v10, v11], [v2, v7, v9, v10, v11], [v0, v1, v4, v6, v12],
          [v4, v6, v7, v12], [v1, v4, v8, v12]] ++ [
          [v0, v4, v9, v12], [v4, v7, v8, v9, v12], [v1, v6, v10, v12], [v0, v1, v11, v12],
          [v1, v8, v10, v11, v12], [v0, v3, v5, v6, v13], [v5, v6, v7, v13], [v3, v5, v8, v13],
          [v0, v3, v9, v13], [v3, v6, v10, v13]] ++ [
          [v3, v8, v9, v10, v13], [v0, v5, v11, v13], [v5, v7, v8, v11, v13], [v0, v6, v12, v13],
          [v6, v7, v10, v12, v13], [v0, v9, v11, v12, v13], [v7, v8, v9, v10, v11, v12, v13]]) : List (List ℕ)).map row
      let P := ([(v0, v7), (v0, v8), (v0, v10), (v1, v7), (v1, v9), (v1, v13), (v2, v8), (v2, v12), (v2, v13), (v3, v7), (v3, v11), (v3, v12), (v4, v10), (v4, v11), (v4, v13), (v5, v9), (v5, v10), (v5, v12), (v6, v8), (v6, v9), (v6, v11)] : List (ℕ × ℕ)).map (fun e => row [e.1,e.2])
      ∀ i j, i ∈ M → j ∈ M → i ≠ j →
        ∃ (t : Fin 14 → Fin 14) (k : ℕ × ℕ), k ∈ ([(v0, v1), (v0, v3), (v0, 16), (v0, 36), (v1, v2), (v1, v3), (v1, v6), (v1, v9), (v1, 16), (v1, 24), (v3, v5), (v3, v8), (v3, v10)] : List (ℕ × ℕ)) ∧
          (∀ r ∈ P, r ∘ t ∈ P) ∧
          (∀ r ∈ M, r ∘ t ∈ M) ∧
          s(M.getD k.1 default ∘ t, M.getD k.2 default ∘ t) = s(i,j))
  (search :
    ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : ℕ, [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] = List.range 14 →
      let M : List (List ℕ) := ([
          [v0, v1, v2, v3, v4, v5, v6], [v2, v4, v5, v6, v7], [v1, v3, v4, v5, v8], [v4, v5, v7, v8],
          [v0, v2, v3, v4, v9], [v2, v4, v7, v9], [v3, v4, v8, v9], [v1, v2, v3, v6, v10],
          [v2, v6, v7, v10], [v1, v3, v8, v10]] ++ [
          [v2, v3, v9, v10], [v0, v1, v2, v5, v11], [v2, v5, v7, v11], [v1, v5, v8, v11],
          [v0, v2, v9, v11], [v1, v2, v10, v11], [v2, v7, v9, v10, v11], [v0, v1, v4, v6, v12],
          [v4, v6, v7, v12], [v1, v4, v8, v12]] ++ [
          [v0, v4, v9, v12], [v4, v7, v8, v9, v12], [v1, v6, v10, v12], [v0, v1, v11, v12],
          [v1, v8, v10, v11, v12], [v0, v3, v5, v6, v13], [v5, v6, v7, v13], [v3, v5, v8, v13],
          [v0, v3, v9, v13], [v3, v6, v10, v13]] ++ [
          [v3, v8, v9, v10, v13], [v0, v5, v11, v13], [v5, v7, v8, v11, v13], [v0, v6, v12, v13],
          [v6, v7, v10, v12, v13], [v0, v9, v11, v12, v13], [v7, v8, v9, v10, v11, v12, v13]])
      ∀ (C : Circuit) (a b : ℕ), Monotone2 C →
        let state (r : List ℕ) := let w := C.wires (List.ofFn (fun i : Fin 14 => r.contains i.val)); (w.getD a false, w.getD b false)
        (∀ p ∈ ([(v0, v7), (v0, v8), (v0, v10), (v1, v7), (v1, v9), (v1, v13), (v2, v8), (v2, v12), (v2, v13), (v3, v7), (v3, v11), (v3, v12), (v4, v10), (v4, v11), (v4, v13), (v5, v9), (v5, v10), (v5, v12), (v6, v8), (v6, v9), (v6, v11)] : List (ℕ × ℕ)), state [p.1,p.2] = (true,true)) →
        (∀ r ∈ M, state r ≠ (true,true)) →
        (∃ p ∈ ([(v0, v1), (v0, v3), (v0, 16), (v0, 36), (v1, v2), (v1, v3), (v1, v6), (v1, v9), (v1, 16), (v1, 24), (v3, v5), (v3, v8), (v3, v10)] : List (ℕ × ℕ)), state (M.getD p.1 []) = (false,true) ∧ state (M.getD p.2 []) = (true,false)) →
        26 ≤ C.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size := by
  intro C a b hm _ _
  dsimp only
  intro hp hn hab hba
  let es : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let hit := fun x : Fin 14 → Bool => ∃ v w : Fin 14, (v.val,w.val) ∈ es ∧ x v = true ∧ x w = true
  let val := fun w (x : Fin 14 → Bool) => (C.wires (List.ofFn x)).getD w false
  let pos (j : ℕ) (i : Fin 14) := let e := es.getD j default; [e.1,e.2].contains i.val
  let maximal : List (List ℕ) := [
      [0, 1, 2, 3, 4, 5, 6], [2, 4, 5, 6, 7], [1, 3, 4, 5, 8], [4, 5, 7, 8],
      [0, 2, 3, 4, 9], [2, 4, 7, 9], [3, 4, 8, 9], [1, 2, 3, 6, 10],
      [2, 6, 7, 10], [1, 3, 8, 10], [2, 3, 9, 10], [0, 1, 2, 5, 11],
      [2, 5, 7, 11], [1, 5, 8, 11], [0, 2, 9, 11], [1, 2, 10, 11],
      [2, 7, 9, 10, 11], [0, 1, 4, 6, 12], [4, 6, 7, 12], [1, 4, 8, 12],
      [0, 4, 9, 12], [4, 7, 8, 9, 12], [1, 6, 10, 12], [0, 1, 11, 12],
      [1, 8, 10, 11, 12], [0, 3, 5, 6, 13], [5, 6, 7, 13], [3, 5, 8, 13],
      [0, 3, 9, 13], [3, 6, 10, 13], [3, 8, 9, 10, 13], [0, 5, 11, 13],
      [5, 7, 8, 11, 13], [0, 6, 12, 13], [6, 7, 10, 12, 13], [0, 9, 11, 12, 13],
      [7, 8, 9, 10, 11, 12, 13]]
  let neg (j : ℕ) (i : Fin 14) := (maximal.getD j []).contains i.val
  let pair (j : ℕ) := ([(0, 1), (0, 3), (0, 16), (0, 36), (1, 2), (1, 3), (1, 6), (1, 9), (1, 16), (1, 24), (3, 5), (3, 8), (3, 10)] : List (ℕ × ℕ)).getD j default
  have positive : ∀ i : Fin 21, hit (pos i.val) := by dsimp [hit,es,pos]; decide +kernel
  have negative : ∀ i : Fin 37, ¬hit (neg i.val) := by dsimp [hit,es,neg,maximal]; decide +kernel
  obtain ⟨x,nx,ax,bx⟩ := hab
  obtain ⟨y,ny,byy,ay⟩ := hba
  obtain ⟨i,bi⟩ := boundary C b hm x nx bx
  obtain ⟨j,aj⟩ := boundary C a hm y ny ay
  change val b (neg i.val) = true at bi
  change val a (neg j.val) = true at aj
  have ai : val a (neg i.val) = false := by
    rcases hn _ (negative i) with h|h
    · exact h
    · exact False.elim (Bool.noConfusion (h.symm.trans bi))
  have bj : val b (neg j.val) = false := by
    rcases hn _ (negative j) with h|h
    · exact False.elim (Bool.noConfusion (h.symm.trans aj))
    · exact h
  let positives := List.ofFn (fun u : Fin 21 => pos u.val)
  let negatives := List.ofFn (fun u : Fin 37 => neg u.val)
  let representatives := List.ofFn (fun u : Fin 13 => pair u.val)
  have geo := geometry 0 1 2 3 4 5 6 7 8 9 10 11 12 13 rfl
  change ∀ x y, x ∈ negatives → y ∈ negatives → x ≠ y →
    ∃ (t : Fin 14 → Fin 14) (k : ℕ × ℕ), k ∈ representatives ∧
      (∀ r ∈ positives, r ∘ t ∈ positives) ∧ (∀ r ∈ negatives, r ∘ t ∈ negatives) ∧
      s(negatives.getD k.1 default ∘ t, negatives.getD k.2 default ∘ t) = s(x,y) at geo
  have hne : neg i.val ≠ neg j.val := by
    intro he
    exact Bool.noConfusion (ai.symm.trans ((congrArg (val a) he).trans aj))
  obtain ⟨t,q,hq,pm,nm,hr⟩ := geo _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩) (List.mem_ofFn.mpr ⟨j,rfl⟩) hne
  obtain ⟨k,hk⟩ := List.mem_ofFn.mp hq
  change pair k.val = q at hk
  subst q
  have pmap (u : Fin 21) : ∃ v : Fin 21, pos u.val ∘ t = pos v.val := by
    obtain ⟨v,hv⟩ := List.mem_ofFn.mp (pm _ (List.mem_ofFn.mpr ⟨u,rfl⟩))
    exact ⟨v,hv.symm⟩
  have nmap (u : Fin 37) : ∃ v : Fin 37, neg u.val ∘ t = neg v.val := by
    obtain ⟨v,hv⟩ := List.mem_ofFn.mp (nm _ (List.mem_ofFn.mpr ⟨u,rfl⟩))
    exact ⟨v,hv.symm⟩
  have repRows : ∀ u : Fin 13, negatives.getD (pair u.val).1 default = neg (pair u.val).1 ∧
      negatives.getD (pair u.val).2 default = neg (pair u.val).2 := by decide +kernel
  rw [(repRows k).1,(repRows k).2] at hr
  have repmap := Sym2.eq_iff.mp hr
  let f (w : ℕ) := if h : w < 14 then (t ⟨w,h⟩).val else w
  let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
  let D : Circuit := ⟨C.gates.map rename,f C.output⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have md : Monotone2 D := by
    intro g hg
    change g ∈ C.gates.map rename at hg
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hg
    exact ⟨(hm o ho).1,by simpa [rename] using (hm o ho).2⟩
  have sim (z : Fin 14 → Bool) (w : ℕ) :
      (D.wires (List.ofFn z)).getD (f w) false = val w (z ∘ t) := by
    let u := List.ofFn (z ∘ t)
    let v := List.ofFn z
    have reads (s : List Bool) (i : ℕ) : (u++s).getD i false = (v++s).getD (f i) false := by
      simp only [u,v,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn]
      by_cases hi : i < 14
      · simp only [f,dite_eq_left hi,ite_eq_left hi,ite_eq_left (t ⟨i,hi⟩).isLt,List.getElem?_ofFn]
        rw [dite_eq_left (t ⟨i,hi⟩).isLt]
        rfl
      · simp only [f,dite_eq_right hi,ite_eq_right hi]
    have run (gs : List Gate) (s : List Bool) : ∃ q : List Bool,
        gs.foldl step (u++s) = u++q ∧ (gs.map rename).foldl step (v++s) = v++q := by
      induction gs generalizing s with
      | nil => exact ⟨s,rfl,rfl⟩
      | cons g gs ih =>
        let bit := g.op.eval (g.inputs.map fun i => (u++s).getD i false)
        have eb : bit = (rename g).op.eval ((rename g).inputs.map fun i => (v++s).getD i false) := by
          change g.op.eval _ = g.op.eval _
          congr 1
          simp only [rename,List.map_map]
          apply List.map_congr_left
          intro i _
          exact reads s i
        obtain ⟨q,h1,h2⟩ := ih (s++[bit])
        refine ⟨q,?_,?_⟩
        · simpa only [List.foldl_cons,step,List.append_assoc,bit] using h1
        · change (gs.map rename).foldl step ((v++s)++[_]) = _
          rw [← eb,List.append_assoc]
          exact h2
    obtain ⟨q,h1,h2⟩ := run C.gates []
    simp only [List.append_nil] at h1 h2
    change ((C.gates.map rename).foldl step v).getD (f w) false = (C.gates.foldl step u).getD w false
    rw [h1,h2]
    exact (reads q w).symm
  have pa (u : Fin 21) : val a (pos u.val ∘ t) = true ∧ val b (pos u.val ∘ t) = true := by
    obtain ⟨v,hv⟩ := pmap u
    rw [hv];exact hp _ (positive v)
  have nn (u : Fin 37) : val a (neg u.val ∘ t) = false ∨ val b (neg u.val ∘ t) = false := by
    obtain ⟨v,hv⟩ := nmap u
    rw [hv];exact hn _ (negative v)
  have sizeEq : D.size = C.size := List.length_map _
  rw [← sizeEq]
  have searchRows (T : Circuit) (a b : ℕ) (hT : Monotone2 T) :
      let state := fun x : Fin 14 → Bool => ((T.wires (List.ofFn x)).getD a false,(T.wires (List.ofFn x)).getD b false)
      (∀ u : Fin 21, state (pos u.val) = (true,true)) →
      (∀ u : Fin 37, state (neg u.val) ≠ (true,true)) →
      (∃ u : Fin 13, state (neg (pair u.val).1) = (false,true) ∧ state (neg (pair u.val).2) = (true,false)) →
      26 ≤ T.size := by
    dsimp only
    intro p n witness
    apply search 0 1 2 3 4 5 6 7 8 9 10 11 12 13 rfl T a b hT
    · intro e he
      change e ∈ List.ofFn (fun u : Fin 21 => es.getD u.val default) at he
      obtain ⟨u,rfl⟩ := List.mem_ofFn.mp he
      exact p u
    · intro r hr
      change r ∈ List.ofFn (fun u : Fin 37 => maximal.getD u.val []) at hr
      obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hr
      exact n u
    · obtain ⟨u,hu⟩ := witness
      have present : pair u.val ∈ representatives := List.mem_ofFn.mpr ⟨u,rfl⟩
      exact ⟨pair u.val,present,hu⟩
  rcases repmap with ⟨left,right⟩|⟨left,right⟩
  · apply searchRows D (f a) (f b) md
    · intro u
      exact Prod.ext ((sim _ _).trans (pa u).1) ((sim _ _).trans (pa u).2)
    · intro u eq
      rcases nn u with h|h
      · exact Bool.noConfusion (h.symm.trans ((sim _ _).symm.trans (congrArg Prod.fst eq)))
      · exact Bool.noConfusion (h.symm.trans ((sim _ _).symm.trans (congrArg Prod.snd eq)))
    · refine ⟨k,Prod.ext ?_ ?_,Prod.ext ?_ ?_⟩
      · exact (sim _ _).trans (left.symm ▸ ai)
      · exact (sim _ _).trans (left.symm ▸ bi)
      · exact (sim _ _).trans (right.symm ▸ aj)
      · exact (sim _ _).trans (right.symm ▸ bj)
  · apply searchRows D (f b) (f a) md
    · intro u
      exact Prod.ext ((sim _ _).trans (pa u).2) ((sim _ _).trans (pa u).1)
    · intro u eq
      rcases nn u with h|h
      · exact Bool.noConfusion (h.symm.trans ((sim _ _).symm.trans (congrArg Prod.snd eq)))
      · exact Bool.noConfusion (h.symm.trans ((sim _ _).symm.trans (congrArg Prod.fst eq)))
    · refine ⟨k,Prod.ext ?_ ?_,Prod.ext ?_ ?_⟩
      · exact (sim _ _).trans (left.symm ▸ bj)
      · exact (sim _ _).trans (left.symm ▸ aj)
      · exact (sim _ _).trans (right.symm ▸ bi)
      · exact (sim _ _).trans (right.symm ▸ ai)
