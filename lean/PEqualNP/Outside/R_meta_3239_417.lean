import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_3239_417
    (pivots :
      let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
        (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ (l : Fin 9) (r : Fin 10) (b : Bool),
        let leftIndex : ℕ := l.val
        let rightIndex : ℕ := r.val
        leftIndex ∈ ([2,3,4,7] : List ℕ) → rightIndex ≠ leftIndex →
        ∃ k : Fin 3,
          let row := (([[9,104,402],[5,100,402],[42,200,261],[42,69,276]] : List (List ℕ)).getD
            (([2,3,4,7] : List ℕ).idxOf leftIndex) []).getD k.val 0
          let x : Fin 9 → Bool := fun i => row.testBit i.val
          let y : Fin 9 → Bool := fun i => if i = l then true else x i
          x l = false ∧ f x = false ∧ f y = true ∧
            (if h : rightIndex < 9 then x ⟨rightIndex,h⟩ else x 0 || x 1) ≠ b)
    (restricted :
      let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
        (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let s (i : ℕ) := ([1,0,5,8,6,2,4,7,3] : List ℕ).getD i i
      ∀ (C : BinaryCircuit) (b : Bool),
        (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun u v => u == a && v == b) →
        (∀ g : BinaryGate, C.gates[0]? = some g →
          (∃ b : Bool, g.op = fun u v => u == false && v == b) ∧ [g.left,g.right] ≤ [s g.left,s g.right]) →
        (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1,false]) != b) = f x) →
        (∀ g gs, C.gates = g :: gs → g.left ∈ ([2,3,4,7] : List ℕ) → g.right < 10 →
          g.right ≠ g.left → ∃ h ∈ gs, h.left = g.left ∨ h.right = g.left) →
        14 ≤ C.size) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.false && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C b basis first computes
  let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 1,false]
  have correct (x : Fin 9 → Bool) : (C.eval (base x) != b) = f x := by
    simpa [f, base, Bool.or_assoc] using computes x
  apply restricted C b basis first correct
  intro g gs hg hl hr hrl
  have hleft : g.left < 9 := by simp at hl; omega
  let l : Fin 9 := ⟨g.left,hleft⟩
  let r : Fin 10 := ⟨g.right,hr⟩
  obtain ⟨⟨sign, signSpec⟩, _⟩ := first g (by rw [hg]; rfl)
  obtain ⟨k, hp⟩ := pivots l r sign hl hrl
  let row := (([[9,104,402],[5,100,402],[42,200,261],[42,69,276]] : List (List ℕ)).getD
    (([2,3,4,7] : List ℕ).idxOf l.val) []).getD k.val 0
  let x : Fin 9 → Bool := fun i => row.testBit i.val
  let y : Fin 9 → Bool := fun i => if i = l then true else x i
  change x l = false ∧ f x = false ∧ f y = true ∧
    (if h : r.val < 9 then x ⟨r.val,h⟩ else x 0 || x 1) ≠ sign at hp
  obtain ⟨xleft,fx,fy,block⟩ := hp
  have hlen (z : Fin 9 → Bool) : (base z).length = 11 := by simp [base]
  have read (z : Fin 9 → Bool) (i : ℕ) :
      (base z).getD i false = if h : i < 9 then z ⟨i,h⟩ else if i = 9 then z 0 || z 1 else false := by
    by_cases h : i < 9
    · have h' : i < (List.ofFn z).length := by simpa using h
      rw [dite_eq_left h, List.getD_append _ _ _ _ h', List.getD_eq_getElem _ _ h', List.getElem_ofFn]
    · have h' : (List.ofFn z).length ≤ i := by simp; omega
      rw [dite_eq_right h, List.getD_append_right _ _ _ _ h']
      simp only [List.length_ofFn]
      by_cases he : i = 9
      · subst i; rfl
      · rw [ite_eq_right he]
        by_cases h10 : i = 10
        · subst i; rfl
        · exact List.getD_eq_default _ _ (by simp; omega)
  have l0 : (0 : Fin 9) ≠ l := by
    intro h; have hv := congrArg Fin.val h; change 0 = g.left at hv; simp [hv.symm] at hl
  have l1 : (1 : Fin 9) ≠ l := by
    intro h; have hv := congrArg Fin.val h; change 1 = g.left at hv; simp [hv.symm] at hl
  have sameBase (i : ℕ) (hi : i ≠ g.left) : (base x).getD i false = (base y).getD i false := by
    rw [read, read]
    split
    · rename_i h
      have hne : (⟨i,h⟩ : Fin 9) ≠ l := fun e => hi (congrArg Fin.val e)
      simp [y, hne]
    · simp [y,l0,l1]
  have blockRead : (base x).getD g.right false ≠ sign := by
    rw [read]
    by_cases hp : g.right < 9
    · simpa [r,hp] using block
    · have he : g.right = 9 := by omega
      simpa [r,hp,he] using block
  have headSame : g.op ((base x).getD g.left false) ((base x).getD g.right false) =
      g.op ((base y).getD g.left false) ((base y).getD g.right false) := by
    rw [signSpec, read x g.left, read y g.left, dite_eq_left hleft, dite_eq_left hleft]
    have yl : y l = true := by simp [y]
    change ((x l == false) && ((base x).getD g.right false == sign)) =
      ((y l == false) && ((base y).getD g.right false == sign))
    rw [xleft, yl, beq_eq_false_iff_ne.mpr blockRead]
    rfl
  let step (w : List Bool) (h : BinaryGate) := w ++ [h.op (w.getD h.left false) (w.getD h.right false)]
  have keep (hs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (hs.foldl step w).getD i false = w.getD i false := by
    induction hs generalizing w with
    | nil => rfl
    | cons h hs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have appendEq (w v : List Bool) (a : Bool) (len : w.length = v.length)
      (rel : ∀ i ≠ g.left, w.getD i false = v.getD i false) :
      ∀ i ≠ g.left, (w ++ [a]).getD i false = (v ++ [a]).getD i false := by
    intro i hi
    by_cases h : i < w.length
    · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (len ▸ h), rel i hi]
    · have h' : v.length ≤ i := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ h',len]
  have outNe : C.output ≠ g.left := by
    intro hout
    let zero : Fin 9 → Bool := fun _ => false
    let pair : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have value (z : Fin 9 → Bool) : C.eval (base z) = z l := by
      change (C.gates.foldl step (base z)).getD C.output false = _
      rw [hout, keep _ _ _ (by rw [hlen]; omega), read, dite_eq_left hleft]
    have hz := correct zero
    have ht := correct pair
    rw [value] at hz ht
    have eq : pair l = false := by simp [pair, Ne.symm l0, Ne.symm l1]
    have zf : f zero = false := by dsimp [f, zero]; decide +kernel
    have tf : f pair = true := by dsimp [f, pair]; decide +kernel
    rw [eq, tf] at ht
    change (false != b) = f zero at hz
    rw [zf] at hz
    rw [hz] at ht
    cases ht
  by_contra! noRead
  have ignore (hs : List BinaryGate) (sub : ∀ h ∈ hs, h ∈ gs)
      (w v : List Bool) (len : w.length = v.length)
      (rel : ∀ i ≠ g.left, w.getD i false = v.getD i false) :
      ∀ i ≠ g.left, (hs.foldl step w).getD i false = (hs.foldl step v).getD i false := by
    induction hs generalizing w v with
    | nil => exact rel
    | cons h hs ih =>
      rw [List.foldl_cons,List.foldl_cons]
      apply ih (fun t ht => sub t (List.mem_cons_of_mem _ ht))
      · simp [step,len]
      · have hn := noRead h (sub h List.mem_cons_self)
        unfold step
        rw [rel _ hn.1, rel _ hn.2]
        exact appendEq _ _ _ len rel
  have eq : C.eval (base x) = C.eval (base y) := by
    change (C.gates.foldl step (base x)).getD C.output false =
      (C.gates.foldl step (base y)).getD C.output false
    rw [hg, List.foldl_cons, List.foldl_cons]
    apply ignore gs (fun _ h => h)
    · simp [step,hlen]
    · unfold step
      rw [headSame]
      exact appendEq _ _ _ (by rw [hlen,hlen]) sameBase
    · exact outNe
  have hx := correct x
  have hy := correct y
  rw [fx, eq, hy, fy] at hx
  cases hx
