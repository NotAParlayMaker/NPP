import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4350_1
    (short :
      have f : (Fin 9 → Bool) → Bool := fun x =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ¬ HasCircuitSize 9 f 14)
    (raw : ∀ (i j : ℕ), (i,j) ∈ ([(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3),
          (2,4),(2,6),(2,7),(2,8),(3,4),(3,6),(4,6),(6,7)] : List (ℕ × ℕ)) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 12 →
      (∀ x : Fin 9 → Bool,
        let w := List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]
        C.eval (w ++ [w.getD i false || w.getD j false]) =
          ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
            (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) → False)
    (computed : ∀ (i j : ℕ), (i,j) ∈ ([(1,9),(1,10),(2,9),(2,10),(3,9),
          (4,10),(6,9),(6,10),(9,10)] : List (ℕ × ℕ)) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 12 →
      (∀ x : Fin 9 → Bool,
        let w := List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]
        C.eval (w ++ [w.getD i false || w.getD j false]) =
          ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
            (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) → False) :
    ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (12 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn
      (Function.update x6 (0 : Fin (9 : ℕ)) Bool.false) ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 :
      Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ))] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : ℕ)
      => (List.ofFn (Function.update x6 (0 : Fin (9 : ℕ)) Bool.false) ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 :
      ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ))]).getD x7 Bool.false) x1)]) = [((0 : Fin (9 : ℕ)), (1 : Fin
      (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 :
      ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1
      : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 :
      ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5
      : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → False := by
  intro l hlen C legal hsize agrees
  let base (x : Fin 9 → Bool) := List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]
  let get (x : Fin 9 → Bool) (i : ℕ) := (base x).getD i false
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have lengthBase (x : Fin 9 → Bool) : (base x).length = 11 := by simp [base]
  have reads (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have get0 (x : Fin 9 → Bool) : get x 0 = false := by
    change (base x).getD (0 : Fin 9).val false = false
    rw [show base x = List.ofFn (Function.update x 0 false) ++ [x 0 || x 4,x 0 || x 3] from rfl,
      List.getD_append _ _ _ _ (by simp), reads]
    exact Function.update_self _ _ _
  have evOr (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  have ok (x : Fin 9 → Bool) : C.eval (base x ++ [l.any (get x)]) = f x := by
    have he := agrees x
    change C.eval (base x ++ [GateOp.or.eval (l.map (get x))]) = f x at he
    have eq : GateOp.or.eval (l.map (get x)) = l.any (get x) := by
      change (l.map (get x)).any id = _
      simp only [List.any_map, Function.id_comp]
    rwa [eq] at he
  let index (i : ℕ) := if i ≤ 10 then i else 0
  have bounded (i : ℕ) : index i ≤ 10 := by dsimp [index]; split <;> omega
  have getIndex (x : Fin 9 → Bool) (i : ℕ) : get x i = get x (index i) := by
    by_cases h : i ≤ 10
    · simp only [index, ite_eq_left h]
    · rw [show index i = 0 from ite_eq_right h, get0]
      exact List.getD_eq_default _ _ (by rw [lengthBase]; omega)
  have normalize :
      (∃ a ≤ 10, ∀ x : Fin 9 → Bool, l.any (get x) = get x a) ∨
      (∃ i j : ℕ, 0 < i ∧ i < j ∧ j ≤ 10 ∧ (i,j) ≠ (4,9) ∧ (i,j) ≠ (3,10) ∧
        ∀ x : Fin 9 → Bool, l.any (get x) = (get x i || get x j)) := by
    cases l with
    | nil => exact Or.inl ⟨0, by decide, fun x => (get0 x).symm⟩
    | cons a tail =>
      cases tail with
      | nil => exact Or.inl ⟨index a, bounded a, fun x => by simpa only [List.any_cons, List.any_nil, Bool.or_false] using getIndex x a⟩
      | cons b tail =>
        have ht : tail = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
        subst tail
        let i := min (index a) (index b)
        let j := max (index a) (index b)
        have least : i ≤ j := le_trans (min_le_left _ _) (le_max_left _ _)
        have greatest : j ≤ 10 := max_le (bounded a) (bounded b)
        have order (x : Fin 9 → Bool) : [a,b].any (get x) = (get x i || get x j) := by
          simp only [List.any_cons, List.any_nil, Bool.or_false, getIndex x a, getIndex x b]
          rcases le_total (index a) (index b) with h | h
          · simp only [i, j, min_eq_left h, max_eq_right h]
          · simp only [i, j, min_eq_right h, max_eq_left h, Bool.or_comm]
        by_cases h0 : i = 0
        · refine Or.inl ⟨j, greatest, fun x => ?_⟩
          rw [order, h0, get0, Bool.false_or]
        by_cases he : i = j
        · exact Or.inl ⟨j, greatest, fun x => by rw [order, he, Bool.or_self]⟩
        by_cases h9 : (i,j) = (4,9)
        · have ei : i = 4 := congrArg Prod.fst h9
          have ej : j = 9 := congrArg Prod.snd h9
          refine Or.inl ⟨9, by decide, fun x => ?_⟩
          rw [order, ei, ej]
          have hi : get x 4 = x 4 := by
            unfold get base
            rw [List.getD_append _ _ _ _ (by simp), ← show (4 : Fin 9).val = 4 from rfl, reads]
            exact Function.update_of_ne (by decide) _ _
          have hj : get x 9 = (x 0 || x 4) := by
            unfold get base
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp
          rw [hi, hj]
          cases x 0 <;> cases x 4 <;> rfl
        by_cases h10 : (i,j) = (3,10)
        · have ei : i = 3 := congrArg Prod.fst h10
          have ej : j = 10 := congrArg Prod.snd h10
          refine Or.inl ⟨10, by decide, fun x => ?_⟩
          rw [order, ei, ej]
          have hi : get x 3 = x 3 := by
            unfold get base
            rw [List.getD_append _ _ _ _ (by simp), ← show (3 : Fin 9).val = 3 from rfl, reads]
            exact Function.update_of_ne (by decide) _ _
          have hj : get x 10 = (x 0 || x 3) := by
            unfold get base
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp
          rw [hi, hj]
          cases x 0 <;> cases x 3 <;> rfl
        exact Or.inr ⟨i,j,by omega,by omega,greatest,h9,h10,order⟩
  rcases normalize with ⟨a, ha, aliasEq⟩ | ⟨i,j,h0,ord,upper,h9,h10,shape⟩
  · let drop (i : ℕ) := if i = 0 then 24 else if i ≥ 12 then i - 1 else i
    let ren (i : ℕ) := if i = 11 then drop a else drop i
    let mapped (g : Gate) : Gate := ⟨g.op, g.inputs.map ren⟩
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have carry (gs : List Gate) (w z : List Bool) (len : w.length = z.length + 1) (minLen : 11 ≤ z.length)
        (cap : z.length + gs.length ≤ 23) (relation : ∀ i : ℕ, w.getD i false = z.getD (ren i) false) :
        ∀ i : ℕ, (gs.foldl step w).getD i false = ((gs.map mapped).foldl step z).getD (ren i) false := by
      induction gs generalizing w z with
      | nil => exact relation
      | cons g gs ih =>
        let value := g.op.eval (g.inputs.map fun i => w.getD i false)
        have same : (g.inputs.map fun i => w.getD i false) = (mapped g).inputs.map (fun i => z.getD i false) := by
          simp only [mapped, List.map_map]
          exact List.map_congr_left (fun i _ => relation i)
        have next : step z (mapped g) = z ++ [value] := by
          change z ++ [g.op.eval ((mapped g).inputs.map fun i => z.getD i false)] = _
          rw [← same]
        change ∀ i, (gs.foldl step (w ++ [value])).getD i false =
          ((gs.map mapped).foldl step (step z (mapped g))).getD (ren i) false
        rw [next]
        have wlen : (w ++ [value]).length = w.length + 1 := by simp
        have zlen : (z ++ [value]).length = z.length + 1 := by simp
        have gslen : (g :: gs).length = gs.length + 1 := rfl
        refine ih (w ++ [value]) (z ++ [value]) (by omega) (by omega) (by omega) ?_
        intro i
        by_cases hi : i < w.length
        · rw [List.getD_append _ _ _ _ hi, relation]
          by_cases h : ren i < z.length
          · rw [List.getD_append _ _ _ _ h]
          · have big : ren i = 24 := by
              by_cases h11 : i = 11
              · simp only [ren, drop, ite_eq_left h11, ite_eq_right (show ¬ 12 ≤ a by omega)] at h ⊢
                by_cases a0 : a = 0
                · simp only [ite_eq_left a0]
                · simp only [ite_eq_right a0] at h
                  omega
              by_cases h0 : i = 0
              · simp only [ren, drop, ite_eq_right h11, ite_eq_left h0]
              simp only [ren, drop, ite_eq_right h11, ite_eq_right h0] at h
              split at h <;> omega
            rw [big, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · have ri : ren i = i - 1 := by
            have high : 12 ≤ i := by omega
            simp only [ren, drop, ite_eq_right (show i ≠ 11 by omega), ite_eq_right (show i ≠ 0 by omega), ite_eq_left high]
          rw [ri, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          congr 1
          omega
    let g₁ : Gate := ⟨GateOp.or, [0,4]⟩
    let g₂ : Gate := ⟨GateOp.or, [0,3]⟩
    let E : Circuit := ⟨g₁ :: g₂ :: C.gates.map mapped, ren C.output⟩
    have eok : FanInTwo E := by
      intro g hg
      change g ∈ g₁ :: g₂ :: C.gates.map mapped at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [g₁]
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [g₂]
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hg
      exact ⟨(legal d hd).1, by simpa only [mapped, List.length_map] using (legal d hd).2⟩
    have esize : E.size ≤ 14 := by
      change (g₁ :: g₂ :: C.gates.map mapped).length ≤ 14
      change C.gates.length ≤ 12 at hsize
      simp only [List.length_cons, List.length_map]
      omega
    refine short ⟨E,eok,esize,?_⟩
    intro x
    let z := List.ofFn x ++ [x 0 || x 4,x 0 || x 3]
    let w := base x ++ [get x a]
    have zl : z.length = 11 := by simp [z]
    have wl : w.length = 12 := by simp [w, lengthBase]
    have prep : step (step (List.ofFn x) g₁) g₂ = z := by
      have first : step (List.ofFn x) g₁ = List.ofFn x ++ [x 0 || x 4] := by
        change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false,(List.ofFn x).getD 4 false]] = _
        rw [← show (0 : Fin 9).val = 0 from rfl, ← show (4 : Fin 9).val = 4 from rfl, reads, reads, evOr]
      rw [first]
      change (List.ofFn x ++ [x 0 || x 4]) ++ [GateOp.or.eval
        [(List.ofFn x ++ [x 0 || x 4]).getD 0 false,(List.ofFn x ++ [x 0 || x 4]).getD 3 false]] = _
      rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp),
        ← show (0 : Fin 9).val = 0 from rfl, ← show (3 : Fin 9).val = 3 from rfl, reads, reads, evOr]
      simp only [List.append_assoc, z]
      rfl
    have baseRead (i : ℕ) (hi : i ≤ 10) : (base x).getD i false = z.getD (drop i) false := by
      by_cases hz : i = 0
      · subst i
        change get x 0 = z.getD 24 false
        rw [get0, List.getD_eq_default _ _ (by omega)]
      have he : drop i = i := by simp only [drop, ite_eq_right hz, ite_eq_right (show ¬ 12 ≤ i by omega)]
      rw [he]
      by_cases low : i < 9
      · let j : Fin 9 := ⟨i,low⟩
        change (List.ofFn (Function.update x 0 false) ++ _).getD j.val false =
          (List.ofFn x ++ _).getD j.val false
        rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp), reads, reads]
        exact Function.update_of_ne (by intro h; exact hz (congrArg Fin.val h)) _ _
      · change (List.ofFn (Function.update x 0 false) ++ _).getD i false = (List.ofFn x ++ _).getD i false
        rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt low),
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt low)]
        simp
    have related (i : ℕ) : w.getD i false = z.getD (ren i) false := by
      by_cases lo : i ≤ 10
      · rw [show ren i = drop i from ite_eq_right (by omega)]
        exact (List.getD_append _ _ _ _ (by rw [lengthBase]; omega)).trans (baseRead i lo)
      by_cases middle : i = 11
      · subst i
        change (base x ++ [get x a]).getD 11 false = z.getD (drop a) false
        rw [List.getD_append_right _ _ _ _ (by rw [lengthBase]), lengthBase]
        change get x a = z.getD (drop a) false
        exact baseRead a ha
      have h : 12 ≤ i := by omega
      have ri : ren i = i - 1 := by
        simp only [ren, drop, ite_eq_right middle, ite_eq_right (show i ≠ 0 by omega), ite_eq_left h]
      rw [ri, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have reach : C.eval w = ((C.gates.map mapped).foldl step z).getD (ren C.output) false := by
      exact carry C.gates w z (by omega) (by omega) (by change C.gates.length ≤ 12 at hsize; omega) related C.output
    change ((C.gates.map mapped).foldl step (step (step (List.ofFn x) g₁) g₂)).getD (ren C.output) false = f x
    rw [prep, ← reach]
    exact (congrArg C.eval (congrArg (fun b => base x ++ [b]) (aliasEq x).symm)).trans (ok x)
  · have witness (x : Fin 9 → Bool) : C.eval (base x ++ [get x i || get x j]) = f x := by
      rw [← shape x]
      exact ok x
    let rawPairs : List (ℕ × ℕ) := [(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3),
      (2,4),(2,6),(2,7),(2,8),(3,4),(3,6),(4,6),(6,7)]
    let computedPairs : List (ℕ × ℕ) := [(1,9),(1,10),(2,9),(2,10),(3,9),(4,10),(6,9),(6,10),(9,10)]
    let p : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
    let perm (k : ℕ) := if hk : k < 9 then (p ⟨k,hk⟩).val else k
    have fixed : p 0 = 0 ∧ p 3 = 3 ∧ p 4 = 4 := by decide
    have holdsZero : ∀ k : Fin 9, p k = 0 ↔ k = 0 := by decide
    have respects (x : Fin 9 → Bool) : f (fun k => x (p k)) = f x := by
      simp only [f, List.any_cons, List.any_nil, Bool.or_false]
      change (x 0 && x 5 || (x 5 && x 8 || (x 8 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 1 || (x 5 && x 7 || (x 8 && x 6 || (x 3 && x 2 || (x 1 && x 6 || (x 7 && x 2 || (x 2 && x 1)))))))))))) =
        (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5))))))))))))
      ac_rfl
    have orbit : ∀ a b : Fin 11, 0 < a.val → a.val < b.val → (a.val,b.val) ≠ (4,9) → (a.val,b.val) ≠ (3,10) →
        (a.val,b.val) ∈ rawPairs ++ computedPairs ∨
        (min (perm a.val) (perm b.val), max (perm a.val) (perm b.val)) ∈ rawPairs ++ computedPairs := by
      decide
    rcases orbit ⟨i, by omega⟩ ⟨j, by omega⟩ h0 ord h9 h10 with here | reflected
    · rcases List.mem_append.mp here with hr | hc
      · exact raw i j hr C legal hsize witness
      · exact computed i j hc C legal hsize witness
    let a := min (perm i) (perm j)
    let b := max (perm i) (perm j)
    let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map perm⟩
    let D : Circuit := ⟨C.gates.map rename, perm C.output⟩
    have legalD : FanInTwo D := by
      intro g hg
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
      exact ⟨(legal t ht).1, by simpa only [rename, List.length_map] using (legal t ht).2⟩
    have sizeD : D.size ≤ 12 := by
      change (C.gates.map rename).length ≤ 12
      rw [List.length_map]
      exact hsize
    have readPerm (x : Fin 9 → Bool) (k : ℕ) : get (fun l => x (p l)) k = get x (perm k) := by
      by_cases hk : k < 9
      · let t : Fin 9 := ⟨k,hk⟩
        rw [show perm k = (p t).val from dite_eq_left hk]
        change (base (fun l => x (p l))).getD t.val false = (base x).getD (p t).val false
        unfold base
        rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp), reads, reads]
        by_cases ht : t = 0
        · rw [ht, fixed.1, Function.update_self, Function.update_self]
        · rw [Function.update_of_ne ht, Function.update_of_ne (fun e => ht ((holdsZero t).mp e))]
      · rw [show perm k = k from dite_eq_right hk]
        unfold get base
        rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hk),
            List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hk)]
        simp only [List.length_ofFn, fixed.1, fixed.2.1, fixed.2.2]
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
    have translate (gs : List Gate) (w z : List Bool) (len : w.length = z.length) (enough : 12 ≤ w.length)
        (rel : ∀ k : ℕ, w.getD k false = z.getD (perm k) false) :
        ∀ k : ℕ, (gs.foldl step w).getD k false = ((gs.map rename).foldl step z).getD (perm k) false := by
      induction gs generalizing w z with
      | nil => exact rel
      | cons g gs ih =>
        let v := g.op.eval (g.inputs.map fun k => w.getD k false)
        have same : (g.inputs.map fun k => w.getD k false) = (rename g).inputs.map (fun k => z.getD k false) := by
          simp only [rename, List.map_map]
          exact List.map_congr_left (fun k _ => rel k)
        have next : step z (rename g) = z ++ [v] := by
          change z ++ [g.op.eval ((rename g).inputs.map fun k => z.getD k false)] = _
          rw [← same]
        change ∀ k, (gs.foldl step (w ++ [v])).getD k false = ((gs.map rename).foldl step (step z (rename g))).getD (perm k) false
        rw [next]
        have more : (w ++ [v]).length = w.length + 1 := by simp
        refine ih (w ++ [v]) (z ++ [v]) (by simp [len]) (by omega) ?_
        intro k
        by_cases low : k < w.length
        · have other : perm k < z.length := by
            by_cases h9 : k < 9
            · rw [show perm k = (p ⟨k,h9⟩).val from dite_eq_left h9]
              have := (p ⟨k,h9⟩).isLt
              omega
            · rw [show perm k = k from dite_eq_right h9]
              omega
          rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ other, rel]
        · rw [show perm k = k from dite_eq_right (show ¬ k < 9 by omega),
            List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), len]
    have flipped (x : Fin 9 → Bool) : D.eval (base x ++ [get x a || get x b]) = f x := by
      let y : Fin 9 → Bool := fun k => x (p k)
      let w := base y ++ [get y i || get y j]
      let z := base x ++ [get x a || get x b]
      have lenW : w.length = 12 := by simp [w, lengthBase]
      have lenZ : z.length = 12 := by simp [z, lengthBase]
      have data : (get y i || get y j) = (get x a || get x b) := by
        simp only [y, readPerm]
        rcases le_total (perm i) (perm j) with le | le
        · simp only [a, b, min_eq_left le, max_eq_right le]
        · simp only [a, b, min_eq_right le, max_eq_left le, Bool.or_comm]
      have rel (k : ℕ) : w.getD k false = z.getD (perm k) false := by
        by_cases hk : k < 11
        · have hperm : perm k < 11 := by
            by_cases hh : k < 9
            · rw [show perm k = (p ⟨k,hh⟩).val from dite_eq_left hh]
              have := (p ⟨k,hh⟩).isLt
              omega
            · rwa [show perm k = k from dite_eq_right hh]
          exact (List.getD_append _ _ _ _ (by rw [lengthBase]; exact hk)).trans
            ((readPerm x k).trans (List.getD_append _ _ _ _ (by rw [lengthBase]; exact hperm)).symm)
        have he : perm k = k := dite_eq_right (show ¬ k < 9 by omega)
        change (base y ++ [get y i || get y j]).getD k false = (base x ++ [get x a || get x b]).getD (perm k) false
        rw [he, List.getD_append_right _ _ _ _ (by rw [lengthBase]; omega),
          List.getD_append_right _ _ _ _ (by rw [lengthBase]; omega), lengthBase, lengthBase, data]
      have eq : C.eval w = D.eval z := translate C.gates w z (lenW.trans lenZ.symm) (le_of_eq lenW.symm) rel C.output
      exact eq.symm.trans ((witness y).trans (respects x))
    rcases List.mem_append.mp reflected with hr | hc
    · exact raw a b hr D legalD sizeD flipped
    · exact computed a b hc D legalD sizeD flipped
