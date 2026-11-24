import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2760_1
    (h0 : ∀ D : Circuit, FanInTwo D → D.size ≤ 12 → ¬ ∀ x : Fin 8 → Bool,
      D.eval (List.ofFn x ++ [!x 0]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 4 && x 7)))
    (h1 : ∀ D : Circuit, FanInTwo D → D.size ≤ 12 → ¬ ∀ x : Fin 8 → Bool,
      D.eval (List.ofFn x ++ [!x 1]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 4 && x 7)))
    (project : ∀ (C : Circuit) (p : List ℕ) (u v : List Bool), FanInTwo C →
      u.length = p.length → v.length = p.length →
      (∀ i : Fin p.length, p.get i < 9 → u.getD i false = v.getD i false) →
      C.eval u ≠ C.eval v →
      let run := fun y : List Bool => C.eval (p.map (fun k => y.getD k false))
      (∃ y z : List Bool, y.length = 9 ∧ z.length = 9 ∧ run y ≠ run z) →
      ∃ D : Circuit, FanInTwo D ∧ D.size < C.size ∧ ∀ y : List Bool, y.length = 9 → D.eval y = run y) :
∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, (1 : ℕ) ≤ x3 ∧ x3 < (9 : ℕ)) →       (4 : ℕ) ∈ x1 ∨ (6 : ℕ) ∈ x1 ∨ (7 : ℕ) ∈ x1 →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  let edges9 (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let edges8 (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 4 && x 7)
  let bank9 (a b : Fin 9) (x : Fin 9 → Bool) := List.ofFn x ++ [!(x 0), x a || x b]
  let bank8 (m : Fin 8) (x : Fin 8 → Bool) := List.ofFn x ++ [!(x m)]
  let special (i : Fin 9) : Prop := i = 4 ∨ i = 6 ∨ i = 7
  let chosen (a b : Fin 9) : Fin 9 := if a = 4 ∨ a = 6 ∨ a = 7 then a else b
  let marker (s : Fin 9) : Fin 8 := if s = 4 then 0 else 1
  let indices (s : Fin 9) : List ℕ :=
    if s = 4 then [0,1,2,3,9,4,5,6,7]
    else if s = 6 then [1,0,4,7,5,2,9,6,3]
    else [1,2,3,7,5,0,6,9,4]
  let refs (a b : Fin 9) : List ℕ :=
    let is := indices (chosen a b)
    is ++ [8,is.getD (if a = 4 ∨ a = 6 ∨ a = 7 then b.val else a.val) 9]
  let bits9 (r : Fin 512) (i : Fin 9) := r.val.testBit i.val
  let flipped (s : Fin 9) (r : Fin 512) : Fin 512 := Fin.ofNat 512 (r.val ^^^ (1 <<< s.val))
  have length11 : ∀ a b : Fin 9, (refs a b).length = 11 := by decide +kernel
  have getPair : ∀ a b : Fin 9, (special a ∨ special b) → a ≠ 0 → b ≠ 0 →
      ∃ r : Fin 512, let t := flipped (chosen a b) r
        edges9 (bits9 r) ≠ edges9 (bits9 t) ∧ ∀ i : Fin 11, (refs a b).getD i.val 9 < 9 →
          (bank9 a b (bits9 r)).getD i.val false = (bank9 a b (bits9 t)).getD i.val false := by
    dsimp only [special,flipped,chosen,edges9,bits9,refs,indices,bank9]; decide +kernel
  intro xs hl hall hs C hf hsize
  obtain ⟨a,b,rfl⟩ : ∃ a b : Nat, xs = [a,b] := by
    cases xs with
    | nil => simp at hl
    | cons a xs => cases xs with
      | nil => simp at hl
      | cons b xs => cases xs with
        | nil => exact ⟨a,b,rfl⟩
        | cons c xs => simp at hl
  have ha := hall a (by simp)
  have hb := hall b (by simp)
  let i : Fin 9 := ⟨a,ha.2⟩
  let j : Fin 9 := ⟨b,hb.2⟩
  have hs' : special i ∨ special j := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    dsimp only [special]; rcases hs with (hh|hh)|(hh|hh)|(hh|hh) <;> first | exact Or.inl (by first | left; exact Fin.ext hh.symm | right; left; exact Fin.ext hh.symm | right; right; exact Fin.ext hh.symm) | exact Or.inr (by first | left; exact Fin.ext hh.symm | right; left; exact Fin.ext hh.symm | right; right; exact Fin.ext hh.symm)
  by_contra! he
  have hread (x : Fin 9 → Bool) (k : Fin 9) : (List.ofFn x ++ [!x 0]).getD k.val false = x k := by
    fin_cases k <;> rfl
  have correct : ∀ x, C.eval (bank9 i j x) = edges9 x := by
    intro x
    have step := Classical.not_not.mp (he x)
    have evalOr (v : List Bool) : GateOp.or.eval v = v.any id := rfl
    simp only [List.map_cons,List.map_nil,evalOr,List.any_cons,List.any_nil,Bool.or_false,id_eq] at step
    dsimp only [bank9]
    simp only [show a = i.val from rfl,show b = j.val from rfl,hread,List.append_assoc,List.cons_append,List.nil_append] at step
    simpa only [edges9] using step
  let s := chosen i j
  let old (x : Fin 8 → Bool) (k : Fin 9) := (List.ofFn x).getD ((indices s).getD k.val 9) false
  have ss : special s := by
    dsimp only [s,chosen]; split
    · assumption
    · exact hs'.resolve_left (by assumption)
  have oldTarget (x : Fin 8 → Bool) : edges9 (old x) = edges8 x := by
    change edges9 (fun k : Fin 9 => (List.ofFn x).getD ((indices s).getD k.val 9) false) = _
    rcases ss with h|h|h <;> rw [h]
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && false) || (false && x 0) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 4 && x 7))
      generalize x 0 = b0
      generalize x 1 = b1
      generalize x 2 = b2
      generalize x 3 = b3
      generalize x 4 = b4
      generalize x 5 = b5
      generalize x 6 = b6
      generalize x 7 = b7
      revert b0 b1 b2 b3 b4 b5 b6 b7
      decide +kernel
    · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 7) || (x 7 && x 5) || (x 5 && x 1) || (x 1 && x 2) || (x 0 && false) || (x 4 && x 6) || (x 7 && x 3) || (x 2 && x 6) || (false && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 4 && x 7))
      generalize x 0 = b0
      generalize x 1 = b1
      generalize x 2 = b2
      generalize x 3 = b3
      generalize x 4 = b4
      generalize x 5 = b5
      generalize x 6 = b6
      generalize x 7 = b7
      revert b0 b1 b2 b3 b4 b5 b6 b7
      decide +kernel
    · change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 7) || (x 7 && x 5) || (x 5 && x 1) || (x 1 && x 0) || (x 2 && x 6) || (x 3 && false) || (x 7 && x 4) || (x 0 && false) || (x 6 && x 4) || (x 4 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 4 && x 7))
      generalize x 0 = b0
      generalize x 1 = b1
      generalize x 2 = b2
      generalize x 3 = b3
      generalize x 4 = b4
      generalize x 5 = b5
      generalize x 6 = b6
      generalize x 7 = b7
      revert b0 b1 b2 b3 b4 b5 b6 b7
      decide +kernel
  have chart (x : Fin 8 → Bool) : (refs i j).map (fun k => (bank8 (marker s) x).getD k false) = bank9 i j (old x) := by
    have first : (indices s).map (fun k => (bank8 (marker s) x).getD k false) = List.ofFn (old x) := by
      dsimp only [old]; rcases ss with h|h|h <;> rw [h] <;> rfl
    have marked : old x 0 = x (marker s) := by
      dsimp only [old]; rcases ss with h|h|h <;> rw [h] <;> rfl
    have zero : old x s = false := by
      dsimp only [old]; rcases ss with h|h|h <;> rw [h] <;> rfl
    have kth (k : Fin 9) : (bank8 (marker s) x).getD ((indices s).getD k.val 9) false = old x k := by
      dsimp only [old]; rcases ss with h|h|h <;> rw [h] <;> fin_cases k <;> rfl
    dsimp only [refs,bank9]; simp only [List.map_append,List.map_cons,List.map_nil]
    change (indices s).map _ ++ [_,(bank8 (marker s) x).getD ((indices s).getD (if i = 4 ∨ i = 6 ∨ i = 7 then j.val else i.val) 9) false] = _
    rw [first]; congr 1
    have eight : (bank8 (marker s) x).getD 8 false = !(x (marker s)) := rfl
    by_cases h : special i
    · have eq : s=i := ite_eq_left h
      have zi : old x i = false := eq ▸ zero
      rw [ite_eq_left h,kth,eight,marked,zi,Bool.false_or]
    · have eq : s=j := ite_eq_right h
      have zj : old x j = false := eq ▸ zero
      rw [ite_eq_right h,kth,eight,marked,zj,Bool.or_false]
  obtain ⟨r,hr⟩ := getPair i j hs' (fun h => by have := congrArg Fin.val h; change a = 0 at this; omega) (fun h => by have := congrArg Fin.val h; change b = 0 at this; omega)
  let t := flipped s r
  have sim (x : Fin 8 → Bool) : C.eval ((refs i j).map (fun k => (bank8 (marker s) x).getD k false)) = edges8 x := by rw [chart,correct,oldTarget]
  obtain ⟨D,hd,hlen,hw⟩ := project C (refs i j) (bank9 i j (bits9 r)) (bank9 i j (bits9 t)) hf (by simp [bank9,length11]) (by simp [bank9,length11]) (by
    intro k hk
    have hlen' : k.val < 11 := k.isLt.trans_eq (length11 i j)
    apply hr.2 ⟨k.val,hlen'⟩
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem k.isLt,Option.getD_some,List.get_eq_getElem] using hk) (by simpa only [correct] using hr.1) (by
    refine ⟨bank8 (marker s) (fun _=>false),bank8 (marker s) (fun _=>true),by simp [bank8],by simp [bank8],?_⟩
    change C.eval _ ≠ C.eval _
    rw [sim,sim]; decide)
  have final (x : Fin 8 → Bool) : D.eval (bank8 (marker s) x) = edges8 x := (hw _ (by simp [bank8])).trans (sim x)
  by_cases hh : s = 4
  · exact h0 D hd (by omega) (by simpa [marker,hh,bank8,edges8] using final)
  · exact h1 D hd (by omega) (by simpa [marker,hh,bank8,edges8] using final)
