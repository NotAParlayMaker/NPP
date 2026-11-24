import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3077_814
    (remove :
      let read := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
      let step := fun (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
        w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
          else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1]
      let shift := fun i : Fin 26 =>
        if i.val = 10 then (9 : Fin 26)
        else if 10 < i.val ∧ i.val < 25 then Fin.ofNat 26 (i.val - 1) else i
      ∀ (W : List Bool) (gs : List (Fin 3 × Fin 26 × Fin 26)) (o : Fin 26),
        W.length = 10 → gs.length ≤ 13 →
        (gs.foldl step (W ++ [W.getD 9 false])).getD o.val false =
          ((gs.map fun g => (g.1, shift g.2.1, shift g.2.2)).foldl step W).getD (shift o).val false)
    (short :
      let read := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
      let step := fun (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
        w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
          else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1]
      let bits := fun (x : ℕ) (i : Fin 9) => x.testBit i.val
      let seed := fun x => List.ofFn (bits x) ++ [bits x 0 || bits x 4]
      let target := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => bits x (Fin.ofNat 9 (e / 10)) && bits x (Fin.ofNat 9 (e % 10)))
      ∀ (o : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)), gs.length ≤ 13 →
        (∀ i < 9, ∃ g ∈ gs, g.2.1.val = i ∨ g.2.2.val = i) →
        ∃ x < 512, (gs.foldl step (seed x)).getD o.val false ≠ target x)
    (genuine :
      let read := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
      let step := fun (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
        w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
          else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1]
      let bits := fun (x : ℕ) (i : Fin 9) => x.testBit i.val
      let seed := fun x => List.ofFn (bits x) ++ [bits x 0 || bits x 4]
      let target := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => bits x (Fin.ofNat 9 (e / 10)) && bits x (Fin.ofNat 9 (e % 10)))
      ∀ (b o : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)),
        b.val ∈ ([1, 2, 3, 5, 6, 7, 8] : List ℕ) → gs.length ≤ 13 →
        (∀ i < 9, ∃ g ∈ gs, g.2.1.val = i ∨ g.2.2.val = i) →
        ∃ x < 512, (((1, 9, b) :: gs).foldl step (seed x)).getD o.val false ≠ target x) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b o gs hlen huse ha hb hcoverage
  let read := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
  let step := fun (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
    w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
      else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1]
  let shift := fun i : Fin 26 =>
    if i.val = 10 then (9 : Fin 26)
    else if 10 < i.val ∧ i.val < 25 then Fin.ofNat 26 (i.val - 1) else i
  let bits := fun (x : ℕ) (i : Fin 9) => x.testBit i.val
  let seed := fun x => List.ofFn (bits x) ++ [bits x 0 || bits x 4]
  let target := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => bits x (Fin.ofNat 9 (e / 10)) && bits x (Fin.ofNat 9 (e % 10)))
  have hLen (x : ℕ) : (seed x).length = 10 := by simp [seed]
  have h9 (x : ℕ) : (seed x).getD 9 false = (bits x 0 || bits x 4) := by
    change (List.ofFn (bits x) ++ [bits x 0 || bits x 4]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hRaw (x : ℕ) (i : Fin 9) : (seed x).getD i.val false = bits x i := by
    change (List.ofFn (bits x) ++ [bits x 0 || bits x 4]).getD i.val false = _
    rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
  have hAbs : ∀ a b : Bool, ((a || b) || a) = (a || b) ∧ ((a || b) || b) = (a || b) := by decide
  have hComm (W : List Bool) (u v : Fin 26) : step W (1, u, v) = step W (1, v, u) := by
    change W ++ [read W u || read W v] = W ++ [read W v || read W u]
    rw [Bool.or_comm]
  have solve (v : Fin 26) (h25 : v.val ≠ 25) :
      ∃ x < 512, (((1, 9, v) :: gs).foldl step (seed x)).getD o.val false ≠ target x := by
    by_cases eligible : v.val ∈ ([1, 2, 3, 5, 6, 7, 8] : List ℕ)
    · exact genuine v o gs eligible hlen hcoverage
    have hCases : v.val = 0 ∨ v.val = 4 ∨ 9 ≤ v.val := by
      simp at eligible
      omega
    have hRed (x : ℕ) : step (seed x) (1, 9, v) = seed x ++ [(seed x).getD 9 false] := by
      change seed x ++ [read (seed x) 9 || read (seed x) v] = _
      have read9 : read (seed x) 9 = (seed x).getD 9 false := rfl
      rw [read9]
      have hv : read (seed x) v = (seed x).getD v.val false := by simp [read, h25]
      rw [hv]
      rcases hCases with h | h | h
      · have h0 : (seed x).getD 0 false = bits x 0 := hRaw x 0
        rw [h, h0, h9]
        rw [(hAbs _ _).1]
      · have h4 : (seed x).getD 4 false = bits x 4 := hRaw x 4
        rw [h, h4, h9]
        rw [(hAbs _ _).2]
      · by_cases he : v.val = 9
        · simp [he]
        · have hf : (seed x).getD v.val false = false :=
            List.getD_eq_default _ _ (by rw [hLen]; omega)
          rw [hf, Bool.or_false]
    have hLow (w : Fin 26) (hw : w.val < 9) : shift w = w := by
      simp [shift, show w.val ≠ 10 by omega, show ¬ 10 < w.val by omega]
    let gs' := gs.map fun g => (g.1, shift g.2.1, shift g.2.2)
    have hLength : gs'.length ≤ 13 := by simpa only [gs', List.length_map] using hlen
    have hCov' : ∀ i < 9, ∃ g ∈ gs', g.2.1.val = i ∨ g.2.2.val = i := by
      intro i hi
      obtain ⟨g, hg, hh⟩ := hcoverage i hi
      refine ⟨(g.1, shift g.2.1, shift g.2.2), List.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
      rcases hh with h | h
      · left
        change (shift g.2.1).val = i
        rwa [hLow g.2.1 (h.symm ▸ hi)]
      · right
        change (shift g.2.2).val = i
        rwa [hLow g.2.2 (h.symm ▸ hi)]
    obtain ⟨x, hx, hOut⟩ := short (shift o) gs' hLength hCov'
    refine ⟨x, hx, ?_⟩
    simp only [List.foldl_cons]
    rw [hRed]
    rw [remove (seed x) gs o (hLen x) hlen]
    exact hOut
  rcases huse with h | h
  · have he : a = 9 := Fin.ext h
    subst a
    exact solve b hb
  · have he : b = 9 := Fin.ext h
    subst b
    obtain ⟨x, hx, hOut⟩ := solve a ha
    refine ⟨x, hx, ?_⟩
    change (((1, a, 9) :: gs).foldl step (seed x)).getD o.val false ≠ target x
    simp only [List.foldl_cons] at hOut ⊢
    rwa [hComm]
