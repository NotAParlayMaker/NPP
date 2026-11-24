import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Delete a second OR that duplicates the first. The other OR has one of four
-- distinct third inputs after applying the graph symmetry.
theorem PEqualNP.Outside.R_meta_3855_731
    (short : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (triple : ∀ i : Fin 9, i.val ∈ ([1, 2, 3, 6] : List ℕ) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x i]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) →       ↑x2 ≤ [(0 : ℕ), (5 : ℕ), (8 : ℕ), (3 : ℕ), (4 : ℕ), (1 : ℕ), (7 : ℕ), (6 : ℕ), (2 : ℕ)].getD ↑x2 ↑x2 →         ↑x1 ≠ (25 : ℕ) →           ↑x2 ≠ (25 : ℕ) →             (∀ x10 < (9 : ℕ), ∃ x12 ∈ x4, ↑x12.2.1 = x10 ∨ ↑x12.2.2 = x10) →               ∃ x11 < (512 : ℕ),                 have x12 : Fin (9 : ℕ) → Bool := fun (x12 : Fin (9 : ℕ)) => x11.testBit ↑x12;                 have x13 : List Bool → Fin (26 : ℕ) → Bool := fun (x13 : List Bool) (x14 : Fin (26 : ℕ)) => if ↑x14 = (25 : ℕ) then Bool.true else x13.getD (↑x14) Bool.false;                 have x14 : List Bool := List.foldl (fun (x14 : List Bool) (x15 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x14 ++ [if ↑x15.1 = (0 : ℕ) then x13 x14 x15.2.1 && x13 x14 x15.2.2 else if ↑x15.1 = (1 : ℕ) then x13 x14 x15.2.1 || x13 x14 x15.2.2 else !x13 x14 x15.2.1]) (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);                 x14.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x15 : ℕ) => x12 (Fin.ofNat (9 : ℕ) (x15 / (10 : ℕ))) && x12 (Fin.ofNat (9 : ℕ) (x15 % (10 : ℕ))) := by
  intro a b out L hL ha hRep _ha25 hb25 _hRaw
  let F (x : Fin 9 → Bool) :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let G (x : Fin 9 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have targetEq (x : Fin 9 → Bool) : F x = G x := by
    dsimp only [F, G, List.any_cons, List.any_nil]
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 ||
      (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 ||
      (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = _
    simp only [Bool.or_false, Bool.or_assoc]
  let T := Fin 3 × Fin 26 × Fin 26
  let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
  let src (w : List Bool) (g : T) :=
    w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
      else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1]
  let dst (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let translate (r : ℕ → ℕ) (g : T) : Gate :=
    let a := g.2.1.val
    let b := g.2.2.val
    if g.1.val = 0 then
      if a = 25 then
        if b = 25 then ⟨GateOp.and, []⟩ else ⟨GateOp.and, [r b]⟩
      else if b = 25 then ⟨GateOp.and, [r a]⟩ else ⟨GateOp.and, [r a, r b]⟩
    else if g.1.val = 1 then
      if a = 25 ∨ b = 25 then ⟨GateOp.and, []⟩ else ⟨GateOp.or, [r a, r b]⟩
    else if a = 25 then ⟨GateOp.or, []⟩ else ⟨GateOp.not, [r a]⟩
  have allowed (r : ℕ → ℕ) (gs : List T) (o : ℕ) :
      FanInTwo ⟨gs.map (translate r), o⟩ := by
    intro g hg
    change g ∈ gs.map (translate r) at hg
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg
    dsimp only [translate]
    split_ifs <;> exact ⟨by simp, by simp⟩
  have value (r : ℕ → ℕ) (w z : List Bool) (p : T)
      (hRead : ∀ i : ℕ, w.getD i false = z.getD (r i) false) :
      (translate r p).op.eval ((translate r p).inputs.map (fun i => z.getD i false)) =
        (if p.1.val = 0 then read w p.2.1 && read w p.2.2
          else if p.1.val = 1 then read w p.2.1 || read w p.2.2 else !read w p.2.1) := by
    by_cases ha : p.2.1.val = 25 <;> by_cases hb : p.2.2.val = 25 <;>
      by_cases h0 : p.1.val = 0 <;> by_cases h1 : p.1.val = 1 <;>
      simp only [translate, read, ha, hb, h0, h1, ite_true, ite_false, Nat.one_ne_zero,
        or_true, or_false, List.map_cons, List.map_nil, hRead]
    all_goals try rfl
    all_goals cases z.getD (r p.2.1.val) false <;> cases z.getD (r p.2.2.val) false <;> rfl
  have simulate (r : ℕ → ℕ) (left right : List Bool)
      (hRead : ∀ (zs : List Bool) i, (left ++ zs).getD i false = (right ++ zs).getD (r i) false)
      (gs : List T) (ys : List Bool) :
      ∃ zs, gs.foldl src (left ++ ys) = left ++ zs ∧
        (gs.map (translate r)).foldl dst (right ++ ys) = right ++ zs := by
    induction gs generalizing ys with
    | nil => exact ⟨ys, rfl, rfl⟩
    | cons p ps ih =>
      let v := if p.1.val = 0 then read (left ++ ys) p.2.1 && read (left ++ ys) p.2.2
        else if p.1.val = 1 then read (left ++ ys) p.2.1 || read (left ++ ys) p.2.2
        else !read (left ++ ys) p.2.1
      have hs : src (left ++ ys) p = left ++ (ys ++ [v]) := by
        change (left ++ ys) ++ [v] = _
        exact List.append_assoc _ _ _
      have hd : dst (right ++ ys) (translate r p) = right ++ (ys ++ [v]) := by
        change (right ++ ys) ++ [((translate r p).op.eval ((translate r p).inputs.map
          (fun i => (right ++ ys).getD i false)))] = _
        rw [value r _ _ p (hRead ys)]
        exact List.append_assoc _ _ _
      rw [List.foldl_cons, List.map_cons, List.foldl_cons, hs, hd]
      exact ih (ys ++ [v])
  let first (x : Fin 9 → Bool) := x 0 || x 4
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [first x]
  let second (x : Fin 9 → Bool) := first x || read (seed x) b
  have base (x : Fin 9 → Bool) : src (seed x) (1, a, b) = seed x ++ [second x] := by
    have hRead : read (seed x) a = first x := by
      dsimp only [read]
      rw [ha, ite_eq_right (by decide)]
      change (List.ofFn x ++ [first x]).getD 9 false = _
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    change _ ++ [if (1 : Fin 3).val = 0 then _ else if (1 : Fin 3).val = 1 then _ else _] = _
    simp only [ite_eq_right (show (1 : Fin 3).val ≠ 0 by decide),
      ite_eq_left (show (1 : Fin 3).val = 1 by rfl), hRead, second]
  by_contra! hAgree
  have matchAll (x : Fin 9 → Bool) :
      (L.foldl src (seed x ++ [second x])).getD out.val false = F x := by
    let bits := BitVec.ofBoolListLE (List.ofFn x)
    have hmask : bits.toNat < 512 := by simpa using bits.isLt
    have hx : (fun i : Fin 9 => bits.toNat.testBit i.val) = x := by
      funext i
      change bits.getLsbD i.val = x i
      dsimp only [bits]
      rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have he := hAgree bits.toNat hmask
    change ¬ (((1, a, b) :: L).foldl src (seed (fun i => bits.toNat.testBit i.val))).getD
      out.val false ≠ F (fun i => bits.toNat.testBit i.val) at he
    rw [hx, List.foldl_cons, base] at he
    exact not_not.mp he
  have kCases : (b.val = 0 ∨ b.val = 4 ∨ 9 ≤ b.val) ∨
      b.val ∈ ([1, 2, 3, 6] : List ℕ) := by
    have finite : ∀ v : Fin 26,
        v.val ≤ ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ).getD v.val v.val →
        (v.val = 0 ∨ v.val = 4 ∨ 9 ≤ v.val) ∨ v.val ∈ ([1, 2, 3, 6] : List ℕ) := by decide
    exact finite b hRep
  have raw (x : Fin 9 → Bool) (i : Fin 9) : read (seed x) ⟨i.val, by omega⟩ = x i := by
    change (if i.val = 25 then true else (List.ofFn x ++ [first x]).getD i.val false) = _
    rw [ite_eq_right (by omega), List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp),
      List.getElem_ofFn]
  rcases kCases with hAlias | hReal
  · have same (x : Fin 9 → Bool) : second x = first x := by
      rcases hAlias with h0 | h4 | hge
      · have hbyte : b = (0 : Fin 26) := Fin.ext h0
        have hr : read (seed x) b = x 0 := by rw [hbyte]; exact raw x 0
        change ((x 0 || x 4) || read (seed x) b) = (x 0 || x 4)
        rw [hr]
        cases x 0 <;> cases x 4 <;> rfl
      · have hbyte : b = (4 : Fin 26) := Fin.ext h4
        have hr : read (seed x) b = x 4 := by rw [hbyte]; exact raw x 4
        change ((x 0 || x 4) || read (seed x) b) = (x 0 || x 4)
        rw [hr]
        cases x 0 <;> cases x 4 <;> rfl
      · by_cases h9 : b.val = 9
        · have hv : read (seed x) b = first x := by
            dsimp only [read]
            rw [h9, ite_eq_right (by decide)]
            change (List.ofFn x ++ [first x]).getD 9 false = _
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp
          change (first x || read (seed x) b) = _
          rw [hv, Bool.or_self]
        · have hv : read (seed x) b = false := by
            dsimp only [read]
            rw [ite_eq_right hb25]
            exact List.getD_eq_default _ _ (by simp [seed]; omega)
          change (first x || read (seed x) b) = _
          rw [hv, Bool.or_false]
    let ρ (i : ℕ) := if i < 10 then i else i - 1
    have aliasRead (x : Fin 9 → Bool) (ys : List Bool) (i : ℕ) :
        ((seed x ++ [second x]) ++ ys).getD i false =
          (seed x ++ ys).getD (ρ i) false := by
      have hs : (seed x).length = 10 := by simp [seed]
      by_cases h : i < 10
      · rw [show ρ i = i from ite_eq_left h, List.append_assoc]
        rw [List.getD_append (seed x) ([second x] ++ ys) false i (by omega),
          List.getD_append (seed x) ys false i (by omega)]
      · rw [show ρ i = i - 1 from ite_eq_right h]
        by_cases h10 : i = 10
        · subst i
          rw [List.append_assoc]
          have hl : (seed x ++ ([second x] ++ ys)).getD 10 false = second x := by
            rw [List.getD_append_right (seed x) ([second x] ++ ys) false 10 (by omega), hs]
            rfl
          have hr : (seed x ++ ys).getD 9 false = first x := by
            rw [List.getD_append (seed x) ys false 9 (by omega)]
            change (List.ofFn x ++ [first x]).getD 9 false = _
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp
          rw [show 10 - 1 = 9 from rfl, hl, hr]
          exact same x
        · have hgt : 11 ≤ i := by omega
          rw [List.getD_append_right _ _ _ _ (by simp; omega),
            List.getD_append_right _ _ _ _ (by omega)]
          have he : i - (seed x ++ [second x]).length = (i - 1) - (seed x).length := by
            simp only [List.length_append, List.length_singleton, hs]
            omega
          rw [he]
    let init : Gate := ⟨GateOp.or, [0,4]⟩
    let C : Circuit := ⟨init :: L.map (translate ρ), ρ out.val⟩
    apply short
    refine ⟨C, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ init :: L.map (translate ρ) at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp [init], by simp [init]⟩
      · exact allowed ρ L (ρ out.val) g hg
    · change (init :: L.map (translate ρ)).length ≤ 14
      simp only [List.length_cons, List.length_map]
      omega
    · intro x
      obtain ⟨ys, hf, hd⟩ := simulate ρ (seed x ++ [second x]) (seed x) (aliasRead x) L []
      simp only [List.append_nil] at hf hd
      have initWire : dst (List.ofFn x) init = seed x := by
        have getRaw (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
          rw [List.getD_eq_getElem (List.ofFn x) false (n := i.val) (by simpa using i.isLt), List.getElem_ofFn]
        change List.ofFn x ++ [(List.ofFn x).getD (0 : Fin 9).val false ||
          ((List.ofFn x).getD (4 : Fin 9).val false || false)] = _
        rw [getRaw 0, getRaw 4, Bool.or_false]
      change ((init :: L.map (translate ρ)).foldl dst (List.ofFn x)).getD (ρ out.val) false = _
      rw [List.foldl_cons, initWire, hd, ← aliasRead x ys out.val, ← hf]
      exact matchAll x
  · let i : Fin 9 := ⟨b.val, by simp at hReal; omega⟩
    let D : Circuit := ⟨L.map (translate id), out.val⟩
    obtain ⟨x, hx⟩ := triple i hReal D (allowed id L _) (by
      change (L.map (translate id)).length ≤ 13
      simpa only [List.length_map] using hL)
    apply hx
    let w := seed x ++ [second x]
    obtain ⟨ys, hf, hd⟩ := simulate id w w (fun _ _ => rfl) L []
    simp only [List.append_nil] at hf hd
    have hr : read (seed x) b = x i := by
      have hbi : b = ⟨i.val, by omega⟩ := Fin.ext rfl
      rw [hbi]
      exact raw x i
    have hw : w = List.ofFn x ++ [first x, first x || x i] := by
      simp only [w, seed, second, hr, List.append_assoc, List.cons_append, List.nil_append]
    change ((L.map (translate id)).foldl dst (List.ofFn x ++ [first x, first x || x i])).getD
      out.val false = G x
    rw [← hw, hd, ← hf]
    exact (matchAll x).trans (targetEq x)
