import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3531_3
    (block9 :
      let init : List ℕ := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
      let step : List ℕ → Bool × ℕ × ℕ → List ℕ := fun w g =>
        w ++ [if g.1 = Bool.true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]
      ∃ g : List (Bool × ℕ × ℕ), ∃ i : ℕ, g.length ≤ 11 ∧ 14 ≤ i ∧ i < 14 + g.length ∧
        (g.foldl step init).getD i 0 = 332367)
    (block12 :
      let init : List ℕ := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
      let step : List ℕ → Bool × ℕ × ℕ → List ℕ := fun w g =>
        w ++ [if g.1 = Bool.true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]
      ∃ g : List (Bool × ℕ × ℕ), ∃ i : ℕ, g.length ≤ 14 ∧ 14 ≤ i ∧ i < 14 + g.length ∧
        (g.foldl step init).getD i 0 = 1764784) :
    ∃ (x1 : List (Bool × ℕ × ℕ)) (x2 : ℕ) (x3 : ℕ) (x4 : Fin (16 : ℕ)),   x1.length ≤ (25 : ℕ) ∧     (14 : ℕ) ≤ x2 ∧       x2 < x3 ∧         x3 < (14 : ℕ) + x1.length ∧           have x5 : ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)].getD ↑x4 (0 : ℕ);           have x6 : ℕ := x5 % (64 : ℕ);           have x7 : ℕ := x5 / (64 : ℕ);           have x8 : List ℕ := List.foldl (fun (x8 : List ℕ) (x9 : Bool × ℕ × ℕ) => x8 ++ [(fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) => if x11.1 = Bool.true then x10.getD x11.2.1 (0 : ℕ) ||| x10.getD x11.2.2 (0 : ℕ) else x10.getD x11.2.1 (0 : ℕ) &&& x10.getD x11.2.2 (0 : ℕ)) x8 x9]) [(95229015649944073 : ℕ), (63038587928642 : ℕ), (256463372304 : ℕ), (4292497062825988 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (189297016294080519 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)] x1;           have x9 : ℕ := x8.getD x2 (0 : ℕ);           have x10 : ℕ := x8.getD x3 (0 : ℕ);           (if x6 < (21 : ℕ) then x9 ||| x10 else x9 &&& x10) = (2097151 : ℕ) ∧ x9.testBit x6 ≠ x10.testBit x6 ∧ x9.testBit x6 = x10.testBit x7 ∧ x10.testBit x6 = x9.testBit x7 := by
  let init : List ℕ := [95229015649944073, 63038587928642, 256463372304, 4292497062825988, 8521482511360, 14003410187716736, 55389823206179104, 189297016294080519, 155696362464215096, 218994303131713984, 183565875465424384, 229736628136996864, 270286071508729856, 288160007409369088]
  let step : List ℕ → Bool × ℕ × ℕ → List ℕ := fun w g =>
    w ++ [if g.1 = Bool.true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]
  let ev : List ℕ → Bool × ℕ × ℕ → ℕ := fun w g =>
    if g.1 = Bool.true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0
  let sh : ℕ → Bool × ℕ × ℕ → Bool × ℕ × ℕ := fun n g =>
    (g.1, if g.2.1 < 14 then g.2.1 else g.2.1 + n, if g.2.2 < 14 then g.2.2 else g.2.2 + n)
  have step_ev : ∀ w g, step w g = w ++ [ev w g] := by
    intro w g
    rfl
  obtain ⟨g9, i9, h9len, h9lo, h9hi, h9val⟩ := block9
  obtain ⟨g12, i12, h12len, h12lo, h12hi, h12val⟩ := block12
  have hinit : init.length = 14 := by decide
  have len_fold : ∀ (gs : List (Bool × ℕ × ℕ)) (s : List ℕ),
      (gs.foldl step s).length = s.length + gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro s
      simp
    | cons g gs ih =>
      intro s
      rw [List.foldl_cons, step_ev, ih, List.length_append, List.length_singleton, List.length_cons]
      omega
  have get_prefix : ∀ (gs : List (Bool × ℕ × ℕ)) (s : List ℕ) (j : ℕ),
      j < s.length → (gs.foldl step s).getD j 0 = s.getD j 0 := by
    intro gs
    induction gs with
    | nil =>
      intro s j hj
      rfl
    | cons g gs ih =>
      intro s j hj
      simp only [List.foldl_cons, step_ev]
      have hj' : j < (s ++ [ev s g]).length := by
        simp [List.length_append]
        omega
      rw [ih (s ++ [ev s g]) j hj', List.getD_append _ _ _ _ hj]
  let w9 := g9.foldl step init
  let w12 := g12.foldl step init
  have hw9 : w9.length = 14 + g9.length := by
    simpa [w9, hinit] using len_fold g9 init
  have hw12 : w12.length = 14 + g12.length := by
    simpa [w12, hinit] using len_fold g12 init
  have hread0 : ∀ j, (if j < 14 then w9.getD j 0 else w9.getD (j + g9.length) 0) = init.getD j 0 := by
    intro j
    by_cases hj : j < 14
    · simp only [hj, ite_true]
      have := get_prefix g9 init j (by simpa [hinit] using hj)
      simpa [w9] using this
    · simp only [hj, ite_false]
      have hzero : init.getD j 0 = 0 := List.getD_eq_default _ _ (by simpa [hinit] using Nat.le_of_not_lt hj)
      have hge : w9.length ≤ j + g9.length := by
        have : (14 : ℕ) ≤ j := by omega
        simpa [hw9] using Nat.add_le_add this (Nat.le_refl g9.length)
      rw [List.getD_eq_default _ _ hge, hzero]
  have inv : ∀ (gs : List (Bool × ℕ × ℕ)) (orig big : List ℕ),
      14 ≤ orig.length →
      big.length = orig.length + g9.length →
      (∀ j, (if j < 14 then big.getD j 0 else big.getD (j + g9.length) 0) = orig.getD j 0) →
      14 ≤ (gs.foldl step orig).length ∧
      ((gs.map (sh g9.length)).foldl step big).length = (gs.foldl step orig).length + g9.length ∧
      (∀ j, (if j < 14 then ((gs.map (sh g9.length)).foldl step big).getD j 0
          else ((gs.map (sh g9.length)).foldl step big).getD (j + g9.length) 0) =
        (gs.foldl step orig).getD j 0) := by
    intro gs
    induction gs with
    | nil =>
      intro orig big h14 hlen hget
      exact ⟨h14, hlen, hget⟩
    | cons g gs ih =>
      intro orig big h14 hlen hget
      simp only [List.map_cons, List.foldl_cons]
      have hL : big.getD (if g.2.1 < 14 then g.2.1 else g.2.1 + g9.length) 0 = orig.getD g.2.1 0 := by
        rw [apply_ite (fun i => big.getD i 0)]
        exact hget g.2.1
      have hR : big.getD (if g.2.2 < 14 then g.2.2 else g.2.2 + g9.length) 0 = orig.getD g.2.2 0 := by
        rw [apply_ite (fun i => big.getD i 0)]
        exact hget g.2.2
      have hev : ev big (sh g9.length g) = ev orig g := by
        simp only [ev, sh, hL, hR]
      have hlen1 : (big ++ [ev big (sh g9.length g)]).length =
          (orig ++ [ev orig g]).length + g9.length := by
        simp [List.length_append, hlen, hev]
        omega
      have h14' : 14 ≤ (orig ++ [ev orig g]).length := by
        simp [List.length_append]
        omega
      have hget1 : ∀ j, (if j < 14 then (big ++ [ev big (sh g9.length g)]).getD j 0
          else (big ++ [ev big (sh g9.length g)]).getD (j + g9.length) 0) =
          (orig ++ [ev orig g]).getD j 0 := by
        intro j
        by_cases hj : j < 14
        · have hjo : j < orig.length := by omega
          have hjb : j < big.length := by omega
          simp only [hj, ite_true, List.getD_append _ _ _ _ hjb, List.getD_append _ _ _ _ hjo]
          have := hget j
          simp only [hj, ite_true] at this
          exact this
        · simp only [hj, ite_false]
          by_cases hlt : j < orig.length
          · have hjb : j + g9.length < big.length := by omega
            rw [List.getD_append _ _ _ _ hjb, List.getD_append _ _ _ _ hlt]
            have := hget j
            simp only [hj, ite_false] at this
            exact this
          · have hge : orig.length ≤ j := Nat.le_of_not_lt hlt
            by_cases heq : j = orig.length
            · subst heq
              have hidx : orig.length + g9.length = big.length := by rw [hlen]
              rw [hidx]
              rw [List.getD_append_right big [ev big (sh g9.length g)] 0 big.length (Nat.le_refl _)]
              rw [Nat.sub_self, List.getD_cons_zero]
              rw [List.getD_append_right orig [ev orig g] 0 orig.length (Nat.le_refl _)]
              rw [Nat.sub_self, List.getD_cons_zero, hev]
            · rw [List.getD_eq_default (l := big ++ [ev big (sh g9.length g)]) (d := 0)
                  (n := j + g9.length) (by
                  simp [List.length_append, hlen]
                  omega),
                List.getD_eq_default (l := orig ++ [ev orig g]) (d := 0) (n := j) (by
                  simp [List.length_append]
                  omega)]
      exact ih (orig ++ [ev orig g]) (big ++ [ev big (sh g9.length g)]) h14' hlen1 hget1
  have hbig : w9.length = init.length + g9.length := by
    simp [hw9, hinit]
  have hinv := inv g12 init w9 (by simp [hinit]) hbig hread0
  let g := g9 ++ g12.map (sh g9.length)
  have hglen : g.length = g9.length + g12.length := by
    simp [g]
  have hfold_len : (g.foldl step init).length = 14 + g.length := by
    simpa [g, hinit] using len_fold g init
  have h9get : (g.foldl step init).getD i9 0 = 332367 := by
    have hi : i9 < w9.length := by simpa [hw9] using h9hi
    have hpre : (g.foldl step init).getD i9 0 = w9.getD i9 0 := by
      have : g.foldl step init = (g12.map (sh g9.length)).foldl step w9 := by
        simp [g, w9, List.foldl_append]
      rw [this]
      exact get_prefix (g12.map (sh g9.length)) w9 i9 hi
    rw [hpre]
    unfold w9
    exact h9val
  have h12get : (g.foldl step init).getD (i12 + g9.length) 0 = 1764784 := by
    have hfold : g.foldl step init = (g12.map (sh g9.length)).foldl step w9 := by
      simp [g, w9, List.foldl_append]
    rw [hfold]
    have h12ge : ¬ i12 < 14 := by omega
    have := hinv.2.2 i12
    simp only [h12ge, ite_false] at this
    rw [this]
    exact h12val
  refine ⟨g, i9, i12 + g9.length, (1 : Fin 16), ?_, h9lo, ?_, ?_, ?_⟩
  · rw [hglen]
    omega
  · omega
  · rw [hglen]
    omega
  · dsimp only
    rw [h9get, h12get]
    decide
