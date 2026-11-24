import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2289_1
    (hBinary : ∀ C : Circuit, FanInTwo C →
      circuitFun 9 C = (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) →
      13 ≤ C.gates.countP (fun g => g.op.eval [true]))
    (hFalse : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) = (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x) →
      15 ≤ D.size)
    (hFew : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → x2 < x3 → x3 < (10 : ℕ) + x1.length →
      1 ≤ x1.countP (fun g => !g.op.eval [true]) →
      x1.countP (fun g => !g.op.eval [true]) ≤ 2 →
      11 ≤ x1.countP (fun g => g.op.eval [true]) →
      (fun (x8 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))]) && { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))])) ≠ fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) :
  ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → x2 < x3 → x3 < (10 : ℕ) + x1.length → (fun (x8 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))]) && { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))])) ≠ fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) := by
  intro gs a b hfan hlen hab hb hEq
  have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have notTrue : GateOp.not.eval [true] = false := rfl
  let first : Gate := ⟨.and, [0, 6]⟩
  let last : Gate := ⟨.and, [a, b]⟩
  let C : Circuit := ⟨[first] ++ gs ++ [last], 10 + gs.length⟩
  have hC : FanInTwo C := by
    intro g hg
    change g ∈ [first] ++ gs ++ [last] at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (rfl | hg) | rfl
    · simp [first]
    · exact hfan g hg
    · simp [last]
  have hlenW (ls : List Gate) (x : List Bool) :
      (ls.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
        x.length + ls.length := by
    induction ls generalizing x with
    | nil => simp
    | cons g ls ih => rw [List.foldl_cons, ih]; simp; omega
  have hEval (x : Fin 9 → Bool) : C.eval (List.ofFn x) =
      (({ gates := gs, output := a } : Circuit).eval (List.ofFn x ++ [x 0 && x 6]) &&
        ({ gates := gs, output := b } : Circuit).eval (List.ofFn x ++ [x 0 && x 6])) := by
    let z := List.ofFn x ++ [x 0 && x 6]
    let w := ({ gates := gs, output := 0 } : Circuit).wires z
    have hfirst : first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false) =
        (x 0 && x 6) := by
      simp [first, andEval, List.getD]
    have hwlen : w.length = 10 + gs.length := by
      change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) z).length = _
      rw [hlenW]
      simp [z]
    change (C.wires (List.ofFn x)).getD (10 + gs.length) false =
      (w.getD a false && w.getD b false)
    have hwires : C.wires (List.ofFn x) = w ++ [last.op.eval (last.inputs.map fun i => w.getD i false)] := by
      dsimp only [C, w, z]
      delta Circuit.wires
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hfirst]
    rw [hwires, List.getD_append_right _ _ _ _ (by omega), hwlen, Nat.sub_self]
    simp [last, andEval]
  have hcorrect : circuitFun 9 C = (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
    funext x
    exact (hEval x).trans (congrFun hEq x)
  have hnb := hBinary C hC hcorrect
  change 13 ≤ ([first] ++ gs ++ [last]).countP
    (fun g => g.op.eval [true]) at hnb
  have hfirstTrue : first.op.eval [true] = true := rfl
  have hlastTrue : last.op.eval [true] = true := rfl
  simp [List.countP_append, hfirstTrue, hlastTrue] at hnb
  have hcounts (ls : List Gate) :
      ls.countP (fun g => !g.op.eval [true]) +
      ls.countP (fun g => g.op.eval [true]) = ls.length := by
    induction ls with
    | nil => rfl
    | cons g ls ih =>
      cases hg : g.op.eval [true] <;> simp [hg] <;> omega
  have hsum := hcounts gs
  by_cases hpos : 1 ≤ gs.countP (fun g => !g.op.eval [true])
  · exact hFew gs a b hfan hlen hab hb hpos (by omega) (by omega) hEq
  have hz : gs.countP (fun g => !g.op.eval [true]) = 0 := by omega
  let D : Circuit := ⟨gs ++ [last], 10 + gs.length⟩
  have hD : FanInTwo D := by
    intro g hg
    change g ∈ gs ++ [last] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hfan g hg
    · obtain rfl := List.mem_singleton.mp hg
      simp [last]
  have hDops : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    change g ∈ gs ++ [last] at hg
    rcases List.mem_append.mp hg with hg | hg
    · have hn := List.countP_eq_zero.mp hz g hg
      have hop := (hfan g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hn (by simp [h, notTrue]))
    · obtain rfl := List.mem_singleton.mp hg
      exact Or.inl rfl
  let leList (x y : List Bool) := ∀ i, x.getD i false = true → y.getD i false = true
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have gateMono (g : Gate) (hg : g.op = .and ∨ g.op = .or)
      (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
      g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
    rcases hg with ho | ho
    · simp only [ho, andEval, List.all_eq_true, List.mem_map, id]
      intro ht y hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact h i (ht _ ⟨i, hi, rfl⟩)
    · simp only [ho, orEval, List.any_eq_true, List.mem_map, id]
      rintro ⟨y, ⟨i, hi, rfl⟩, ht⟩
      exact ⟨f' i, ⟨i, hi, rfl⟩, h i ht⟩
  have foldMono (ls : List Gate) (hls : ∀ g ∈ ls, g.op = .and ∨ g.op = .or) :
      ∀ x y : List Bool, x.length = y.length → leList x y →
        leList (ls.foldl step x) (ls.foldl step y) := by
    induction ls with
    | nil => intro _ _ _ hxy; exact hxy
    | cons g ls ih =>
      intro x y hl hxy
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hls g' (List.mem_cons_of_mem _ hg'))
      · simp [step, hl]
      · intro i hi
        unfold step at hi ⊢
        by_cases hlt : i < x.length
        · rw [List.getD_append _ _ _ _ hlt] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact hxy i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
          by_cases he : i - x.length = 0
          · rw [he] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            exact gateMono g (hls g List.mem_cons_self) _ _ hxy hi
          · obtain ⟨k, hk⟩ : ∃ k, i - x.length = k + 1 := ⟨i - x.length - 1, by omega⟩
            rw [hk] at hi
            simp at hi
  let H (x : Fin 9 → Bool) (t : Bool) := D.eval (List.ofFn x ++ [t])
  have Hmono (x y : Fin 9 → Bool) (r s : Bool)
      (hx : ∀ i, x i = true → y i = true) (hr : r = true → s = true) :
      H x r = true → H y s = true := by
    apply foldMono D.gates hDops _ _ (by simp) ?_ D.output
    intro k hk
    have hxlen : (List.ofFn x).length = 9 := by simp
    have hylen : (List.ofFn y).length = 9 := by simp
    by_cases hlt : k < 9
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega), List.getElem_ofFn] at hk
      rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega), List.getElem_ofFn]
      exact hx ⟨k, hlt⟩ hk
    · rw [List.getD_append_right _ _ _ _ (by omega), hxlen] at hk
      rw [List.getD_append_right _ _ _ _ (by omega), hylen]
      by_cases he : k = 9
      · subst k
        simp only [Nat.sub_self, List.getD_cons_zero] at hk ⊢
        exact hr hk
      · obtain ⟨d, hd⟩ : ∃ d, k - 9 = d + 1 := ⟨k - 10, by omega⟩
        rw [hd] at hk
        simp at hk
  have same (x : Fin 9 → Bool) : H x (x 0 && x 6) = circuitFun 9 C x := by
    have hfirst : first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false) =
        (x 0 && x 6) := by simp [first, andEval, List.getD]
    dsimp only [H, D, C]
    delta circuitFun
    delta Circuit.eval
    delta Circuit.wires
    simp only [List.cons_append, List.nil_append, List.foldl_cons, hfirst]
  let edges : List (Fin 9 × Fin 9) :=
    [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)]
  have hgraph (x : Fin 9 → Bool) :
      circuitFun 9 C x = edges.any (fun e => x e.1 && x e.2) := by
    rw [hcorrect]
    simp [edges, Bool.or_assoc]
  have hmissing : ∀ e : Fin 9 × Fin 9, e ∈ edges →
      ¬ ((0 = e.1 ∨ 0 = e.2) ∧ (6 = e.1 ∨ 6 = e.2)) := by decide +kernel
  have hReplaced (x : Fin 9 → Bool) : H x false = circuitFun 9 C x := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro ht
      rw [← same x]
      exact Hmono x x false (x 0 && x 6) (fun _ h => h) (by simp) ht
    · intro hx
      rw [hgraph] at hx
      obtain ⟨e, he, ht⟩ := List.any_eq_true.mp hx
      have hep := Bool.and_eq_true_iff.mp ht
      let y : Fin 9 → Bool := fun i => decide (i = e.1 ∨ i = e.2)
      have hy (i : Fin 9) : y i = true → x i = true := by
        intro hi
        rcases of_decide_eq_true hi with rfl | rfl
        · exact hep.1
        · exact hep.2
      have hy0 : (y 0 && y 6) = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        have hpair := Bool.and_eq_true_iff.mp hh
        exact hmissing e he ⟨of_decide_eq_true hpair.1, of_decide_eq_true hpair.2⟩
      have hyC : circuitFun 9 C y = true := by
        rw [hgraph]
        apply List.any_eq_true.mpr
        exact ⟨e, he, by simp [y]⟩
      have hyH : H y false = true := by
        rw [← hy0, same]
        exact hyC
      exact Hmono y x false false hy (fun h => h) hyH
  have hDsize := hFalse D hD (fun x => (hReplaced x).trans (congrFun hcorrect x))
  change 15 ≤ (gs ++ [last]).length at hDsize
  simp only [List.length_append, List.length_singleton] at hDsize
  omega
