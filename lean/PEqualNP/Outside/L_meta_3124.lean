import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3124

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeF (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def listDeps (l : List ℕ) : Finset (Fin 9) :=
  l.foldr (fun i (acc : Finset (Fin 9)) =>
    if hi : i < 9 then insert ⟨i, hi⟩ acc
    else if i = 9 then insert (0 : Fin 9) acc
    else acc) ∅

def wireDeps (x1 : List ℕ) (w : ℕ) : Finset (Fin 9) :=
  if h : w < 9 then {⟨w, h⟩}
  else if w = 9 then {0}
  else if w = 10 then listDeps x1
  else ∅

lemma listDeps_card (l : List ℕ) : (listDeps l).card ≤ l.length := by
  induction l with
  | nil => simp [listDeps]
  | cons a t ih =>
    simp only [listDeps, List.foldr_cons, List.length_cons] at ih ⊢
    split_ifs
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)
    · exact ih.trans (Nat.le_succ _)

lemma wireDeps_card (x1 : List ℕ) (hx1 : x1.length ≤ 2) (w : ℕ) :
    (wireDeps x1 w).card ≤ 2 := by
  unfold wireDeps
  split_ifs
  · simp
  · simp
  · exact (listDeps_card x1).trans hx1
  · simp

def baseList (x1 : List ℕ) (x : Fin 9 → Bool) : List Bool :=
  let x8 : List Bool := List.ofFn x ++ [!x 0]
  x8 ++ [GateOp.or.eval (x1.map fun i => x8.getD i false)]

lemma getD_x8_eq (x y : Fin 9 → Bool) (i : ℕ)
    (h : ∀ v : Fin 9, (if hi : i < 9 then v = ⟨i, hi⟩ else if i = 9 then v = 0 else False) → x v = y v) :
    (List.ofFn x ++ [!x 0]).getD i false = (List.ofFn y ++ [!y 0]).getD i false := by
  by_cases hi : i < 9
  · have hlenx : (List.ofFn x).length = 9 := List.length_ofFn
    have hleny : (List.ofFn y).length = 9 := List.length_ofFn
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp only [List.getElem_ofFn]
    exact h ⟨i, hi⟩ (by simp [hi])
  · by_cases h9 : i = 9
    · subst h9
      have h0 : x 0 = y 0 := h 0 (by simp)
      simp [List.getD_eq_getElem?_getD, h0]
    · have hx : (List.ofFn x ++ [!x 0]).length ≤ i := by simp; omega
      have hy : (List.ofFn y ++ [!y 0]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hx, List.getD_eq_default _ _ hy]

lemma listDeps_eq (l : List ℕ) (x y : Fin 9 → Bool)
    (h : ∀ v ∈ listDeps l, x v = y v) :
    l.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) =
    l.map (fun i => (List.ofFn y ++ [!y 0]).getD i false) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons]
    congr 1
    · apply getD_x8_eq
      intro v hv
      apply h v
      simp only [listDeps, List.foldr_cons]
      split_ifs at hv ⊢
      · subst hv; exact Finset.mem_insert_self _ _
      · subst hv; exact Finset.mem_insert_self _ _
    · apply ih
      intro v hv
      apply h v
      simp only [listDeps, List.foldr_cons] at hv ⊢
      split_ifs
      · exact Finset.mem_insert_of_mem hv
      · exact Finset.mem_insert_of_mem hv
      · exact hv

lemma baseList_getD_eq (x1 : List ℕ) (w : ℕ) (x y : Fin 9 → Bool)
    (h : ∀ v ∈ wireDeps x1 w, x v = y v) :
    (baseList x1 x).getD w false = (baseList x1 y).getD w false := by
  dsimp only [baseList]
  by_cases hw : w < 10
  · have hlenx : (List.ofFn x ++ [!x 0]).length = 10 := by simp
    have hleny : (List.ofFn y ++ [!y 0]).length = 10 := by simp
    rw [List.getD_append (List.ofFn x ++ [!x 0]) _ _ _ (by omega),
        List.getD_append (List.ofFn y ++ [!y 0]) _ _ _ (by omega)]
    apply getD_x8_eq
    intro v hv
    apply h v
    unfold wireDeps
    split_ifs at hv ⊢
    · subst hv; simp
    · subst hv; simp
  · by_cases h10 : w = 10
    · subst h10
      have hlenx : (List.ofFn x ++ [!x 0]).length = 10 := by simp
      have hleny : (List.ofFn y ++ [!y 0]).length = 10 := by simp
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      simp only [hlenx, hleny, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      congr 1
      apply listDeps_eq
      intro v hv
      apply h v
      simpa [wireDeps] using hv
    · have hx : (List.ofFn x ++ [!x 0] ++ [GateOp.or.eval (x1.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]).length ≤ w := by simp; omega
      have hy : (List.ofFn y ++ [!y 0] ++ [GateOp.or.eval (x1.map fun i => (List.ofFn y ++ [!y 0]).getD i false)]).length ≤ w := by simp; omega
      rw [List.getD_eq_default _ _ hx, List.getD_eq_default _ _ hy]

def gateDeps (x1 : List ℕ) (g : Gate) : Finset (Fin 9) :=
  g.inputs.foldr (fun w acc => wireDeps x1 w ∪ acc) ∅

lemma gateDeps_card (x1 : List ℕ) (hx1 : x1.length ≤ 2) (l : List ℕ) :
    (l.foldr (fun w acc => wireDeps x1 w ∪ acc) ∅).card ≤ 2 * l.length := by
  induction l with
  | nil => simp
  | cons w t ih =>
    simp only [List.foldr_cons, List.length_cons]
    have h1 := Finset.card_union_le (wireDeps x1 w) (t.foldr (fun w acc => wireDeps x1 w ∪ acc) ∅)
    have h2 := wireDeps_card x1 hx1 w
    omega

lemma gate_eval_eq (x1 : List ℕ) (g : Gate) (x y : Fin 9 → Bool)
    (h : ∀ v ∈ gateDeps x1 g, x v = y v) :
    g.op.eval (g.inputs.map fun i => (baseList x1 x).getD i false) =
    g.op.eval (g.inputs.map fun i => (baseList x1 y).getD i false) := by
  congr 1
  have aux : ∀ l : List ℕ,
      (∀ v ∈ l.foldr (fun w acc => wireDeps x1 w ∪ acc) ∅, x v = y v) →
      l.map (fun i => (baseList x1 x).getD i false) =
      l.map (fun i => (baseList x1 y).getD i false) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons w t ih =>
      intro hl
      simp only [List.map_cons]
      congr 1
      · apply baseList_getD_eq
        intro v hv
        apply hl v
        simp only [List.foldr_cons, Finset.mem_union]
        exact Or.inl hv
      · apply ih
        intro v hv
        apply hl v
        simp only [List.foldr_cons, Finset.mem_union]
        exact Or.inr hv
  exact aux g.inputs h

lemma circuit_small_deps (x1 : List ℕ) (hx1 : x1.length ≤ 2) (C : Circuit)
    (hfan : FanInTwo C) (hsmall : ¬ ∃ g : Gate, C.gates[1]? = some g) :
    ∃ S : Finset (Fin 9), S.card ≤ 4 ∧
      ∀ x y : Fin 9 → Bool, (∀ v ∈ S, x v = y v) →
        C.eval (baseList x1 x) = C.eval (baseList x1 y) := by
  cases hgs : C.gates with
  | nil =>
    refine ⟨wireDeps x1 C.output, (wireDeps_card x1 hx1 C.output).trans (by omega), ?_⟩
    intro x y h
    simp only [Circuit.eval, Circuit.wires, hgs, List.foldl_nil]
    exact baseList_getD_eq x1 C.output x y h
  | cons g rest =>
    cases rest with
    | nil =>
      have hg : g.inputs.length ≤ 2 := (hfan g (by simp [hgs])).2
      by_cases ho : C.output = 11
      · refine ⟨gateDeps x1 g, (gateDeps_card x1 hx1 g.inputs).trans (by omega), ?_⟩
        intro x y h
        have hlenx : (baseList x1 x).length = 11 := by simp [baseList]
        have hleny : (baseList x1 y).length = 11 := by simp [baseList]
        simp only [Circuit.eval, Circuit.wires, hgs, List.foldl_cons, List.foldl_nil]
        rw [ho, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [hlenx, hleny, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        exact gate_eval_eq x1 g x y h
      · refine ⟨wireDeps x1 C.output, (wireDeps_card x1 hx1 C.output).trans (by omega), ?_⟩
        intro x y h
        have hlenx : (baseList x1 x).length = 11 := by simp [baseList]
        have hleny : (baseList x1 y).length = 11 := by simp [baseList]
        simp only [Circuit.eval, Circuit.wires, hgs, List.foldl_cons, List.foldl_nil]
        by_cases hlt : C.output < 11
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact baseList_getD_eq x1 C.output x y h
        · have hx : (baseList x1 x ++ [g.op.eval (g.inputs.map fun i => (baseList x1 x).getD i false)]).length ≤ C.output := by simp [hlenx]; omega
          have hy : (baseList x1 y ++ [g.op.eval (g.inputs.map fun i => (baseList x1 y).getD i false)]).length ≤ C.output := by simp [hleny]; omega
          rw [List.getD_eq_default _ _ hx, List.getD_eq_default _ _ hy]
    | cons g2 rest2 =>
      exfalso
      apply hsmall
      exact ⟨g2, by simp [hgs]⟩

lemma edgeF_depends : ∀ v : Fin 9,
    ∃ x y : Fin 9 → Bool, (∀ u : Fin 9, u ≠ v → x u = y u) ∧ edgeF x ≠ edgeF y := by
  intro v
  fin_cases v
  · exact ⟨fun i => decide (i = 1), fun i => decide (i = 1 ∨ i = 0), by decide, by decide⟩
  · exact ⟨fun i => decide (i = 0), fun i => decide (i = 0 ∨ i = 1), by decide, by decide⟩
  · exact ⟨fun i => decide (i = 1), fun i => decide (i = 1 ∨ i = 2), by decide, by decide⟩
  · exact ⟨fun i => decide (i = 2), fun i => decide (i = 2 ∨ i = 3), by decide, by decide⟩
  · exact ⟨fun i => decide (i = 3), fun i => decide (i = 3 ∨ i = 4), by decide, by decide⟩
  · exact ⟨fun i => decide (i = 0), fun i => decide (i = 0 ∨ i = 5), by decide, by decide⟩
  · exact ⟨fun i => decide (i = 1), fun i => decide (i = 1 ∨ i = 6), by decide, by decide⟩
  · exact ⟨fun i => decide (i = 2), fun i => decide (i = 2 ∨ i = 7), by decide, by decide⟩
  · exact ⟨fun i => decide (i = 3), fun i => decide (i = 3 ∨ i = 8), by decide, by decide⟩

theorem main (x1 : List ℕ) (hx1 : x1.length ≤ 2) (C : Circuit)
    (hfan : FanInTwo C) (_hsz : C.size ≤ 13)
    (hsmall : ¬ ∃ g : Gate, C.gates[1]? = some g) :
    ∃ x : Fin 9 → Bool, C.eval (baseList x1 x) ≠ edgeF x := by
  obtain ⟨S, hScard, hSeq⟩ := circuit_small_deps x1 hx1 C hfan hsmall
  have hex : ∃ v : Fin 9, v ∉ S := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin 9)) ⊆ S := fun v _ => hall v
    have hle := Finset.card_le_card hsub
    simp at hle
    omega
  obtain ⟨v, hv⟩ := hex
  obtain ⟨x, y, hxy, hne⟩ := edgeF_depends v
  have hev : C.eval (baseList x1 x) = C.eval (baseList x1 y) :=
    hSeq x y (fun u hu => hxy u (fun e => hv (e ▸ hu)))
  by_cases hx : C.eval (baseList x1 x) = edgeF x
  · exact ⟨y, fun hy => hne (hx.symm.trans (hev.trans hy))⟩
  · exact ⟨x, hx⟩

end PEqualNP.Outside.L_meta_3124

theorem PEqualNP.Outside.L_meta_3124 :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3124.main
