import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8253_aux

def T (n : ℕ) (S : Finset ℕ) : Finset ℕ := if (S.filter (fun x => x < n)).card ≤ 2 then S else {n}

def gate (l : List Bool) (g : Finset ℕ × Finset ℕ) : List Bool :=
  l ++ [decide (∀ x ∈ g.1, l.getD x false = true) || decide (∀ x ∈ g.2, l.getD x false = true)]

def M (n : ℕ) (g : Finset ℕ × Finset ℕ) : Finset ℕ × Finset ℕ := (T n g.1, T n g.2)

theorem fold_rel (n : ℕ) (R : List Bool → List Bool → Prop)
    (hstep : ∀ l l' g, R l l' → R (gate l (M n g)) (gate l' g)) :
    ∀ (gs : List (Finset ℕ × Finset ℕ)) l l', R l l' →
      R ((gs.map (M n)).foldl gate l) (gs.foldl gate l') := by
  intro gs
  induction gs with
  | nil => intro l l' h; simpa using h
  | cons g gs ih => intro l l' h; simpa using ih _ _ (hstep l l' g h)

theorem getD_pre (n : ℕ) (x : Fin n → Bool) (a : List Bool) (i : ℕ) (hi : i < n + 1) :
    ((List.ofFn x ++ [false]) ++ a).getD i false = (List.ofFn x ++ [false]).getD i false := by
  rw [List.getD_append]
  simpa using hi

theorem getD_n (n : ℕ) (x : Fin n → Bool) (a : List Bool) :
    ((List.ofFn x ++ [false]) ++ a).getD n false = false := by
  rw [getD_pre n x a n (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append]

theorem getD_lt (n : ℕ) (x : Fin n → Bool) (a : List Bool) (i : ℕ) (hi : i < n) :
    ((List.ofFn x ++ [false]) ++ a).getD i false = x ⟨i, hi⟩ := by
  rw [getD_pre n x a i (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hi]

theorem side_eq (n : ℕ) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun i => x i = true)).card ≤ 2)
    (a : List Bool) (S : Finset ℕ) :
    decide (∀ y ∈ T n S, ((List.ofFn x ++ [false]) ++ a).getD y false = true) =
      decide (∀ y ∈ S, ((List.ofFn x ++ [false]) ++ a).getD y false = true) := by
  unfold T
  split_ifs with h
  · rfl
  · have h1 : ¬ (∀ y ∈ S, ((List.ofFn x ++ [false]) ++ a).getD y false = true) := by
      intro hall
      apply h
      refine le_trans ?_ hx
      have : S.filter (fun y => y < n) ⊆ (Finset.univ.filter (fun i => x i = true)).map Fin.valEmbedding := by
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [Finset.mem_map]
        refine ⟨⟨y, hy.2⟩, ?_, rfl⟩
        have := hall y hy.1
        rw [getD_lt n x a y hy.2] at this
        simpa using this
      simpa using Finset.card_le_card this
    rw [decide_eq_false h1]
    simp [getD_n]

theorem side_le (n : ℕ) (x : Fin n → Bool) (a : List Bool) (l' : List Bool)
    (hle : ∀ i, ((List.ofFn x ++ [false]) ++ a).getD i false = true → l'.getD i false = true)
    (S : Finset ℕ) :
    decide (∀ y ∈ T n S, ((List.ofFn x ++ [false]) ++ a).getD y false = true) = true →
      decide (∀ y ∈ S, l'.getD y false = true) = true := by
  unfold T
  split_ifs with h
  · simp only [decide_eq_true_eq]
    intro h2 y hy
    exact hle y (h2 y hy)
  · simp [getD_n]

theorem getD_snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false = if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : i - l.length ≠ 0 := by omega
    simp [List.getElem?_cons, this]

end PEqualNP.Outside.L_meta_8253_aux

open PEqualNP.Outside.L_meta_8253_aux in
theorem PEqualNP.Outside.L_meta_8253 : ∀ (x1 : ℕ) (x2 : List (Finset ℕ × Finset ℕ)),   have x3 : List (Finset ℕ × Finset ℕ) → (Fin x1 → Bool) → Finset ℕ → Bool := fun (x3 : List (Finset ℕ × Finset ℕ)) (x4 : Fin x1 → Bool) (x5 : Finset ℕ) =>     have x6 : List Bool := List.foldl (fun (x6 : List Bool) (x7 : Finset ℕ × Finset ℕ) => x6 ++ [Decidable.decide (∀ x8 ∈ x7.1, x6.getD x8 Bool.false = Bool.true) || Decidable.decide (∀ x8 ∈ x7.2, x6.getD x8 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x3;     Decidable.decide (∀ x7 ∈ x5, x6.getD x7 Bool.false = Bool.true);   (∀ (x4 : ℕ) (x5 : x4 < x2.length), ∀ x6 ∈ x2[x4].1 ∪ x2[x4].2, x6 < x1 + (1 : ℕ) + x4) →     ∃ (x5 : List (Finset ℕ × Finset ℕ)),       x5.length = x2.length ∧         (∀ (x6 : ℕ) (x7 : x6 < x5.length), ∀ x8 ∈ x5[x6].1 ∪ x5[x6].2, x8 < x1 + (1 : ℕ) + x6) ∧           (∀ x6 ∈ x5, {x8 ∈ x6.1 | x8 < x1}.card ≤ (2 : ℕ) ∧ {x8 ∈ x6.2 | x8 < x1}.card ≤ (2 : ℕ)) ∧             ∀ (x6 : Fin x1 → Bool) (x7 : Finset ℕ),               ((have x8 : Finset (Fin x1) := {x8 : Fin x1 | x6 x8 = Bool.true};                   x8.card ≤ (2 : ℕ)) →                   x3 x5 x6 x7 = x3 x2 x6 x7) ∧                 (x3 x5 x6 x7 = Bool.true → x3 x2 x6 x7 = Bool.true) := by
  intro x1 x2 x3 h
  refine ⟨x2.map (M x1), by simp, ?_, ?_, ?_⟩
  · intro i hi y hy
    simp only [List.getElem_map, M, Finset.mem_union] at hy
    have hi' : i < x2.length := by simpa using hi
    have hb := h i hi'
    rcases hy with hy | hy
    · unfold T at hy
      split_ifs at hy
      · exact hb y (Finset.mem_union_left _ hy)
      · rw [Finset.mem_singleton] at hy; omega
    · unfold T at hy
      split_ifs at hy
      · exact hb y (Finset.mem_union_right _ hy)
      · rw [Finset.mem_singleton] at hy; omega
  · intro g hg
    rw [List.mem_map] at hg
    obtain ⟨g0, -, rfl⟩ := hg
    constructor
    · show ((T x1 g0.1).filter (fun x8 => x8 < x1)).card ≤ 2
      unfold T
      split_ifs with h1
      · exact h1
      · exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
    · show ((T x1 g0.2).filter (fun x8 => x8 < x1)).card ≤ 2
      unfold T
      split_ifs with h1
      · exact h1
      · exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
  · intro x6 x7
    constructor
    · intro hx0
      have hx : (Finset.univ.filter (fun i => x6 i = true)).card ≤ 2 := hx0
      have key := fold_rel x1 (fun l l' => l = l' ∧ ∃ a, l = (List.ofFn x6 ++ [false]) ++ a)
        (by
          rintro l l' g ⟨rfl, a, rfl⟩
          constructor
          · simp only [gate, M]
            exact congrArg (fun b => _ ++ [b]) (congrArg₂ (· || ·) (side_eq x1 x6 hx a g.1) (side_eq x1 x6 hx a g.2))
          · exact ⟨_, List.append_assoc _ _ _⟩) x2 (List.ofFn x6 ++ [false]) (List.ofFn x6 ++ [false]) ⟨rfl, [], by simp⟩
      show decide _ = decide _
      have e : (x2.map (M x1)).foldl gate (List.ofFn x6 ++ [false]) = x2.foldl gate (List.ofFn x6 ++ [false]) := key.1
      exact congrArg (fun l => decide (∀ y ∈ x7, l.getD y false = true)) e
    · have key := fold_rel x1 (fun l l' => (∃ a, l = (List.ofFn x6 ++ [false]) ++ a) ∧ l.length = l'.length ∧
          ∀ i, l.getD i false = true → l'.getD i false = true)
        (by
          rintro l l' g ⟨⟨a, rfl⟩, hlen, hle⟩
          refine ⟨⟨_, List.append_assoc _ _ _⟩, ?_, ?_⟩
          · simp only [gate, List.length_append, List.length_singleton, hlen]
          intro i
          simp only [gate, M]
          rw [getD_snoc, getD_snoc, ← hlen]
          split_ifs
          · exact hle i
          · have s1 := side_le x1 x6 a l' hle g.1
            have s2 := side_le x1 x6 a l' hle g.2
            simp only [Bool.or_eq_true] at s1 s2 ⊢
            intro hh
            rcases hh with hh | hh
            · exact Or.inl (s1 hh)
            · exact Or.inr (s2 hh)
          · exact id) x2 (List.ofFn x6 ++ [false]) (List.ofFn x6 ++ [false]) ⟨⟨[], by simp⟩, rfl, fun i h => h⟩
      show decide _ = true → decide _ = true
      have e := key.2.2
      simp only [decide_eq_true_eq]
      intro h2 y hy
      exact e y (h2 y hy)
