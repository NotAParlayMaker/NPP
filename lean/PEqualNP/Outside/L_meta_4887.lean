import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4887

theorem aux (n : ℕ) (fs : List ((Fin n → Bool) → Bool)) :
    ∀ (l : List (Bool → Set (Fin n → Bool))),
    (∀ k : Fin l.length,
      ∃ A ∈ fs.map (fun f (b : Bool) => {z | f z = b}) ++ l.take k,
      ∃ B ∈ fs.map (fun f (b : Bool) => {z | f z = b}) ++ l.take k,
      ∃ c : Bool, ∀ b : Bool, l.get k b ⊆ if b = c then A b ∪ B b else A b ∩ B b) →
    ∃ gs : List Gate, gs.length = l.length ∧
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      ∀ y : Fin n → Bool,
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (fs.map fun f => f y)).length = fs.length + l.length ∧
        ∀ (p : ℕ) (S : Bool → Set (Fin n → Bool)) (b : Bool),
          (fs.map (fun f (b : Bool) => {z | f z = b}) ++ l)[p]? = some S → y ∈ S b →
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (fs.map fun f => f y)).getD p false = b := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], rfl, by simp, fun y => ⟨by simp, ?_⟩⟩
    intro p S b hS hy
    simp only [List.append_nil, List.getElem?_map] at hS
    simp only [List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h : fs[p]? with
    | none => simp [h] at hS
    | some f =>
      simp only [h, Option.map_some, Option.some.injEq] at hS
      subst hS
      simpa [h] using hy
  | append_singleton l a ih =>
    intro hc
    have hl : ∀ k : Fin l.length,
        ∃ A ∈ fs.map (fun f (b : Bool) => {z | f z = b}) ++ l.take k,
        ∃ B ∈ fs.map (fun f (b : Bool) => {z | f z = b}) ++ l.take k,
        ∃ c : Bool, ∀ b : Bool, l.get k b ⊆ if b = c then A b ∪ B b else A b ∩ B b := by
      intro k
      obtain ⟨A, hA, B, hB, c, h⟩ := hc ⟨k, by simp⟩
      have ht : (l ++ [a]).take k = l.take k := List.take_append_of_le_length (by omega)
      have hg : (l ++ [a]).get ⟨k, by simp⟩ = l.get k := by
        simp [List.getElem_append_left k.isLt]
      rw [ht] at hA hB
      rw [hg] at h
      exact ⟨A, hA, B, hB, c, h⟩
    obtain ⟨gs, hlen, hmono, hw⟩ := ih hl
    obtain ⟨A, hA, B, hB, c, h⟩ := hc ⟨l.length, by simp⟩
    have ht : (l ++ [a]).take l.length = l := by simp
    have hg : (l ++ [a]).get ⟨l.length, by simp⟩ = a := by simp
    rw [ht] at hA hB
    rw [hg] at h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hB
    refine ⟨gs ++ [⟨if c then GateOp.or else GateOp.and, [i, j]⟩], by simp [hlen], ?_, ?_⟩
    · intro g hg'
      rcases List.mem_append.mp hg' with hg' | hg'
      · exact hmono g hg'
      · simp only [List.mem_singleton] at hg'
        subst hg'
        cases c <;> simp
    · intro y
      obtain ⟨hL, hV⟩ := hw y
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨by simp only [List.length_append, List.length_singleton, hL]; omega, ?_⟩
      intro p S b hS hy
      set w := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (fs.map fun f => f y) with hwdef
      have hE : (fs.map (fun f (b : Bool) => {z | f z = b}) ++ l).length = w.length := by
        simp [hL]
      have hiv : ∀ (q : ℕ) (hq : q < (fs.map (fun f (b : Bool) => {z | f z = b}) ++ l).length)
          (b : Bool), y ∈ (fs.map (fun f (b : Bool) => {z | f z = b}) ++ l)[q] b →
          w.getD q false = b := fun q hq b hyq => hV q _ b (List.getElem?_eq_getElem hq) hyq
      by_cases hp : p < (fs.map (fun f (b : Bool) => {z | f z = b}) ++ l).length
      · have hS' : (fs.map (fun f (b : Bool) => {z | f z = b}) ++ l)[p]? = some S := by
          rw [← List.append_assoc, List.getElem?_append_left hp] at hS
          exact hS
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hV p S b hS' hy
      · have hpe : p = (fs.map (fun f (b : Bool) => {z | f z = b}) ++ l).length := by
          rw [← List.append_assoc] at hS
          have := (List.getElem?_eq_some_iff.mp hS).1
          simp at this hp ⊢
          omega
        rw [← List.append_assoc, hpe, List.getElem?_append_right (le_refl _)] at hS
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hS
        subst hS
        rw [List.getD_eq_getElem?_getD, hpe, hE, List.getElem?_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        have hwi := hiv i hi
        have hwj := hiv j hj
        simp only [List.getD_eq_getElem?_getD] at hwi hwj
        have hab := h b hy
        cases c <;> cases b <;>
          simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_union, Set.mem_inter_iff,
            reduceCtorEq] at hab ⊢ <;>
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            List.any_cons, List.any_nil, id] <;>
          first
          | (obtain ⟨h1, h2⟩ := hab; simp [hwi _ h1, hwj _ h2])
          | (rcases hab with h1 | h1 <;> first | simp [hwi _ h1] | simp [hwj _ h1])

end PEqualNP.Outside.L_meta_4887

theorem PEqualNP.Outside.L_meta_4887 : ∀ (x1 : ℕ) (x2 : List ((Fin x1 → Bool) → Bool)) (x3 : List (Bool → Set (Fin x1 → Bool))) (x4 : Bool → Set (Fin x1 → Bool)),   have x5 : List (Bool → Set (Fin x1 → Bool)) := List.map (fun (x5 : (Fin x1 → Bool) → Bool) (x6 : Bool) => {x7 : Fin x1 → Bool | x5 x7 = x6}) x2;   x4 ∈ x5 ++ x3 →     (∀ (x7 : Fin x3.length),         have x8 : List (Bool → Set (Fin x1 → Bool)) := x5 ++ List.take (↑x7) x3;         ∃ x9 ∈ x8, ∃ x10 ∈ x8, ∃ (x11 : Bool), ∀ (x12 : Bool), x3.get x7 x12 ⊆ if x12 = x11 then x9 x12 ∪ x10 x12 else x9 x12 ∩ x10 x12) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x3.length ∧ ∀ (x9 : Fin x1 → Bool) (x10 : Bool), x9 ∈ x4 x10 → x8.eval (List.map (fun (x12 : (Fin x1 → Bool) → Bool) => x12 x9) x2) = x10 := by
  intro n fs l T
  dsimp only
  intro hT hc
  obtain ⟨gs, hlen, hmono, hw⟩ := PEqualNP.Outside.L_meta_4887.aux n fs l hc
  obtain ⟨o, ho, rfl⟩ := List.getElem_of_mem hT
  refine ⟨⟨gs, o⟩, hmono, by simp [Circuit.size, hlen], ?_⟩
  intro y b hy
  exact (hw y).2 o _ b (List.getElem?_eq_getElem ho) hy
