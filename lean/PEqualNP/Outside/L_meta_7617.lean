import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_7617

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def X5 (n : ℕ) : Set (Set (Fin n → Bool)) :=
  {∅, Set.univ} ∪ Set.range fun (i : Fin n) => {x : Fin n → Bool | x i = Bool.true}

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W]

theorem wlen (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem gate_cases {α : Type} (op : GateOp) (ins : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : ins.length ≤ 2) (f : α → ℕ → Bool) :
    (({x : α | op.eval (ins.map (f x)) = true} = ∅ ∨ {x : α | op.eval (ins.map (f x)) = true} = Set.univ) ∨
      (∃ i, {x : α | op.eval (ins.map (f x)) = true} = {x | f x i = true})) ∨
      ∃ i j, {x : α | op.eval (ins.map (f x)) = true} = {x | f x i = true} ∩ {x | f x j = true} ∨
        {x : α | op.eval (ins.map (f x)) = true} = {x | f x i = true} ∪ {x | f x j = true} := by
  match ins, hl with
  | [], _ =>
    left; left
    rcases hop with rfl | rfl
    · right; ext x; simp [GateOp.eval]
    · left; ext x; simp [GateOp.eval]
  | [a], _ =>
    left; right
    refine ⟨a, ?_⟩
    rcases hop with rfl | rfl <;> (ext x; simp [GateOp.eval])
  | [a, b], _ =>
    right
    refine ⟨a, b, ?_⟩
    rcases hop with rfl | rfl
    · left; ext x; simp [GateOp.eval]
    · right; ext x; simp [GateOp.eval]
  | _ :: _ :: _ :: _, h => simp at h

theorem key (n : ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ x6 : Finset (Set (Fin n → Bool)), x6.card ≤ gs.length ∧ (∀ s ∈ x6, s ∉ X5 n) ∧
      (∀ x7 : Set (Set (Fin n → Bool)), X5 n ⊆ x7 →
        (∀ a ∈ x7, ∀ b ∈ x7, ∀ c ∈ x6, c = a ∩ b ∨ c = a ∪ b → c ∈ x7) → ∀ c ∈ x6, c ∈ x7) ∧
      ∀ j : ℕ, {x : Fin n → Bool | (W gs (List.ofFn x)).getD j Bool.false = Bool.true} ∈ X5 n ∪ ↑x6 := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨∅, by simp, by simp, by simp, fun j => ?_⟩
    left
    by_cases hj : j < n
    · right
      refine ⟨⟨j, hj⟩, ?_⟩
      ext x
      simp [W, List.getD_eq_getElem?_getD, hj]
    · left; left
      ext x
      simp [W, List.getD_eq_getElem?_getD, hj]
  | append_singleton gs g ih =>
    obtain ⟨x6, hc, hn, hg, hw⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
    have hgm := hm g (by simp)
    have hlen : ∀ x : Fin n → Bool, (W gs (List.ofFn x)).length = n + gs.length := by
      intro x; rw [wlen]; simp
    obtain ⟨S, hSdef⟩ : ∃ S : Set (Fin n → Bool), S = {x : Fin n → Bool |
        g.op.eval (g.inputs.map fun i => (W gs (List.ofFn x)).getD i false) = true} := ⟨_, rfl⟩
    have hnew : ∀ j, {x : Fin n → Bool | (W (gs ++ [g]) (List.ofFn x)).getD j Bool.false = Bool.true} =
        if j = n + gs.length then S
        else {x : Fin n → Bool | (W gs (List.ofFn x)).getD j Bool.false = Bool.true} := by
      intro j
      split_ifs with h
      · subst h
        rw [hSdef]
        ext x
        simp only [Set.mem_setOf_eq]
        rw [W_snoc, ← hlen x]
        simp [List.getD_eq_getElem?_getD]
      · ext x
        simp only [Set.mem_setOf_eq]
        rw [W_snoc]
        rcases lt_or_gt_of_ne h with h1 | h1
        · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact h1)]
        · rw [List.getD_eq_default _ _ (by simp [hlen]; omega),
            List.getD_eq_default _ _ (by rw [hlen]; omega)]
    have hS : S ∈ X5 n ∪ ↑x6 ∨ ∃ a ∈ X5 n ∪ ↑x6, ∃ b ∈ X5 n ∪ ↑x6, S = a ∩ b ∨ S = a ∪ b := by
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
        have := hgm.1
        simpa using this
      rcases gate_cases g.op g.inputs hop hgm.2
        (fun (x : Fin n → Bool) i => (W gs (List.ofFn x)).getD i false) with
        ((h | h) | ⟨i, h⟩) | ⟨i, j, h⟩
      · left; left; left; left; rw [hSdef]; exact h
      · left; left; left; right; rw [hSdef]; exact h
      · left; rw [hSdef, h]; exact hw i
      · right
        refine ⟨_, hw i, _, hw j, ?_⟩
        rw [hSdef]; exact h
    by_cases hSm : S ∈ X5 n ∪ ↑x6
    · refine ⟨x6, ?_, hn, hg, fun j => ?_⟩
      · simp; omega
      · rw [hnew]; split_ifs
        · exact hSm
        · exact hw j
    · refine ⟨insert S x6, ?_, ?_, ?_, fun j => ?_⟩
      · refine (Finset.card_insert_le _ _).trans ?_
        simp; omega
      · intro s hs
        rcases Finset.mem_insert.1 hs with h | h
        · subst h; intro h; exact hSm (Or.inl h)
        · exact hn s h
      · intro x7 h5 hcl
        have h6 : ∀ c ∈ x6, c ∈ x7 :=
          hg x7 h5 (fun a ha b hb c hc h => hcl a ha b hb c (Finset.mem_insert_of_mem hc) h)
        have hall : ∀ a ∈ X5 n ∪ ↑x6, a ∈ x7 := by
          rintro a (ha | ha)
          · exact h5 ha
          · exact h6 a ha
        intro c hc
        rcases Finset.mem_insert.1 hc with h | h
        · subst h
          rcases hS with h | ⟨a, ha, b, hb, hab⟩
          · exact absurd h hSm
          · exact hcl a (hall a ha) b (hall b hb) _ (Finset.mem_insert_self _ _) hab
        · exact h6 c h
      · rw [hnew]; split_ifs
        · right; simp
        · rcases hw j with h | h
          · left; exact h
          · right; exact Finset.mem_coe.2 (Finset.mem_insert_of_mem h)

end PEqualNP.Outside.L_meta_7617

theorem PEqualNP.Outside.L_meta_7617 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     let x4 : Type := Fin x1 → Bool;     have x5 : Set (Set x4) := {∅, Set.univ} ∪ Set.range fun (x5 : Fin x1) => {x6 : x4 | x6 x5 = Bool.true};     ∃ (x6 : Finset (Set x4)), x6.card ≤ x2.size ∧ (∀ x7 ∈ x6, x7 ∉ x5) ∧ (∀ (x7 : Set (Set x4)), x5 ⊆ x7 → (∀ x9 ∈ x7, ∀ x11 ∈ x7, ∀ x13 ∈ x6, x13 = x9 ∩ x11 ∨ x13 = x9 ∪ x11 → x13 ∈ x7) → ∀ x10 ∈ x6, x10 ∈ x7) ∧ ∀ (x7 : ℕ), {x8 : x4 | (x2.wires (List.ofFn x8)).getD x7 Bool.false = Bool.true} ∈ x5 ∪ ↑x6 := by
  intro x1 x2 hm
  exact PEqualNP.Outside.L_meta_7617.key x1 x2.gates hm
