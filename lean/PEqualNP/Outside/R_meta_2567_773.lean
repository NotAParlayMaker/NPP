import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2567_773
    (search : ∃ (op : GateOp) (b : Fin 26) (g : Gate) (D : Circuit),
      (op = GateOp.or ∧ b ∈ ([1,13,15] : List (Fin 26)) ∨ op = GateOp.and ∧ b = 13) ∧
      (∃ a c : ℕ, g.inputs = [a,c] ∧ a < c ∧ c ≤ 26 ∧
        (g.op = GateOp.or ∨ g.op = GateOp.and ∧
          (a < 13 ∧ 13 ≤ c ∧ c < 26 ∧ (a+c)%13 ∈ ([0,1,3,9] : List ℕ) ∨
            op = GateOp.or ∧ b = 1 ∧ a = 13 ∧ c = 26))) ∧
      Monotone2 D ∧ D.size ≤ 61 ∧
      let near := fun p l : Fin 13 => (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
      let read := fun s t =>
        let x := vec s t
        let w := List.ofFn x ++ [op.eval [x 0,x b]]
        D.eval (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
        ∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false)
    (prepend : ∀ (g : Gate) (D : Circuit),
      (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs.length ≤ 2 → Monotone2 D →
      ∃ E : Circuit, Monotone2 E ∧ E.size = D.size + 1 ∧
        ∀ w : List Bool, E.eval w = D.eval (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.GateOp) (x2 : Fin (26 : ℕ)) (x3 : Fin (26 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x1 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧     (x2, x3) ∈ [((0 : Fin (26 : ℕ)), (1 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)))] ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         x4.size ≤ (62 : ℕ) ∧           let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => x4.eval (List.ofFn (x6 x8 x9) ++ [x1.eval [x6 x8 x9 x2, x6 x8 x9 x3]]);           (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false := by
  obtain ⟨op, b, g, D, first, ⟨a, c, inputs, _, _, second⟩, model, size, tests⟩ := search
  have opAllowed : op = GateOp.and ∨ op = GateOp.or := by
    rcases first with h | h
    · exact Or.inr h.1
    · exact Or.inl h.1
  have bAllowed : (0, b) ∈ ([(0,1),(0,13),(0,15)] : List (Fin 26 × Fin 26)) := by
    rcases first with ⟨_, h⟩ | ⟨_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with e | e | e <;> subst b <;> simp
    · simp
  have secondAllowed : g.op = GateOp.and ∨ g.op = GateOp.or :=
    second.elim Or.inr (fun h => Or.inl h.1)
  obtain ⟨E, ok, small, eval⟩ := prepend g D secondAllowed (by simp [inputs]) model
  refine ⟨op, 0, b, E, opAllowed, bAllowed, ok, by omega, ?_⟩
  let near := fun p l : Fin 13 => (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
  let w := fun s t =>
    let x := vec s t
    List.ofFn x ++ [op.eval [x 0,x b]]
  let read := fun s t => D.eval (w s t ++ [g.op.eval (g.inputs.map fun i => (w s t).getD i false)])
  change (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false) at tests
  change (∀ p l : Fin 13, near p l → E.eval (w {p} {l}) = true) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 → E.eval (w s (off s)) = false ∧ E.eval (w (off s) s) = false)
  constructor
  · intro p l edge
    exact (eval _).trans (tests.1 p l edge)
  · intro s card
    have h := tests.2 s card
    exact ⟨(eval _).trans h.1, (eval _).trans h.2⟩
