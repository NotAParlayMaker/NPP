import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_4063_aux
open PEqualNP.CircuitLowerBounds

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ h; simpa using h
  | cons g gs ih =>
    intro w1 w2 hl h
    simp only [List.foldl_cons]
    apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    · simp [hl]
    · have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
          g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
        rcases hgs g (List.mem_cons_self) with ho | ho <;> rw [ho] <;> simp only [GateOp.eval]
        · simp only [List.all_eq_true, List.mem_map, id]
          rintro hall _ ⟨a, ha, rfl⟩
          exact h a (hall _ ⟨a, ha, rfl⟩)
        · simp only [List.any_eq_true, List.mem_map, id]
          rintro ⟨_, ⟨a, ha, rfl⟩, hb⟩
          exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩
      intro i hi
      rcases Nat.lt_trichotomy i w1.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h i hi
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp at hi ⊢
        exact hv hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi (by simp)

theorem gateVal_mono (n : ℕ) (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (hx : PEqualNP.EdgeOwnership.gateVal n C j x = true) :
    PEqualNP.EdgeOwnership.gateVal n C j y = true := by
  unfold PEqualNP.EdgeOwnership.gateVal Circuit.wires at *
  refine fold_mono C.gates hC _ _ (by simp) ?_ _ hx
  intro i hi
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hi ⊢
    simp only [List.getElem_ofFn] at hi ⊢
    exact hxy _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

def E : List (Fin 11 × Fin 11) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8),
  (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
def M : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596,
  1066, 1186, 1288, 1408, 1546]

def P (x : Fin 11 → Bool) : Prop :=
  (∃ e ∈ E, x e.1 = true ∧ x e.2 = true) ∨ ∃ m ∈ M, ∀ i : Fin 11, x i = true → m.testBit i.val = true

instance (x : Fin 11 → Bool) : Decidable (P x) := by unfold P; infer_instance

set_option maxRecDepth 100000 in
theorem keyB : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    P ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] := by decide

theorem key (x : Fin 11 → Bool) : P x := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10] := by
    funext i; fin_cases i <;> rfl
  rw [hx]; exact keyB _ _ _ _ _ _ _ _ _ _ _

end PEqualNP.Outside.L_meta_4063_aux

theorem PEqualNP.Outside.L_meta_4063 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ), PEqualNP.EdgeOwnership.AndOrOnly x3 → (∀ x6 ∈ x2, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false) → PEqualNP.TopForm.BelowF x1 x3 x4 := by
  intro G masks C j hC hF x hx
  rcases PEqualNP.Outside.L_meta_4063_aux.key x with ⟨e, he, h1, h2⟩ | ⟨m, hm, hle⟩
  · have hadj : ∀ e ∈ PEqualNP.Outside.L_meta_4063_aux.E, G.Adj e.1 e.2 := by
      set_option maxRecDepth 100000 in decide
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨e.1, e.2, hadj e he, h1, h2⟩
  · exfalso
    have hm' : m ∈ masks := by simpa [PEqualNP.Outside.L_meta_4063_aux.M, masks] using hm
    have := PEqualNP.Outside.L_meta_4063_aux.gateVal_mono 11 C hC j x _ hle hx
    rw [hF m hm'] at this
    exact absurd this (by simp)
