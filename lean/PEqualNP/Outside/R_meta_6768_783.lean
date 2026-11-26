import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_6768_783
    (hOne : let G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        (∀ v : Fin 11, v.val < 4 → (∀ j < C.size, v.val ∈ (gateAt C j).inputs → (gateAt C j).op = GateOp.or) ∧ ∀ i j k : ℕ, i < j → j < k → k < C.size → v.val ∈ (gateAt C i).inputs → v.val ∈ (gateAt C j).inputs → v.val ∉ (gateAt C k).inputs) →
        (∀ v : Fin 11, v.val < 4 → ∃ j < C.size, v.val ∈ (gateAt C j).inputs) →
        (∃ v : Fin 11, v.val < 4 ∧ ∀ i < C.size, ∀ j < C.size, v.val ∈ (gateAt C i).inputs → v.val ∈ (gateAt C j).inputs → i = j) →
        ∃ v : Fin 11, v.val < 4 ∧ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧
          (∃ w < 11 + i, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + i) = wval C x w) ∧
          (∃ w < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = wval C x w) ∧
          (∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + k) = wval C x w))
    (hTwo : let G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        (∀ v : Fin 11, v.val < 4 → (∀ j < C.size, v.val ∈ (gateAt C j).inputs → (gateAt C j).op = GateOp.or) ∧ ∀ i j k : ℕ, i < j → j < k → k < C.size → v.val ∈ (gateAt C i).inputs → v.val ∈ (gateAt C j).inputs → v.val ∉ (gateAt C k).inputs) →
        (∀ v : Fin 11, v.val < 4 → ∃ i j : ℕ, i < j ∧ j < C.size ∧ v.val ∈ (gateAt C i).inputs ∧ v.val ∈ (gateAt C j).inputs) →
        ∃ v : Fin 11, v.val < 4 ∧ ∃ k < C.size, v.val ∉ (gateAt C k).inputs ∧
          ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + k) = wval C x w) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)), ↑x8 < (4 : ℕ) → (∀ x10 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x10 x11 x12 : ℕ), x10 < x11 → x11 < x12 → x12 < x2.size → ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs → ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → ↑x8 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) := by
  dsimp only
  intro C hL hT hJ hS hB hSp
  obtain ⟨⟨_, hRB, hLen⟩, hF, _⟩ := hL
  have hpre : ∀ (gs : List Gate) (w : List Bool), ∃ t : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧
        t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      rw [List.foldl_cons, ht]
      simp
  have hin : ∀ (x : Fin 11 → Bool) (i : ℕ) (hi : i < 11), wval C x i = x ⟨i, hi⟩ := by
    intro x i hi
    obtain ⟨t, ht, _⟩ := hpre C.gates (List.ofFn x)
    unfold wval Circuit.wires
    rw [ht, List.getD_append _ _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have hout : ∀ (x : Fin 11 → Bool) (i : ℕ), 11 + C.gates.length ≤ i → wval C x i = false := by
    intro x i hi
    obtain ⟨t, ht, hl⟩ := hpre C.gates (List.ofFn x)
    unfold wval Circuit.wires
    rw [ht, List.getD_eq_default]
    simp [hl]; omega
  have hgate : ∀ (x : Fin 11 → Bool) (j : ℕ) (hj : j < C.gates.length),
      wval C x (11 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wval C x i) := by
    intro x j hj
    have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have hga : gateAt C j = C.gates[j] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
    obtain ⟨t1, ht1, hl1⟩ := hpre (C.gates.take j) (List.ofFn x)
    set W := (C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x) with hW
    have hWl : W.length = 11 + j := by
      rw [ht1]; simp [hl1]; omega
    obtain ⟨t2, ht2, _⟩ := hpre (C.gates.drop (j + 1))
      (W ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => W.getD i false)])
    have hfull : C.wires (List.ofFn x) = (W ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => W.getD i false)]) ++ t2 := by
      unfold Circuit.wires
      rw [← ht2, hW]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hlow : ∀ i < 11 + j, wval C x i = W.getD i false := by
      intro i hi
      unfold wval
      rw [hfull, List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
    unfold wval
    rw [hfull, List.getD_append _ _ _ _ (by simp; omega), ← hWl]
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp only [Nat.sub_self, List.getD_cons_zero]
    rw [hga]
    congr 1
    apply List.map_congr_left
    intro i hi
    have := hlow i (hRB j hj i (by rw [hga]; exact hi))
    unfold wval at this
    rw [hfull] at this
    exact this.symm

  have hcopy : ∀ v : Fin 11, v.val < 4 → ∀ j < C.size, v.val ∈ (gateAt C j).inputs →
      ∃ w < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = wval C x w := by
    intro v hv j hj hvj
    have hop := (hSp v hv).1 j hj hvj
    have hga : gateAt C j = C.gates[j] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
    have hl : (gateAt C j).inputs.length = 2 := by
      rw [hga]; exact hLen _ (List.getElem_mem hj)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
    have hra : a < 11 + j := hRB j hj a (by rw [hab]; simp)
    have hrb : b < 11 + j := hRB j hj b (by rw [hab]; simp)
    have hvx : ∀ x : Fin 11 → Bool, x v = false → wval C x v.val = false := by
      intro x hx; rw [hin x v.val v.isLt]; simpa using hx
    by_cases ha : a = v.val
    · refine ⟨b, hrb, fun x hx => ?_⟩
      rw [hgate x j hj, hop, hab, ha, List.map_cons, List.map_cons, List.map_nil, hvx x hx]
      cases wval C x b <;> rfl
    · have hb : b = v.val := by
        rw [hab] at hvj; simp at hvj; omega
      refine ⟨a, hra, fun x hx => ?_⟩
      rw [hgate x j hj, hop, hab, hb, List.map_cons, List.map_cons, List.map_nil, hvx x hx]
      cases wval C x a <;> rfl

  have hRead : ∀ v : Fin 11, v.val < 4 → ∃ j < C.size, v.val ∈ (gateAt C j).inputs := by
    intro v hv
    by_contra hno
    push Not at hno
    have hind : ∀ x y : Fin 11 → Bool, (∀ i, i ≠ v → x i = y i) →
        ∀ w, w ≠ v.val → wval C x w = wval C y w := by
      intro x y hxy w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        by_cases h1 : w < 11
        · rw [hin x w h1, hin y w h1]
          apply hxy
          intro h; apply hw; rw [← h]
        · by_cases h2 : w < 11 + C.gates.length
          · obtain ⟨j, rfl⟩ : ∃ j, w = 11 + j := ⟨w - 11, by omega⟩
            have hj : j < C.gates.length := by omega
            rw [hgate x j hj, hgate y j hj]
            congr 1
            apply List.map_congr_left
            intro i hi
            apply ih i (hRB j hj i hi)
            intro hiv; exact hno j hj (hiv ▸ hi)
          · rw [hout x w (by omega), hout y w (by omega)]
    have hcf : ∀ x : Fin 11 → Bool, PEqualNP.MetaComplexity.circuitFun 11 C x = wval C x C.output := fun x => rfl
    have hcontra : ∀ a : Fin 11, a ≠ v →
        graphFun (edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]) ∅ (fun i => decide (i = v)) = false →
        graphFun (edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]) ∅ (fun i => decide (i = a)) = false →
        graphFun (edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]) ∅ (fun i => decide (i = a) || decide (i = v)) = true →
        False := by
      intro a hav h0 h1 h2
      by_cases ho : C.output = v.val
      · have := hcf (fun i => decide (i = v))
        rw [hF, h0, ho, hin _ v.val v.isLt] at this
        simp at this
      · have e1 := hcf (fun i => decide (i = a))
        have e2 := hcf (fun i => decide (i = a) || decide (i = v))
        rw [hF] at e1 e2
        rw [h1] at e1
        rw [h2] at e2
        have := hind (fun i => decide (i = a)) (fun i => decide (i = a) || decide (i = v))
          (fun i hi => by simp [hi]) C.output ho
        rw [← e1, ← e2] at this
        exact Bool.false_ne_true this
    have h4 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
      rcases v with ⟨k, hk⟩
      simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      simp at hv
      omega
    rcases h4 with rfl | rfl | rfl | rfl
    · exact hcontra 9 (by decide) (by decide) (by decide) (by decide)
    · exact hcontra 4 (by decide) (by decide) (by decide) (by decide)
    · exact hcontra 5 (by decide) (by decide) (by decide) (by decide)
    · exact hcontra 6 (by decide) (by decide) (by decide) (by decide)
  by_cases hall : ∀ v : Fin 11, v.val < 4 → ∃ i j : ℕ, i < j ∧ j < C.size ∧
      v.val ∈ (gateAt C i).inputs ∧ v.val ∈ (gateAt C j).inputs
  · obtain ⟨v, hv, k, hk, hkn, hck⟩ := hTwo C ⟨⟨‹_›, hRB, hLen⟩, hF, ‹_›⟩ hT hJ hS hB hSp hall
    obtain ⟨i, j, hij, hj, hvi, hvj⟩ := hall v hv
    have hci := hcopy v hv i (by omega) hvi
    have hcj := hcopy v hv j hj hvj
    have hki : k ≠ i := fun h => hkn (h ▸ hvi)
    have hkj : k ≠ j := fun h => hkn (h ▸ hvj)
    refine ⟨v, hv, ?_⟩
    rcases lt_or_gt_of_ne hki with h | h
    · exact ⟨k, i, j, h, hij, hj, hck, hci, hcj⟩
    · rcases lt_or_gt_of_ne hkj with h' | h'
      · exact ⟨i, k, j, h, h', hj, hci, hck, hcj⟩
      · exact ⟨i, j, k, hij, h', hk, hci, hcj, hck⟩
  · push Not at hall
    obtain ⟨v, hv, hv1⟩ := hall
    refine hOne C ⟨⟨‹_›, hRB, hLen⟩, hF, ‹_›⟩ hT hJ hS hB hSp hRead ⟨v, hv, fun i hi j hj hvi hvj => ?_⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hv1 i j h hj hvi hvj
    · exact hv1 j i h hi hvj hvi
