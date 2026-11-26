import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18407_aux

open PEqualNP.CircuitLowerBounds

theorem getD_zip (w1 w2 : List Bool) (h : w1.length = w2.length) (i : ℕ) :
    (List.zipWith (fun a b => a || b) w1 w2).getD i false = (w1.getD i false || w2.getD i false) := by
  induction w1 generalizing w2 i with
  | nil => cases w2 <;> simp_all
  | cons a t ih =>
    cases w2 with
    | nil => simp at h
    | cons b s =>
      cases i with
      | zero => simp
      | succ i => simp only [List.zipWith_cons_cons, List.getD_cons_succ]; exact ih s (by simpa using h) i

theorem any_or (l : List ℕ) (f g : ℕ → Bool) :
    (l.map fun i => f i || g i).any id = ((l.map f).any id || (l.map g).any id) := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.any_cons, ih, id]; cases f a <;> cases g a <;> simp

theorem fold_hom (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.or) (w1 w2 : List Bool)
    (h : w1.length = w2.length) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.zipWith (fun a b => a || b) w1 w2) =
    List.zipWith (fun a b => a || b)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2) := by
  induction gs generalizing w1 w2 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hop : g.op = GateOp.or := hg g (by simp)
    have e : (List.zipWith (fun a b => a || b) w1 w2 ++
        [g.op.eval (g.inputs.map fun i => (List.zipWith (fun a b => a || b) w1 w2).getD i false)]) =
        List.zipWith (fun a b => a || b) (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
          (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) := by
      rw [List.zipWith_append h]
      simp only [getD_zip w1 w2 h, hop, GateOp.eval, any_or, List.zipWith_cons_cons, List.zipWith_nil_left]
    rw [e]
    exact ih (fun g' hg' => hg g' (by simp [hg'])) _ _ (by simp [h])

theorem len_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons]; simp; omega

theorem eval_hom {n : ℕ} (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.or) (a b : Fin n → Bool) :
    C.eval (List.ofFn fun i => a i || b i) = (C.eval (List.ofFn a) || C.eval (List.ofFn b)) := by
  have hz : (List.ofFn fun i => a i || b i) = List.zipWith (fun a b => a || b) (List.ofFn a) (List.ofFn b) := by
    apply List.ext_getElem <;> simp
  unfold Circuit.eval Circuit.wires
  rw [hz, fold_hom C.gates hg _ _ (by simp), getD_zip]
  rw [len_fold, len_fold]; simp


theorem eval_hom2 (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.or) (a b c d : Fin 13 → Bool) :
    C.eval (List.ofFn (fun i => a i || c i) ++ List.ofFn (fun i => b i || d i)) =
      (C.eval (List.ofFn a ++ List.ofFn b) || C.eval (List.ofFn c ++ List.ofFn d)) := by
  rw [← List.ofFn_fin_append, ← List.ofFn_fin_append, ← List.ofFn_fin_append, ← eval_hom C hg]
  congr 2
  funext i
  induction i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]

theorem key (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.or) (f g a b : Fin 13 → Bool)
    (h1 : ∀ i, f i = (f i || a i)) (h2 : ∀ i, g i = (g i || b i))
    (h : C.eval (List.ofFn f ++ List.ofFn g) = false) : C.eval (List.ofFn a ++ List.ofFn b) = false := by
  have e1 : f = fun i => f i || a i := funext h1
  have e2 : g = fun i => g i || b i := funext h2
  rw [e1, e2, eval_hom2 C hg] at h
  simp at h
  exact h.2

end PEqualNP.Outside.L_meta_18407_aux

open PEqualNP.Outside.L_meta_18407_aux in
theorem PEqualNP.Outside.L_meta_18407 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → (∀ (x5 x6 : Fin (13 : ℕ)), x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ)) → x1.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) → (∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x9 - x8 = (0 : Fin (13 : ℕ)) ∨ x9 - x8 = (1 : Fin (13 : ℕ)) ∨ x9 - x8 = (3 : Fin (13 : ℕ)) ∨ x9 - x8 = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) → x1.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x6, ¬(x10 - x9 = (0 : Fin (13 : ℕ)) ∨ x10 - x9 = (1 : Fin (13 : ℕ)) ∨ x10 - x9 = (3 : Fin (13 : ℕ)) ∨ x10 - x9 = (9 : Fin (13 : ℕ))))) = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro C hm hna _ hacc hrej
  exfalso
  have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hgm
    have h1 := (hm g hgm).1
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hgm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd ⟨i, h1⟩ hna
    · exact h1
  have r1 := hrej {0, 2, 3, 4} (by decide) (by decide)
  have r2 := hrej {0, 1, 2, 5} (by decide) (by decide)
  have a1 := key C hg _ _ (fun x => decide (x = 3)) (fun _ => false) (by decide) (by decide) r1
  have a2 := key C hg _ _ (fun _ => false) (fun x => decide (x = 3)) (by decide) (by decide) r2
  have t := hacc 3 3 (by decide)
  have e1 : (fun x : Fin 13 => decide (x = 3)) = fun x => decide (x = 3) || false := by funext x; simp
  have e2 : (fun x : Fin 13 => decide (x = 3)) = fun x => false || decide (x = 3) := by funext x; simp
  rw [show (List.ofFn fun x : Fin 13 => decide (x = 3)) ++ List.ofFn (fun x : Fin 13 => decide (x = 3)) = List.ofFn (fun x : Fin 13 => decide (x = 3) || false) ++ List.ofFn (fun x : Fin 13 => false || decide (x = 3)) by simp, eval_hom2 C hg, a1, a2] at t
  exact absurd t (by decide)
