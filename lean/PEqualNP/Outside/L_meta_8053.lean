import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8053

theorem imp_le : ∀ p q : Bool, (p = true → q = true) → p ≤ q := by decide

theorem le_imp : ∀ p q : Bool, p ≤ q → p = true → q = true := by decide

theorem or2 : ∀ p q p' q' : Bool, (p = true → p' = true) → (q = true → q' = true) →
    (p || q) = true → (p' || q') = true := by decide

theorem rel_append {u v u' v' : List Bool} (hl : u.length = v.length)
    (hp : ∀ i, u.getD i false = true → v.getD i false = true)
    (hl' : u'.length = v'.length)
    (hp' : ∀ i, u'.getD i false = true → v'.getD i false = true) :
    (u ++ u').length = (v ++ v').length ∧
      ∀ i, (u ++ u').getD i false = true → (v ++ v').getD i false = true := by
  refine ⟨by rw [List.length_append, List.length_append, hl, hl'], ?_⟩
  intro i hi
  have h2 := hp i
  have h3 := hp' (i - u.length)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at h2 h3 hi ⊢
  rw [← hl]
  by_cases hlt : i < u.length
  · rw [if_pos hlt] at hi ⊢
    exact h2 hi
  · rw [if_neg hlt] at hi ⊢
    exact h3 hi

theorem ofFn_rel {n : ℕ} (f g : Fin n → Bool) (h : ∀ j, f j = true → g j = true) :
    (List.ofFn f).length = (List.ofFn g).length ∧
      ∀ i, (List.ofFn f).getD i false = true → (List.ofFn g).getD i false = true := by
  refine ⟨by rw [List.length_ofFn, List.length_ofFn], ?_⟩
  intro i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
  by_cases hlt : i < n
  · simp only [dif_pos hlt, Option.getD_some] at hi ⊢
    exact h _ hi
  · simp [hlt] at hi

theorem single_rel (a b : Bool) (hab : a = true → b = true) :
    ∀ i, [a].getD i false = true → [b].getD i false = true := by
  intro i
  cases i with
  | zero => exact hab
  | succ k =>
    intro hi
    simp at hi

theorem all_mono (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) (l : List ℕ) :
    (l.map f).all id = true → (l.map f').all id = true := by
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun h1 => ⟨h a h1.1, ih h1.2⟩

theorem any_mono (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) (l : List ℕ) :
    (l.map f).any id = true → (l.map f').any id = true := by
  induction l with
  | nil => intro h1; exact h1
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    intro h1
    rcases h1 with h1 | h1
    · exact Or.inl (h a h1)
    · exact Or.inr (ih h1)

theorem gate_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with hg | hg
  · rw [hg]
    exact all_mono f f' h g.inputs
  · have hg' : g.op = GateOp.or := hg
    rw [hg']
    exact any_mono f f' h g.inputs

theorem wires_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (u v : List Bool), u.length = v.length →
      (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).getD i false = true := by
  induction gs with
  | nil => intro u v _ hp; exact hp
  | cons g t ih =>
    intro u v hl hp
    rw [List.foldl_cons, List.foldl_cons]
    have hstep := rel_append hl hp (u' := [g.op.eval (g.inputs.map fun i => u.getD i false)])
      (v' := [g.op.eval (g.inputs.map fun i => v.getD i false)]) rfl
      (single_rel _ _ (gate_mono g (hgs g (by simp)).1 _ _ hp))
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ hstep.1 hstep.2

def X (x : Fin 42 → Bool) (j : Fin 7) (k : ℕ) : Bool :=
  x (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑j + k) % (21 : ℕ)))

def L (x : Fin 42 → Bool) : List Bool :=
  (List.ofFn x ++ List.ofFn fun (j : Fin 7) => X x j 5 || X x j 17) ++
    List.ofFn fun (j : Fin 7) => X x j 5 || X x j 17 || X x j 20

theorem L_rel (a b : Fin 42 → Bool) (hab : ∀ i, a i = true → b i = true) :
    (L a).length = (L b).length ∧ ∀ i, (L a).getD i false = true → (L b).getD i false = true := by
  have hab' : ∀ j k, X a j k = true → X b j k = true := fun j k => hab _
  have h1 := ofFn_rel a b hab
  have h2 := ofFn_rel (fun (j : Fin 7) => X a j 5 || X a j 17) (fun (j : Fin 7) => X b j 5 || X b j 17)
    (fun j => or2 _ _ _ _ (hab' _ _) (hab' _ _))
  have h3 := ofFn_rel (fun (j : Fin 7) => X a j 5 || X a j 17 || X a j 20)
    (fun (j : Fin 7) => X b j 5 || X b j 17 || X b j 20)
    (fun j => or2 _ _ _ _ (or2 _ _ _ _ (hab' _ _) (hab' _ _)) (hab' _ _))
  have h12 := rel_append h1.1 h1.2 h2.1 h2.2
  exact rel_append h12.1 h12.2 h3.1 h3.2

theorem main (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    Monotone fun (x : Fin 42 → Bool) => C.eval (L x) := by
  intro a b hab
  apply imp_le
  have hr := L_rel a b (fun i => le_imp _ _ (hab i))
  exact wires_mono C.gates hC _ _ hr.1 hr.2 C.output

end PEqualNP.Outside.L_meta_8053

theorem PEqualNP.Outside.L_meta_8053 : have x1 : (Fin (42 : ℕ) → Bool) → List Bool := fun (x1 : Fin (42 : ℕ) → Bool) =>   have x2 : Fin (7 : ℕ) → ℕ → Bool := fun (x2 : Fin (7 : ℕ)) (x3 : ℕ) => x1 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x2 + x3) % (21 : ℕ)));   (List.ofFn x1 ++ List.ofFn fun (x3 : Fin (7 : ℕ)) => x2 x3 (5 : ℕ) || x2 x3 (17 : ℕ)) ++ List.ofFn fun (x3 : Fin (7 : ℕ)) => x2 x3 (5 : ℕ) || x2 x3 (17 : ℕ) || x2 x3 (20 : ℕ); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → Monotone fun (x4 : Fin (42 : ℕ) → Bool) => x2.eval (x1 x4) :=
  PEqualNP.Outside.L_meta_8053.main
