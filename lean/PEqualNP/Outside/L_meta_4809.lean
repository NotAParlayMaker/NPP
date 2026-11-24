import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4809
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem orm (a b a' b' : Bool) (h1 : a = true → a' = true) (h2 : b = true → b' = true) :
    (a || b) = true → (a' || b') = true := by
  intro h
  rw [Bool.or_eq_true] at h ⊢
  exact h.imp h1 h2

def e9 (c : Fin 42) (x : Fin 42 → Bool) : Fin 43 → Bool :=
  fun i => Fin.lastCases (x 0 || x c) x i

def e10 (c : Fin 42) (a b : Fin 43) (x : Fin 42 → Bool) : Fin 44 → Bool :=
  fun j => Fin.lastCases (e9 c x a || e9 c x b) (e9 c x) j

theorem e9_mono (c : Fin 42) (x y : Fin 42 → Bool) (h : ∀ i, x i = true → y i = true) :
    ∀ i, e9 c x i = true → e9 c y i = true := by
  intro i
  refine Fin.lastCases ?_ (fun t => ?_) i
  · unfold e9
    rw [Fin.lastCases_last, Fin.lastCases_last]
    exact orm _ _ _ _ (h 0) (h c)
  · unfold e9
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    exact h t

theorem e10_mono (c : Fin 42) (a b : Fin 43) (x y : Fin 42 → Bool)
    (h : ∀ i, x i = true → y i = true) : ∀ j, e10 c a b x j = true → e10 c a b y j = true := by
  intro j
  refine Fin.lastCases ?_ (fun t => ?_) j
  · unfold e10
    rw [Fin.lastCases_last, Fin.lastCases_last]
    exact orm _ _ _ _ (e9_mono c x y h a) (e9_mono c x y h b)
  · unfold e10
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    exact e9_mono c x y h t

end PEqualNP.Outside.L_meta_4809

open PEqualNP.Outside.L_meta_4809 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4809 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (42 : ℕ)) (x3 x4 : Fin (43 : ℕ)) (x5 : (Fin (42 : ℕ) → Bool) → Prop),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x7 : Fin (42 : ℕ) → Bool),         ((x5 x7 ∧ ∀ (x8 : Fin (42 : ℕ) → Bool), (∀ (x9 : Fin (42 : ℕ)), x8 x9 = Bool.true → x7 x9 = Bool.true) → x5 x8 → x8 = x7) ∨ ¬x5 x7 ∧ ∀ (x8 : Fin (42 : ℕ) → Bool), (∀ (x9 : Fin (42 : ℕ)), x7 x9 = Bool.true → x8 x9 = Bool.true) → ¬x5 x8 → x8 = x7) →           have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin (43 : ℕ)) => Fin.lastCases (x7 (0 : Fin (42 : ℕ)) || x7 x2) x7 x9;           x1.eval (List.ofFn fun (x10 : Fin (44 : ℕ)) => Fin.lastCases (x9 x3 || x9 x4) x9 x10) = Bool.true ↔ x5 x7) →       ∀ (x8 : Fin (42 : ℕ) → Bool),         have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin (43 : ℕ)) => Fin.lastCases (x8 (0 : Fin (42 : ℕ)) || x8 x2) x8 x9;         x1.eval (List.ofFn fun (x10 : Fin (44 : ℕ)) => Fin.lastCases (x9 x3 || x9 x4) x9 x10) = Bool.true ↔ x5 x8 := by
  intro C c a b P hC H x
  have hleg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    refine ⟨?_, (hC g hg).2⟩
    rcases (hC g hg).1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have mono : ∀ u v : Fin 42 → Bool, (∀ i, u i = true → v i = true) →
      C.eval (List.ofFn (e10 c a b u)) = true → C.eval (List.ofFn (e10 c a b v)) = true := by
    intro u v huv h
    exact mono2 C.gates hleg _ _ (by simp) (ofFn_mono 44 _ _ (e10_mono c a b u v huv)) C.output h
  have H' : ∀ y : Fin 42 → Bool,
      ((P y ∧ ∀ z : Fin 42 → Bool, (∀ i, z i = true → y i = true) → P z → z = y) ∨
        (¬ P y ∧ ∀ z : Fin 42 → Bool, (∀ i, y i = true → z i = true) → ¬ P z → z = y)) →
      (C.eval (List.ofFn (e10 c a b y)) = true ↔ P y) := fun y hy => H y hy
  show C.eval (List.ofFn (e10 c a b x)) = true ↔ P x
  by_cases hP : P x
  · obtain ⟨m, hmx, hmin⟩ := Finite.exists_le_minimal (p := P) hP
    have hm := H' m (Or.inl ⟨hmin.1, fun z hz hpz =>
      le_antisymm (fun i => Bool.le_iff_imp.2 (hz i)) (hmin.2 hpz (fun i => Bool.le_iff_imp.2 (hz i)))⟩)
    exact ⟨fun _ => hP, fun _ => mono m x (fun i => Bool.le_iff_imp.1 (hmx i)) (hm.2 hmin.1)⟩
  · obtain ⟨M, hxM, hmax⟩ := Finite.exists_le_maximal (p := fun y : Fin 42 → Bool => ¬ P y) hP
    have hM := H' M (Or.inr ⟨hmax.1, fun z hz hpz =>
      le_antisymm (hmax.2 hpz (fun i => Bool.le_iff_imp.2 (hz i))) (fun i => Bool.le_iff_imp.2 (hz i))⟩)
    exact ⟨fun h => absurd (hM.1 (mono x M (fun i => Bool.le_iff_imp.1 (hxM i)) h)) hmax.1,
      fun hp => absurd hp hP⟩
