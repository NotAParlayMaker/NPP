import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4809

open PEqualNP.CircuitLowerBounds

def wst (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_app_lt (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_last (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    intro hf i hi
    exact h i hi (hf i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨i, hi, hf⟩
    exact ⟨i, hi, h i hi hf⟩

theorem mono_fold (gs : List Gate) (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (U V : List Bool), U.length = V.length →
    (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (gs.foldl wst U).getD i false = true → (gs.foldl wst V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h; simpa using h
  | cons g gs ih =>
    intro U V hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hop g' (List.mem_cons_of_mem g hg')) _ _ (by simp [wst, hl])
    intro i hi
    rcases lt_trichotomy i U.length with hlt | heq | hgt
    · rw [show wst U g = U ++ _ from rfl, getD_app_lt _ _ _ hlt] at hi
      rw [show wst V g = V ++ _ from rfl, getD_app_lt _ _ _ (by omega)]
      exact h i hi
    · subst heq
      rw [show wst U g = U ++ _ from rfl, getD_last] at hi
      rw [show wst V g = V ++ _ from rfl, hl, getD_last]
      exact eval_mono g.op (hop g (List.mem_cons_self ..)) g.inputs _ _ (fun i _ => h i) hi
    · rw [getD_ge _ _ (by simp [wst]; omega)] at hi
      cases hi

theorem ofFn_rel {k : ℕ} (a b : Fin k → Bool) (h : ∀ i, a i = true → b i = true) :
    ∀ i, (List.ofFn a).getD i false = true → (List.ofFn b).getD i false = true := by
  intro i hi
  by_cases hlt : i < k
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some] at hi ⊢
    exact h _ hi
  · rw [getD_ge _ _ (by simp; omega)] at hi
    cases hi

theorem circ_mono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) {k : ℕ}
    (a b : Fin k → Bool) (h : ∀ i, a i = true → b i = true) :
    C.eval (List.ofFn a) = true → C.eval (List.ofFn b) = true := by
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  exact mono_fold C.gates hop (List.ofFn a) (List.ofFn b) (by simp) (ofFn_rel a b h) C.output

theorem lastCases_mono {k : ℕ} (u v : Bool) (a b : Fin k → Bool) (huv : u = true → v = true)
    (h : ∀ i, a i = true → b i = true) :
    ∀ i : Fin (k + 1), Fin.lastCases u a i = true → Fin.lastCases v b i = true := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using huv
  · simpa using h j

def cnt (y : Fin 42 → Bool) : ℕ := (Finset.univ.filter fun i => y i = true).card

theorem eq_of_le_cnt (y z : Fin 42 → Bool) (hle : ∀ i, y i = true → z i = true)
    (hc : cnt z ≤ cnt y) : y = z := by
  have hsub : (Finset.univ.filter fun i => y i = true) ⊆ (Finset.univ.filter fun i => z i = true) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hle i hi
  have heq := Finset.eq_of_subset_of_card_le hsub hc
  funext i
  have := congrArg (fun s => i ∈ s) heq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
  cases hy : y i <;> cases hz : z i <;> simp_all

end PEqualNP.Outside.L_meta_4809

open PEqualNP.Outside.L_meta_4809

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_4809 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (42 : ℕ)) (x3 x4 : Fin (43 : ℕ)) (x5 : (Fin (42 : ℕ) → Bool) → Prop),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x7 : Fin (42 : ℕ) → Bool),         ((x5 x7 ∧ ∀ (x8 : Fin (42 : ℕ) → Bool), (∀ (x9 : Fin (42 : ℕ)), x8 x9 = Bool.true → x7 x9 = Bool.true) → x5 x8 → x8 = x7) ∨ ¬x5 x7 ∧ ∀ (x8 : Fin (42 : ℕ) → Bool), (∀ (x9 : Fin (42 : ℕ)), x7 x9 = Bool.true → x8 x9 = Bool.true) → ¬x5 x8 → x8 = x7) →           have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin (43 : ℕ)) => Fin.lastCases (x7 (0 : Fin (42 : ℕ)) || x7 x2) x7 x9;           x1.eval (List.ofFn fun (x10 : Fin (44 : ℕ)) => Fin.lastCases (x9 x3 || x9 x4) x9 x10) = Bool.true ↔ x5 x7) →       ∀ (x8 : Fin (42 : ℕ) → Bool),         have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin (43 : ℕ)) => Fin.lastCases (x8 (0 : Fin (42 : ℕ)) || x8 x2) x8 x9;         x1.eval (List.ofFn fun (x10 : Fin (44 : ℕ)) => Fin.lastCases (x9 x3 || x9 x4) x9 x10) = Bool.true ↔ x5 x8 := by
  dsimp only
  intro C x2 x3 x4 P hC hext x
  classical
  have gmono : ∀ a b : Fin 42 → Bool, (∀ i, a i = true → b i = true) →
      C.eval (List.ofFn fun x10 : Fin 44 => Fin.lastCases
        ((Fin.lastCases (a 0 || a x2) a x3) || (Fin.lastCases (a 0 || a x2) a x4))
        (fun x9 : Fin 43 => Fin.lastCases (a 0 || a x2) a x9) x10) = true →
      C.eval (List.ofFn fun x10 : Fin 44 => Fin.lastCases
        ((Fin.lastCases (b 0 || b x2) b x3) || (Fin.lastCases (b 0 || b x2) b x4))
        (fun x9 : Fin 43 => Fin.lastCases (b 0 || b x2) b x9) x10) = true := by
    intro a b hab
    have h1 : ∀ i : Fin 43, Fin.lastCases (a 0 || a x2) a i = true →
        Fin.lastCases (b 0 || b x2) b i = true := by
      apply lastCases_mono
      · simp only [Bool.or_eq_true]
        rintro (h | h)
        · exact Or.inl (hab _ h)
        · exact Or.inr (hab _ h)
      · exact hab
    apply circ_mono C hC
    apply lastCases_mono
    · simp only [Bool.or_eq_true]
      rintro (h | h)
      · exact Or.inl (h1 _ h)
      · exact Or.inr (h1 _ h)
    · exact h1
  constructor
  · intro hg
    by_contra hP
    set S := Finset.univ.filter fun y : Fin 42 → Bool => (∀ i, x i = true → y i = true) ∧ ¬ P y
    have hne : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => hi, hP⟩⟩
    obtain ⟨M, hMS, hMmax⟩ := Finset.exists_max_image S cnt hne
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hMS
    have hmax : ∀ y : Fin 42 → Bool, (∀ i, M i = true → y i = true) → ¬ P y → y = M := by
      intro y hy hPy
      have hyS : y ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun i hi => hy i (hMS.1 i hi), hPy⟩
      exact (eq_of_le_cnt M y hy (hMmax y hyS)).symm
    have := (hext M (Or.inr ⟨hMS.2, hmax⟩)).mp (gmono x M hMS.1 hg)
    exact hMS.2 this
  · intro hP
    set S := Finset.univ.filter fun y : Fin 42 → Bool => (∀ i, y i = true → x i = true) ∧ P y
    have hne : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => hi, hP⟩⟩
    obtain ⟨m, hmS, hmmin⟩ := Finset.exists_min_image S cnt hne
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmS
    have hmin : ∀ y : Fin 42 → Bool, (∀ i, y i = true → m i = true) → P y → y = m := by
      intro y hy hPy
      have hyS : y ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun i hi => hmS.1 i (hy i hi), hPy⟩
      exact eq_of_le_cnt y m hy (hmmin y hyS)
    exact gmono m x hmS.1 ((hext m (Or.inl ⟨hmS.2, hmin⟩)).mpr hmS.2)
