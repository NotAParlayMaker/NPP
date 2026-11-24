import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2802

open PEqualNP.CircuitLowerBounds

def F (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def inp (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_agree (S : ℕ → Prop) (gs : List Gate) (hS : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ S i) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ j, ¬ S j → w.getD j false = w'.getD j false) →
      ∀ j, ¬ S j → (gs.foldl step w).getD j false = (gs.foldl step w').getD j false := by
  induction gs with
  | nil => intro w w' _ h; exact h
  | cons g gs ih =>
    intro w w' hl h
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (hS g List.mem_cons_self i hi)
    apply ih (fun g' hg' => hS g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro j hj
      simp only [step]
      rcases lt_trichotomy j w.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h j hj
      · subst heq
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right le_rfl, List.getElem?_append_right (by omega)]
        simpa [hl, List.getD_eq_getElem?_getD] using hv
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma indep (C : Circuit) (S : ℕ → Prop) (x x' : Fin 9 → Bool)
    (hS : ∀ i ∈ C.gates.flatMap Gate.inputs, ¬ S i) (hout : ¬ S C.output)
    (hag : ∀ j, ¬ S j → (inp x).getD j false = (inp x').getD j false) :
    C.eval (inp x) = C.eval (inp x') := by
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  apply fold_agree S C.gates _ _ _ (by simp [inp]) hag _ hout
  intro g hg i hi
  exact hS i (List.mem_flatMap.2 ⟨g, hg, hi⟩)

lemma getD_inp (x : Fin 9 → Bool) (j : ℕ) :
    (inp x).getD j false =
      if h : j < 9 then x ⟨j, h⟩ else if j = 9 then (x 0 || x 6) else false := by
  unfold inp
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ (by simpa using h1),
      List.getD_eq_getElem _ _ (by simpa using h1), List.getElem_ofFn]
  · subst h2
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma agree_of (S : ℕ → Prop) (x x' : Fin 9 → Bool)
    (h1 : ∀ i : Fin 9, ¬ S i → x i = x' i)
    (h9 : ¬ S 9 → (x 0 || x 6) = (x' 0 || x' 6)) :
    ∀ j, ¬ S j → (inp x).getD j false = (inp x').getD j false := by
  intro j hj
  rw [getD_inp, getD_inp]
  split_ifs with a b
  · exact h1 ⟨j, a⟩ hj
  · subst b; exact h9 hj
  · rfl

lemma countP_eq_sum (L : List ℕ) :
    L.countP (fun v => decide (v < 10)) = ∑ v ∈ Finset.range 10, L.count v := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.countP_cons, ih]
    simp only [List.count_cons, Finset.sum_add_distrib]
    congr 1
    by_cases ha : a < 10
    · simp [ha, Finset.mem_range]
    · simp [ha, Finset.mem_range]

lemma fold_prefix (gs : List Gate) (w : List Bool) (j : ℕ) (h : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step]
    exact List.getD_append _ _ _ _ h

lemma eval_low (C : Circuit) (x : Fin 9 → Bool) (h : C.output < 10) :
    C.eval (inp x) = (inp x).getD C.output false := by
  unfold Circuit.eval
  rw [wires_eq, fold_prefix _ _ _ (by simpa [inp] using h)]

lemma out_high (C : Circuit) (hC : ∀ x, C.eval (inp x) = F x) : 10 ≤ C.output := by
  by_contra hlt
  push_neg at hlt
  have key : ∀ x, F x = (inp x).getD C.output false := fun x => by rw [← hC, eval_low C x hlt]
  rw [show C.output = C.output from rfl] at key
  interval_cases h : C.output
  · have := key (fun i => decide (i = 0)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 1)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 2)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 3)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 4)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 5)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 6)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 7)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 8)); revert this; rw [getD_inp]; decide
  · have := key (fun i => decide (i = 0)); revert this; rw [getD_inp]; decide

lemma no_read (C : Circuit) (hC : ∀ x, C.eval (inp x) = F x) (S : ℕ → Prop)
    (hS : ∀ i ∈ C.gates.flatMap Gate.inputs, ¬ S i) (hout : ¬ S C.output)
    (x x' : Fin 9 → Bool) (h1 : ∀ i : Fin 9, ¬ S i → x i = x' i)
    (h9 : ¬ S 9 → (x 0 || x 6) = (x' 0 || x' 6)) (hF : F x ≠ F x') : False :=
  hF (by rw [← hC, ← hC]; exact indep C S x x' hS hout (agree_of S x x' h1 h9))

lemma not_mem_of (L : List ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ v, P v → L.count v = 0) : ∀ i ∈ L, ¬ P i := by
  intro i hi hp
  have := h i hp
  rw [List.count_eq_zero] at this
  exact this hi

theorem main (C : Circuit) (hC : ∀ x, C.eval (inp x) = F x)
    (hcnt : List.countP (fun v => decide (v < 10)) (C.output :: C.gates.flatMap Gate.inputs)
      ≤ 15) :
    ∃ v : Fin 9, v ≠ 0 ∧ v ≠ 6 ∧ C.output ≠ (v : ℕ) ∧
      List.count (v : ℕ) (C.gates.flatMap Gate.inputs) = 1 := by
  set L := C.gates.flatMap Gate.inputs with hL
  have ho := out_high C hC
  have one : ∀ (v u : ℕ), v < 9 → u < 9 → v ≠ 0 → v ≠ 6 →
      F (fun i => decide ((i : ℕ) = u)) ≠ F (fun i => decide ((i : ℕ) = u ∨ (i : ℕ) = v)) →
      1 ≤ L.count v := by
    intro v u hv hu h0 h6 hF
    by_contra hc
    push_neg at hc
    have hag : ∀ i : Fin 9, (i : ℕ) ≠ v →
        (fun i : Fin 9 => decide ((i : ℕ) = u)) i =
          (fun i : Fin 9 => decide ((i : ℕ) = u ∨ (i : ℕ) = v)) i := by
      intro i hi
      simp [hi]
    refine no_read C hC (fun i => i = v)
      (not_mem_of L (fun i => i = v) (fun w hw => by subst hw; omega)) (by omega)
      _ _ (fun i hi => hag i hi) ?_ hF
    intro _
    exact congrArg₂ (fun a b => a || b)
      (hag 0 (by rw [show ((0 : Fin 9) : ℕ) = 0 from rfl]; omega))
      (hag 6 (by rw [show ((6 : Fin 9) : ℕ) = 6 from rfl]; omega))
  have c1 := one 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c2 := one 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c3 := one 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c4 := one 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c5 := one 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c7 := one 7 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have c8 := one 8 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have d09 : 1 ≤ L.count 0 + L.count 9 := by
    by_contra hc
    push_neg at hc
    refine no_read C hC (fun i => i = 0 ∨ i = 9)
      (not_mem_of L (fun i => i = 0 ∨ i = 9) (fun w hw => by rcases hw with rfl | rfl <;> omega))
      (by omega) (fun i => decide ((i : ℕ) = 1)) (fun i => decide ((i : ℕ) = 1 ∨ (i : ℕ) = 0))
      ?_ (fun h => absurd (Or.inr rfl) h) (by decide)
    intro i hi
    simp only [not_or] at hi
    simp [hi.1]
  have d69 : 1 ≤ L.count 6 + L.count 9 := by
    by_contra hc
    push_neg at hc
    refine no_read C hC (fun i => i = 6 ∨ i = 9)
      (not_mem_of L (fun i => i = 6 ∨ i = 9) (fun w hw => by rcases hw with rfl | rfl <;> omega))
      (by omega) (fun i => decide ((i : ℕ) = 1)) (fun i => decide ((i : ℕ) = 1 ∨ (i : ℕ) = 6))
      ?_ (fun h => absurd (Or.inr rfl) h) (by decide)
    intro i hi
    simp only [not_or] at hi
    simp [hi.1]
  have d06 : 1 ≤ L.count 9 → 1 ≤ L.count 0 + L.count 6 := by
    intro _
    by_contra hc
    push_neg at hc
    refine no_read C hC (fun i => i = 0 ∨ i = 6)
      (not_mem_of L (fun i => i = 0 ∨ i = 6) (fun w hw => by rcases hw with rfl | rfl <;> omega))
      (by omega) (fun i => decide ((i : ℕ) = 0 ∨ (i : ℕ) = 4))
      (fun i => decide ((i : ℕ) = 6 ∨ (i : ℕ) = 4)) ?_ (fun _ => by decide) (by decide)
    intro i hi
    simp only [not_or] at hi
    simp [hi.1, hi.2]
  have hsum := countP_eq_sum L
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
  have hle : List.countP (fun v => decide (v < 10)) L ≤ 15 := by
    rw [List.countP_cons] at hcnt
    omega
  by_contra hne
  push_neg at hne
  have e : ∀ v : Fin 9, v ≠ 0 → v ≠ 6 → L.count (v : ℕ) ≠ 1 := fun v a b =>
    hne v a b (by have := v.isLt; omega)
  have e1 := e 1 (by decide) (by decide)
  have e2 := e 2 (by decide) (by decide)
  have e3 := e 3 (by decide) (by decide)
  have e4 := e 4 (by decide) (by decide)
  have e5 := e 5 (by decide) (by decide)
  have e7 := e 7 (by decide) (by decide)
  have e8 := e 8 (by decide) (by decide)
  simp only [Fin.val_one, Fin.isValue] at e1 e2 e3 e4 e5 e7 e8
  have : ((2 : Fin 9) : ℕ) = 2 := rfl
  have : ((3 : Fin 9) : ℕ) = 3 := rfl
  have : ((4 : Fin 9) : ℕ) = 4 := rfl
  have : ((5 : Fin 9) : ℕ) = 5 := rfl
  have : ((7 : Fin 9) : ℕ) = 7 := rfl
  have : ((8 : Fin 9) : ℕ) = 8 := rfl
  simp_all only
  omega

end PEqualNP.Outside.L_meta_2802

theorem PEqualNP.Outside.L_meta_2802 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin (9 : ℕ) → Bool), x3.eval (x2 x4) = x1 x4) → List.countP (fun (x5 : ℕ) => Decidable.decide (x5 < (10 : ℕ))) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) ≤ (15 : ℕ) → ∃ (x6 : Fin (9 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) ∧ x6 ≠ (6 : Fin (9 : ℕ)) ∧ x3.output ≠ ↑x6 ∧ List.count (↑x6) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) = (1 : ℕ) := by
  intro f g C hC hcnt
  exact PEqualNP.Outside.L_meta_2802.main C hC hcnt
