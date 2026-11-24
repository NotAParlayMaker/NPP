import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5359

open PEqualNP.CircuitLowerBounds

def E (u v : Fin 42) : Bool :=
  decide (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ [0, 5, 7, 17, 20])

def nbr (a : Fin 42) : List (Fin 42) :=
  [0, 5, 7, 17, 20].map fun d => if a.val < 21 then (⟨21 + (a.val + d) % 21, by omega⟩ : Fin 42)
    else (⟨(a.val - 21 + 21 - d) % 21, by omega⟩ : Fin 42)

def chk : Bool := (List.finRange 42).all fun a =>
  (nbr a).all (fun y => E a y || E y a) &&
  (List.finRange 42).all fun h => a == h || (nbr a).any fun y => !E y h && !E h y

set_option maxRecDepth 100000 in
theorem chk_eq : chk = true := by decide

theorem pick (a h : Fin 42) (hne : a ≠ h) :
    ∃ y, (E a y || E y a) = true ∧ E y h = false ∧ E h y = false := by
  have := chk_eq
  simp only [chk, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    beq_iff_eq, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at this
  obtain ⟨h1, h2⟩ := this a
  rcases h2 h with h3 | ⟨y, hy, h4, h5⟩
  · exact absurd h3 hne
  · exact ⟨y, by simpa using h1 y hy, h4, h5⟩

theorem getD_app (w : List Bool) (v : Bool) (j : ℕ) :
    (w ++ [v]).getD j false =
      if j < w.length then w.getD j false else if j = w.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem fold_inv (a : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, a ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length → (∀ j, j ≠ a → w.getD j false = w'.getD j false) →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').length ∧
    ∀ j, j ≠ a →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD j false := by
  induction gs with
  | nil => intro w w' hl hj; exact ⟨hl, hj⟩
  | cons g gs ih =>
    intro w w' hl hj
    simp only [List.foldl_cons]
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      apply hj
      rintro rfl
      exact hg g (by simp) hi
    apply ih (fun g' hg' => hg g' (by simp [hg']))
    · simp [hl]
    · intro j hja
      rw [getD_app, getD_app, hv, hl, hj j hja]

theorem fold_pre (gs : List Gate) : ∀ w : List Bool, ∀ j, j < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false =
      w.getD j false := by
  induction gs with
  | nil => intro w j _; rfl
  | cons g gs ih =>
    intro w j hj
    simp only [List.foldl_cons]
    rw [ih _ j (by simp; omega), getD_app, if_pos hj]

theorem eval_eq (C : Circuit) (a : ℕ) (hg : ∀ g ∈ C.gates, a ∉ g.inputs) (ho : C.output ≠ a)
    (L L' : List Bool) (hl : L.length = L'.length)
    (hj : ∀ j, j ≠ a → L.getD j false = L'.getD j false) : C.eval L = C.eval L' :=
  (fold_inv a C.gates hg L L' hl hj).2 _ ho

theorem eval_out (C : Circuit) (L : List Bool) (h : C.output < L.length) :
    C.eval L = L.getD C.output false :=
  fold_pre C.gates L _ h

def y6 (x1 : Fin 42) (x9 : Fin 42 → Bool) : Fin 43 → Bool :=
  fun i => Fin.lastCases (x9 0 || x9 x1) x9 i

def inp (x1 : Fin 42) (x2 x3 : Fin 43) (x9 : Fin 42 → Bool) : List Bool :=
  List.ofFn fun j : Fin 44 => Fin.lastCases (y6 x1 x9 x2 || y6 x1 x9 x3) (y6 x1 x9) j

theorem y6_eq (x1 : Fin 42) (x9 : Fin 42 → Bool) (k : Fin 43) :
    y6 x1 x9 k = if h : k.val < 42 then x9 ⟨k.val, h⟩ else (x9 0 || x9 x1) := by
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [y6, Fin.lastCases_last]; simp
  · simp [y6]

theorem inp_getD (x1 : Fin 42) (x2 x3 : Fin 43) (x9 : Fin 42 → Bool) (j : ℕ) :
    (inp x1 x2 x3 x9).getD j false =
      if h : j < 42 then x9 ⟨j, h⟩ else if j = 42 then (x9 0 || x9 x1) else
      if j = 43 then (y6 x1 x9 x2 || y6 x1 x9 x3) else false := by
  simp only [inp, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h44 : j < 44
  · rw [dif_pos h44]
    by_cases h43 : j = 43
    · subst h43; rfl
    · have : (⟨j, h44⟩ : Fin 44) = Fin.castSucc ⟨j, by omega⟩ := rfl
      simp only [Option.getD_some]
      rw [this, Fin.lastCases_castSucc, y6_eq]
      simp only [Fin.coe_castSucc]
      split_ifs <;> first | rfl | omega
  · rw [dif_neg h44]
    split_ifs <;> first | rfl | omega

def P (x9 : Fin 42 → Bool) : Prop := ∃ x7 x8 : Fin 42, E x7 x8 = true ∧ x9 x7 = true ∧ x9 x8 = true

theorem E_self (u : Fin 42) : E u u = false := by
  simp only [E, decide_eq_false_iff_not]; omega

theorem core (C : Circuit) (x1 : Fin 42) (x2 x3 : Fin 43) (a h : Fin 42) (hah : a ≠ h)
    (hg : ∀ g ∈ C.gates, a.val ∉ g.inputs) (ho : C.output ≠ a.val)
    (hfun : ∀ x9, C.eval (inp x1 x2 x3 x9) = true ↔ P x9)
    (hA : ∀ x9 : Fin 42 → Bool, x9 h = true →
      (x9 0 || x9 x1) = ((x9 0 && (0 : Fin 42) != a) || (x9 x1 && x1 != a)))
    (hB : ∀ x9 : Fin 42 → Bool, x9 h = true →
      (y6 x1 x9 x2 || y6 x1 x9 x3) =
        (y6 x1 (fun i => x9 i && i != a) x2 || y6 x1 (fun i => x9 i && i != a) x3)) : False := by
  obtain ⟨y, hy1, hy2, hy3⟩ := pick a h hah
  have hya : y ≠ a := by rintro rfl; simp [E_self] at hy1
  let x9 : Fin 42 → Bool := fun i => i == a || i == y || i == h
  have hx9h : x9 h = true := by simp [x9]
  have heq : C.eval (inp x1 x2 x3 x9) = C.eval (inp x1 x2 x3 (fun i => x9 i && i != a)) := by
    apply eval_eq C a.val hg ho
    · simp [inp]
    · intro j hj
      rw [inp_getD, inp_getD]
      split_ifs with h1 h2 h3
      · have : ((⟨j, h1⟩ : Fin 42) != a) = true := by
          simp only [bne_iff_ne, ne_eq, Fin.ext_iff]; exact hj
        rw [this, Bool.and_true]
      · exact hA x9 hx9h
      · exact hB x9 hx9h
      · rfl
  have hP : P x9 := by
    rcases Bool.or_eq_true_iff.mp hy1 with e | e
    · exact ⟨a, y, e, by simp [x9], by simp [x9]⟩
    · exact ⟨y, a, e, by simp [x9], by simp [x9]⟩
  have hP' : P (fun i => x9 i && i != a) := by
    rw [← hfun, ← heq, hfun]; exact hP
  obtain ⟨u, v, e, hu, hv⟩ := hP'
  simp only [x9, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hu hv
  rcases hu with ⟨(⟨rfl | rfl⟩ | rfl), hu⟩ <;> rcases hv with ⟨(⟨rfl | rfl⟩ | rfl), hv⟩ <;>
    simp_all [E_self]

theorem cnt (n a b c d : ℕ) (h : List.count n [a, b, c, d] = 1) :
    (n = a ∧ n ≠ b ∧ n ≠ c ∧ n ≠ d) ∨ (n ≠ a ∧ n = b ∧ n ≠ c ∧ n ≠ d) ∨
    (n ≠ a ∧ n ≠ b ∧ n = c ∧ n ≠ d) ∨ (n ≠ a ∧ n ≠ b ∧ n ≠ c ∧ n = d) := by
  by_cases ha : a = n <;> by_cases hb : b = n <;> by_cases hc : c = n <;> by_cases hd : d = n <;>
    simp [List.count_cons, ha, hb, hc, hd] at h <;> omega

theorem y6_pt (x1 a : Fin 42) (x9 : Fin 42 → Bool)
    (hA : (x9 0 || x9 x1) = ((x9 0 && (0 : Fin 42) != a) || (x9 x1 && x1 != a)))
    (k : Fin 43) (hk : k.val ≠ a.val) :
    y6 x1 x9 k = y6 x1 (fun i => x9 i && i != a) k := by
  rw [y6_eq, y6_eq]
  split_ifs with h
  · have : ((⟨k.val, h⟩ : Fin 42) != a) = true := by
      simp only [bne_iff_ne, ne_eq, Fin.ext_iff]; exact hk
    rw [this, Bool.and_true]
  · exact hA

theorem hB_other (x1 a : Fin 42) (x9 : Fin 42 → Bool) (x2 x3 : Fin 43)
    (hA : (x9 0 || x9 x1) = ((x9 0 && (0 : Fin 42) != a) || (x9 x1 && x1 != a)))
    (hk : x3.val ≠ a.val) (ht : y6 x1 (fun i => x9 i && i != a) x3 = true) :
    (y6 x1 x9 x2 || y6 x1 x9 x3) =
      (y6 x1 (fun i => x9 i && i != a) x2 || y6 x1 (fun i => x9 i && i != a) x3) := by
  rw [y6_pt x1 a x9 hA x3 hk, ht]; simp

theorem hB_none (x1 a : Fin 42) (x9 : Fin 42 → Bool) (x2 x3 : Fin 43)
    (hA : (x9 0 || x9 x1) = ((x9 0 && (0 : Fin 42) != a) || (x9 x1 && x1 != a)))
    (h2 : x2.val ≠ a.val) (h3 : x3.val ≠ a.val) :
    (y6 x1 x9 x2 || y6 x1 x9 x3) =
      (y6 x1 (fun i => x9 i && i != a) x2 || y6 x1 (fun i => x9 i && i != a) x3) := by
  rw [y6_pt x1 a x9 hA x2 h2, y6_pt x1 a x9 hA x3 h3]

theorem hA_none (x1 a : Fin 42) (x9 : Fin 42 → Bool) (h0 : a.val ≠ 0) (h1 : a ≠ x1) :
    (x9 0 || x9 x1) = ((x9 0 && (0 : Fin 42) != a) || (x9 x1 && x1 != a)) := by
  have e0 : ((0 : Fin 42) != a) = true := by
    simp only [bne_iff_ne, ne_eq, Fin.ext_iff]; simp; omega
  have e1 : (x1 != a) = true := by simp only [bne_iff_ne, ne_eq]; exact fun h => h1 h.symm
  rw [e0, e1, Bool.and_true, Bool.and_true]

end PEqualNP.Outside.L_meta_5359

open PEqualNP.Outside.L_meta_5359 in
theorem PEqualNP.Outside.L_meta_5359 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ)) →     x2 < x3 →       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) →         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) →           (∀ (x9 : Fin (42 : ℕ) → Bool),               have x10 : Fin (43 : ℕ) → Bool := fun (x10 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x9 (0 : Fin (42 : ℕ)) || x9 x1) x9 x10;               x4.eval (List.ofFn fun (x11 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x10 x2 || x10 x3) x10 x11) = Bool.true ↔ ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)), (↑x11 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x12 ∧ (↑x12 + (21 : ℕ) - ↑x11) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x9 x11 = Bool.true ∧ x9 x12 = Bool.true) →             ∀ (x10 : Fin (42 : ℕ)), List.count ↑x10 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x12 ∈ x4.gates, ↑x10 ∈ x12.inputs := by
  intro x1 x2 x3 x4 _ _ _ _ hfun a hcount
  by_contra hno
  have hg : ∀ g ∈ x4.gates, a.val ∉ g.inputs := fun g hg hi => hno ⟨g, hg, hi⟩
  have hf : ∀ x9, x4.eval (inp x1 x2 x3 x9) = true ↔ P x9 := fun x9 => by
    have := hfun x9
    simp only [P, E, decide_eq_true_eq]
    exact this
  have bt : ∀ u : Fin 42, u.val ≠ a.val → (u != a) = true := fun u hu => by
    simp only [bne_iff_ne, ne_eq, Fin.ext_iff]; exact hu
  have bf : ∀ u : Fin 42, u.val = a.val → (u != a) = false := fun u hu => by
    simp only [bne_eq_false_iff_eq, Fin.ext_iff]; exact hu
  by_cases ho : x4.output = a.val
  · have h1 := (hf (fun i => i == a)).mp (by
      rw [eval_out x4 _ (by rw [ho]; simp [inp]; omega), ho, inp_getD, dif_pos a.isLt]
      simp)
    obtain ⟨u, v, e, hu, hv⟩ := h1
    simp only [beq_iff_eq] at hu hv
    subst hu hv
    simp [E_self] at e
  rcases cnt _ _ _ _ _ hcount with ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ |
      ⟨c0, c1, c2, c3⟩
  · have hA : ∀ x9 : Fin 42 → Bool, x9 x1 = true →
        (x9 0 || x9 x1) = ((x9 0 && (0 : Fin 42) != a) || (x9 x1 && x1 != a)) := by
      intro x9 hh
      rw [bf 0 (by simp; omega), bt x1 (by omega), hh]; simp
    exact core x4 x1 x2 x3 a x1 (fun h => c1 (by rw [h])) hg ho hf hA
      (fun x9 hh => hB_none x1 a x9 x2 x3 (hA x9 hh) (by omega) (by omega))
  · have hA : ∀ x9 : Fin 42 → Bool, x9 0 = true →
        (x9 0 || x9 x1) = ((x9 0 && (0 : Fin 42) != a) || (x9 x1 && x1 != a)) := by
      intro x9 hh
      rw [bt 0 (by simp; omega), bf x1 (by omega), hh]; simp
    exact core x4 x1 x2 x3 a 0 (fun h => c0 (by rw [h]; rfl)) hg ho hf hA
      (fun x9 hh => hB_none x1 a x9 x2 x3 (hA x9 hh) (by omega) (by omega))
  · have hA := fun x9 => hA_none x1 a x9 (by omega) (fun h => c1 (by rw [h]))
    by_cases h42 : x3.val < 42
    · refine core x4 x1 x2 x3 a ⟨x3.val, h42⟩ (fun h => c3 (by rw [h])) hg ho hf (fun x9 _ => hA x9)
        (fun x9 hh => hB_other x1 a x9 x2 x3 (hA x9) (by omega) ?_)
      rw [y6_eq, dif_pos h42]
      beta_reduce
      rw [hh, bt _ (by simp; omega)]; rfl
    · refine core x4 x1 x2 x3 a 0 (fun h => c0 (by rw [h]; rfl)) hg ho hf (fun x9 _ => hA x9)
        (fun x9 hh => hB_other x1 a x9 x2 x3 (hA x9) (by omega) ?_)
      rw [y6_eq, dif_neg h42]
      beta_reduce
      rw [hh, bt 0 (by simp; omega)]; rfl
  · have hA := fun x9 => hA_none x1 a x9 (by omega) (fun h => c1 (by rw [h]))
    have h42 : x2.val < 42 := by omega
    refine core x4 x1 x2 x3 a ⟨x2.val, h42⟩ (fun h => c2 (by rw [h])) hg ho hf (fun x9 _ => hA x9)
      (fun x9 hh => ?_)
    rw [Bool.or_comm (y6 x1 x9 x2), Bool.or_comm (y6 x1 _ x2)]
    refine hB_other x1 a x9 x3 x2 (hA x9) (by omega) ?_
    rw [y6_eq, dif_pos h42]
    beta_reduce
    rw [hh, bt _ (by simp; omega)]; rfl

