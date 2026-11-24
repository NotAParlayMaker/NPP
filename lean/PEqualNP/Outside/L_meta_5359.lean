import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_5359

theorem getD_snoc (l : List Bool) (e : Bool) (i : ℕ) :
    (l ++ [e]).getD i false = if i < l.length then l.getD i false else if i = l.length then e else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : i - l.length ≠ 0 := by omega
    simp [this]

theorem len_fold (gs : List Gate) (a : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).length
      = a.length + gs.length := by
  induction gs generalizing a with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons]; rw [ih]; simp; omega

theorem prefix_fold (gs : List Gate) (a : List Bool) (i : ℕ) (hi : i < a.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD i false
      = a.getD i false := by
  induction gs generalizing a with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega), getD_snoc]
    simp only [hi, ↓reduceIte]

theorem agree_fold (gs : List Gate) (v : ℕ) (hv : ∀ g ∈ gs, v ∉ g.inputs) (a b : List Bool)
    (hl : a.length = b.length) (hab : ∀ i, i ≠ v → a.getD i false = b.getD i false) :
    ∀ i, i ≠ v →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD i false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).getD i false := by
  induction gs generalizing a b with
  | nil => simpa using hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have he : g.op.eval (g.inputs.map fun i => a.getD i false)
        = g.op.eval (g.inputs.map fun i => b.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro j hj
      exact hab j (fun h => hv g (by simp) (h ▸ hj))
    apply ih (fun g' hg' => hv g' (by simp [hg'])) _ _ (by simp [hl])
    intro i hi
    rw [getD_snoc, getD_snoc, he, hl]
    split_ifs <;> first | rfl | exact hab i hi



abbrev inc (a b : Fin 42) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ [0, 5, 7, 17, 20]

def c1 (v : Fin 42) : Fin 42 := Fin.ofNat 42 (if v.val < 21 then 21 + v.val else v.val - 21)
def c2 (v : Fin 42) : Fin 42 :=
  Fin.ofNat 42 (if v.val < 21 then 21 + (v.val + 5) % 21 else (v.val - 21 + 16) % 21)

theorem cand : ∀ v t : Fin 42, t ≠ v → ∃ w ∈ [c1 v, c2 v],
    (inc v w ∨ inc w v) ∧ ¬ inc t w ∧ ¬ inc w t := by
  decide +kernel


def inp (x1 : Fin 42) (x2 x3 : Fin 43) (y : Fin 42 → Bool) : List Bool :=
  List.ofFn fun (x11 : Fin ((43 : ℕ) + (1 : ℕ))) =>
    Fin.lastCases ((fun i : Fin 43 => Fin.lastCases (y 0 || y x1) y i) x2 ||
      (fun i : Fin 43 => Fin.lastCases (y 0 || y x1) y i) x3)
      (fun i : Fin 43 => Fin.lastCases (y 0 || y x1) y i) x11

theorem inp_getD (x1 : Fin 42) (x2 x3 : Fin 43) (y : Fin 42 → Bool) (j : Fin 42) :
    (inp x1 x2 x3 y).getD j.val false = y j := by
  unfold inp
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (by omega), Option.getD_some]
  have hj : (⟨j.val, by omega⟩ : Fin ((43 : ℕ) + (1 : ℕ))) = Fin.castSucc (Fin.castSucc j) := rfl
  rw [hj, Fin.lastCases_castSucc, Fin.lastCases_castSucc]

end PEqualNP.Outside.L_meta_5359

theorem PEqualNP.Outside.L_meta_5359 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ)) →     x2 < x3 →       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) →         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) →           (∀ (x9 : Fin (42 : ℕ) → Bool),               have x10 : Fin (43 : ℕ) → Bool := fun (x10 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x9 (0 : Fin (42 : ℕ)) || x9 x1) x9 x10;               x4.eval (List.ofFn fun (x11 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x10 x2 || x10 x3) x10 x11) = Bool.true ↔ ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)), (↑x11 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x12 ∧ (↑x12 + (21 : ℕ) - ↑x11) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x9 x11 = Bool.true ∧ x9 x12 = Bool.true) →             ∀ (x10 : Fin (42 : ℕ)), List.count ↑x10 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x12 ∈ x4.gates, ↑x10 ∈ x12.inputs := by
  intro x1 x2 x3 x4 h1 h23 hne hlast hf v hc
  by_contra hno
  push Not at hno
  simp only [List.count_cons, List.count_nil, beq_iff_eq] at hc
  have h1' : x1.val = 1 ∨ x1.val = 21 ∨ x1.val = 22 := by
    rcases h1 with rfl | rfl | rfl <;> simp
  have h23' : x2.val < x3.val := h23
  have hv42 : v.val < 42 := v.isLt
  have hx3 : x3.val < 43 := x3.isLt
  -- the partner t
  have hT : ∃ t : Fin 42, t ≠ v ∧ (((0 : Fin 42) = v ∨ x1 = v) → (t = 0 ∨ t = x1)) ∧
      ((v.val = x2.val ∨ v.val = x3.val) → (t.val = x2.val ∨ t.val = x3.val ∨
        (x3.val = 42 ∧ t = 0))) := by
    by_cases hv0 : v.val = 0
    · refine ⟨x1, ?_, ?_, ?_⟩
      · intro h; rw [Fin.ext_iff] at h; omega
      · intro _; exact Or.inr rfl
      · intro h; split_ifs at hc <;> omega
    by_cases hv1 : v.val = x1.val
    · refine ⟨0, ?_, ?_, ?_⟩
      · intro h; exact hv0 (by rw [← h]; rfl)
      · intro _; exact Or.inl rfl
      · intro h; split_ifs at hc <;> omega
    have hA : ¬ ((0 : Fin 42) = v ∨ x1 = v) := by
      rintro (h | h)
      · exact hv0 (by rw [← h]; rfl)
      · exact hv1 (by rw [← h])
    by_cases hv2 : v.val = x2.val
    · by_cases h42 : x3.val < 42
      · refine ⟨⟨x3.val, h42⟩, ?_, fun h => absurd h hA, ?_⟩
        · intro h; rw [Fin.ext_iff] at h; simp at h; omega
        · intro _; exact Or.inr (Or.inl rfl)
      · refine ⟨0, ?_, fun h => absurd h hA, ?_⟩
        · intro h; rw [Fin.ext_iff] at h; simp at h; omega
        · intro _; exact Or.inr (Or.inr ⟨by omega, rfl⟩)
    by_cases hv3 : v.val = x3.val
    · refine ⟨⟨x2.val, by omega⟩, ?_, fun h => absurd h hA, ?_⟩
      · intro h; rw [Fin.ext_iff] at h; simp at h; omega
      · intro _; exact Or.inl rfl
    · exfalso; split_ifs at hc <;> omega
  obtain ⟨t, htv, hT1, hT2⟩ := hT
  -- the wires seen by the circuit, as a function of the variables
  have hz : ∀ y y' : Fin 42 → Bool, y t = true → y' t = true → (∀ i, i ≠ v → y i = y' i) →
      ∀ k, k ≠ v.val →
      (List.ofFn fun (x11 : Fin ((43 : ℕ) + (1 : ℕ))) =>
        Fin.lastCases ((Fin.lastCases (y 0 || y x1) y : Fin 43 → Bool) x2 ||
          (Fin.lastCases (y 0 || y x1) y : Fin 43 → Bool) x3)
          (Fin.lastCases (y 0 || y x1) y : Fin 43 → Bool) x11).getD k false =
      (List.ofFn fun (x11 : Fin ((43 : ℕ) + (1 : ℕ))) =>
        Fin.lastCases ((Fin.lastCases (y' 0 || y' x1) y' : Fin 43 → Bool) x2 ||
          (Fin.lastCases (y' 0 || y' x1) y' : Fin 43 → Bool) x3)
          (Fin.lastCases (y' 0 || y' x1) y' : Fin 43 → Bool) x11).getD k false := by
    intro y y' hy hy' hyy k hk
    have W42 : (y 0 || y x1) = (y' 0 || y' x1) := by
      by_cases hA : ((0 : Fin 42) = v ∨ x1 = v)
      · rcases hT1 hA with rfl | rfl <;> simp [hy, hy']
      · push Not at hA
        rw [hyy 0 hA.1, hyy x1 hA.2]
    have Z : ∀ j : Fin 43, j.val ≠ v.val →
        (Fin.lastCases (y 0 || y x1) y : Fin 43 → Bool) j =
        (Fin.lastCases (y' 0 || y' x1) y' : Fin 43 → Bool) j := by
      intro j hj
      induction j using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; exact W42
      | cast j' =>
        simp only [Fin.lastCases_castSucc]
        apply hyy
        intro h; apply hj; rw [← h]; simp
    have W43 : ((Fin.lastCases (y 0 || y x1) y : Fin 43 → Bool) x2 ||
          (Fin.lastCases (y 0 || y x1) y : Fin 43 → Bool) x3) =
        ((Fin.lastCases (y' 0 || y' x1) y' : Fin 43 → Bool) x2 ||
          (Fin.lastCases (y' 0 || y' x1) y' : Fin 43 → Bool) x3) := by
      by_cases e2 : x2.val = v.val
      · rcases hT2 (Or.inl e2.symm) with h | h | ⟨h42, rfl⟩
        · exact absurd (Fin.ext (h.trans e2)) htv
        · have : x3 = Fin.castSucc t := Fin.ext (by simp [h])
          rw [this]; simp [Fin.lastCases_castSucc, hy, hy']
        · have : x3 = Fin.last 42 := Fin.ext (by simp [h42])
          rw [this]; simp only [Fin.lastCases_last, hy, hy', Bool.true_or, Bool.or_true]
      by_cases e3 : x3.val = v.val
      · rcases hT2 (Or.inr e3.symm) with h | h | ⟨h42, _⟩
        · have : x2 = Fin.castSucc t := Fin.ext (by simp [h])
          rw [this]; simp [Fin.lastCases_castSucc, hy, hy']
        · exact absurd (Fin.ext (h.trans e3)) htv
        · omega
      rw [Z x2 e2, Z x3 e3]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      List.getElem?_ofFn]
    split_ifs with hk44
    · simp only [Option.getD_some]
      have hik : (⟨k, hk44⟩ : Fin 44).val ≠ v.val := hk
      generalize (⟨k, hk44⟩ : Fin 44) = i at hik ⊢
      induction i using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; exact W43
      | cast j =>
        simp only [Fin.lastCases_castSucc]
        exact Z j (by simpa using hik)
    · rfl
  have hfI : ∀ y : Fin 42 → Bool, x4.eval (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 y) = true ↔
      ∃ a b : Fin 42, PEqualNP.Outside.L_meta_5359.inc a b ∧ y a = true ∧ y b = true :=
    fun y => hf y
  have hzI : ∀ y y' : Fin 42 → Bool, y t = true → y' t = true → (∀ i, i ≠ v → y i = y' i) →
      ∀ k, k ≠ v.val → (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 y).getD k false =
        (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 y').getD k false := hz
  have hlen : ∀ y, (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 y).length = 44 := by
    intro y; simp [PEqualNP.Outside.L_meta_5359.inp]
  have hself : ∀ a : Fin 42, ¬ PEqualNP.Outside.L_meta_5359.inc a a := by
    intro a h; unfold PEqualNP.Outside.L_meta_5359.inc at h; omega
  obtain ⟨w, -, hw1, hw2, hw3⟩ := PEqualNP.Outside.L_meta_5359.cand v t htv
  by_cases hout : x4.output = v.val
  · let y0 : Fin 42 → Bool := fun i => decide (i = v)
    have e1 : x4.eval (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 y0) = true := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [hout, PEqualNP.Outside.L_meta_5359.prefix_fold _ _ _ (by rw [hlen]; omega),
        PEqualNP.Outside.L_meta_5359.inp_getD]
      simp [y0]
    obtain ⟨a, b, hab, ha, hb⟩ := (hfI y0).1 e1
    simp only [y0, decide_eq_true_eq] at ha hb
    subst ha; subst hb
    exact hself _ hab
  · let x : Fin 42 → Bool := fun i => decide (i = v ∨ i = t ∨ i = w)
    let x' : Fin 42 → Bool := fun i => decide (i = t ∨ i = w)
    have ex : x4.eval (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 x) = true := by
      rw [hfI]
      rcases hw1 with h | h
      · exact ⟨v, w, h, by simp [x], by simp [x]⟩
      · exact ⟨w, v, h, by simp [x], by simp [x]⟩
    have ex' : x4.eval (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 x') = false := by
      by_contra hc'
      rw [Bool.not_eq_false, hfI] at hc'
      obtain ⟨a, b, hab, ha, hb⟩ := hc'
      simp only [x', decide_eq_true_eq] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hself _ hab
      · exact hw2 hab
      · exact hw3 hab
      · exact hself _ hab
    have heq : x4.eval (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 x) =
        x4.eval (PEqualNP.Outside.L_meta_5359.inp x1 x2 x3 x') := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      apply PEqualNP.Outside.L_meta_5359.agree_fold x4.gates v.val hno
      · rw [hlen, hlen]
      · apply hzI x x' (by simp [x]) (by simp [x'])
        intro i hi
        simp [x, x', hi]
      · exact hout
    rw [ex, ex'] at heq
    exact Bool.noConfusion heq
