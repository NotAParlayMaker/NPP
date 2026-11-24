import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4676

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def S : Finset (Fin 13) := {0, 1, 3, 9}

def T : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ S → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ S}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ S)) = Bool.false

def Corr (C : Circuit) (l : List ℕ) : Prop :=
  T fun (x5 : List Bool) => C.eval (x5 ++ [l.any fun (x6 : ℕ) => x5.getD x6 Bool.false])

def Ord (C : Circuit) : Prop :=
  ∀ (x5 : Fin C.gates.length), ∀ x6 ∈ (C.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5

def R : List (List ℕ) := [[], [0], [13], [0, 1], [0, 2], [0, 13], [0, 14], [0, 15], [0, 17], [0, 20], [13, 14], [13, 15]]

def remap (σ : ℕ → ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (fun g => (⟨g.op, g.inputs.map σ⟩ : Gate)), σ C.output⟩

theorem getD_snoc (w : List Bool) (v : Bool) (j : ℕ) :
    (w ++ [v]).getD j false =
      if j < w.length then w.getD j false else if j = w.length then v else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem fold_rel (σ : ℕ → ℕ) (h1 : ∀ j, 26 ≤ j → σ j = j) (h2 : ∀ j, j < 26 → σ j < 26) :
    ∀ (gs : List Gate) (w w' : List Bool), w.length = w'.length → 26 ≤ w.length →
      (∀ j, w'.getD (σ j) false = w.getD j false) →
      ∀ j, ((gs.map (fun g => (⟨g.op, g.inputs.map σ⟩ : Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (σ j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false := by
  intro gs
  induction gs with
  | nil => intro w w' _ _ hw j; exact hw j
  | cons g gs ih =>
    intro w w' hl h26 hw
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [hl]
    · simp; omega
    · intro j
      have hv : g.op.eval ((g.inputs.map σ).map fun i => w'.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [List.map_map]; congr 1; apply List.map_congr_left; intro i _; exact hw i
      rw [getD_snoc, getD_snoc, hv]
      by_cases hj : j < w.length
      · have : σ j < w'.length := by
          by_cases h : j < 26
          · have := h2 j h; omega
          · rw [h1 j (by omega)]; omega
        rw [if_pos this, if_pos hj]; exact hw j
      · rw [h1 j (by omega), if_neg hj, if_neg (by omega), ← hl]

theorem eval_remap (σ : ℕ → ℕ) (h1 : ∀ j, 26 ≤ j → σ j = j) (h2 : ∀ j, j < 26 → σ j < 26)
    (C : Circuit) (X Y : List Bool) (hl : Y.length = X.length) (h26 : 26 ≤ Y.length)
    (hXY : ∀ j, X.getD (σ j) false = Y.getD j false) :
    (remap σ C).eval X = C.eval Y :=
  fold_rel σ h1 h2 C.gates Y X hl h26 hXY C.output

theorem mono_remap (σ : ℕ → ℕ) (C : Circuit) (h : Monotone2 C) : Monotone2 (remap σ C) := by
  intro g hg
  simp only [remap, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa using h g0 hg0

theorem ord_remap (σ : ℕ → ℕ) (h1 : ∀ j, 26 ≤ j → σ j = j) (h2 : ∀ j, j < 26 → σ j < 26)
    (C : Circuit) (h : Ord C) : Ord (remap σ C) := by
  intro i a ha
  have hi : i.val < C.gates.length := by simpa [remap] using i.isLt
  have hg : (remap σ C).gates.get i =
      ⟨(C.gates.get ⟨i.val, hi⟩).op, (C.gates.get ⟨i.val, hi⟩).inputs.map σ⟩ := by
    rw [List.get_eq_getElem]; simp [remap]
  rw [hg, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have := h ⟨i.val, hi⟩ b (by simpa using hb)
  by_cases hb26 : b < 26
  · have := h2 b hb26; simp at this ⊢; omega
  · rw [h1 b (by omega)]; simpa using this

def U : Finset (Fin 13) := {1, 3, 9}

theorem S_inv : ∀ w ∈ U, ∀ d : Fin 13, (w * d ∈ S ↔ d ∈ S) := by decide

theorem U_alg : ∀ u ∈ U, ∀ c q r : Fin 13, (u * u) * (u * q + c - c) = q ∧
    u * ((u * u) * (q - c)) + c = q ∧ (u * u) * (q - c) - (u * u) * (r - c) = (u * u) * (q - r) := by
  decide

theorem U_cube : ∀ w ∈ U, w * w ∈ U ∧ (w * w) * w = 1 := by decide

def sig (u c : Fin 13) (j : ℕ) : ℕ :=
  if h : j < 13 then (u * (⟨j, h⟩ : Fin 13) + c).val
  else if h' : j < 26 then 13 + (u * (⟨j - 13, by omega⟩ : Fin 13) + c).val else j

theorem sig_ge (u c : Fin 13) (j : ℕ) (h : 26 ≤ j) : sig u c j = j := by
  unfold sig; rw [dif_neg (by omega), dif_neg (by omega)]

theorem sig_lt (u c : Fin 13) (j : ℕ) (h : j < 26) : sig u c j < 26 := by
  unfold sig; split_ifs <;> omega

theorem getD_two (A B : Fin 13 → Bool) (j : ℕ) :
    (List.ofFn A ++ List.ofFn B).getD j false =
      if h : j < 13 then A ⟨j, h⟩ else if h' : j < 26 then B ⟨j - 13, by omega⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h h'
  · rw [List.getElem?_append_left (by simpa using h), List.getElem?_ofFn]; simp [h]
  · rw [List.getElem?_append_right (by simp; omega), List.length_ofFn, List.getElem?_ofFn]
    simp [show j - 13 < 13 by omega]
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem transfer (u v c : Fin 13) (huv : v * u = 1) (C : Circuit) (l rep : List ℕ)
    (hset : ∀ j < 26, (j ∈ l.map (sig u c) ↔ j ∈ rep))
    (A B A' B' : Fin 13 → Bool) (hA : ∀ q, A (u * q + c) = A' q) (hB : ∀ q, B (u * q + c) = B' q) :
    (remap (sig u c) C).eval ((List.ofFn A ++ List.ofFn B) ++
        [rep.any fun j => (List.ofFn A ++ List.ofFn B).getD j false]) =
      C.eval ((List.ofFn A' ++ List.ofFn B') ++
        [l.any fun j => (List.ofFn A' ++ List.ofFn B').getD j false]) := by
  have hg : ∀ j, (List.ofFn A ++ List.ofFn B).getD (sig u c j) false =
      (List.ofFn A' ++ List.ofFn B').getD j false := by
    intro j
    rw [getD_two, getD_two]
    by_cases h : j < 13
    · have hs : sig u c j = (u * (⟨j, h⟩ : Fin 13) + c).val := by unfold sig; rw [dif_pos h]
      rw [dif_pos h, hs, dif_pos (Fin.isLt _), ← hA]
    · by_cases h' : j < 26
      · have hs : sig u c j = 13 + (u * (⟨j - 13, by omega⟩ : Fin 13) + c).val := by
          unfold sig; rw [dif_neg h, dif_pos h']
        rw [dif_neg h, dif_pos h', hs, dif_neg (by omega), dif_pos (by omega), ← hB]
        congr 1; ext; simp
      · rw [sig_ge u c j (by omega)]; simp [h, h']
  have hlen : (List.ofFn A ++ List.ofFn B).length = 26 := by simp
  have hor : rep.any (fun j => (List.ofFn A ++ List.ofFn B).getD j false) =
      l.any (fun j => (List.ofFn A' ++ List.ofFn B').getD j false) := by
    simp only [← hg]
    rw [show (l.any fun j => (List.ofFn A ++ List.ofFn B).getD (sig u c j) false) =
      (l.map (sig u c)).any (fun j => (List.ofFn A ++ List.ofFn B).getD j false) by
        rw [List.any_map]; rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨j, hj, hv⟩
      have h26 : j < 26 := by
        by_contra hc
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hv; simp at hv
      exact ⟨j, (hset j h26).2 hj, hv⟩
    · rintro ⟨j, hj, hv⟩
      have h26 : j < 26 := by
        by_contra hc
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hv; simp at hv
      exact ⟨j, (hset j h26).1 hj, hv⟩
  apply eval_remap (sig u c) (sig_ge u c) (sig_lt u c)
  · simp
  · simp
  · intro j
    rw [getD_snoc, getD_snoc, hor]
    simp only [List.length_append, List.length_ofFn]
    by_cases hj : j < 26
    · rw [if_pos (by simpa using sig_lt u c j hj), if_pos (by omega)]; exact hg j
    · rw [sig_ge u c j (by omega)]; simp only [show ¬ j < 13 + 13 by omega, if_false]

theorem key (u c : Fin 13) (hu : u ∈ U) (C : Circuit) (l rep : List ℕ)
    (hset : ∀ j < 26, (j ∈ l.map (sig u c) ↔ j ∈ rep)) (hC : Corr C l) :
    Corr (remap (sig u c) C) rep := by
  obtain ⟨hv, huv⟩ := U_cube u hu
  set v := u * u
  let π : Fin 13 → Fin 13 := fun q => u * q + c
  let πi : Fin 13 → Fin 13 := fun q => v * (q - c)
  have h1 : ∀ q, πi (π q) = q := fun q => (U_alg u hu c q q).1
  have h2 : ∀ q, π (πi q) = q := fun q => (U_alg u hu c q q).2.1
  have hsub : ∀ r s, πi r - πi s = v * (r - s) := fun r s => (U_alg u hu c r s).2.2
  have hS : ∀ r s, (πi r - πi s ∈ S ↔ r - s ∈ S) := by intro r s; rw [hsub]; exact S_inv v hv _
  obtain ⟨hpos, hneg⟩ := hC
  beta_reduce at hpos hneg ⊢
  constructor
  · intro p q hpq
    beta_reduce
    rw [transfer u v c huv C l rep hset _ _ (fun x => decide (x = πi p)) (fun x => decide (x = πi q))]
    · exact hpos _ _ ((hS p q).2 hpq)
    · intro x; simp only [decide_eq_decide]
      constructor
      · intro h; rw [← h]; exact (h1 x).symm
      · intro h; rw [h]; exact h2 p
    · intro x; simp only [decide_eq_decide]
      constructor
      · intro h; rw [← h]; exact (h1 x).symm
      · intro h; rw [h]; exact h2 q
  · intro P hcard harc
    beta_reduce
    have hinj : Function.Injective πi := Function.LeftInverse.injective h2
    rw [transfer u v c huv C l rep hset _ _ (fun x => decide (x ∈ P.image πi))
      (fun x => decide (∀ y ∈ P.image πi, y - x ∉ S))]
    · apply hneg
      · rw [Finset.card_image_of_injective P hinj, hcard]
      · intro m
        rw [Finset.filter_image]
        refine Finset.card_image_le.trans (le_trans (le_of_eq ?_) (harc (π m)))
        congr 1
        apply Finset.filter_congr
        intro x _
        rw [← hS x (π m), h1]
    · intro x; simp only [decide_eq_decide, Finset.mem_image]
      constructor
      · intro h; exact ⟨π x, h, h1 x⟩
      · rintro ⟨r, hr, rfl⟩
        have := h2 r
        simp only [π] at this
        rw [this]; exact hr
    · intro x; simp only [decide_eq_decide, Finset.forall_mem_image]
      apply forall₂_congr; intro y _
      rw [← hS y (π x), h1]

def tbl : List (List (Fin 13 × Fin 13 × ℕ)) :=
  [[(1, 0, 1), (1, 0, 3), (1, 0, 4), (9, 0, 3), (3, 1, 3), (3, 0, 4), (9, 0, 4), (9, 2, 4), (3, 2, 4), (3, 0, 3), (9, 1, 3), (1, 2, 4), (1, 1, 3), (1, 0, 5), (1, 0, 6), (1, 0, 7), (9, 0, 6), (1, 0, 8), (3, 0, 7), (9, 0, 7), (1, 0, 9), (9, 0, 9), (3, 0, 6), (3, 0, 8), (3, 0, 9), (9, 0, 8), (1, 0, 1)],
  [(1, 0, 3), (1, 12, 1), (1, 12, 3), (1, 12, 4), (9, 4, 3), (3, 11, 3), (3, 10, 4), (9, 4, 4), (9, 6, 4), (3, 12, 4), (3, 10, 3), (9, 5, 3), (1, 1, 4), (9, 4, 8), (1, 12, 5), (1, 12, 6), (1, 12, 7), (9, 4, 6), (1, 12, 8), (3, 10, 7), (9, 4, 7), (1, 12, 9), (9, 4, 9), (3, 10, 6), (3, 10, 8), (3, 10, 9), (1, 12, 1)],
  [(1, 0, 4), (1, 12, 3), (1, 11, 1), (1, 11, 3), (1, 11, 4), (9, 8, 3), (3, 8, 3), (3, 7, 4), (9, 8, 4), (9, 10, 4), (3, 9, 4), (3, 7, 3), (9, 9, 3), (3, 7, 9), (9, 8, 8), (1, 11, 5), (1, 11, 6), (1, 11, 7), (9, 8, 6), (1, 11, 8), (3, 7, 7), (9, 8, 7), (1, 11, 9), (9, 8, 9), (3, 7, 6), (3, 7, 8), (1, 11, 1)],
  [(9, 0, 3), (1, 12, 4), (1, 11, 3), (1, 10, 1), (1, 10, 3), (1, 10, 4), (9, 12, 3), (3, 5, 3), (3, 4, 4), (9, 12, 4), (9, 1, 4), (3, 6, 4), (3, 4, 3), (3, 4, 8), (3, 4, 9), (9, 12, 8), (1, 10, 5), (1, 10, 6), (1, 10, 7), (9, 12, 6), (1, 10, 8), (3, 4, 7), (9, 12, 7), (1, 10, 9), (9, 12, 9), (3, 4, 6), (1, 10, 1)],
  [(3, 1, 3), (9, 4, 3), (1, 11, 4), (1, 10, 3), (1, 9, 1), (1, 9, 3), (1, 9, 4), (9, 3, 3), (3, 2, 3), (3, 1, 4), (9, 3, 4), (9, 5, 4), (3, 3, 4), (3, 1, 6), (3, 1, 8), (3, 1, 9), (9, 3, 8), (1, 9, 5), (1, 9, 6), (1, 9, 7), (9, 3, 6), (1, 9, 8), (3, 1, 7), (9, 3, 7), (1, 9, 9), (9, 3, 9), (1, 9, 1)],
  [(3, 0, 4), (3, 11, 3), (9, 8, 3), (1, 10, 4), (1, 9, 3), (1, 8, 1), (1, 8, 3), (1, 8, 4), (9, 7, 3), (3, 12, 3), (3, 11, 4), (9, 7, 4), (9, 9, 4), (9, 7, 9), (3, 11, 6), (3, 11, 8), (3, 11, 9), (9, 7, 8), (1, 8, 5), (1, 8, 6), (1, 8, 7), (9, 7, 6), (1, 8, 8), (3, 11, 7), (9, 7, 7), (1, 8, 9), (1, 8, 1)],
  [(9, 0, 4), (3, 10, 4), (3, 8, 3), (9, 12, 3), (1, 9, 4), (1, 8, 3), (1, 7, 1), (1, 7, 3), (1, 7, 4), (9, 11, 3), (3, 9, 3), (3, 8, 4), (9, 11, 4), (1, 7, 9), (9, 11, 9), (3, 8, 6), (3, 8, 8), (3, 8, 9), (9, 11, 8), (1, 7, 5), (1, 7, 6), (1, 7, 7), (9, 11, 6), (1, 7, 8), (3, 8, 7), (9, 11, 7), (1, 7, 1)],
  [(9, 2, 4), (9, 4, 4), (3, 7, 4), (3, 5, 3), (9, 3, 3), (1, 8, 4), (1, 7, 3), (1, 6, 1), (1, 6, 3), (1, 6, 4), (9, 2, 3), (3, 6, 3), (3, 5, 4), (9, 2, 7), (1, 6, 9), (9, 2, 9), (3, 5, 6), (3, 5, 8), (3, 5, 9), (9, 2, 8), (1, 6, 5), (1, 6, 6), (1, 6, 7), (9, 2, 6), (1, 6, 8), (3, 5, 7), (1, 6, 1)],
  [(3, 2, 4), (9, 6, 4), (9, 8, 4), (3, 4, 4), (3, 2, 3), (9, 7, 3), (1, 7, 4), (1, 6, 3), (1, 5, 1), (1, 5, 3), (1, 5, 4), (9, 6, 3), (3, 3, 3), (3, 2, 7), (9, 6, 7), (1, 5, 9), (9, 6, 9), (3, 2, 6), (3, 2, 8), (3, 2, 9), (9, 6, 8), (1, 5, 5), (1, 5, 6), (1, 5, 7), (9, 6, 6), (1, 5, 8), (1, 5, 1)],
  [(3, 0, 3), (3, 12, 4), (9, 10, 4), (9, 12, 4), (3, 1, 4), (3, 12, 3), (9, 11, 3), (1, 6, 4), (1, 5, 3), (1, 4, 1), (1, 4, 3), (1, 4, 4), (9, 10, 3), (1, 4, 8), (3, 12, 7), (9, 10, 7), (1, 4, 9), (9, 10, 9), (3, 12, 6), (3, 12, 8), (3, 12, 9), (9, 10, 8), (1, 4, 5), (1, 4, 6), (1, 4, 7), (9, 10, 6), (1, 4, 1)],
  [(9, 1, 3), (3, 10, 3), (3, 9, 4), (9, 1, 4), (9, 3, 4), (3, 11, 4), (3, 9, 3), (9, 2, 3), (1, 5, 4), (1, 4, 3), (1, 3, 1), (1, 3, 3), (1, 3, 4), (9, 1, 6), (1, 3, 8), (3, 9, 7), (9, 1, 7), (1, 3, 9), (9, 1, 9), (3, 9, 6), (3, 9, 8), (3, 9, 9), (9, 1, 8), (1, 3, 5), (1, 3, 6), (1, 3, 7), (1, 3, 1)],
  [(1, 2, 4), (9, 5, 3), (3, 7, 3), (3, 6, 4), (9, 5, 4), (9, 7, 4), (3, 8, 4), (3, 6, 3), (9, 6, 3), (1, 4, 4), (1, 3, 3), (1, 2, 1), (1, 2, 3), (1, 2, 7), (9, 5, 6), (1, 2, 8), (3, 6, 7), (9, 5, 7), (1, 2, 9), (9, 5, 9), (3, 6, 6), (3, 6, 8), (3, 6, 9), (9, 5, 8), (1, 2, 5), (1, 2, 6), (1, 2, 1)],
  [(1, 1, 3), (1, 1, 4), (9, 9, 3), (3, 4, 3), (3, 3, 4), (9, 9, 4), (9, 11, 4), (3, 5, 4), (3, 3, 3), (9, 10, 3), (1, 3, 4), (1, 2, 3), (1, 1, 1), (1, 1, 6), (1, 1, 7), (9, 9, 6), (1, 1, 8), (3, 3, 7), (9, 9, 7), (1, 1, 9), (9, 9, 9), (3, 3, 6), (3, 3, 8), (3, 3, 9), (9, 9, 8), (1, 1, 5), (1, 1, 1)],
  [(1, 0, 5), (9, 4, 8), (3, 7, 9), (3, 4, 8), (3, 1, 6), (9, 7, 9), (1, 7, 9), (9, 2, 7), (3, 2, 7), (1, 4, 8), (9, 1, 6), (1, 2, 7), (1, 1, 6), (1, 0, 2), (1, 0, 10), (1, 0, 11), (9, 0, 10), (3, 1, 10), (3, 0, 11), (9, 0, 11), (9, 2, 11), (3, 2, 11), (3, 0, 10), (9, 1, 10), (1, 2, 11), (1, 1, 10), (1, 0, 2)],
  [(1, 0, 6), (1, 12, 5), (9, 8, 8), (3, 4, 9), (3, 1, 8), (3, 11, 6), (9, 11, 9), (1, 6, 9), (9, 6, 7), (3, 12, 7), (1, 3, 8), (9, 5, 6), (1, 1, 7), (1, 0, 10), (1, 12, 2), (1, 12, 10), (1, 12, 11), (9, 4, 10), (3, 11, 10), (3, 10, 11), (9, 4, 11), (9, 6, 11), (3, 12, 11), (3, 10, 10), (9, 5, 10), (1, 1, 11), (1, 12, 2)],
  [(1, 0, 7), (1, 12, 6), (1, 11, 5), (9, 12, 8), (3, 1, 9), (3, 11, 8), (3, 8, 6), (9, 2, 9), (1, 5, 9), (9, 10, 7), (3, 9, 7), (1, 2, 8), (9, 9, 6), (1, 0, 11), (1, 12, 10), (1, 11, 2), (1, 11, 10), (1, 11, 11), (9, 8, 10), (3, 8, 10), (3, 7, 11), (9, 8, 11), (9, 10, 11), (3, 9, 11), (3, 7, 10), (9, 9, 10), (1, 11, 2)],
  [(9, 0, 6), (1, 12, 7), (1, 11, 6), (1, 10, 5), (9, 3, 8), (3, 11, 9), (3, 8, 8), (3, 5, 6), (9, 6, 9), (1, 4, 9), (9, 1, 7), (3, 6, 7), (1, 1, 8), (9, 0, 10), (1, 12, 11), (1, 11, 10), (1, 10, 2), (1, 10, 10), (1, 10, 11), (9, 12, 10), (3, 5, 10), (3, 4, 11), (9, 12, 11), (9, 1, 11), (3, 6, 11), (3, 4, 10), (1, 10, 2)],
  [(1, 0, 8), (9, 4, 6), (1, 11, 7), (1, 10, 6), (1, 9, 5), (9, 7, 8), (3, 8, 9), (3, 5, 8), (3, 2, 6), (9, 10, 9), (1, 3, 9), (9, 5, 7), (3, 3, 7), (3, 1, 10), (9, 4, 10), (1, 11, 11), (1, 10, 10), (1, 9, 2), (1, 9, 10), (1, 9, 11), (9, 3, 10), (3, 2, 10), (3, 1, 11), (9, 3, 11), (9, 5, 11), (3, 3, 11), (1, 9, 2)],
  [(3, 0, 7), (1, 12, 8), (9, 8, 6), (1, 10, 7), (1, 9, 6), (1, 8, 5), (9, 11, 8), (3, 5, 9), (3, 2, 8), (3, 12, 6), (9, 1, 9), (1, 2, 9), (9, 9, 7), (3, 0, 11), (3, 11, 10), (9, 8, 10), (1, 10, 11), (1, 9, 10), (1, 8, 2), (1, 8, 10), (1, 8, 11), (9, 7, 10), (3, 12, 10), (3, 11, 11), (9, 7, 11), (9, 9, 11), (1, 8, 2)],
  [(9, 0, 7), (3, 10, 7), (1, 11, 8), (9, 12, 6), (1, 9, 7), (1, 8, 6), (1, 7, 5), (9, 2, 8), (3, 2, 9), (3, 12, 8), (3, 9, 6), (9, 5, 9), (1, 1, 9), (9, 0, 11), (3, 10, 11), (3, 8, 10), (9, 12, 10), (1, 9, 11), (1, 8, 10), (1, 7, 2), (1, 7, 10), (1, 7, 11), (9, 11, 10), (3, 9, 10), (3, 8, 11), (9, 11, 11), (1, 7, 2)],
  [(1, 0, 9), (9, 4, 7), (3, 7, 7), (1, 10, 8), (9, 3, 6), (1, 8, 7), (1, 7, 6), (1, 6, 5), (9, 6, 8), (3, 12, 9), (3, 9, 8), (3, 6, 6), (9, 9, 9), (9, 2, 11), (9, 4, 11), (3, 7, 11), (3, 5, 10), (9, 3, 10), (1, 8, 11), (1, 7, 10), (1, 6, 2), (1, 6, 10), (1, 6, 11), (9, 2, 10), (3, 6, 10), (3, 5, 11), (1, 6, 2)],
  [(9, 0, 9), (1, 12, 9), (9, 8, 7), (3, 4, 7), (1, 9, 8), (9, 7, 6), (1, 7, 7), (1, 6, 6), (1, 5, 5), (9, 10, 8), (3, 9, 9), (3, 6, 8), (3, 3, 6), (3, 2, 11), (9, 6, 11), (9, 8, 11), (3, 4, 11), (3, 2, 10), (9, 7, 10), (1, 7, 11), (1, 6, 10), (1, 5, 2), (1, 5, 10), (1, 5, 11), (9, 6, 10), (3, 3, 10), (1, 5, 2)],
  [(3, 0, 6), (9, 4, 9), (1, 11, 9), (9, 12, 7), (3, 1, 7), (1, 8, 8), (9, 11, 6), (1, 6, 7), (1, 5, 6), (1, 4, 5), (9, 1, 8), (3, 6, 9), (3, 3, 8), (3, 0, 10), (3, 12, 11), (9, 10, 11), (9, 12, 11), (3, 1, 11), (3, 12, 10), (9, 11, 10), (1, 6, 11), (1, 5, 10), (1, 4, 2), (1, 4, 10), (1, 4, 11), (9, 10, 10), (1, 4, 2)],
  [(3, 0, 8), (3, 10, 6), (9, 8, 9), (1, 10, 9), (9, 3, 7), (3, 11, 7), (1, 7, 8), (9, 2, 6), (1, 5, 7), (1, 4, 6), (1, 3, 5), (9, 5, 8), (3, 3, 9), (9, 1, 10), (3, 10, 10), (3, 9, 11), (9, 1, 11), (9, 3, 11), (3, 11, 11), (3, 9, 10), (9, 2, 10), (1, 5, 11), (1, 4, 10), (1, 3, 2), (1, 3, 10), (1, 3, 11), (1, 3, 2)],
  [(3, 0, 9), (3, 10, 8), (3, 7, 6), (9, 12, 9), (1, 9, 9), (9, 7, 7), (3, 8, 7), (1, 6, 8), (9, 6, 6), (1, 4, 7), (1, 3, 6), (1, 2, 5), (9, 9, 8), (1, 2, 11), (9, 5, 10), (3, 7, 10), (3, 6, 11), (9, 5, 11), (9, 7, 11), (3, 8, 11), (3, 6, 10), (9, 6, 10), (1, 4, 11), (1, 3, 10), (1, 2, 2), (1, 2, 10), (1, 2, 2)],
  [(9, 0, 8), (3, 10, 9), (3, 7, 8), (3, 4, 6), (9, 3, 9), (1, 8, 9), (9, 11, 7), (3, 5, 7), (1, 5, 8), (9, 10, 6), (1, 3, 7), (1, 2, 6), (1, 1, 5), (1, 1, 10), (1, 1, 11), (9, 9, 10), (3, 4, 10), (3, 3, 11), (9, 9, 11), (9, 11, 11), (3, 5, 11), (3, 3, 10), (9, 10, 10), (1, 3, 11), (1, 2, 10), (1, 1, 2), (1, 1, 2)],
  [(1, 0, 1), (1, 12, 1), (1, 11, 1), (1, 10, 1), (1, 9, 1), (1, 8, 1), (1, 7, 1), (1, 6, 1), (1, 5, 1), (1, 4, 1), (1, 3, 1), (1, 2, 1), (1, 1, 1), (1, 0, 2), (1, 12, 2), (1, 11, 2), (1, 10, 2), (1, 9, 2), (1, 8, 2), (1, 7, 2), (1, 6, 2), (1, 5, 2), (1, 4, 2), (1, 3, 2), (1, 2, 2), (1, 1, 2), (1, 0, 0)]]

def W (a b : ℕ) : Fin 13 × Fin 13 × ℕ := (tbl.getD a []).getD b (0, 0, 0)

def okb (a b : ℕ) : Bool :=
  decide ((W a b).1 ∈ U) && decide ((W a b).2.2 < 12) && (List.range 26).all fun j =>
    decide ((j = sig (W a b).1 (W a b).2.1 a ∨ j = sig (W a b).1 (W a b).2.1 b) ↔
      j ∈ R.getD (W a b).2.2 [])

set_option maxRecDepth 100000 in
theorem tableAll : ((List.range 27).all fun a => (List.range 27).all fun b => okb a b) = true := by
  decide

theorem tableOk (a : ℕ) (ha : a < 27) (b : ℕ) (hb : b < 27) :
    (W a b).1 ∈ U ∧ (W a b).2.2 < 12 ∧ ∀ j < 26,
      ((j = sig (W a b).1 (W a b).2.1 a ∨ j = sig (W a b).1 (W a b).2.1 b) ↔
        j ∈ R.getD (W a b).2.2 []) := by
  have h := tableAll
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h a ha b hb
  simp only [okb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

theorem sig_min (u c : Fin 13) (j : ℕ) (hj : j < 26) (x : ℕ) :
    (j = sig u c x ↔ j = sig u c (min x 26)) := by
  by_cases hx : x < 26
  · rw [min_eq_left hx.le]
  · rw [min_eq_right (by omega), sig_ge u c x (by omega), sig_ge u c 26 le_rfl]; omega

theorem main (C : Circuit) (l : List ℕ) (hlen : l.length ≤ 2) (hmono : Monotone2 C) (hord : Ord C)
    (hC : Corr C l) : ∃ (D : Circuit), ∃ rep ∈ R, Monotone2 D ∧ Ord D ∧ Corr D rep ∧ D.size ≤ C.size := by
  obtain ⟨hu, hri, hset⟩ := tableOk (min (l.getD 0 26) 26) (by omega) (min (l.getD 1 26) 26) (by omega)
  set u := (W (min (l.getD 0 26) 26) (min (l.getD 1 26) 26)).1
  set c := (W (min (l.getD 0 26) 26) (min (l.getD 1 26) 26)).2.1
  set ri := (W (min (l.getD 0 26) 26) (min (l.getD 1 26) 26)).2.2
  refine ⟨remap (sig u c) C, R.getD ri [], ?_, mono_remap _ C hmono,
    ord_remap _ (sig_ge u c) (sig_lt u c) C hord, key u c hu C l _ ?_ hC, by simp [remap, Circuit.size]⟩
  · rw [List.getD_eq_getElem _ _ (by simpa [R] using hri)]; exact List.getElem_mem _
  · intro j hj
    rw [← hset j hj, ← sig_min u c j hj, ← sig_min u c j hj]
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
    · simp only [List.map_nil, List.getD_nil, List.not_mem_nil, false_iff]
      rw [sig_ge u c 26 le_rfl]; omega
    · simp only [List.map_cons, List.map_nil, List.mem_singleton, List.getD_cons_zero,
        List.getD_cons_succ, List.getD_nil]
      rw [sig_ge u c 26 le_rfl]; omega
    · simp
    · simp at hlen

end PEqualNP.Outside.L_meta_4676

open PEqualNP.Outside.L_meta_4676 in
theorem PEqualNP.Outside.L_meta_4676 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List ℕ), x7.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), ∃ x13 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x12 ∧ x4 x12 ∧ x3 x12 x13 ∧ x12.size ≤ x6.size := by
  intro x1 x2 x3 x4 x5 C l hlen hmono hord hC
  exact main C l hlen hmono hord hC
