import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9109_aux

open PEqualNP.CircuitLowerBounds

def fmap (n : ℕ) (p : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then (p ⟨i, h⟩).val else i

theorem fmap_lt (n : ℕ) (p : Fin n → Fin n) (i m : ℕ) (hn : n ≤ m) (hi : i < m) :
    fmap n p i < m := by
  unfold fmap
  split_ifs with h
  · have := (p ⟨i, h⟩).isLt
    omega
  · exact hi

theorem fmap_ge (n : ℕ) (p : Fin n → Fin n) (i : ℕ) (hi : n ≤ i) : fmap n p i = i := by
  unfold fmap
  rw [dif_neg (by omega)]

def rg (n : ℕ) (p : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fmap n p)⟩

theorem getD_app (w : List Bool) (a : Bool) (j : ℕ) (h : j < w.length) :
    (w ++ [a]).getD j false = w.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem key (n : ℕ) (p : Fin n → Fin n) (gs : List Gate) :
    ∀ w w' : List Bool, w.length = w'.length → n ≤ w.length →
      (∀ j, w.getD (fmap n p j) false = w'.getD j false) →
      ∀ j, ((gs.map (rg n p)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
          (fmap n p j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD
          j false := by
  induction gs with
  | nil => intro w w' _ _ h j; exact h j
  | cons g gs ih =>
    intro w w' hl hn h
    simp only [List.map_cons, List.foldl_cons]
    have he : (rg n p g).op.eval ((rg n p g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [he]
    apply ih
    · simp [hl]
    · simp; omega
    · intro j
      by_cases hj : j < w.length
      · rw [getD_app _ _ _ (fmap_lt n p j _ hn hj), getD_app _ _ _ (by omega)]
        exact h j
      · rw [fmap_ge n p j (by omega)]
        simp only [List.getD_eq_getElem?_getD]
        by_cases hj2 : j = w.length
        · subst hj2
          simp [hl]
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem flen (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp only [List.foldl_cons]; rw [ih]; simp; omega

theorem fpad (gs : List Gate) : ∀ w : List Bool, ∀ j, j < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
      j false = w.getD j false := by
  induction gs with
  | nil => intro w j _; rfl
  | cons g gs ih =>
    intro w j hj
    simp only [List.foldl_cons]
    rw [ih _ _ (by simp; omega), getD_app _ _ _ hj]

def pp : Fin 9 → Fin 9 := ![4, 0, 1, 6, 7, 3, 5, 2, 8]

theorem iso : ∀ x : Fin 9 → Bool,
    ([(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)))) =
    Decidable.decide (∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), (x ∘ pp) x6 = Bool.true ∧ (x ∘ pp) x7 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_9109_aux

open PEqualNP.Outside.L_meta_9109_aux in
theorem PEqualNP.Outside.L_meta_9109 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), x5 x6 = Bool.true ∧ x5 x7 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true)) x4) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = (15 : ℕ) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6) = (fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)))) x6 := by
  intro C hF hs hC
  have hout : C.output < 9 + C.gates.length := by
    have h1 := hC (fun _ => true)
    have h2 : (fun (x5 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), x5 x6 = Bool.true ∧ x5 x7 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true)) (fun _ => true) = true := by decide
    rw [h2] at h1
    by_contra hc
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [flen]; simp; omega)] at h1
    simp at h1
  refine ⟨⟨C.gates.map (rg 9 pp) ++ List.replicate (15 - C.size) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩, fmap 9 pp C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_replicate] at hg
    rcases hg with ⟨g0, hg0, rfl⟩ | ⟨_, rfl⟩
    · obtain ⟨h1, h2⟩ := hF g0 hg0
      exact ⟨h1, by simpa [rg] using h2⟩
    · simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hs ⊢
    omega
  · intro x
    have hk := key 9 pp C.gates (List.ofFn x) (List.ofFn (x ∘ pp)) (by simp) (by simp)
      (by
        intro j
        by_cases hj : j < 9
        · simp [fmap, hj, List.getD_eq_getElem?_getD]
          interval_cases j <;> rfl
        · rw [fmap_ge 9 pp j (by omega)]
          simp [List.getD_eq_getElem?_getD, hj, List.getElem?_eq_none, Nat.le_of_not_lt hj]) C.output
    have hx := hC (x ∘ pp)
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at hx ⊢
    simp only [List.foldl_append]
    rw [fpad _ _ _ (by rw [flen]; simp; exact fmap_lt 9 pp _ _ (by omega) hout), hk, hx]
    exact (iso x).symm
