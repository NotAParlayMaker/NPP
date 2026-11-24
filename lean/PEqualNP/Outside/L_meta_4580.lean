import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4580

abbrev inc (x3 x4 : Fin 13) : Prop := x3 = x4 ∨ x3 = x4 + (1 : Fin 13) ∨ x3 = x4 + (3 : Fin 13) ∨ x3 = x4 + (9 : Fin 13)

def pi (d : Bool) (a b : Fin 13 → Fin 13) : Fin (13 + 13) → Fin (13 + 13) :=
  Fin.addCases (motive := fun _ => Fin (13 + 13)) (fun p => if d then Fin.natAdd 13 (a p) else Fin.castAdd 13 (a p))
    (fun l => if d then Fin.castAdd 13 (b l) else Fin.natAdd 13 (b l))

def incB (p l : Fin 13) : Bool := decide (inc p l)

abbrev Valid (d : Bool) (a ai b bi : Fin 13 → Fin 13) : Prop :=
  (∀ p, ai (a p) = p) ∧ (∀ p, a (ai p) = p) ∧ (∀ l, bi (b l) = l) ∧ (∀ l, b (bi l) = l) ∧
    ∀ p l, (if d then incB (b l) (a p) else incB (a p) (b l)) = incB p l

def lav (Q : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter fun l => ∀ q ∈ Q, ¬ inc q l
def pav (R : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter fun p => ∀ r ∈ R, ¬ inc p r

def pats : List ℕ := [8191, 15860, 31200, 107904]

def table : List (Bool × (Fin 13 → Fin 13) × (Fin 13 → Fin 13) × (Fin 13 → Fin 13) × (Fin 13 → Fin 13)) := [
  (false, ![3, 7, 0, 8, 5, 2, 6, 11, 9, 10, 4, 12, 1], ![2, 12, 5, 0, 10, 4, 6, 1, 3, 8, 9, 7, 11], ![7, 4, 12, 5, 2, 6, 10, 8, 9, 1, 3, 11, 0], ![12, 9, 4, 10, 1, 3, 5, 0, 7, 8, 6, 11, 2]),
  (true, ![0, 11, 12, 5, 9, 8, 2, 6, 10, 1, 3, 7, 4], ![0, 9, 6, 10, 12, 3, 7, 11, 5, 4, 8, 1, 2], ![1, 12, 8, 5, 9, 11, 2, 6, 10, 4, 3, 7, 0], ![12, 0, 6, 10, 9, 3, 7, 11, 2, 4, 8, 5, 1]),
  (false, ![1, 0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10], ![1, 0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10], ![0, 12, 2, 7, 5, 4, 6, 3, 8, 9, 11, 10, 1], ![0, 12, 2, 7, 5, 4, 6, 3, 8, 9, 11, 10, 1]),
  (false, ![1, 2, 5, 4, 3, 0, 12, 9, 8, 10, 11, 7, 6], ![5, 0, 1, 4, 3, 2, 12, 11, 8, 7, 9, 10, 6], ![1, 2, 4, 3, 0, 12, 9, 8, 7, 10, 11, 6, 5], ![4, 0, 1, 3, 2, 12, 11, 8, 7, 6, 9, 10, 5]),
  (false, ![1, 2, 5, 4, 11, 7, 9, 12, 6, 10, 3, 0, 8], ![11, 0, 1, 10, 3, 2, 8, 5, 12, 6, 9, 4, 7], ![1, 2, 4, 8, 11, 6, 9, 3, 10, 7, 0, 12, 5], ![10, 0, 1, 7, 2, 12, 5, 9, 3, 6, 8, 4, 11]),
  (true, ![11, 0, 12, 5, 10, 8, 6, 2, 9, 1, 4, 7, 3], ![1, 9, 7, 12, 10, 3, 6, 11, 5, 8, 4, 0, 2], ![1, 0, 8, 6, 11, 9, 2, 5, 10, 4, 7, 3, 12], ![1, 0, 6, 11, 9, 7, 3, 10, 2, 5, 8, 4, 12]),
  (true, ![11, 5, 12, 0, 8, 10, 6, 2, 3, 1, 7, 4, 9], ![3, 9, 7, 8, 11, 1, 6, 10, 4, 12, 5, 0, 2], ![1, 8, 0, 9, 11, 6, 2, 3, 4, 10, 7, 5, 12], ![2, 0, 6, 7, 8, 11, 5, 10, 1, 3, 9, 4, 12]),
  (true, ![3, 7, 12, 2, 5, 6, 4, 10, 11, 0, 8, 1, 9], ![9, 11, 3, 0, 6, 4, 5, 1, 10, 12, 7, 8, 2], ![3, 8, 2, 5, 6, 7, 0, 11, 1, 9, 4, 10, 12], ![6, 8, 2, 0, 10, 3, 4, 5, 1, 9, 11, 7, 12]),
  (true, ![0, 11, 12, 1, 9, 6, 7, 8, 4, 5, 3, 2, 10], ![0, 3, 11, 10, 8, 9, 5, 6, 7, 4, 12, 1, 2], ![1, 12, 2, 10, 9, 7, 8, 4, 5, 6, 3, 11, 0], ![12, 0, 2, 10, 7, 8, 9, 5, 6, 4, 3, 11, 1]),
  (true, ![0, 3, 12, 7, 9, 8, 1, 6, 4, 2, 11, 5, 10], ![0, 6, 9, 1, 8, 11, 7, 3, 5, 4, 12, 10, 2], ![3, 12, 8, 10, 9, 4, 2, 7, 5, 11, 1, 6, 0], ![12, 10, 6, 0, 5, 8, 11, 7, 2, 4, 3, 9, 1]),
  (true, ![0, 3, 12, 2, 9, 6, 5, 8, 10, 7, 11, 1, 4], ![0, 11, 3, 1, 12, 6, 5, 9, 7, 4, 8, 10, 2], ![3, 12, 2, 5, 9, 6, 8, 11, 10, 7, 1, 4, 0], ![12, 10, 2, 0, 11, 3, 5, 9, 6, 4, 8, 7, 1]),
  (true, ![0, 1, 12, 11, 6, 9, 7, 8, 10, 5, 2, 3, 4], ![0, 1, 10, 11, 12, 9, 4, 6, 7, 5, 8, 3, 2], ![1, 2, 12, 7, 9, 10, 8, 11, 6, 5, 3, 4, 0], ![12, 0, 1, 10, 11, 9, 8, 3, 6, 4, 5, 7, 2]),
  (false, ![1, 5, 0, 8, 4, 2, 11, 10, 3, 6, 7, 12, 9], ![2, 0, 5, 8, 4, 1, 9, 10, 3, 12, 7, 6, 11], ![5, 4, 12, 8, 1, 2, 10, 7, 3, 6, 11, 9, 0], ![12, 4, 5, 8, 1, 0, 9, 7, 3, 11, 6, 10, 2]),
  (false, ![1, 5, 0, 6, 7, 11, 2, 12, 3, 8, 4, 10, 9], ![2, 0, 6, 8, 10, 1, 3, 4, 9, 12, 11, 5, 7], ![5, 4, 10, 6, 11, 2, 12, 3, 7, 8, 1, 9, 0], ![12, 10, 5, 7, 1, 0, 3, 8, 9, 11, 2, 4, 6]),
  (false, ![1, 5, 7, 6, 4, 2, 3, 10, 11, 8, 0, 9, 12], ![10, 0, 5, 6, 4, 1, 3, 2, 9, 11, 7, 8, 12], ![5, 4, 6, 3, 1, 2, 7, 10, 8, 12, 0, 9, 11], ![10, 4, 5, 3, 1, 0, 2, 6, 8, 11, 7, 12, 9]),
  (true, ![11, 0, 12, 1, 4, 6, 8, 7, 9, 5, 10, 2, 3], ![1, 3, 11, 12, 4, 9, 5, 7, 6, 8, 10, 0, 2], ![1, 0, 2, 4, 7, 9, 8, 10, 5, 6, 11, 3, 12], ![1, 0, 2, 11, 3, 8, 9, 4, 6, 5, 7, 10, 12]),
  (false, ![3, 0, 2, 1, 12, 4, 7, 6, 5, 9, 8, 10, 11], ![1, 3, 2, 0, 5, 8, 7, 6, 10, 9, 11, 12, 4], ![0, 12, 1, 11, 3, 4, 6, 5, 9, 8, 7, 10, 2], ![0, 2, 12, 4, 5, 7, 6, 10, 9, 8, 11, 3, 1]),
  (false, ![3, 0, 2, 9, 8, 7, 4, 10, 5, 1, 12, 6, 11], ![1, 9, 2, 0, 6, 8, 11, 5, 4, 3, 7, 12, 10], ![0, 12, 6, 8, 7, 4, 1, 9, 5, 11, 3, 10, 2], ![0, 6, 12, 10, 5, 8, 2, 4, 3, 7, 11, 9, 1]),
  (false, ![3, 0, 7, 9, 5, 2, 12, 11, 8, 1, 4, 6, 10], ![1, 9, 5, 0, 10, 4, 11, 2, 8, 3, 12, 7, 6], ![0, 4, 6, 9, 2, 12, 11, 8, 5, 1, 3, 10, 7], ![0, 9, 4, 10, 1, 8, 2, 12, 7, 3, 11, 6, 5])]

abbrev Fits (t : Bool × (Fin 13 → Fin 13) × (Fin 13 → Fin 13) × (Fin 13 → Fin 13) × (Fin 13 → Fin 13))
    (Q R : Finset (Fin 13)) : Prop :=
  Valid t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 ∧ ∃ v ∈ pats,
    (∀ p ∈ Q, v.testBit (pi t.1 t.2.1 t.2.2.2.1 (Fin.castAdd 13 p)).val = true) ∧
    (∀ l ∈ R, v.testBit (pi t.1 t.2.1 t.2.2.2.1 (Fin.natAdd 13 l)).val = true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem finQ : ∀ Q ∈ ({0, 1, 3, 9} : Finset (Fin 13)).powerset, ∃ t ∈ table, Fits t Q (lav Q) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem finR : ∀ R ∈ ({0, 4, 10, 12} : Finset (Fin 13)).powerset, ∃ t ∈ table, Fits t (pav R) R := by
  decide +kernel

theorem transValid : ∀ c : Fin 13, Valid false (· + c) (· - c) (· + c) (· - c) := by
  decide

theorem lineQ (p l : Fin 13) (h : inc p l) : p + -l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  revert p l; decide

theorem lineR (p l : Fin 13) (h : inc p l) : l + -p ∈ ({0, 4, 10, 12} : Finset (Fin 13)) := by
  revert p l; decide

def rg (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rel (ρ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (rg ρ), ρ C.output⟩

def rho (π : Fin 26 → Fin 26) (i : ℕ) : ℕ := if h : i < 26 then (π ⟨i, h⟩).val else i

theorem getD_snoc {α} (W : List α) (b d : α) (j : ℕ) (h : j < W.length) :
    (W ++ [b]).getD j d = W.getD j d := List.getD_append _ _ _ _ h

theorem sim {α : Type} (dflt : α) (F : Gate → List α → α) (ρ : ℕ → ℕ) (n : ℕ)
    (hρ : ∀ i, n ≤ i → ρ i = i) (hρn : ∀ i < n, ρ i < n)
    (hF : ∀ g W W', (g.inputs.map fun i => W'.getD (ρ i) dflt) = (g.inputs.map fun i => W.getD i dflt) →
      F (rg ρ g) W' = F g W) :
    ∀ (gs : List Gate) (W W' : List α), n ≤ W.length → W'.length = W.length →
      (∀ j, W'.getD (ρ j) dflt = W.getD j dflt) →
      ∀ j, ((gs.map (rg ρ)).foldl (fun w g => w ++ [F g w]) W').getD (ρ j) dflt =
        (gs.foldl (fun w g => w ++ [F g w]) W).getD j dflt
  | [], W, W', _, _, h => h
  | g :: gs, W, W', hn, hl, h => by
    simp only [List.map_cons, List.foldl_cons]
    have e : F (rg ρ g) W' = F g W := hF g W W' (List.map_congr_left fun i _ => h i)
    rw [e]
    apply sim dflt F ρ n hρ hρn hF gs _ _ (by simp; omega) (by simp [hl])
    intro j
    by_cases hj : j < W.length
    · have hj' : ρ j < W'.length := by
        by_cases hjn : j < n
        · have := hρn j hjn; omega
        · rw [hρ j (by omega)]; omega
      rw [getD_snoc _ _ _ _ hj, getD_snoc _ _ _ _ hj', h j]
    · rw [hρ j (by omega)]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

theorem rho_ge (π : Fin 26 → Fin 26) (i : ℕ) (h : 26 ≤ i) : rho π i = i := by
  simp [rho]; omega

theorem rho_lt (π : Fin 26 → Fin 26) (i : ℕ) (h : i < 26) : rho π i < 26 := by
  simp only [rho, dif_pos h]; exact (π _).isLt

theorem rel_eval (π : Fin 26 → Fin 26) (C : Circuit) (X : Fin 26 → Bool) :
    circuitFun 26 (rel (rho π) C) X = circuitFun 26 C (X ∘ π) := by
  simp only [circuitFun, Circuit.eval, Circuit.wires, rel]
  apply sim false (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)) (rho π) 26
    (rho_ge π) (rho_lt π) _ C.gates _ _ (by simp) (by simp)
  · intro j
    by_cases hj : j < 26
    · simp only [rho, dif_pos hj]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (π _).isLt),
        List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn,
        List.getElem_ofFn]
      rfl
    · rw [rho_ge π j (by omega), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  · intro g W W' h
    simp only [rg, List.map_map]
    exact congrArg g.op.eval h

theorem rel_lineDeg (π : Fin 26 → Fin 26) (C : Circuit) (M M' : Finset ℕ)
    (hM : ∀ j : Fin 26, ((π j).val ∈ M ↔ j.val ∈ M')) :
    (rel (rho π) C).lineDeg 26 M = C.lineDeg 26 M' := by
  simp only [Circuit.lineDeg, Circuit.lineDegrees, rel]
  apply sim 0 (fun g d => g.lineDegree d) (rho π) 26 (rho_ge π) (rho_lt π) _ C.gates _ _
    (by simp) (by simp)
  · intro j
    by_cases hj : j < 26
    · simp only [rho, dif_pos hj]
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact (π _).isLt),
        List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hj)]
      simp only [List.getElem_map, List.getElem_range]
      have := hM ⟨j, hj⟩
      by_cases h1 : j ∈ M'
      · rw [if_pos (this.mpr h1), if_pos h1]
      · rw [if_neg (fun h => h1 (this.mp h)), if_neg h1]
    · rw [rho_ge π j (by omega), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  · intro g W W' h
    simp only [Gate.lineDegree, rg, List.map_map, Function.comp_def]
    rw [h]; rfl

theorem rel_size (ρ : ℕ → ℕ) (C : Circuit) : (rel ρ C).size = C.size := by
  simp [rel, Circuit.size]

theorem rel_mono (ρ : ℕ → ℕ) (C : Circuit) (h : Monotone2 C) : Monotone2 (rel ρ C) := by
  intro g hg
  simp only [rel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa [rg] using h g0 hg0

theorem mono_fold (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, W'.length = W.length →
      (∀ j, W.getD j false = true → W'.getD j false = true) →
      ∀ j, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD j false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD j false = true := by
  induction gs with
  | nil => intro W W' _ h; exact h
  | cons g gs ih =>
    intro W W' hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hm g' (by simp [hg'])) _ _ (by simp [hl])
    have hg : g.op.eval (g.inputs.map fun i => W.getD i false) = true →
        g.op.eval (g.inputs.map fun i => W'.getD i false) = true := by
      rcases hm g (by simp) with ho | ho <;> rw [ho] <;>
        simp only [GateOp.eval, List.all_map, List.any_map, List.all_eq_true, List.any_eq_true,
          Function.comp_apply, id]
      · intro H x hx; exact h x (H x hx)
      · rintro ⟨x, hx, H⟩; exact ⟨x, hx, h x H⟩
    intro j
    by_cases hj : j < W.length
    · rw [getD_snoc _ _ _ _ hj, getD_snoc _ _ _ _ (by omega)]; exact h j
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
      intro H
      rcases Nat.lt_or_ge (j - W.length) 1 with h1 | h1
      · have : j - W.length = 0 := by omega
        rw [this] at H ⊢; simpa using hg (by simpa using H)
      · rw [List.getD_eq_default _ _ (by simp; omega)] at H; exact absurd H (by simp)

theorem mono (C : Circuit) (hm : Monotone2 C) (X Y : Fin 26 → Bool)
    (h : ∀ i, X i = true → Y i = true) (hx : circuitFun 26 C X = true) : circuitFun 26 C Y = true := by
  simp only [circuitFun, Circuit.eval, Circuit.wires] at hx ⊢
  refine mono_fold C.gates (fun g hg => ?_) _ _ (by simp) ?_ _ hx
  · have := (hm g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; exact this
  · intro j hj
    by_cases hj' : j < 26
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hj')] at hj ⊢
      simp only [List.getElem_ofFn] at hj ⊢; exact h _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj; exact absurd hj (by simp)

def ind (S T : Finset (Fin 13)) : Fin 26 → Bool := fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ S)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ T)) x7

def x4f (C : Circuit) (S T : Finset (Fin 13)) : Bool := circuitFun 26 C (ind S T)

def gen (x5 x6 : Finset (Fin 13)) : Prop := (∀ (x7 : Fin 13), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬inc x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, inc x7 x9) ∧ (¬∃ (x7 : Fin 13), ∀ x8 ∈ x5, inc x8 x7) ∧ ¬∃ (x7 : Fin 13), ∀ x8 ∈ x6, inc x7 x8

def good6 (C : Circuit) : Prop := (∀ (x7 x8 : Fin 13), inc x7 x8 → x4f C {x7} {x8} = true) ∧ ∀ (x7 x8 : Finset (Fin 13)), gen x7 x8 → x4f C x7 x8 = false

def good7 (C : Circuit) : Prop := 2 ≤ min (C.lineDeg 26 (Finset.range 13)) (C.lineDeg 26 (Finset.Ico 13 26)) ∧
  3 ≤ max (C.lineDeg 26 (Finset.range 13)) (C.lineDeg 26 (Finset.Ico 13 26))

def pre (f : Fin 13 → Fin 13) (S : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter fun p => f p ∈ S

theorem mem_pre (f : Fin 13 → Fin 13) (S : Finset (Fin 13)) (x : Fin 13) : x ∈ pre f S ↔ f x ∈ S := by
  simp [pre]

theorem ind_pi (d : Bool) (a b : Fin 13 → Fin 13) (S T : Finset (Fin 13)) :
    ind S T ∘ pi d a b = if d then ind (pre a T) (pre b S) else ind (pre a S) (pre b T) := by
  funext i
  refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i <;>
    cases d <;> simp only [ind, pi, pre, Function.comp_apply, Fin.addCases_left, Fin.addCases_right,
      Bool.false_eq_true, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]

theorem pre_single (f fi : Fin 13 → Fin 13) (h1 : ∀ p, fi (f p) = p) (h2 : ∀ p, f (fi p) = p) (s : Fin 13) :
    pre f {s} = {fi s} := by
  ext p; simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro rfl; rw [h1]
  · rintro rfl; rw [h2]

theorem genN (a ai b bi : Fin 13 → Fin 13) (ha : ∀ p, a (ai p) = p) (hb : ∀ l, b (bi l) = l)
    (hinc : ∀ p l, inc (a p) (b l) ↔ inc p l) (S T : Finset (Fin 13)) (g : gen S T) :
    gen (pre a S) (pre b T) := by
  obtain ⟨g1, g2, g3, g4⟩ := g
  unfold gen; simp only [mem_pre]
  refine ⟨fun l => ?_, fun p hp => ?_, ?_, ?_⟩
  · rw [g1]; constructor
    · intro H p hp hi; exact H _ hp ((hinc p l).mpr hi)
    · intro H s hs hi; exact H (ai s) (by rwa [ha]) ((hinc _ l).mp (by rwa [ha]))
  · obtain ⟨t, ht, hi⟩ := g2 _ hp
    exact ⟨bi t, by rwa [hb], (hinc p _).mp (by rwa [hb])⟩
  · rintro ⟨l, H⟩
    exact g3 ⟨b l, fun s hs => by have := (hinc (ai s) l).mpr (H _ (by rwa [ha])); rwa [ha] at this⟩
  · rintro ⟨p, H⟩
    exact g4 ⟨a p, fun t ht => by have := (hinc p (bi t)).mpr (H _ (by rwa [hb])); rwa [hb] at this⟩

theorem genD (a ai b bi : Fin 13 → Fin 13) (ha : ∀ p, a (ai p) = p) (hb : ∀ l, b (bi l) = l)
    (hinc : ∀ p l, inc (b l) (a p) ↔ inc p l) (S T : Finset (Fin 13)) (g : gen S T) :
    gen (pre a T) (pre b S) := by
  obtain ⟨g1, g2, g3, g4⟩ := g
  have hS : ∀ s, s ∈ S ↔ ∀ t ∈ T, ¬ inc s t := by
    intro s; constructor
    · intro hs t ht; exact (g1 t).mp ht s hs
    · intro H; by_contra hs; obtain ⟨t, ht, hi⟩ := g2 s hs; exact H t ht hi
  unfold gen; simp only [mem_pre]
  refine ⟨fun l => ?_, fun p hp => ?_, ?_, ?_⟩
  · rw [hS]; constructor
    · intro H p hp hi; exact H _ hp ((hinc p l).mpr hi)
    · intro H t ht hi; exact H (ai t) (by rwa [ha]) ((hinc _ l).mp (by rwa [ha]))
  · have : ∃ s ∈ S, inc s (a p) := by
      by_contra H; exact hp ((g1 _).mpr (fun s hs hi => H ⟨s, hs, hi⟩))
    obtain ⟨s, hs, hi⟩ := this
    exact ⟨bi s, by rwa [hb], (hinc p _).mp (by rwa [hb])⟩
  · rintro ⟨l, H⟩
    exact g4 ⟨b l, fun t ht => by have := (hinc (ai t) l).mpr (H _ (by rwa [ha])); rwa [ha] at this⟩
  · rintro ⟨p, H⟩
    exact g3 ⟨a p, fun s hs => by have := (hinc p (bi s)).mpr (H _ (by rwa [hb])); rwa [hb] at this⟩

theorem x4f_rel (d : Bool) (a b : Fin 13 → Fin 13) (C : Circuit) (S T : Finset (Fin 13)) :
    x4f (rel (rho (pi d a b)) C) S T =
      if d then x4f C (pre a T) (pre b S) else x4f C (pre a S) (pre b T) := by
  simp only [x4f, rel_eval, ind_pi]; cases d <;> rfl

theorem transfer (d : Bool) (a ai b bi : Fin 13 → Fin 13) (hv : Valid d a ai b bi) (C : Circuit)
    (hm : Monotone2 C) (h6 : good6 C) (h7 : good7 C) :
    Monotone2 (rel (rho (pi d a b)) C) ∧ (rel (rho (pi d a b)) C).size = C.size ∧
      good6 (rel (rho (pi d a b)) C) ∧ good7 (rel (rho (pi d a b)) C) := by
  obtain ⟨hai, ha, hbi, hb, hv⟩ := hv
  refine ⟨rel_mono _ C hm, rel_size _ C, ?_, ?_⟩
  · cases d
    · have hinc : ∀ p l, inc (a p) (b l) ↔ inc p l := fun p l => by
        have := hv p l; simp only [Bool.false_eq_true, ↓reduceIte] at this; unfold incB at this
        exact decide_eq_decide.mp this
      refine ⟨fun s t hst => ?_, fun S T g => ?_⟩
      · rw [x4f_rel, if_neg (by simp), pre_single a ai hai ha, pre_single b bi hbi hb]
        exact h6.1 _ _ ((hinc _ _).mp (by rwa [ha, hb]))
      · rw [x4f_rel, if_neg (by simp)]; exact h6.2 _ _ (genN a ai b bi ha hb hinc S T g)
    · have hinc : ∀ p l, inc (b l) (a p) ↔ inc p l := fun p l => by
        have := hv p l; simp only [↓reduceIte] at this; unfold incB at this
        exact decide_eq_decide.mp this
      refine ⟨fun s t hst => ?_, fun S T g => ?_⟩
      · rw [x4f_rel, if_pos rfl, pre_single a ai hai ha, pre_single b bi hbi hb]
        exact h6.1 _ _ ((hinc _ _).mp (by rwa [ha, hb]))
      · rw [x4f_rel, if_pos rfl]; exact h6.2 _ _ (genD a ai b bi ha hb hinc S T g)
  · have key : ∀ (M M' : Finset ℕ), (∀ j : Fin 26, ((pi d a b j).val ∈ M ↔ j.val ∈ M')) →
        (rel (rho (pi d a b)) C).lineDeg 26 M = C.lineDeg 26 M' := fun M M' h => rel_lineDeg _ C M M' h
    have hP : ∀ j : Fin 26, ((pi d a b j).val ∈ Finset.range 13 ↔
        j.val ∈ (if d then Finset.Ico 13 26 else Finset.range 13)) := by
      intro j
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) j <;>
        cases d <;> simp only [pi, Fin.addCases_left, Fin.addCases_right, Bool.false_eq_true,
          ↓reduceIte] <;> simp <;> omega
    have hL : ∀ j : Fin 26, ((pi d a b j).val ∈ Finset.Ico 13 26 ↔
        j.val ∈ (if d then Finset.range 13 else Finset.Ico 13 26)) := by
      intro j
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) j <;>
        cases d <;> simp only [pi, Fin.addCases_left, Fin.addCases_right, Bool.false_eq_true,
          ↓reduceIte] <;> simp <;> omega
    unfold good7 at h7 ⊢
    rw [key _ _ hP, key _ _ hL]
    cases d
    · exact h7
    · simp only [if_pos rfl]; rw [min_comm, max_comm]; exact h7

theorem fin_fits (t : Bool × (Fin 13 → Fin 13) × (Fin 13 → Fin 13) × (Fin 13 → Fin 13) × (Fin 13 → Fin 13))
    (Q R : Finset (Fin 13)) (hf : Fits t Q R) (C : Circuit) (hm : Monotone2 C) (h6 : good6 C) (h7 : good7 C)
    (hacc : x4f C Q R = true) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ good6 C' ∧ good7 C' ∧
      ∃ v ∈ pats, (circuitFun 26 C' fun i => v.testBit i) = true := by
  obtain ⟨d, a, ai, b, bi⟩ := t
  obtain ⟨hv, v, hvm, hQ, hR⟩ := hf
  obtain ⟨m', s', g6, g7⟩ := transfer d a ai b bi hv C hm h6 h7
  refine ⟨_, m', s'.le, g6, g7, v, hvm, ?_⟩
  rw [rel_eval]
  refine mono C hm _ _ (fun i hi => ?_) hacc
  revert hi
  refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
  · intro hi; simp only [ind, Fin.addCases_left, decide_eq_true_eq] at hi; exact hQ p hi
  · intro hi; simp only [ind, Fin.addCases_right, decide_eq_true_eq] at hi; exact hR l hi

theorem main (C : Circuit) (hm : Monotone2 C) (h6 : good6 C) (h7 : good7 C)
    (hacc : ∃ A B : Finset (Fin 13), (∀ x15 ∈ A, ∀ x17 ∈ B, ¬ inc x15 x17) ∧ x4f C A B = true) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ good6 C' ∧ good7 C' ∧
      ∃ v ∈ pats, (circuitFun 26 C' fun i => v.testBit i) = true := by
  obtain ⟨A, B, hAB, hA⟩ := hacc
  set L' := lav A with hL'
  set P' := pav L' with hP'
  have memL : ∀ l, l ∈ L' ↔ ∀ q ∈ A, ¬ inc q l := fun l => by simp [hL', lav]
  have memP : ∀ p, p ∈ P' ↔ ∀ l ∈ L', ¬ inc p l := fun p => by simp [hP', pav]
  have hacc : x4f C P' L' = true := by
    refine mono C hm _ _ (fun i hi => ?_) hA
    revert hi
    refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
    · simp only [ind, Fin.addCases_left, decide_eq_true_eq]
      intro hp; rw [memP]; intro l hl; exact (memL l).mp hl p hp
    · simp only [ind, Fin.addCases_right, decide_eq_true_eq]
      intro hl; rw [memL]; intro q hq; exact hAB q hq l hl
  have c1 : ∀ l, l ∈ L' ↔ ∀ p ∈ P', ¬ inc p l := by
    intro l; constructor
    · intro hl p hp; exact (memP p).mp hp l hl
    · intro H; rw [memL]; intro q hq
      exact H q ((memP q).mpr fun l' hl' => (memL l').mp hl' q hq)
  have c2 : ∀ p ∉ P', ∃ l ∈ L', inc p l := by
    intro p hp; by_contra H; exact hp ((memP p).mpr fun l hl hi => H ⟨l, hl, hi⟩)
  have ng : ¬ gen P' L' := fun g => by rw [h6.2 _ _ g] at hacc; exact absurd hacc (by simp)
  have hor : (∃ l, ∀ p ∈ P', inc p l) ∨ (∃ p, ∀ l ∈ L', inc p l) := by
    by_cases h1 : ∃ l, ∀ p ∈ P', inc p l
    · exact Or.inl h1
    by_cases h2 : ∃ p, ∀ l ∈ L', inc p l
    · exact Or.inr h2
    exact absurd ⟨c1, c2, h1, h2⟩ ng
  have tv := transValid
  rcases hor with ⟨l0, hl0⟩ | ⟨p0, hp0⟩
  · obtain ⟨tv0, tv1, tv2, tv3, tv4⟩ := tv (-l0)
    have hinc : ∀ p l, inc (p + -l0) (l + -l0) ↔ inc p l := fun p l => by
      have := tv4 p l; simp only [Bool.false_eq_true, ↓reduceIte] at this; unfold incB at this
      exact decide_eq_decide.mp this
    obtain ⟨m1, s1, g6, g7⟩ := transfer false (· + -l0) (· - -l0) (· + -l0) (· - -l0) (tv (-l0)) C hm h6 h7
    set Q := ({0, 1, 3, 9} : Finset (Fin 13)).filter (fun q => q - -l0 ∈ P') with hQ
    have hQs : Q ∈ ({0, 1, 3, 9} : Finset (Fin 13)).powerset := by
      rw [Finset.mem_powerset]; exact Finset.filter_subset _ _
    have acc1 : x4f (rel (rho (pi false (· + -l0) (· + -l0))) C) Q (lav Q) = true := by
      rw [x4f_rel, if_neg (by simp)]
      refine mono C hm _ _ (fun i hi => ?_) hacc
      revert hi
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
      · simp only [ind, Fin.addCases_left, decide_eq_true_eq, pre, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro hp; rw [hQ, Finset.mem_filter]
        exact ⟨lineQ p l0 (hl0 p hp), by simpa using hp⟩
      · simp only [ind, Fin.addCases_right, decide_eq_true_eq, pre, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro hl; simp only [lav, Finset.mem_filter, Finset.mem_univ, true_and]
        intro q hq hi
        rw [hQ, Finset.mem_filter] at hq
        have e : q = (q - -l0) + -l0 := by simp
        rw [e, hinc] at hi
        exact (memP _).mp hq.2 l hl hi
    obtain ⟨t, ht, hf⟩ := finQ Q hQs
    obtain ⟨C', a1, a2, a3, a4, a5⟩ := fin_fits t Q (lav Q) hf _ m1 g6 g7 acc1
    exact ⟨C', a1, a2.trans s1.le, a3, a4, a5⟩
  · obtain ⟨tv0, tv1, tv2, tv3, tv4⟩ := tv (-p0)
    have hinc : ∀ p l, inc (p + -p0) (l + -p0) ↔ inc p l := fun p l => by
      have := tv4 p l; simp only [Bool.false_eq_true, ↓reduceIte] at this; unfold incB at this
      exact decide_eq_decide.mp this
    obtain ⟨m1, s1, g6, g7⟩ := transfer false (· + -p0) (· - -p0) (· + -p0) (· - -p0) (tv (-p0)) C hm h6 h7
    set R := ({0, 4, 10, 12} : Finset (Fin 13)).filter (fun r => r - -p0 ∈ L') with hR
    have hRs : R ∈ ({0, 4, 10, 12} : Finset (Fin 13)).powerset := by
      rw [Finset.mem_powerset]; exact Finset.filter_subset _ _
    have acc1 : x4f (rel (rho (pi false (· + -p0) (· + -p0))) C) (pav R) R = true := by
      rw [x4f_rel, if_neg (by simp)]
      refine mono C hm _ _ (fun i hi => ?_) hacc
      revert hi
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
      · simp only [ind, Fin.addCases_left, decide_eq_true_eq, pre, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro hp; simp only [pav, Finset.mem_filter, Finset.mem_univ, true_and]
        intro r hr hi
        rw [hR, Finset.mem_filter] at hr
        have e : r = (r - -p0) + -p0 := by simp
        rw [e, hinc] at hi
        exact (memP p).mp hp _ hr.2 hi
      · simp only [ind, Fin.addCases_right, decide_eq_true_eq, pre, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro hl; rw [hR, Finset.mem_filter]
        exact ⟨lineR p0 l (hp0 l hl), by simpa using hl⟩
    obtain ⟨t, ht, hf⟩ := finR R hRs
    obtain ⟨C', a1, a2, a3, a4, a5⟩ := fin_fits t (pav R) R hf _ m1 g6 g7 acc1
    exact ⟨C', a1, a2.trans s1.le, a3, a4, a5⟩

end PEqualNP.Outside.L_meta_4580

theorem PEqualNP.Outside.L_meta_4580 : let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7; have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8; have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x7 x8 : x1), x3 x7 x8 → x4 x6 {x7} {x8} = Bool.true) ∧ ∀ (x7 x8 : x2), x5 x7 x8 → x4 x6 x7 x8 = Bool.false; have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) =>   have x8 : ℕ := x7.lineDeg (26 : ℕ) (Finset.range (13 : ℕ));   have x9 : ℕ := x7.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));   (2 : ℕ) ≤ Min.min x8 x9 ∧ (3 : ℕ) ≤ Max.max x8 x9; have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ x9 ∈ [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 fun (x10 : Fin (26 : ℕ)) => x9.testBit ↑x10) = Bool.true; ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → x6 x9 → x7 x9 → (∃ (x13 : x2) (x14 : x2), (∀ x15 ∈ x13, ∀ x17 ∈ x14, ¬x3 x15 x17) ∧ x4 x9 x13 x14 = Bool.true) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ x14.size ≤ x9.size ∧ x6 x14 ∧ x7 x14 ∧ x8 x14 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 C hm h6 h7 hacc
  obtain ⟨C', a1, a2, a3, a4, v, hv, a5⟩ := PEqualNP.Outside.L_meta_4580.main C hm h6 h7 hacc
  exact ⟨C', a1, a2, a3, a4, v, hv, a5⟩
