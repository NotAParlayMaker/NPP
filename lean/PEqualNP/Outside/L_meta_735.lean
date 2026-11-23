import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_735

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires { gates := gs, output := o } x = gs.foldl step x := rfl

theorem getD_snoc_eq (L : List Bool) (S d : Bool) (k : ℕ) (hk : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst hk
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (L : List Bool) (d : Bool) (j : ℕ) (hj : L.length ≤ j) : L.getD j d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getD_snoc_ne (L : List Bool) (S d : Bool) (j : ℕ) (hj : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases h : j < L.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [getD_big _ _ _ (by simp; omega), getD_big _ _ _ (by omega)]

/-- The new index of an old wire. -/
noncomputable def phi (n n' G : ℕ) (e : Fin n' → Fin n) (i : ℕ) : ℕ :=
  if i < n then
    (if hz : ∃ j : Fin n', (e j).val = i then (Classical.choose hz).val else n' + G)
  else if i < n + G then n' + (i - n) else n' + G

def rm (f : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map f }

theorem phi_gate (n n' G : ℕ) (e : Fin n' → Fin n) (t : ℕ) (ht : t < G) :
    phi n n' G e (n + t) = n' + t := by
  unfold phi
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem phi_ne (n n' G : ℕ) (e : Fin n' → Fin n) (t : ℕ) (ht : t < G) (i : ℕ)
    (hi : i ≠ n + t) : phi n n' G e i ≠ n' + t := by
  unfold phi
  split
  · split
    · rename_i hz
      have := (Classical.choose hz).isLt
      omega
    · omega
  · split <;> omega

def Inv (n n' G : ℕ) (e : Fin n' → Fin n) (t : ℕ) (w w' : List Bool) : Prop :=
  w.length = n + t ∧ w'.length = n' + t ∧
    ∀ i, w'.getD (phi n n' G e i) false = w.getD i false

theorem inv_step {n n' G : ℕ} {e : Fin n' → Fin n} {t : ℕ} {w w' : List Bool}
    (h : Inv n n' G e t w w') (ht : t < G) (g : Gate) :
    Inv n n' G e (t + 1) (step w g) (step w' (rm (phi n n' G e) g)) := by
  obtain ⟨hl, hl', hi⟩ := h
  have hv : (rm (phi n n' G e) g).op.eval
      ((rm (phi n n' G e) g).inputs.map fun i => w'.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [rm, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hi i
  refine ⟨by simp [step, hl]; omega, by simp [step, hl']; omega, ?_⟩
  intro i
  simp only [step, hv]
  by_cases h1 : i = n + t
  · rw [h1, phi_gate n n' G e t ht, getD_snoc_eq _ _ _ _ hl', getD_snoc_eq _ _ _ _ hl]
  · rw [getD_snoc_ne _ _ _ _ (by rw [hl']; exact phi_ne n n' G e t ht i h1),
      getD_snoc_ne _ _ _ _ (by rw [hl]; exact h1)]
    exact hi i

theorem inv_foldl {n n' G : ℕ} {e : Fin n' → Fin n} (rs : List Gate) :
    ∀ (t : ℕ) (w w' : List Bool), t + rs.length = G → Inv n n' G e t w w' →
      Inv n n' G e G (rs.foldl step w) ((rs.map (rm (phi n n' G e))).foldl step w') := by
  induction rs with
  | nil =>
    intro t w w' ht h
    simp only [List.length_nil, Nat.add_zero] at ht
    subst ht
    exact h
  | cons g rs ih =>
    intro t w w' ht h
    simp only [List.length_cons] at ht
    exact ih (t + 1) _ _ (by omega) (inv_step h (by omega) g)

theorem inv_init (n n' G : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n)
    (hZ : ∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k)
    (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n')
    (hz : ∀ k ∈ Z, x.getD (k : ℕ) false = false)
    (he : ∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) :
    Inv n n' G e 0 x x' := by
  refine ⟨by simpa using hx, by simpa using hx', ?_⟩
  intro i
  unfold phi
  split
  · rename_i hin
    split
    · rename_i hex
      rw [← he (Classical.choose hex), Classical.choose_spec hex]
    · rename_i hex
      rw [getD_big _ _ _ (by omega)]
      have hk : (⟨i, hin⟩ : Fin n) ∈ Z := by
        by_contra hk
        obtain ⟨j, hj⟩ := (hZ ⟨i, hin⟩).mp hk
        exact hex ⟨j, by rw [hj]⟩
      exact (hz _ hk).symm
  · rename_i hin
    rw [getD_big x _ _ (by omega)]
    split
    · exact getD_big _ _ _ (by omega)
    · exact getD_big _ _ _ (by omega)

end PEqualNP.Outside.L_meta_735

theorem PEqualNP.Outside.L_meta_735 : ∀ (n n' : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k) → n' + Z.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ phi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ Z, x.getD (k : ℕ) false = false) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := 0 } x').getD (phi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := phi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' Z e _ hZ _ gates
  refine ⟨PEqualNP.Outside.L_meta_735.phi n n' gates.length e, ?_⟩
  intro x x' hx hx' hz he
  have hinv := PEqualNP.Outside.L_meta_735.inv_foldl (e := e) gates 0 x x' (by simp)
    (PEqualNP.Outside.L_meta_735.inv_init n n' gates.length Z e hZ x x' hx hx' hz he)
  obtain ⟨-, -, hi⟩ := hinv
  constructor
  · intro i
    exact hi i
  · intro o
    exact hi o
