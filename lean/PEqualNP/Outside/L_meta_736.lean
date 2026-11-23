import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_736_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def relGate (psi : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map psi⟩

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma run_simulation (n N : ℕ) (psi : ℕ → ℕ)
    (hsmall : ∀ i, i < n → psi i < N)
    (hlarge : ∀ i, n ≤ i → psi i = N + (i - n)) (gs : List Gate) :
    ∀ (t : ℕ) (w w' : List Bool), w.length = n + t → w'.length = N + t →
      (∀ i, w'.getD (psi i) false = w.getD i false) →
      ∀ i, (run (gs.map (relGate psi)) w').getD (psi i) false =
        (run gs w).getD i false := by
  induction gs with
  | nil =>
    intro t w w' hw hw' hagree
    exact hagree
  | cons g gs ih =>
    intro t w w' hw hw' hagree
    change ∀ i, (run (gs.map (relGate psi)) (step w' (relGate psi g))).getD
      (psi i) false = (run gs (step w g)).getD i false
    apply ih (t + 1) (step w g) (step w' (relGate psi g))
    · simp [step, hw, Nat.add_assoc]
    · simp [step, hw', Nat.add_assoc]
    · have heval : (relGate psi g).op.eval
          ((relGate psi g).inputs.map fun i => w'.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [relGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact hagree i
      intro i
      simp only [step, heval]
      by_cases hi : i < w.length
      · have hi' : psi i < w'.length := by
          by_cases hn : i < n
          · have := hsmall i hn
            omega
          · rw [hlarge i (by omega)]
            omega
        rw [getD_snoc_lt _ _ _ hi', getD_snoc_lt _ _ _ hi]
        exact hagree i
      · by_cases heq : i = w.length
        · have hpsi : psi i = w'.length := by
            rw [hlarge i (by omega)]
            omega
          rw [hpsi, heq, getD_snoc_eq, getD_snoc_eq]
        · have hi' : w'.length + 1 ≤ psi i := by
            rw [hlarge i (by omega)]
            omega
          rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]


noncomputable def psi (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n)
    (hc : ∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) (i : ℕ) : ℕ :=
  if hi : i < n then
    if ho : (⟨i, hi⟩ : Fin n) ∈ O then n'
    else (Classical.choose ((hc ⟨i, hi⟩).mp ho)).val
  else n' + 1 + (i - n)

lemma psi_small (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n)
    (hc : ∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k)
    (i : ℕ) (hi : i < n) : psi n n' O e hc i < n' + 1 := by
  classical
  unfold psi
  rw [dite_eq_left hi]
  split_ifs with ho
  · omega
  · exact Nat.lt_succ_of_lt (Classical.choose ((hc ⟨i, hi⟩).mp ho)).isLt

lemma psi_large (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n)
    (hc : ∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k)
    (i : ℕ) (hi : n ≤ i) : psi n n' O e hc i = n' + 1 + (i - n) := by
  simp [psi, Nat.not_lt.mpr hi]

lemma psi_initial (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n)
    (hc : ∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k)
    (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n')
    (hO : ∀ k ∈ O, x.getD (k : ℕ) false = true)
    (he : ∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false)
    (i : ℕ) : (x' ++ [true]).getD (psi n n' O e hc i) false = x.getD i false := by
  classical
  by_cases hi : i < n
  · by_cases ho : (⟨i, hi⟩ : Fin n) ∈ O
    · have hp : psi n n' O e hc i = n' := by simp [psi, hi, ho]
      rw [hp]
      have ht : (x' ++ [true]).getD n' false = true := by rw [← hx']; simp
      rw [ht]
      exact (hO ⟨i, hi⟩ ho).symm
    · let j : Fin n' := Classical.choose ((hc ⟨i, hi⟩).mp ho)
      have hj : e j = ⟨i, hi⟩ := Classical.choose_spec ((hc ⟨i, hi⟩).mp ho)
      have hp : psi n n' O e hc i = j.val := by simp [psi, hi, ho, j]
      rw [hp, List.getD_append _ _ _ _ (by simp [hx'])]
      have hv := he j
      rw [hj] at hv
      exact hv.symm
  · rw [psi_large n n' O e hc i (by omega)]
    rw [List.getD_eq_default _ _ (by simp [hx'])]
    rw [List.getD_eq_default _ _ (by omega)]


end PEqualNP.Outside.L_meta_736_aux

theorem PEqualNP.Outside.L_meta_736 : ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' O e _hmono hc _hcard gates
  let psi := PEqualNP.Outside.L_meta_736_aux.psi n n' O e hc
  refine ⟨psi, ?_⟩
  intro x x' hx hx' hO he
  have hsim := PEqualNP.Outside.L_meta_736_aux.run_simulation n (n' + 1) psi
    (PEqualNP.Outside.L_meta_736_aux.psi_small n n' O e hc)
    (PEqualNP.Outside.L_meta_736_aux.psi_large n n' O e hc) gates
    0 x (x' ++ [true]) (by omega) (by simp [hx'])
    (PEqualNP.Outside.L_meta_736_aux.psi_initial n n' O e hc x x' hx hx' hO he)
  have hw : ∀ i : ℕ,
      (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 }
        x').getD (psi i) false =
      (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false := by
    intro i
    change (PEqualNP.Outside.L_meta_736_aux.run
      (gates.map (PEqualNP.Outside.L_meta_736_aux.relGate psi)) (x' ++ [true])).getD
      (psi i) false = (PEqualNP.Outside.L_meta_736_aux.run gates x).getD i false
    exact hsim i
  exact ⟨hw, fun o => hw o⟩
