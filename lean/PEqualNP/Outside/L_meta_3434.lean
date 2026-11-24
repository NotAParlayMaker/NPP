import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3434

open PEqualNP.CircuitLowerBounds

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def remapGate (σ : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map σ }

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_singleton {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]

lemma getD_of_length_le {α : Type} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_remap (σ : ℕ → ℕ) (n : ℕ) (gs : List Gate) :
    ∀ (w₁ w₂ : List Bool),
      n ≤ w₁.length →
      w₁.length = w₂.length →
      (∀ k, n ≤ k → σ k = k) →
      (∀ k < n, σ k < n ∨ w₁.length + gs.length ≤ σ k) →
      (∀ k, w₂.getD (σ k) false = w₁.getD k false) →
      ∀ k, ((gs.map (remapGate σ)).foldl wireStep w₂).getD (σ k) false =
        (gs.foldl wireStep w₁).getD k false := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ _ _ _ hinv k
    exact hinv k
  | cons g gs ih =>
    intro w₁ w₂ hn hlen hfix hgap hinv k
    simp only [List.map_cons, List.foldl_cons]
    let v₁ := g.op.eval (g.inputs.map fun i => w₁.getD i false)
    let v₂ := (remapGate σ g).op.eval ((remapGate σ g).inputs.map fun i => w₂.getD i false)
    have hv : v₂ = v₁ := by
      dsimp only [v₁, v₂, remapGate]
      rw [List.map_map]
      congr 1
      apply List.map_inj_left.mpr
      intro i _
      exact hinv i
    let w₁' := wireStep w₁ g
    let w₂' := wireStep w₂ (remapGate σ g)
    have hlen1 : w₁'.length = w₁.length + 1 := by
      dsimp only [w₁', wireStep]
      simp only [List.length_append, List.length_singleton]
    have hlen2 : w₂'.length = w₂.length + 1 := by
      dsimp only [w₂', wireStep]
      simp only [List.length_append, List.length_singleton]
    have hlen' : w₁'.length = w₂'.length := by omega
    have hn' : n ≤ w₁'.length := by omega
    have hgap' : ∀ j < n, σ j < n ∨ w₁'.length + gs.length ≤ σ j := by
      intro j hj
      rcases hgap j hj with hlo | hhi
      · exact Or.inl hlo
      · right
        simp only [List.length_cons] at hhi
        omega
    have hinv' : ∀ j, w₂'.getD (σ j) false = w₁'.getD j false := by
      intro j
      by_cases hj : j < n
      · rcases hgap j hj with hlo | hhi
        · have hs2 : σ j < w₂.length := by omega
          have hj1 : j < w₁.length := by omega
          dsimp only [w₁', w₂', wireStep]
          rw [getD_append_left w₂ _ (σ j) false hs2, getD_append_left w₁ _ j false hj1]
          exact hinv j
        · have hj1 : j < w₁.length := by omega
          simp only [List.length_cons] at hhi
          have hs2 : w₂'.length ≤ σ j := by omega
          have hs2_old : w₂.length ≤ σ j := by omega
          rw [getD_of_length_le w₂' (σ j) false hs2]
          dsimp only [w₁', wireStep]
          rw [getD_append_left w₁ _ j false hj1]
          have hjold := hinv j
          rw [getD_of_length_le w₂ (σ j) false hs2_old] at hjold
          exact hjold
      · have hjn : n ≤ j := by omega
        have hfixj : σ j = j := hfix j hjn
        rw [hfixj]
        by_cases hlt : j < w₁.length
        · have hlt2 : j < w₂.length := by omega
          dsimp only [w₁', w₂', wireStep]
          rw [getD_append_left w₂ _ j false hlt2, getD_append_left w₁ _ j false hlt]
          have h := hinv j
          rwa [hfixj] at h
        · by_cases heq : j = w₁.length
          · subst heq
            have hlt2 : w₁.length = w₂.length := hlen
            change w₂'.getD w₁.length false = w₁'.getD w₁.length false
            dsimp only [w₁', w₂', wireStep]
            rw [getD_append_right_singleton w₁ v₁ false, hlt2, getD_append_right_singleton w₂ v₂ false, hv]
          · have hgt1 : w₁'.length ≤ j := by omega
            have hgt2 : w₂'.length ≤ j := by omega
            rw [getD_of_length_le w₂' j false hgt2, getD_of_length_le w₁' j false hgt1]
    exact ih w₁' w₂' hn' hlen' hfix hgap' hinv' k

lemma solve (σ : ℕ → ℕ) (C : Circuit) (x₁ x₂ : List Bool)
    (hlen : x₁.length = x₂.length)
    (hfix : ∀ k, x₁.length ≤ k → σ k = k)
    (hgap : ∀ k < x₁.length, σ k < x₁.length ∨ x₁.length + C.size ≤ σ k)
    (hinv : ∀ k, x₂.getD (σ k) false = x₁.getD k false) :
    { gates := C.gates.map (fun g => { op := g.op, inputs := g.inputs.map σ : Gate }),
      output := σ C.output : Circuit }.eval x₂ = C.eval x₁ := by
  exact foldl_remap σ x₁.length C.gates x₁ x₂ (le_refl _) hlen hfix hgap hinv C.output

end PEqualNP.Outside.L_meta_3434

theorem PEqualNP.Outside.L_meta_3434 : ∀ (x1 : ℕ → ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.length ≤ x6 → x1 x6 = x6) → (∀ x7 < x3.length, x1 x7 < x3.length ∨ x3.length + x2.size ≤ x1 x7) → (∀ (x8 : ℕ), x4.getD (x1 x8) Bool.false = x3.getD x8 Bool.false) → { gates := List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map x1 x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := x1 x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 = x2.eval x3 := by
  exact PEqualNP.Outside.L_meta_3434.solve
