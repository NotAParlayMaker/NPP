import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1646

-- Two common neighbours of two distinct vertices coincide (no 4-cycle).
theorem common_nbr_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) {a b w₁ w₂ : Fin n} (hab : a ≠ b)
    (h₁a : G.Adj a w₁) (h₁b : G.Adj b w₁) (h₂a : G.Adj a w₂) (h₂b : G.Adj b w₂) : w₁ = w₂ := by
  have h := hG a b hab
  exact Finset.card_le_one.mp h w₁ (by simp [h₁a, h₁b]) w₂ (by simp [h₂a, h₂b])

-- A block of the cover never holds two distinct vertices `u` and `y` with `u` adjacent to `x`
-- and `xy` in `U`: its centre would be a second common neighbour of `u` and `y` besides `x`.
theorem block_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (U : Finset (Sym2 (Fin n)))
    (hU : ∀ e ∈ U, e ∈ G.edgeSet) (x : Fin n) (B : Finset (Fin n))
    (hB : B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))
    {u y : Fin n} (hu : u ∈ B) (hy : y ∈ B) (hxy : s(x, y) ∈ U) (hxu : G.Adj x u) (huy : u ≠ y) :
    False := by
  rcases hB with h1 | ⟨_, c, hc, hcU⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    simp only [Finset.mem_singleton] at hu hy
    exact huy (hu.trans hy.symm)
  · have hxy' : G.Adj x y := (SimpleGraph.mem_edgeSet G).mp (hU _ hxy)
    have hxc : x = c :=
      common_nbr_eq G hG huy hxu.symm hxy'.symm (hc u hu).symm (hc y hy).symm
    subst hxc
    exact hcU y hy hxy

end PEqualNP.Outside.L_meta_1646

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G _ hG U hU x Y hY R π hπ hcov
  classical
  -- the block chosen for each covered vertex
  let f : Fin n → Finset (Fin n) := fun v => if h : ∃ B ∈ π, v ∈ B then h.choose else ∅
  have hf : ∀ v ∈ R, f v ∈ π ∧ v ∈ f v := by
    intro v hv
    have h : ∃ B ∈ π, v ∈ B := hcov v hv
    simp only [f, h]
    exact h.choose_spec
  -- two vertices of `Y` never share a block
  have hinj : Set.InjOn f ↑(R ∩ Y) := by
    intro y₁ hy₁ y₂ hy₂ heq
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hy₁ hy₂
    by_contra hne
    obtain ⟨hB, hy₁B⟩ := hf y₁ hy₁.1
    obtain ⟨-, hy₂B⟩ := hf y₂ hy₂.1
    rw [← heq] at hy₂B
    exact PEqualNP.Outside.L_meta_1646.block_unique G hG U hU x (f y₁) (hπ _ hB).2 hy₁B hy₂B
      (hY y₂ hy₂.2) ((SimpleGraph.mem_edgeSet G).mp (hU _ (hY y₁ hy₁.2))) hne
  refine ⟨?_, ?_⟩
  · exact Finset.card_le_card_of_injOn f (fun y hy => (hf y (Finset.mem_inter.mp hy).1).1) hinj
  · intro hR hRY
    obtain ⟨r, hrR, hrY⟩ := Finset.not_subset.mp hRY
    obtain ⟨Br, hBr, hrBr⟩ := hcov r hrR
    have hmaps : ∀ y ∈ R ∩ Y, f y ∈ π.erase Br := by
      intro y hy
      obtain ⟨hyR, hyY⟩ := Finset.mem_inter.mp hy
      obtain ⟨hfy, hyf⟩ := hf y hyR
      refine Finset.mem_erase.mpr ⟨?_, hfy⟩
      intro hEq
      rw [hEq] at hyf
      have hry : r ≠ y := fun h => hrY (h ▸ hyY)
      exact PEqualNP.Outside.L_meta_1646.block_unique G hG U hU x Br (hπ _ hBr).2 hrBr hyf
        (hY y hyY) (hR r hrR) hry
    have h1 := Finset.card_le_card_of_injOn f hmaps hinj
    have h2 := Finset.card_erase_of_mem hBr
    have h3 : 0 < π.card := Finset.card_pos.mpr ⟨Br, hBr⟩
    omega
