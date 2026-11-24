import Mathlib

open Module

theorem PEqualNP.Outside.R_gct_196_73
    (hcentred : ∀ K : Submodule ℂ (Fin 4 × Fin 7 → ℂ),
      (∀ t ∈ K, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧
        (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
          if a < b then t (a, j) * t (b, l) else 0) = 0 ∧
        (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
          ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
            if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧
        (∑ j, ∑ l, ∑ m, ∑ n,
          if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
            t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) →
      Module.finrank ℂ K + 1 ≤ 7)
    (range_bound : ∀ L : Submodule ℂ (Fin 4 × Fin 7 → ℂ),
      (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0) →
      let f : (Fin 4 × Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
        LinearMap.pi fun i => ∑ j, LinearMap.proj (i, j)
      Module.finrank ℂ (LinearMap.range (f.comp L.subtype)) ≤ 3) :
    ∀ L : Submodule ℂ (Fin 4 × Fin 7 → ℂ), (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) → Module.finrank ℂ L ≤ 9 := by
  intro L hL
  let f : (Fin 4 × Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
    LinearMap.pi fun i => ∑ j, LinearMap.proj (i, j)
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.comp L.subtype)
  have hr : Module.finrank ℂ (LinearMap.range (f.comp L.subtype)) ≤ 3 := by
    simpa [f] using range_bound L (fun t ht => (hL t ht).1)
  set K : Submodule ℂ (Fin 4 × Fin 7 → ℂ) :=
    (LinearMap.ker (f.comp L.subtype)).map L.subtype with hKdef
  have hK : Module.finrank ℂ K = Module.finrank ℂ (LinearMap.ker (f.comp L.subtype)) :=
    (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective L.subtype L.injective_subtype
        (LinearMap.ker (f.comp L.subtype)))).symm
  have hKA := hcentred K (by
    intro t ht
    obtain ⟨x, hxk, rfl⟩ := Submodule.mem_map.mp ht
    obtain ⟨_, h2, h3, h4⟩ := hL x.1 x.2
    refine ⟨?_, h2, h3, h4⟩
    intro i
    have hi := congrFun (LinearMap.mem_ker.mp hxk) i
    simpa [f] using hi)
  omega
