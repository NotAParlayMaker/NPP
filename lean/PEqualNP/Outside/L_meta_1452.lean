import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1452

theorem of_one_point_le {n : ℕ} {x : Fin n → Bool} {p : Fin n}
    (hp : x p = true) :
    (fun q : Fin n => decide (q = p)) ≤ x := by
  intro q
  by_cases hq : q = p
  · subst hq
    simp [hp]
  · simp [hq]

theorem exists_on_colour {n f k : ℕ} {c : Fin f → Fin n → Fin k}
    {T : Fin f → Fin k → (Fin n → Bool) → Bool} {j : Fin f} {a : Fin k}
    {x : Fin n → Bool}
    (hEmpty : ∀ (j2 : Fin f) (a2 : Fin k) (z : Fin n → Bool),
      (∀ p2 : Fin n, z p2 = true → c j2 p2 ≠ a2) → T j2 a2 z = false)
    (hT : T j a x = true) :
    ∃ p : Fin n, x p = true ∧ c j p = a := by
  by_contra h
  have hnone : ∀ p2 : Fin n, x p2 = true → c j p2 ≠ a := by
    intro p2 hp2
    exact fun hcol => h ⟨p2, hp2, hcol⟩
  have : T j a x = false := hEmpty j a x hnone
  exact Bool.eq_false_iff.mp this hT

theorem unique_on_colour_of_inj {n f k : ℕ} {c : Fin f → Fin n → Fin k}
    {j : Fin f} {a : Fin k} {x : Fin n → Bool} {p : Fin n}
    (hinj : Set.InjOn (c j) {i : Fin n | x i = true})
    (hp : x p = true) (hcol : c j p = a) :
    ∀ q : Fin n, x q = true → c j q = a → q = p := by
  intro q hq hcq
  exact hinj hq hp (hcq.trans hcol.symm)

theorem true_of_le {b c : Bool} (hle : b ≤ c) (hb : b = true) : c = true :=
  Bool.le_iff_imp.mp hle hb

end PEqualNP.Outside.L_meta_1452

theorem PEqualNP.Outside.L_meta_1452 :
    ∀ (n f k w : ℕ) (L : Finset (Fin n)) (c : Fin f → Fin n → Fin k)
      (T : Fin f → Fin k → (Fin n → Bool) → Bool),
      (∀ S : Finset (Fin n), S.card ≤ w →
        ∃ j0 : Fin f, Set.InjOn (c j0) (S : Set (Fin n))) →
      (∀ (j1 : Fin f) (a1 : Fin k) (u v : Fin n → Bool),
        u ≤ v → T j1 a1 u ≤ T j1 a1 v) →
      (∀ (j2 : Fin f) (a2 : Fin k) (z : Fin n → Bool),
        (∀ p2 : Fin n, z p2 = true → c j2 p2 ≠ a2) → T j2 a2 z = false) →
      (∀ (j3 : Fin f) (a3 : Fin k) (y : Fin n → Bool) (p3 : Fin n),
        y p3 = true → c j3 p3 = a3 →
          (∀ q3 : Fin n, y q3 = true → c j3 q3 = a3 → q3 = p3) →
          (T j3 a3 y = true ↔ p3 ∈ L)) →
      ∀ x : Fin n → Bool,
        (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ w →
          ((∀ j : Fin f, ∃ a : Fin k, T j a x = true) ↔
            ∃ p : Fin n, x p = true ∧ p ∈ L) := by
  intro n f k w L c T hInj hMono hEmpty hUnique x hx
  constructor
  · intro hAll
    let S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => x i = true)
    obtain ⟨j0, hinj⟩ := hInj S hx
    obtain ⟨a, hT⟩ := hAll j0
    have hinj' : Set.InjOn (c j0) {i : Fin n | x i = true} := by
      intro i hi j hj he
      exact hinj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩) he
    obtain ⟨p, hp, hcol⟩ :=
      PEqualNP.Outside.L_meta_1452.exists_on_colour hEmpty hT
    have huniq :=
      PEqualNP.Outside.L_meta_1452.unique_on_colour_of_inj hinj' hp hcol
    have hpL : p ∈ L := (hUnique j0 a x p hp hcol huniq).mp hT
    exact ⟨p, hp, hpL⟩
  · intro hEx
    obtain ⟨p, hp, hpL⟩ := hEx
    intro j
    refine ⟨c j p, ?_⟩
    let y : Fin n → Bool := fun q => decide (q = p)
    have hy : y p = true := by simp [y]
    have hcol : c j p = c j p := rfl
    have huniq : ∀ q3 : Fin n, y q3 = true → c j q3 = c j p → q3 = p := by
      intro q3 hq3 _
      simpa [y] using hq3
    have hTy : T j (c j p) y = true :=
      (hUnique j (c j p) y p hy hcol huniq).mpr hpL
    have hle : y ≤ x := PEqualNP.Outside.L_meta_1452.of_one_point_le hp
    exact PEqualNP.Outside.L_meta_1452.true_of_le (hMono j (c j p) y x hle) hTy
