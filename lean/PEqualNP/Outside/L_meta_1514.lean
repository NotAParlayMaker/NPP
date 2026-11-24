import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1514

private lemma third_fin3 {x y : Fin 3} (hxy : x ≠ y) :
    ∃ z : Fin 3, x ≠ z ∧ y ≠ z := by
  fin_cases x <;> fin_cases y <;> simp_all <;> decide

private lemma vertex_not_mem {n : ℕ} {V : Fin 3 → Fin n} {M : Fin 3 → Finset (Fin n)}
    (hV : Function.Injective V)
    (hM : ∀ x y z : Fin 3, x ≠ y → y ≠ z → x ≠ z → M x ∩ M y = {V z})
    (x : Fin 3) : V x ∉ M x := by
  intro hx
  have ⟨y, hxy⟩ : ∃ y : Fin 3, x ≠ y := by
    fin_cases x
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  obtain ⟨z, hxz, hyz⟩ := third_fin3 hxy
  have h1 : M x ∩ M y = {V z} := hM x y z hxy hyz hxz
  have h2 : M y ∩ M z = {V x} := hM y z x hyz hxz.symm hxy.symm
  have hVy : V x ∈ M y := by
    have : V x ∈ M y ∩ M z := by rw [h2]; exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp this).1
  have hVz : V x = V z := by
    have : V x ∈ M x ∩ M y := Finset.mem_inter.mpr ⟨hx, hVy⟩
    rw [h1] at this
    exact Finset.mem_singleton.mp this
  exact hxz (hV hVz)

private lemma y_not_mem_other {n : ℕ} {V : Fin 3 → Fin n} {M Y : Fin 3 → Finset (Fin n)}
    (hM : ∀ x y z : Fin 3, x ≠ y → y ≠ z → x ≠ z → M x ∩ M y = {V z})
    (hY : ∀ x : Fin 3, ∀ p ∈ Y x, p ∈ M x ∧ ∀ y : Fin 3, p ≠ V y)
    {x w : Fin 3} (hxw : x ≠ w) {p : Fin n} (hp : p ∈ Y x) : p ∉ M w := by
  intro hpw
  obtain ⟨hpx, hpV⟩ := hY x p hp
  obtain ⟨z, hxz, hwz⟩ := third_fin3 hxw
  have h1 : M x ∩ M w = {V z} := hM x w z hxw hwz hxz
  have hpeq : p = V z := by
    have : p ∈ M x ∩ M w := Finset.mem_inter.mpr ⟨hpx, hpw⟩
    rw [h1] at this
    exact Finset.mem_singleton.mp this
  exact hpV z hpeq

private lemma side_contra {n : ℕ} {V : Fin 3 → Fin n} {M : Fin 3 → Finset (Fin n)}
    {A B : Finset (Fin n)} {x y z : Fin 3} {p q : Fin n}
    (hVx : V x ∉ M x) (hVy : V y ∉ M y)
    (hpz : p ∉ M z) (hqz : q ∉ M z) (hpy : p ∉ M y)
    (hAB : ∀ w : Fin 3, ¬ ((∃ v ∈ A, v ∉ M w) ∧ (∃ v ∈ B, v ∉ M w)))
    (hAz : ∀ v ∈ A, v ∈ M z)
    (hAx : p ∈ A ∨ V x ∈ A) (hAy : q ∈ A ∨ V y ∈ A)
    (hBx : p ∈ B ∨ V x ∈ B) : False := by
  have hVxA : V x ∈ A := hAx.resolve_left (fun hpA => hpz (hAz p hpA))
  have hVyA : V y ∈ A := hAy.resolve_left (fun hqA => hqz (hAz q hqA))
  have hBxM : ∀ v ∈ B, v ∈ M x := fun v hvB =>
    by_contra fun hvMx => hAB x ⟨⟨V x, hVxA, hVx⟩, ⟨v, hvB, hvMx⟩⟩
  have hByM : ∀ v ∈ B, v ∈ M y := fun v hvB =>
    by_contra fun hvMy => hAB y ⟨⟨V y, hVyA, hVy⟩, ⟨v, hvB, hvMy⟩⟩
  have hpB : p ∈ B := hBx.resolve_right (fun hVxB => hVx (hBxM (V x) hVxB))
  exact hpy (hByM p hpB)

end PEqualNP.Outside.L_meta_1514

theorem PEqualNP.Outside.L_meta_1514 : ∀ (n : ℕ) (V : Fin 3 → Fin n) (M Y : Fin 3 → Finset (Fin n)) (P Q : Finset (Fin n)),
    Function.Injective V →
    (∀ x y z : Fin 3, x ≠ y → y ≠ z → x ≠ z → M x ∩ M y = {V z}) →
    (∀ x : Fin 3, ∀ p ∈ Y x, p ∈ M x ∧ ∀ y : Fin 3, p ≠ V y) →
    (∀ x : Fin 3, ¬ ((∃ v ∈ P, v ∉ M x) ∧ (∃ v ∈ Q, v ∉ M x))) →
    ∀ x y : Fin 3,
      (∃ p ∈ Y x, (∃ v ∈ P, v = p ∨ v = V x) ∧ (∃ v ∈ Q, v = p ∨ v = V x)) →
      (∃ p ∈ Y y, (∃ v ∈ P, v = p ∨ v = V y) ∧ (∃ v ∈ Q, v = p ∨ v = V y)) →
      x = y := by
  intro n V M Y P Q hV hM hY hPQ x y hx hy
  by_contra hxy
  obtain ⟨z, hxz, hyz⟩ := PEqualNP.Outside.L_meta_1514.third_fin3 hxy
  obtain ⟨p, hpY, hPx, hQx⟩ := hx
  obtain ⟨q, hqY, hPy, hQy⟩ := hy
  have hpP : p ∈ P ∨ V x ∈ P := by
    rcases hPx with ⟨v, hv, rfl | rfl⟩
    · exact Or.inl hv
    · exact Or.inr hv
  have hpQ : p ∈ Q ∨ V x ∈ Q := by
    rcases hQx with ⟨v, hv, rfl | rfl⟩
    · exact Or.inl hv
    · exact Or.inr hv
  have hqP : q ∈ P ∨ V y ∈ P := by
    rcases hPy with ⟨v, hv, rfl | rfl⟩
    · exact Or.inl hv
    · exact Or.inr hv
  have hqQ : q ∈ Q ∨ V y ∈ Q := by
    rcases hQy with ⟨v, hv, rfl | rfl⟩
    · exact Or.inl hv
    · exact Or.inr hv
  have hVx : V x ∉ M x := PEqualNP.Outside.L_meta_1514.vertex_not_mem hV hM x
  have hVy : V y ∉ M y := PEqualNP.Outside.L_meta_1514.vertex_not_mem hV hM y
  have hpz : p ∉ M z := PEqualNP.Outside.L_meta_1514.y_not_mem_other hM hY hxz hpY
  have hqz : q ∉ M z := PEqualNP.Outside.L_meta_1514.y_not_mem_other hM hY hyz hqY
  have hpy : p ∉ M y := PEqualNP.Outside.L_meta_1514.y_not_mem_other hM hY hxy hpY
  by_cases hPz : ∃ v ∈ P, v ∉ M z
  · have hQz : ∀ v ∈ Q, v ∈ M z := fun v hvQ =>
      by_contra fun hvMz => hPQ z ⟨hPz, ⟨v, hvQ, hvMz⟩⟩
    exact PEqualNP.Outside.L_meta_1514.side_contra hVx hVy hpz hqz hpy
      (fun w ⟨h1, h2⟩ => hPQ w ⟨h2, h1⟩) hQz hpQ hqQ hpP
  · have hPz' : ∀ v ∈ P, v ∈ M z := fun v hvP =>
      by_contra fun hvMz => hPz ⟨v, hvP, hvMz⟩
    exact PEqualNP.Outside.L_meta_1514.side_contra hVx hVy hpz hqz hpy
      hPQ hPz' hpP hqP hpQ
