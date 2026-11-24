import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1514_aux

theorem third : ∀ x y : Fin 3, x ≠ y → ∃ z : Fin 3, z ≠ x ∧ z ≠ y := by decide

theorem key {n : ℕ} (V : Fin 3 → Fin n) (M : Fin 3 → Finset (Fin n)) (P Q : Finset (Fin n))
    (hPQ : ∀ x : Fin 3, ¬ ((∃ v ∈ P, v ∉ M x) ∧ (∃ v ∈ Q, v ∉ M x)))
    (x y z : Fin 3) (p q a c d : Fin n) (hpz : p ∉ M z) (hqz : q ∉ M z) (hqx : q ∉ M x)
    (hVx : V x ∉ M x) (hVy : V y ∉ M y) (ha : a ∈ P) (ha' : a = p ∨ a = V x)
    (hc : c ∈ P) (hc' : c = q ∨ c = V y) (hd : d ∈ Q) (hd' : d = q ∨ d = V y)
    (hPz : ∀ v ∈ P, v ∈ M z) : False := by
  have haV : a = V x := by
    rcases ha' with h | h
    · subst h; exact absurd (hPz _ ha) hpz
    · exact h
  have hcV : c = V y := by
    rcases hc' with h | h
    · subst h; exact absurd (hPz _ hc) hqz
    · exact h
  subst haV hcV
  rcases hd' with h | h
  · subst h; exact hPQ x ⟨⟨_, ha, hVx⟩, ⟨_, hd, hqx⟩⟩
  · subst h; exact hPQ y ⟨⟨_, hc, hVy⟩, ⟨_, hd, hVy⟩⟩

theorem memV {n : ℕ} (V : Fin 3 → Fin n) (M : Fin 3 → Finset (Fin n))
    (hM : ∀ x y z : Fin 3, x ≠ y → y ≠ z → x ≠ z → M x ∩ M y = {V z})
    (x y z : Fin 3) (h1 : x ≠ y) (h2 : y ≠ z) (h3 : x ≠ z) : V z ∈ M x ∧ V z ∈ M y := by
  have : V z ∈ M x ∩ M y := by rw [hM x y z h1 h2 h3]; simp
  exact Finset.mem_inter.1 this

theorem eqV {n : ℕ} (V : Fin 3 → Fin n) (M : Fin 3 → Finset (Fin n))
    (hM : ∀ x y z : Fin 3, x ≠ y → y ≠ z → x ≠ z → M x ∩ M y = {V z})
    (x y z : Fin 3) (h1 : x ≠ y) (h2 : y ≠ z) (h3 : x ≠ z) (w : Fin n)
    (hx : w ∈ M x) (hy : w ∈ M y) : w = V z := by
  have : w ∈ M x ∩ M y := Finset.mem_inter.2 ⟨hx, hy⟩
  rw [hM x y z h1 h2 h3] at this
  simpa using this

end PEqualNP.Outside.L_meta_1514_aux

open PEqualNP.Outside.L_meta_1514_aux in
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
  obtain ⟨z, hzx, hzy⟩ := third x y hxy
  obtain ⟨p, hp, ⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hx
  obtain ⟨q, hq, ⟨c, hc, hc'⟩, ⟨d, hd, hd'⟩⟩ := hy
  have hpY := hY x p hp
  have hqY := hY y q hq
  have hpz : p ∉ M z := fun h => hpY.2 y (eqV V M hM x z y (Ne.symm hzx) hzy hxy p hpY.1 h)
  have hqz : q ∉ M z := fun h => hqY.2 x (eqV V M hM y z x (Ne.symm hzy) hzx (Ne.symm hxy) q hqY.1 h)
  have hqx : q ∉ M x := fun h => hqY.2 z (eqV V M hM x y z hxy (Ne.symm hzy) (Ne.symm hzx) q h hqY.1)
  have hpy : p ∉ M y := fun h => hpY.2 z (eqV V M hM x y z hxy (Ne.symm hzy) (Ne.symm hzx) p hpY.1 h)
  have hVx : V x ∉ M x := by
    intro h
    have h2 := (memV V M hM y z x (Ne.symm hzy) hzx (Ne.symm hxy)).1
    exact hzx (hV (eqV V M hM x y z hxy (Ne.symm hzy) (Ne.symm hzx) _ h h2)).symm
  have hVy : V y ∉ M y := by
    intro h
    have h2 := (memV V M hM x z y (Ne.symm hzx) hzy hxy).1
    exact hzy (hV (eqV V M hM x y z hxy (Ne.symm hzy) (Ne.symm hzx) _ h2 h)).symm
  by_cases hPz : ∀ v ∈ P, v ∈ M z
  · exact key V M P Q hPQ x y z p q a c d hpz hqz hqx hVx hVy ha ha' hc hc' hd hd' hPz
  · have hQz : ∀ v ∈ Q, v ∈ M z := by
      intro v hv
      by_contra hn
      push Not at hPz
      exact hPQ z ⟨hPz, ⟨v, hv, hn⟩⟩
    have hPQ' : ∀ x : Fin 3, ¬ ((∃ v ∈ Q, v ∉ M x) ∧ (∃ v ∈ P, v ∉ M x)) :=
      fun w h => hPQ w ⟨h.2, h.1⟩
    exact key V M Q P hPQ' x y z p q b d c hpz hqz hqx hVx hVy hb hb' hd hd' hc hc' hQz
