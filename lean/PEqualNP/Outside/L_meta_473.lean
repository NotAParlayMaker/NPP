import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_473 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)) (T0 : Finset V) (T1 : Finset (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → (∀ u ∈ T0, ∃ v, G0.Adj u v) → (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) → (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) → (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  intro V G0 N num G' T0 T1 hN hinj hG' hneigh hT1 hcov
  classical
  let F : { u // u ∈ T0 } → Fin N := fun u =>
    ⟨num u.1, hN u.1 (Classical.choose (hneigh u.1 u.2)) (Classical.choose_spec (hneigh u.1 u.2))⟩
  have hFval : ∀ u : { u // u ∈ T0 }, (F u).val = num u.1 := fun _ => rfl
  have hFinj : Function.Injective F := by
    intro u w h
    have hnum : num u.1 = num w.1 := by rw [← hFval u, ← hFval w, h]
    apply Subtype.ext
    exact hinj u.1 (Classical.choose (hneigh u.1 u.2)) w.1 (Classical.choose (hneigh w.1 w.2))
      (Classical.choose_spec (hneigh u.1 u.2)) (Classical.choose_spec (hneigh w.1 w.2)) hnum
  have hT1eq : T1 = T0.attach.image F := by
    ext a
    rw [hT1 a, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, hnum⟩
      exact ⟨⟨u, hu⟩, Finset.mem_attach T0 ⟨u, hu⟩, Fin.ext (by rw [hFval]; exact hnum)⟩
    · rintro ⟨u, -, h⟩
      exact ⟨u.1, u.2, by rw [← hFval u]; exact congrArg Fin.val h⟩
  constructor
  · intro a b hab
    rw [hG' a b] at hab
    obtain ⟨u, v, huv, hua, hvb⟩ := hab
    have ha : a = ⟨num u, hN u v huv⟩ := Fin.ext hua.symm
    have hb : b = ⟨num v, hN v u huv.symm⟩ := Fin.ext hvb.symm
    rw [ha, hb]
    rcases hcov u v huv with h | h
    · left
      rw [hT1 ⟨num u, hN u v huv⟩]
      exact ⟨u, h, rfl⟩
    · right
      rw [hT1 ⟨num v, hN v u huv.symm⟩]
      exact ⟨v, h, rfl⟩
  · rw [hT1eq, Finset.card_image_of_injective T0.attach hFinj, Finset.card_attach]
