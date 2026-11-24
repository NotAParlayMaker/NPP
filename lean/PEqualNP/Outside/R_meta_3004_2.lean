import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3004_2
    (search :
      let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let step := fun (ws : List ℕ) (z : ℕ) =>
        ∃ a ∈ ws, ∃ b ∈ ws, z = a &&& b ∨ z = a ||| b
      let valid := fun (seed L : List ℕ) =>
        ∀ i : Fin L.length, step (seed ++ L.take i.val) (L.get i)
      ∃ (g : ℕ) (M : List ℕ),
        step A g ∧ M.length ≤ 24 ∧ valid (g :: A) M ∧ step ((g :: A) ++ M) 2097151)
    (compact :
      let step := fun (ws : List ℕ) (z : ℕ) =>
        ∃ a ∈ ws, ∃ b ∈ ws, z = a &&& b ∨ z = a ||| b
      let valid := fun (seed L : List ℕ) =>
        ∀ i : Fin L.length, step (seed ++ L.take i.val) (L.get i)
      ∀ (A : List ℕ) (g t : ℕ) (M : List ℕ), t ∉ A →
        step A g → valid (g :: A) M → step ((g :: A) ++ M) t →
        ∃ S : List ℕ, S.length ≤ M.length + 2 ∧ S.Nodup ∧
          (∀ z ∈ S, z ∉ A) ∧ t ∈ S ∧ valid A S) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (26 : ℕ) ∧ x2.Nodup ∧ (∀ x3 ∈ x2, x3 ∉ x1) ∧ (2097151 : ℕ) ∈ x2 ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  have fresh : (2097151 : ℕ) ∉ A := by decide +kernel
  obtain ⟨g, M, hg, hm, legal, finish⟩ := search
  obtain ⟨S, bound, nd, outside, seen, steps⟩ :=
    compact A g 2097151 M fresh hg legal finish
  exact ⟨S, by omega, nd, outside, seen, steps⟩
