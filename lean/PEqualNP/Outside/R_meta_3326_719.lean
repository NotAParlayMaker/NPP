import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3326_719
    (reify :
      let step := fun (ws : List ℕ) (z : ℕ) =>
        ∃ a ∈ ws, ∃ b ∈ ws, z = a &&& b ∨ z = a ||| b
      ∀ (A : List (BitVec 59)) (v : Fin 40 → BitVec 59)
          (s : Fin 25 → Fin 40 × Fin 40 × Bool),
        A.length = 15 →
        (∀ i : ℕ, i < 15 → v (Fin.ofNat 40 i) = A.getD i 0) →
        (∀ i : Fin 25, (s i).1.val < 15 + i.val ∧ (s i).2.1.val < 15 + i.val) →
        (∀ i : Fin 25, v (Fin.ofNat 40 (15 + i.val)) =
          if (s i).2.2 then v (s i).1 ||| v (s i).2.1 else v (s i).1 &&& v (s i).2.1) →
        ∃ M : List ℕ, M.length ≤ 24 ∧
          (∀ i : Fin M.length, step (A.map BitVec.toNat ++ M.take i.val) (M.get i)) ∧
          step (A.map BitVec.toNat ++ M) (v 39).toNat)
    (certificate :
      let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
        8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
        155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
        270286071508633728, 288160007407550752]
      ∃ g ∈ ([17871361015808, 95274182876594239, 1, 284526031944024591,
          72622777407897600, 241600541374316567] : List ℕ),
        ∃ (v : Fin 40 → BitVec 59) (s : Fin 25 → Fin 40 × Fin 40 × Bool),
          let a := BitVec.ofNat 59 g :: A.map (BitVec.ofNat 59)
          (∀ i : ℕ, i < 15 → v (Fin.ofNat 40 i) = a.getD i 0) ∧
          (∀ i : Fin 25, (s i).1.val < 15 + i.val ∧ (s i).2.1.val < 15 + i.val) ∧
          (∀ i : Fin 25, v (Fin.ofNat 40 (15 + i.val)) =
            if (s i).2.2 then v (s i).1 ||| v (s i).2.1 else v (s i).1 &&& v (s i).2.1) ∧
          v 39 = BitVec.ofNat 59 2097151) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; have x2 : List ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 : ℕ) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = x4 &&& x5 ∨ x3 = x4 ||| x5; ∃ x3 ∈ [(17871361015808 : ℕ), (95274182876594239 : ℕ), (1 : ℕ), (284526031944024591 : ℕ), (72622777407897600 : ℕ), (241600541374316567 : ℕ)], ∃ (x4 : List ℕ), x4.length ≤ (24 : ℕ) ∧ (∀ (x5 : Fin x4.length), x2 (x3 :: x1 ++ List.take (↑x5) x4) (x4.get x5)) ∧ x2 (x3 :: x1 ++ x4) (2097151 : ℕ) := by
  dsimp only
  obtain ⟨g, hg, v, s, hInputs, hOrder, hTransfer, hTarget⟩ := certificate
  let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
    8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
    155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
    270286071508633728, 288160007407550752]
  let a := BitVec.ofNat 59 g :: A.map (BitVec.ofNat 59)
  have hWidth : ∀ g ∈ ([17871361015808, 95274182876594239, 1, 284526031944024591,
      72622777407897600, 241600541374316567] : List ℕ), (BitVec.ofNat 59 g).toNat = g := by
    decide +kernel
  have hMap : a.map BitVec.toNat = g :: A := by
    change (BitVec.ofNat 59 g).toNat :: (A.map (BitVec.ofNat 59)).map BitVec.toNat = g :: A
    rw [hWidth g hg]
    rfl
  obtain ⟨M, hSize, hValid, hFinish⟩ := reify a v s (by rfl) hInputs hOrder hTransfer
  rw [hMap] at hValid hFinish
  rw [hTarget] at hFinish
  exact ⟨g, hg, M, hSize, hValid, hFinish⟩
