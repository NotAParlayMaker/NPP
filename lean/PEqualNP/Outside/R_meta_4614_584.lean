import Mathlib
import PEqualNP.Defs

-- At the maximum cut width, each suffix gate consumes two live values exactly once.
-- The other branch searches an ordinary DAG over at most twelve distinct masked ports.
theorem PEqualNP.Outside.R_meta_4614_584
    (search : let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let valid := fun (S U : List ℕ) => ∀ i : Fin U.length, ∃ a ∈ S ++ U.take i.val, ∃ b ∈ S ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
      let cover := fun (K : List ℕ) (q t : ℕ) => ∀ j : ℕ, ∃ i : ℕ, q.testBit i = true ∧ t.testBit i = t.testBit j ∧ ∀ x ∈ K, if t.testBit j = true then x.testBit i = true → x.testBit j = true else x.testBit j = true → x.testBit i = true
      let step := fun (X Y : List ℕ) => ∃ a ∈ X, ∃ b ∈ X.erase a, ∃ z, (z = a &&& b ∨ z = a ||| b) ∧ Y.Perm (z :: (X.erase a).erase b)
      let budget := fun (K : List ℕ) (t k : ℕ) => ∃ U : List ℕ, U.length ≤ k ∧ valid K U ∧ t ∈ K ++ U
      let route := fun (P : List ℕ) (t k : ℕ) => P.Nodup ∧ ((P.length ≤ k ∧ budget P t k) ∨ (P.length = k + 1 ∧ Relation.ReflTransGen step P [t]))
      ∃ (F K : List ℕ) (q : ℕ), F.length ≤ 14 ∧ valid A F ∧ K ⊆ A ++ F ∧
        cover K q 2097151 ∧ route (K.map (fun a => a &&& q)) (2097151 &&& q) 12)
    (architecture : let valid := fun (S U : List ℕ) => ∀ i : Fin U.length, ∃ a ∈ S ++ U.take i.val, ∃ b ∈ S ++ U.take i.val, U.get i = a &&& b ∨ U.get i = a ||| b
      let step := fun (X Y : List ℕ) => ∃ a ∈ X, ∃ b ∈ X.erase a, ∃ z, (z = a &&& b ∨ z = a ||| b) ∧ Y.Perm (z :: (X.erase a).erase b)
      let budget := fun (K : List ℕ) (t k : ℕ) => ∃ U : List ℕ, U.length ≤ k ∧ valid K U ∧ t ∈ K ++ U
      let route := fun (P : List ℕ) (t k : ℕ) => P.Nodup ∧ ((P.length ≤ k ∧ budget P t k) ∨ (P.length = k + 1 ∧ Relation.ReflTransGen step P [t]))
      ∀ (S : List ℕ) (t k : ℕ), budget S t k ↔ ∃ P ⊆ S, route P t k) :
    have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; have x3 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x4 : List ℕ) (x5 : List ℕ) (x6 : ℕ) (x7 : List ℕ), x4.length ≤ (14 : ℕ) ∧ x5.length ≤ (13 : ℕ) ∧ x7.length ≤ (12 : ℕ) ∧ x1 x3 x4 ∧ (∀ x8 ∈ x5, x8 ∈ x3 ++ x4) ∧ x2 x5 x6 (2097151 : ℕ) ∧ x1 (List.map (fun (x8 : ℕ) => x8 &&& x6) x5) x7 ∧ (2097151 : ℕ) &&& x6 ∈ List.map (fun (x8 : ℕ) => x8 &&& x6) x5 ++ x7 := by
  obtain ⟨F,K,q,hF,front,ports,cover,nd,shape⟩ := search
  let P := K.map (fun x => x &&& q)
  have width : P.length ≤ 13 := by dsimp [P]; rcases shape with ⟨h,_⟩ | ⟨h,_⟩ <;> omega
  obtain ⟨V,hV,valid,seen⟩ := (architecture P (2097151 &&& q) 12).mpr ⟨P, fun _ e => e, nd, shape⟩
  exact ⟨F,K,q,V,hF,by simpa [P] using width,hV,front,fun _ h => ports h,cover,valid,seen⟩
