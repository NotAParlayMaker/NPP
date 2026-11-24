import PEqualNP.Defs

-- The first comparable signature fixes at least one row. Clamping the inputs
-- on that row commutes with both gates. The compiler lifts a residual output
-- to a full word, joins it with the recorded signature, and drops duplicates.
theorem PEqualNP.Outside.R_meta_3004_317
    (compile : let ok (p xs : List ℕ) := ∀ i : Fin xs.length,
        ∃ a ∈ p ++ xs.take i.val, ∃ b ∈ p ++ xs.take i.val,
          xs.get i = a &&& b ∨ xs.get i = a ||| b
      ∀ (p head tail : List ℕ) (h t : ℕ) (upper : Bool),
        h ∈ p ++ head → t ∉ p → ok p head →
        let f (w : ℕ) := if upper then w &&& h else w ||| h
        let q := (p ++ head).map f
        ok q tail → t ∈ q ++ tail →
        ∃ ys : List ℕ, ys.length ≤ head.length + tail.length + 1 ∧ ys.Nodup ∧
          (∀ a ∈ ys, a ∉ p) ∧ t ∈ ys ∧ ok p ys)
    (frontier : let p : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]
      let ok (p xs : List ℕ) := ∀ i : Fin xs.length,
        ∃ a ∈ p ++ xs.take i.val, ∃ b ∈ p ++ xs.take i.val,
          xs.get i = a &&& b ∨ xs.get i = a ||| b
      let t : ℕ := 2097151
      ∃ (xs : List ℕ) (h : ℕ) (upper : Bool) (tail : List ℕ),
        xs.length + tail.length ≤ 24 ∧
        (∀ x ∈ xs, x &&& t ≠ x ∧ x &&& t ≠ t) ∧
        (if upper then h &&& t = t ∧ h ≠ 288230376151711743 else h &&& t = h ∧ h ≠ 0) ∧
        h ≠ t ∧ ok p (xs ++ [h]) ∧
        let q := (p ++ xs ++ [h]).map (fun w => if upper then w &&& h else w ||| h)
        ok q tail ∧ t ∈ q ++ tail) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (26 : ℕ) ∧ x2.Nodup ∧ (∀ x3 ∈ x2, x3 ∉ x1) ∧ (2097151 : ℕ) ∈ x2 ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  dsimp only at frontier ⊢
  obtain ⟨xs,h,upper,tail,budget,_,_,_,validHead,validTail,available⟩ := frontier
  let p : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]
  have hp : h ∈ p ++ (xs ++ [h]) := by simp
  have fresh : (2097151 : ℕ) ∉ p := by decide
  have solved := compile p (xs ++ [h]) tail h 2097151 upper hp fresh validHead
  simp only [← List.append_assoc] at solved
  obtain ⟨ys,size,nd,noraw,hit,ok⟩ := solved validTail available
  exact ⟨ys,by simp at size;omega,nd,noraw,hit,ok⟩
