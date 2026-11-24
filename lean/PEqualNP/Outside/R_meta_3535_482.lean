import Mathlib
import PEqualNP.Defs
theorem PEqualNP.Outside.R_meta_3535_482
    (assemble : let T := ℕ × ℕ
    let sat := fun (w : ℕ) (p : T) => w &&& p.1 = p.1 ∧ w &&& p.2 = 0
    let sub := fun (p q : T) => p.1 &&& q.1 = p.1 ∧ p.2 &&& q.2 = p.2
    let mix := fun (u v : T) (t : Bool) => if t then (u.1 &&& v.1,u.2 ||| v.2) else (u.1 ||| v.1,u.2 &&& v.2)
    let ok := fun (A : List ℕ) (D : List T) => ∀ p∈D, ∃ x∈A, sat x p
    let step := fun (E D : List T) => ∃ u∈E, ∃ v∈E, ∃ t : Bool, ∀ p∈D, ∃ q∈mix u v t :: E, sub p q
    let prog := fun (B L : List ℕ) => ∀ i : Fin L.length, ∃ a∈ B ++ L.take i.val, ∃ b∈ B ++ L.take i.val,
        L.get i=a &&& b ∨ L.get i=a ||| b
    ∀ (B : List ℕ) (D : ℕ → List T) (n : ℕ), ok B (D 0) → (∀ i<n, step (D i) (D (i+1))) →
      ∃ L : List ℕ, L.length=n ∧ prog B L ∧ ok (B++L) (D n))
    (rows : let B : List ℕ := [63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752,191866593364673099,193001360500003407]
    let prog := fun (B L : List ℕ) => ∀ i : Fin L.length, ∃ a∈ B ++ L.take i.val, ∃ b∈ B ++ L.take i.val,
        L.get i=a &&& b ∨ L.get i=a ||| b
    ∀ (L : List ℕ), prog B L → ∀ w∈B++L, w &&& 2097144 = 2097144 ∧ w &&& 193072008452374528 = 0 → w ||| 7 = 2097151)
    (rectangles : let T := ℕ × ℕ
    let sat := fun (w : ℕ) (p : T) => w &&& p.1 = p.1 ∧ w &&& p.2 = 0
    let sub := fun (p q : T) => p.1 &&& q.1 = p.1 ∧ p.2 &&& q.2 = p.2
    let mix := fun (u v : T) (t : Bool) => if t then (u.1 &&& v.1,u.2 ||| v.2) else (u.1 ||| v.1,u.2 &&& v.2)
    let ok := fun (A : List ℕ) (D : List T) => ∀ p∈D, ∃ x∈A, sat x p
    let step := fun (E D : List T) => ∃ u∈E, ∃ v∈E, ∃ t : Bool, ∀ p∈D, ∃ q∈mix u v t :: E, sub p q
    let B : List ℕ := [63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752,191866593364673099,193001360500003407]
    ∃ D : ℕ → List T, ok B (D 0) ∧ (∀ i<22, step (D i) (D (i+1))) ∧ (2097144,193072008452374528)∈D 22) :
have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)] ++ [(191866593364673099 : ℕ), (193001360500003407 : ℕ), (7 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (22 : ℕ) ∧ (∃ x3 ∈ x1 ++ x2, x3 ||| (7 : ℕ) = (2097151 : ℕ)) ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  let B : List Nat := [63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752,191866593364673099,193001360500003407]
  let A : List Nat := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752,191866593364673099,193001360500003407,7]
  obtain ⟨D,start,steps,target⟩ := rectangles
  obtain ⟨L,len,bl,ok⟩ := assemble B D 22 start steps
  obtain ⟨w,hw,good⟩ := ok _ target
  have base : ∀ v∈B, v∈A := by decide
  have grow (T : List Nat) : B++T ⊆ A++T := by
    intro v hv
    exact (List.mem_append.mp hv).elim (fun h => List.mem_append_left _ (base _ h)) (List.mem_append_right _)
  refine ⟨L,len.le,⟨w,grow _ hw,rows L bl w hw good⟩,?_⟩
  intro i
  obtain ⟨a,ha,b,hb,h⟩ := bl i
  exact ⟨a,grow _ ha,b,grow _ hb,h⟩
