import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3326_1
    (lift : let op := fun (ws : List Nat) (x : Nat) => ∃ a∈ws, ∃ b∈ws, x=a &&& b ∨ x=a ||| b
    let valid := fun (base xs : List Nat) => ∀ i : Fin xs.length, op (base ++ xs.take i.val) (xs.get i)
    let down := fun x : Nat => x >>> 1
    ∀ raw xs : List Nat, valid (raw.map down) xs →
      ∃ ys : List Nat, ys.map down=xs ∧ valid raw ys)
    (synthesis : let raw : List Nat := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
    let op := fun (ws : List Nat) (x : Nat) => ∃ a∈ws, ∃ b∈ws, x=a &&& b ∨ x=a ||| b
    let valid := fun (base xs : List Nat) => ∀ i : Fin xs.length, op (base ++ xs.take i.val) (xs.get i)
    let down := fun x : Nat => x >>> 1
    ∃ s ∈ ([1, 95274182876594239, 284526031944024591, 241600541374316567] : List Nat), ∃ xs : List Nat,
      let base := if s=1 then raw.map down else s::raw
      xs.length≤24 ∧ valid base xs ∧
        (if s=1 then 1048575 ∈ base++xs else op (base++xs) 2097151)) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; have x2 : List ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 : ℕ) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = x4 &&& x5 ∨ x3 = x4 ||| x5; ∃ x3 ∈ [(17871361015808 : ℕ), (95274182876594239 : ℕ), (1 : ℕ), (284526031944024591 : ℕ), (72622777407897600 : ℕ), (241600541374316567 : ℕ)], ∃ (x4 : List ℕ), x4.length ≤ (24 : ℕ) ∧ (∀ (x5 : Fin x4.length), x2 (x3 :: x1 ++ List.take (↑x5) x4) (x4.get x5)) ∧ x2 (x3 :: x1 ++ x4) (2097151 : ℕ) := by
  let raw : List Nat := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let op := fun (ws : List Nat) (x : Nat) => ∃ a∈ws, ∃ b∈ws, x=a &&& b ∨ x=a ||| b
  let valid := fun (base xs : List Nat) => ∀ i : Fin xs.length, op (base ++ xs.take i.val) (xs.get i)
  let down := fun x : Nat => x >>> 1
  change ∀ a b : List Nat, valid (a.map down) b → ∃ ys : List Nat, ys.map down=b ∧ valid a ys at lift
  change ∃ s ∈ ([1, 95274182876594239, 284526031944024591, 241600541374316567] : List Nat), ∃ xs : List Nat,
    let base := if s=1 then raw.map down else s::raw
    xs.length≤24 ∧ valid base xs ∧ (if s=1 then 1048575 ∈ base++xs else op (base++xs) 2097151) at synthesis
  change ∃ s ∈ ([17871361015808, 95274182876594239, 1, 284526031944024591, 72622777407897600, 241600541374316567] : List Nat), ∃ xs : List Nat, xs.length≤24 ∧ valid (s::raw) xs ∧ op ((s::raw)++xs) 2097151
  obtain ⟨s,mem,xs,claim⟩ := synthesis
  have allowed : s ∈ ([17871361015808, 95274182876594239, 1, 284526031944024591, 72622777407897600, 241600541374316567] : List Nat) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem ⊢
    rcases mem with h|h|h|h <;> simp [h]
  by_cases unit : s=1
  · subst s
    simp only at claim
    obtain ⟨len,prev,out⟩ := claim
    obtain ⟨ys,eq,build⟩ := lift raw xs prev
    have size : ys.length=xs.length := by simpa using congrArg List.length eq
    have hit : 1048575 ∈ (raw++ys).map down := by simpa [List.map_append,eq] using out
    obtain ⟨w,hw,ew⟩ := List.mem_map.mp hit
    have half : w/2=1048575 := by simpa [down,Nat.shiftRight_eq_div_pow] using ew
    have last : 2097151=1 ||| w := by
      have alternatives : w=2097150 ∨ w=2097151 := by omega
      rcases alternatives with rfl|rfl <;> decide
    refine ⟨1,allowed,ys,by omega,?_,1,by simp,w,List.mem_cons_of_mem _ hw,Or.inr last⟩
    intro i
    obtain ⟨a,ha,b,hb,h⟩ := build i
    exact ⟨a,List.mem_cons_of_mem _ ha,b,List.mem_cons_of_mem _ hb,h⟩
  · simp only [ite_eq_right unit] at claim
    exact ⟨s,allowed,xs,claim⟩
