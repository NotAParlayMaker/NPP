import Mathlib.Tactic
import PEqualNP.Defs

-- In the edge list, 9a + b represents the edge from a to b.
-- The first hypothesis gives a binary gate lower bound with unrestricted input signs.
-- The second uses only 23 wires and reads its output at the last gate.
theorem PEqualNP.Outside.R_meta_3618_1
  (lower : ∀ (n : ℕ) (op : Fin n → Bool) (a b : Fin n → ℕ × Bool) (o : ℕ)
      (v : (Fin 9 → Bool) → ℕ → Bool),
    (∀ j, (a j).1 < 10 + j.val ∧ (b j).1 < 10 + j.val) → o < 10 + n →
    (∀ x (i : Fin 9), v x i.val = x i) → (∀ x, v x 9 = false) →
    (∀ x j, let read := fun (p : ℕ × Bool) => v x p.1 ^^ p.2
            v x (10 + j.val) = if op j then read (a j) && read (b j)
                                         else read (a j) || read (b j)) →
    (∀ x, v x o = ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) → 13 ≤ n)
  (core : ∀ (extra : Fin 22) (op : Fin 13 → Bool) (a b : Fin 13 → Fin 22 × Bool)
      (v : (Fin 9 → Bool) → Fin 23 → Bool),
    (∀ j, (a j).1.val < 10 + j.val ∧ (b j).1.val < 10 + j.val) →
    (∀ j, ∀ p ∈ [a j, b j], p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 = extra) →
    (∀ x (i : Fin 9), v x (Fin.ofNat 23 i.val) = x i) → (∀ x, v x 9 = false) →
    (∀ x j, let read := fun (p : Fin 22 × Bool) => v x p.1.castSucc ^^ p.2
            v x (Fin.ofNat 23 (10 + j.val)) =
                if op j then read (a j) && read (b j) else read (a j) || read (b j)) →
    ∃ x, v x 22 ≠ ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) :
  ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (∀ (x7 : Fin x1), (x3 x7).1 < (10 : ℕ) + ↑x7 ∧ (x4 x7).1 < (10 : ℕ) + ↑x7) →     x5.1 < (10 : ℕ) + x1 →       x5.2 = Bool.false →         ∀ (x10 : Finset ℕ),           x10.Nonempty →             x10.card ≤ (3 : ℕ) →               x1 + x10.card ≤ (14 : ℕ) →                 (have x14 : ℕ × Bool → Prop := fun (x14 : ℕ × Bool) => x14.2 = Bool.true → x14.1 = (0 : ℕ) ∨ x14.1 = (9 : ℕ) ∨ x14.1 ∈ x10;                   x14 x5 ∧ ∀ (x15 : Fin x1), x14 (x3 x15) ∧ x14 (x4 x15)) →                   (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x6 x15 ↑x16 = x15 x16) →                     (∀ (x16 : Fin (9 : ℕ) → Bool), x6 x16 (9 : ℕ) = Bool.false) →                       (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                           have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x6 x17 x19.1 ^^ x19.2;                           x6 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                         (∀ (x18 : Fin (9 : ℕ) → Bool), (x6 x18 x5.1 ^^ x5.2) = (x18 (0 : Fin (9 : ℕ)) && x18 (1 : Fin (9 : ℕ)) || x18 (1 : Fin (9 : ℕ)) && x18 (2 : Fin (9 : ℕ)) || x18 (2 : Fin (9 : ℕ)) && x18 (3 : Fin (9 : ℕ)) || x18 (3 : Fin (9 : ℕ)) && x18 (4 : Fin (9 : ℕ)) || x18 (4 : Fin (9 : ℕ)) && x18 (0 : Fin (9 : ℕ)) || x18 (0 : Fin (9 : ℕ)) && x18 (5 : Fin (9 : ℕ)) || x18 (1 : Fin (9 : ℕ)) && x18 (6 : Fin (9 : ℕ)) || x18 (2 : Fin (9 : ℕ)) && x18 (7 : Fin (9 : ℕ)) || x18 (3 : Fin (9 : ℕ)) && x18 (8 : Fin (9 : ℕ)) || x18 (5 : Fin (9 : ℕ)) && x18 (7 : Fin (9 : ℕ)) || x18 (6 : Fin (9 : ℕ)) && x18 (8 : Fin (9 : ℕ)) || x18 (8 : Fin (9 : ℕ)) && x18 (5 : Fin (9 : ℕ)))) → False := by
  intro n op a b out val hreads hout hsign S hne _hcard hcost hsigns hin hc hgate houtput
  have encodedEdges :
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)) =
      ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).map
          (fun e => (Fin.ofNat 9 (e / 9), Fin.ofNat 9 (e % 9))) := by decide
  have same (x : Fin 9 → Bool) : ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) =
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by
    rw [encodedEdges, List.any_map] <;> rfl

  have agrees (x : Fin 9 → Bool) : val x out.1 = ([1, 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) := by
    simpa only [same, hsign, Bool.xor_false, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_assoc] using houtput x
  have lo := lower n op a b out.1 val hreads hout hin hc (fun x j => hgate x j) agrees
  have pos := Finset.card_pos.mpr hne
  have size : n = 13 := by omega
  subst n
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
  have lastWire : out.1 = 22 := by
    by_contra h
    have short : out.1 < 10 + 12 := by omega
    have impossible := lower 12 (fun j => op j.castSucc) (fun j => a j.castSucc)
      (fun j => b j.castSucc) out.1 val (fun j => hreads j.castSucc) short hin hc
      (fun x j => hgate x j.castSucc) agrees
    omega
  have bound {j : Fin 13} {p : ℕ × Bool} (h : p.1 < 10 + j.val) : p.1 < 22 := by
    have := j.isLt
    omega
  let pack (p : ℕ × Bool) (h : p.1 < 22) : Fin 22 × Bool := (⟨p.1, h⟩, p.2)
  let a' (j : Fin 13) := pack (a j) (bound (hreads j).1)
  let b' (j : Fin 13) := pack (b j) (bound (hreads j).2)
  let v (x : Fin 9 → Bool) (i : Fin 23) := val x i.val
  have signs (p : ℕ × Bool) (lt : p.1 < 22)
      (allowed : p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ ({c} : Finset ℕ))
      (neg : p.2 = true) :
      (pack p lt).1 = 0 ∨ (pack p lt).1 = 9 ∨ (pack p lt).1 = Fin.ofNat 22 c := by
    rcases allowed neg with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · have eq := Finset.mem_singleton.mp h
      apply Or.inr ∘ Or.inr
      apply Fin.ext
      change p.1 = c % 22
      rw [← eq, Nat.mod_eq_of_lt lt]
  obtain ⟨x, bad⟩ := core (Fin.ofNat 22 c) op a' b' v hreads
    (by
      intro j p hp neg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact signs _ _ (hsigns.2 j).1 neg
      · exact signs _ _ (hsigns.2 j).2 neg)
    (by
      intro x i
      have h : i.val < 23 := by have := i.isLt; omega
      simpa only [v, Fin.val_ofNat, Nat.mod_eq_of_lt h] using hin x i)
    hc
    (by
      intro x j
      have h : 10 + j.val < 23 := by have := j.isLt; omega
      simpa only [v, Fin.val_ofNat, Nat.mod_eq_of_lt h, a', b', pack, Fin.val_castSucc]
        using hgate x j)
  have v22 : (22 : Fin 23).val = 22 := by decide
  exact bad (by simpa only [v, v22, lastWire] using agrees x)
