import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17487_aux

def F1 (x1 : List Bool) : Bool := (List.range (13 : ℕ)).any fun (x2 : ℕ) => x1.getD ((13 : ℕ) + x2) Bool.false && [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].any fun (x3 : ℕ) => x1.getD ((x3 + (13 : ℕ) - x2) % (13 : ℕ)) Bool.false

def F2 (x2 : List ℕ) : ℕ := List.foldl (fun (x3 x4 : ℕ) => x3 ||| x4) (0 : ℕ) (List.map (fun (x3 : ℕ) => x2.getD ((13 : ℕ) + x3) (0 : ℕ) &&& List.foldl (fun (x4 x5 : ℕ) => x4 ||| x5) (0 : ℕ) (List.map (fun (x4 : ℕ) => x2.getD ((x4 + (13 : ℕ) - x3) % (13 : ℕ)) (0 : ℕ)) [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) (List.range (13 : ℕ)))

def V (x3 : List (Bool × List Bool)) : List ℕ := List.ofFn fun (x5 : Fin (26 : ℕ)) => List.foldr Nat.bit (0 : ℕ) (List.map (fun (x6 : Bool × List Bool) => x6.2.getD (↑x5) Bool.false) x3)

theorem foldl_or (g : ℕ → Bool) (h F : ℕ → ℕ) (l : List ℕ) (hF : ∀ k ∈ l, F k = Nat.bit (g k) (h k)) (b : Bool) (n : ℕ) :
    List.foldl (fun x y : ℕ => x ||| y) (Nat.bit b n) (l.map F) = Nat.bit (b || l.any g) (List.foldl (fun x y : ℕ => x ||| y) n (l.map h)) := by
  induction l generalizing b n with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldl_cons, List.any_cons]
    rw [hF a (by simp), Nat.lor_bit, ih (fun k hk => hF k (by simp [hk]))]
    simp [Bool.or_assoc]

theorem foldl_or0 (g : ℕ → Bool) (h F : ℕ → ℕ) (l : List ℕ) (hF : ∀ k ∈ l, F k = Nat.bit (g k) (h k)) :
    List.foldl (fun x y : ℕ => x ||| y) 0 (l.map F) = Nat.bit (l.any g) (List.foldl (fun x y : ℕ => x ||| y) 0 (l.map h)) := by
  have := foldl_or g h F l hF false 0
  rwa [Nat.bit_false_zero, Bool.false_or] at this

theorem step (B : List Bool) (M N : List ℕ) (hN : ∀ j < 26, N.getD j 0 = Nat.bit (B.getD j false) (M.getD j 0)) :
    F2 N = Nat.bit (F1 B) (F2 M) := by
  unfold F2 F1
  rw [foldl_or0 (g := fun x3 => B.getD (13 + x3) false && [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].any fun x4 => B.getD ((x4 + 13 - x3) % 13) false)
    (h := fun x3 => M.getD (13 + x3) 0 &&& List.foldl (fun x y : ℕ => x ||| y) 0 (List.map (fun x4 => M.getD ((x4 + 13 - x3) % 13) 0) [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]))]
  intro k hk
  have hk' : k < 13 := List.mem_range.mp hk
  rw [hN _ (by omega), foldl_or0 (g := fun x4 => B.getD ((x4 + 13 - k) % 13) false) (h := fun x4 => M.getD ((x4 + 13 - k) % 13) 0), Nat.land_bit]
  intro j hj
  exact hN _ (by have := Nat.mod_lt (j + 13 - k) (show 13 > 0 by norm_num); omega)

theorem main (x3 : List (Bool × List Bool)) (h : ∀ x4 ∈ x3, x4.1 = F1 x4.2) :
    F2 (V x3) = List.foldr Nat.bit 0 (List.map Prod.fst x3) := by
  induction x3 with
  | nil => decide
  | cons s t ih =>
    rw [List.map_cons, List.foldr_cons, ← ih (fun x hx => h x (by simp [hx])), h s (by simp)]
    apply step
    intro j hj
    simp only [V, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_eq_left, Option.getD_some, List.map_cons, List.foldr_cons]

end PEqualNP.Outside.L_meta_17487_aux

theorem PEqualNP.Outside.L_meta_17487 : have x1 : List Bool → Bool := fun (x1 : List Bool) => (List.range (13 : ℕ)).any fun (x2 : ℕ) => x1.getD ((13 : ℕ) + x2) Bool.false && [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].any fun (x3 : ℕ) => x1.getD ((x3 + (13 : ℕ) - x2) % (13 : ℕ)) Bool.false; have x2 : List ℕ → ℕ := fun (x2 : List ℕ) => List.foldl (fun (x3 x4 : ℕ) => x3 ||| x4) (0 : ℕ) (List.map (fun (x3 : ℕ) => x2.getD ((13 : ℕ) + x3) (0 : ℕ) &&& List.foldl (fun (x4 x5 : ℕ) => x4 ||| x5) (0 : ℕ) (List.map (fun (x4 : ℕ) => x2.getD ((x4 + (13 : ℕ) - x3) % (13 : ℕ)) (0 : ℕ)) [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) (List.range (13 : ℕ))); ∀ (x3 : List (Bool × List Bool)),   (∀ x4 ∈ x3, x4.1 = x1 x4.2) →     have x5 : List ℕ := List.ofFn fun (x5 : Fin (26 : ℕ)) => List.foldr Nat.bit (0 : ℕ) (List.map (fun (x6 : Bool × List Bool) => x6.2.getD (↑x5) Bool.false) x3);     x2 x5 = List.foldr Nat.bit (0 : ℕ) (List.map Prod.fst x3) := by
  intro x1 x2 x3 h
  exact PEqualNP.Outside.L_meta_17487_aux.main x3 h
