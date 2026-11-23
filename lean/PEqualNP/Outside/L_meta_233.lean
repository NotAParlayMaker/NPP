import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_233_aux
open MetaComplexity
private abbrev Input := Fin 3 → Bool
private def amo (x : Input) := decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)
private def typing (x y : Input) : ℕ :=
  if !x 1 && !x 2 then (if y 1 then 1 else 2)
  else if y 0 then 0 else if x 1 then 2 else 1

private def width (i : Fin 3) (b : Bool) := if b then 0 else if i=0 then 1 else 2

-- Each negative literal is used on one or two rectangles of positive/negative pairs.
private def left (i : Fin 3) (k : ℕ) (x : Input) : Bool :=
  amo x && (if i=0 then x 1 || x 2 else if k=0 then !x 1 && !x 2
    else (x 1 || x 2) && !x i)
private def right (i : Fin 3) (k : ℕ) (y : Input) : Bool :=
  !amo y && (if i=0 then y 0 else if k=0 then (if i=1 then y 1 else !y 1) else !y 0)
private def L (i : Fin 3) (b : Bool) : Matrix Input (Fin (width i b)) ℚ :=
  fun x k => if left i k x then 1 else 0
private def R (i : Fin 3) (b : Bool) : Matrix (Fin (width i b)) Input ℚ :=
  fun k y => if right i k y then 1 else 0

set_option maxRecDepth 8000 in
private theorem factored : ∀ i b x y, typedMatrix 3 amo typing i b x y = (L i b * R i b) x y := by
  intro i b x y
  have tab : ∀ (j : Fin 3) (s : Bool) (u v : Input),
      (if amo u=true ∧ amo v=false ∧ typing u v = j.val ∧ u j=s then 1 else 0 : ℕ) =
      ∑ k : Fin (width j s), (if left j k u then 1 else 0 : ℕ)*(if right j k v then 1 else 0 : ℕ) := by decide
  have h := congrArg (fun t : ℕ => (t : ℚ)) (tab i b x y)
  simpa [typedMatrix,Matrix.mul_apply,L,R,Nat.cast_ite] using h

theorem upper : HasTypedRank 3 amo 5 := by
  refine ⟨typing,?_,?_⟩
  · unfold IsTyping
    decide
  · have hr (i : Fin 3) (b : Bool) : (typedMatrix 3 amo typing i b).rank ≤ width i b := by
      have eq : typedMatrix 3 amo typing i b = L i b * R i b := Matrix.ext (factored i b)
      rw [eq]
      exact (Matrix.rank_mul_le_right _ _).trans (by simpa using (Matrix.rank_le_card_height (R i b)))
    calc
      _ ≤ ∑ i, ∑ b, width i b := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hr i b
      _ = 5 := by decide

end PEqualNP.Outside.L_meta_233_aux

theorem PEqualNP.Outside.L_meta_233 : PEqualNP.MetaComplexity.HasTypedRank 3
    (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 5 :=
  PEqualNP.Outside.L_meta_233_aux.upper
