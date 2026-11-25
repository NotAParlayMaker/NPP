import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_8978
import PEqualNP.Outside.L_meta_8980
import PEqualNP.Outside.L_meta_8981
import PEqualNP.Outside.L_meta_8982
import PEqualNP.Outside.L_meta_9018
import PEqualNP.Outside.L_meta_9020

namespace PEqualNP.Outside.L_meta_9021

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def bitsOf {k l : ℕ} (u : Fin (2 ^ k)) (v : Fin (2 ^ l)) (t : Fin (k + l)) : Bool :=
  if t.val < k then (u : ℕ).testBit t.val else (v : ℕ).testBit (t.val - k)

theorem adj_bits {k l : ℕ} (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool) (u : Fin (2 ^ k))
    (v : Fin (2 ^ l)) : adjFun A (bitsOf u v) = A u v := by
  unfold adjFun
  have h1 : (fun i : Fin k => bitsOf u v (Fin.castAdd l i)) = fun i : Fin k => (u : ℕ).testBit i := by
    funext i
    simp [bitsOf, i.isLt]
  have h2 : (fun j : Fin l => bitsOf u v (Fin.natAdd k j)) = fun j : Fin l => (v : ℕ).testBit j := by
    funext j
    simp [bitsOf]
  rw [h1, h2, PEqualNP.Outside.L_meta_8978 k u, PEqualNP.Outside.L_meta_8978 l v]
  congr 1
  · ext
    simp
  · ext
    simp

theorem main_proof (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (h : HasCircuitSize (k + l) (adjFun A) s) :
    RepSizeAtMost A (2 * s + 3 * 2 ^ k + 3 * 2 ^ l) := by
  obtain ⟨C, hCm, hCs, hCe⟩ := PEqualNP.Outside.L_meta_9020 (k + l) s (adjFun A) h
  obtain ⟨P, hPm, hPl, w1, hw1⟩ := PEqualNP.Outside.L_meta_8980 k (2 ^ l)
  obtain ⟨Q, hQm, hQl, w2, hw2⟩ := PEqualNP.Outside.L_meta_8981 (2 ^ k) l
  let D : Set (List Bool) := {x | ∃ (u : Fin (2 ^ k)) (v : Fin (2 ^ l)), x = oneEach u v}
  have hD : ∀ x ∈ D, x.length = 2 ^ k + 2 ^ l := by
    rintro x ⟨u, v, rfl⟩
    simp [oneEach]
  let W1 : Fin (k + k) → ℕ := fun j =>
    if hj : j.val < k then w1 ⟨j.val, hj⟩ true else w1 ⟨j.val - k, by omega⟩ false
  let W2 : Fin (l + l) → ℕ := fun j =>
    if hj : j.val < l then w2 ⟨j.val, hj⟩ true else w2 ⟨j.val - l, by omega⟩ false
  let F1 : Fin (k + k) → List Bool → Bool := fun j x =>
    ((⟨P, 0⟩ : Circuit).wires x).getD (W1 j) false
  let F2 : Fin (l + l) → List Bool → Bool := fun j x =>
    ((⟨Q, 0⟩ : Circuit).wires x).getD (W2 j) false
  obtain ⟨R, hRm, hRl, v1, v2, hR⟩ := PEqualNP.Outside.L_meta_8982 (2 ^ k + 2 ^ l) (k + k) (l + l)
    D P Q W1 W2 F1 F2 hD hPm hQm (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  let W : Fin ((k + l) + (k + l)) → ℕ := fun t =>
    if ht : t.val < k + l then
      (if h' : t.val < k then v1 ⟨t.val, by omega⟩ else v2 ⟨t.val - k, by omega⟩)
    else
      (if h' : t.val - (k + l) < k then v1 ⟨k + (t.val - (k + l)), by omega⟩
        else v2 ⟨l + (t.val - (k + l) - k), by omega⟩)
  let G : Fin ((k + l) + (k + l)) → List Bool → Bool := fun t x =>
    ((⟨R, 0⟩ : Circuit).wires x).getD (W t) false
  obtain ⟨C', hC'm, hC's, hC'e⟩ := PEqualNP.Outside.L_meta_9018 (2 ^ k + 2 ^ l) ((k + l) + (k + l))
    D R W G C hD hRm hCm (fun _ _ _ => rfl)
  refine ⟨C', hC'm, ?_, ?_⟩
  · have hsz : C'.size ≤ R.length + C.size := hC's
    omega
  · intro u v
    have hx : oneEach u v ∈ D := ⟨u, v, rfl⟩
    rw [hC'e _ hx]
    have hpos : ∀ i : Fin (k + l), G (Fin.castAdd (k + l) i) (oneEach u v) = bitsOf u v i := by
      intro i
      by_cases hi : i.val < k
      · have e1 : W (Fin.castAdd (k + l) i) = v1 ⟨i.val, by omega⟩ := by
          simp [W, hi]
        have e2 := (hR _ hx).1 ⟨i.val, by omega⟩
        have e3 : W1 ⟨i.val, by omega⟩ = w1 ⟨i.val, hi⟩ true := by
          simp [W1, hi]
        simp only [G, e1, e2, F1, e3, hw1 u v ⟨i.val, hi⟩ true, bitsOf, hi]
        simp
      · have e1 : W (Fin.castAdd (k + l) i) = v2 ⟨i.val - k, by omega⟩ := by
          simp [W, hi]
        have e2 := (hR _ hx).2 ⟨i.val - k, by omega⟩
        have hi2 : i.val - k < l := by omega
        have e3 : W2 ⟨i.val - k, by omega⟩ = w2 ⟨i.val - k, hi2⟩ true := by
          simp [W2, hi2]
        simp only [G, e1, e2, F2, e3, hw2 u v ⟨i.val - k, hi2⟩ true, bitsOf, hi]
        simp
    have hneg : ∀ i : Fin (k + l), G (Fin.natAdd (k + l) i) (oneEach u v) = !bitsOf u v i := by
      intro i
      by_cases hi : i.val < k
      · have e1 : W (Fin.natAdd (k + l) i) = v1 ⟨k + i.val, by omega⟩ := by
          simp [W, hi]
        have e2 := (hR _ hx).1 ⟨k + i.val, by omega⟩
        have e3 : W1 ⟨k + i.val, by omega⟩ = w1 ⟨i.val, hi⟩ false := by
          simp [W1]
        simp only [G, e1, e2, F1, e3, hw1 u v ⟨i.val, hi⟩ false, bitsOf, hi]
        simp
      · have e1 : W (Fin.natAdd (k + l) i) = v2 ⟨l + (i.val - k), by omega⟩ := by
          simp [W, hi]
        have e2 := (hR _ hx).2 ⟨l + (i.val - k), by omega⟩
        have hi2 : i.val - k < l := by omega
        have e3 : W2 ⟨l + (i.val - k), by omega⟩ = w2 ⟨i.val - k, hi2⟩ false := by
          simp [W2]
        simp only [G, e1, e2, F2, e3, hw2 u v ⟨i.val - k, hi2⟩ false, bitsOf, hi]
        simp
    have hlist : (List.ofFn fun j => G j (oneEach u v)) =
        List.ofFn (bitsOf u v) ++ List.ofFn fun i => !bitsOf u v i := by
      rw [List.ofFn_add]
      congr 1
      · congr 1
        funext i
        exact hpos i
      · congr 1
        funext i
        exact hneg i
    rw [hlist, hCe, adj_bits]

end PEqualNP.Outside.L_meta_9021

theorem PEqualNP.Outside.L_meta_9021 : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 3 * 2 ^ k + 3 * 2 ^ l) :=
  fun k l s A h => PEqualNP.Outside.L_meta_9021.main_proof k l s A h
