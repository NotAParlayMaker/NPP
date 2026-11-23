import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

private theorem ladder_run (n d : ℕ) (P : Finset ℕ) (hn : 0 < n) (hd : 0 < d)
    (hP : P.card + 1 ≤ d) :
    ∃ u v : ℕ, u ≤ v ∧ v < n ∧ (∀ w ∈ P, ¬ (u < w ∧ w ≤ v)) ∧
      (n + d - 1) / d - 1 ≤ v - u := by
  classical
  let k := (n - 1) / d
  have hwidth : (n + d - 1) / d - 1 = k := by
    rw [show n + d - 1 = n - 1 + d by omega, Nat.add_div_right _ hd]
    simp [k]
  have hend : d * k < n := by
    have h := Nat.div_mul_le_self (n - 1) d
    change d * ((n - 1) / d) < n
    rw [Nat.mul_comm]
    omega
  have clear_interval :
      ∃ i : Fin d, ∀ w ∈ P, ¬ (i.val * k < w ∧ w ≤ (i.val + 1) * k) := by
    by_contra h
    have blocked (i : Fin d) :
        ∃ w ∈ P, i.val * k < w ∧ w ≤ (i.val + 1) * k := by
      by_contra hnone
      exact h ⟨i, fun w hw hbounds => hnone ⟨w, hw, hbounds⟩⟩
    choose f hfmem hlo hhi using blocked
    let g (i : Fin d) : ↥P := ⟨f i, hfmem i⟩
    have hmono : StrictMono f := by
      intro i j hij
      calc
        f i ≤ (i.val + 1) * k := hhi i
        _ ≤ j.val * k := Nat.mul_le_mul_right k (show i.val + 1 ≤ j.val from hij)
        _ < f j := hlo j
    have hinj : Function.Injective g := by
      intro i j heq
      exact hmono.injective (congrArg Subtype.val heq)
    have hcard : d ≤ P.card := by
      simpa using Fintype.card_le_of_injective g hinj
    omega
  obtain ⟨i, hi⟩ := clear_interval
  refine ⟨i.val * k, (i.val + 1) * k, ?_, ?_, hi, ?_⟩
  · exact Nat.mul_le_mul_right k (Nat.le_succ _)
  · exact lt_of_le_of_lt (Nat.mul_le_mul_right k i.isLt) hend
  · rw [hwidth, Nat.add_mul, Nat.one_mul]
    omega

private theorem ladderPowSplit1349 (h a : ℕ) (ha : a ≤ h) :
    (2 : ℕ) ^ h = 2 ^ (h - a) * 2 ^ a := by
  rw [← Nat.pow_add, Nat.sub_add_cancel ha]

private theorem ladderQuotient1349 (h a : ℕ) (ha : a ≤ h) :
    2 ^ h * (2 ^ h + 1) / 2 ^ a = 2 ^ (h - a) * (2 ^ h + 1) := by
  have product : (2 : ℕ) ^ h * (2 ^ h + 1) =
      (2 ^ (h - a) * (2 ^ h + 1)) * 2 ^ a := by
    calc
      _ = (2 ^ (h - a) * 2 ^ a) * (2 ^ h + 1) :=
        congrArg (fun n : ℕ => n * (2 ^ h + 1)) (ladderPowSplit1349 h a ha)
      _ = _ := by grind only
  rw [product, Nat.mul_div_cancel _ (by exact Nat.two_pow_pos _ : 0 < (2 : ℕ) ^ a)]

theorem ladderCost1349 (h u v : ℕ) (hh : 1 ≤ h) (huv : u ≤ v) (hv : v ≤ h + 2) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (v - u - 1) - 1) ≤
      ((if u = 0 then 2 ^ h * 2 ^ h + 2 ^ h + 1 else if u = h + 2 then 0
        else 2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h) -
       (if v = 0 then 2 ^ h * 2 ^ h + 2 ^ h + 1 else if v = h + 2 then 0
        else 2 ^ h * (2 ^ h + 1) / 2 ^ (v - 1) - 2 ^ h)) *
        (if v = h + 2 then 2 ^ h else 2 ^ (v - 1) - 1) := by
  let q : ℕ := 2 ^ h
  have qPos : 0 < q := Nat.two_pow_pos h
  let F (j : ℕ) : ℕ := if j = 0 then q * q + q + 1 else if j = h + 2 then 0
    else q * (q + 1) / 2 ^ (j - 1) - q
  change q * q / 2 * (2 ^ (v - u - 1) - 1) ≤
    (F u - F v) * (if v = h + 2 then q else 2 ^ (v - 1) - 1)
  by_cases small : v - u ≤ 1
  · have e : v - u - 1 = 0 := by omega
    simp [e]
  have huEnd : u ≠ h + 2 := by omega
  have ha : u - 1 ≤ h := by omega
  let A : ℕ := 2 ^ (h - (u - 1))
  have levelLower : A * (q + 1) ≤ F u + q := by
    by_cases hu0 : u = 0
    · subst u
      simp [F, A, q, Nat.mul_add]
      omega
    · have e : F u = A * (q + 1) - q := by
        simp only [F, ite_eq_right hu0, ite_eq_right huEnd]
        rw [show q * (q + 1) / 2 ^ (u - 1) = A * (q + 1) from
          ladderQuotient1349 h (u - 1) ha]
      rw [e]
      omega
  by_cases hvEnd : v = h + 2
  · subst v
    have fEnd : F (h + 2) = 0 := by simp [F]
    rw [fEnd, Nat.sub_zero, ite_eq_left rfl]
    by_cases hu0 : u = 0
    · subst u
      have e : h + 2 - 0 - 1 = h + 1 := by omega
      have z : F 0 = q * q + q + 1 := by simp [F]
      rw [e, Nat.pow_succ, z]
      change q * q / 2 * (q * 2 - 1) ≤ (q * q + q + 1) * q
      calc
        _ ≤ q * q / 2 * (q * 2) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = (q * q / 2 * 2) * q := by grind only
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · have e : h + 2 - u - 1 = h - (u - 1) := by omega
      rw [e]
      change q * q / 2 * (A - 1) ≤ F u * q
      have aPos : 0 < A := by dsimp [A]; exact Nat.two_pow_pos _
      have aSplit : A - 1 + 1 = A := by omega
      have recA : q * (A - 1) + q = q * A := by
        calc
          _ = q * (A - 1 + 1) := by grind only
          _ = _ := by rw [aSplit]
      have qa : q * A ≤ A * (q + 1) := by grind only
      have cost : q * (A - 1) ≤ F u := by omega
      calc
        _ ≤ q * q * (A - 1) := Nat.mul_le_mul_right _ (by omega)
        _ = (q * (A - 1)) * q := by grind only
        _ ≤ _ := Nat.mul_le_mul_right _ cost
  · let a := u - 1
    let b := v - 1
    let X : ℕ := 2 ^ (h - b)
    let B : ℕ := 2 ^ b
    let D : ℕ := 2 ^ (b - a)
    have hb : b ≤ h := by dsimp [b]; omega
    have ab : a ≤ b := by dsimp [a, b]; omega
    have hv0 : v ≠ 0 := by omega
    have levelV : F v = X * (q + 1) - q := by
      simp only [F, ite_eq_right hv0, ite_eq_right hvEnd]
      rw [show q * (q + 1) / 2 ^ (v - 1) = X * (q + 1) from ladderQuotient1349 h b hb]
    have xPos : 1 ≤ X := by dsimp [X]; exact Nat.two_pow_pos _
    have xGe := Nat.mul_le_mul_right (q + 1) xPos
    rw [Nat.one_mul] at xGe
    have levelVExact : F v + q = X * (q + 1) := by rw [levelV]; omega
    have aFactor : A = X * D := by
      change (2 : ℕ) ^ (h - a) = 2 ^ (h - b) * 2 ^ (b - a)
      rw [← Nat.pow_add]
      congr 1
      omega
    have dPos : 0 < D := by dsimp [D]; exact Nat.two_pow_pos _
    have dSplit : D - 1 + 1 = D := by omega
    have recD : X * (D - 1) * (q + 1) + X * (q + 1) = A * (q + 1) := by
      calc
        _ = X * (D - 1 + 1) * (q + 1) := by grind only
        _ = _ := by rw [dSplit, aFactor]
    have delta : X * (D - 1) * (q + 1) ≤ F u - F v := by omega
    have xFactor : X * B = q := (ladderPowSplit1349 h b hb).symm
    have bLarge : 2 ≤ B := by
      have e : b = (b - 1) + 1 := by dsimp [b]; omega
      change 2 ≤ (2 : ℕ) ^ b
      rw [e, Nat.pow_succ]
      have pos : 0 < (2 : ℕ) ^ (b - 1) := by exact Nat.two_pow_pos _
      omega
    have bSplit : B - 1 + 1 = B := by omega
    have recB : X * (B - 1) + X = q := by
      calc
        _ = X * (B - 1 + 1) := by grind only
        _ = _ := by rw [bSplit, xFactor]
    have xLe := Nat.mul_le_mul_left X (show 1 ≤ B - 1 by omega)
    rw [Nat.mul_one] at xLe
    have qBound : q ≤ (X * (B - 1)) * 2 := by omega
    have squareBound : q * q / 2 ≤ X * (B - 1) * (q + 1) := by
      have e := Nat.mul_le_mul_right q qBound
      have f : X * (B - 1) * 2 * q = (X * (B - 1) * q) * 2 := by grind only
      rw [f] at e
      have g : X * (B - 1) * (q + 1) = X * (B - 1) * q + X * (B - 1) := by grind only
      omega
    have expLe : v - u - 1 ≤ b - a := by dsimp [a, b]; omega
    have powLe : (2 : ℕ) ^ (v - u - 1) ≤ D := Nat.pow_le_pow_right (by decide) expLe
    rw [ite_eq_right hvEnd]
    change q * q / 2 * (2 ^ (v - u - 1) - 1) ≤ (F u - F v) * (B - 1)
    calc
      _ ≤ q * q / 2 * (D - 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (X * (B - 1) * (q + 1)) * (D - 1) := Nat.mul_le_mul_right _ squareBound
      _ = (X * (D - 1) * (q + 1)) * (B - 1) := by grind only
      _ ≤ _ := Nat.mul_le_mul_right _ delta

end PEqualNP.Outside.L_meta_1349

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  classical
  intro h t hh
  let n := h + 3
  let d := 2 ^ t
  let q := 2 ^ h
  let level (i : ℕ) : ℕ :=
    if i = 0 then q * q + q + 1 else if i = h + 2 then 0
    else q * (q + 1) / 2 ^ (i - 1) - q
  let cost (uv : ℕ × ℕ) : ℕ :=
    (level uv.1 - level uv.2) * (if uv.2 = h + 2 then q else 2 ^ (uv.2 - 1) - 1)
  let feasible := (Finset.range n).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ d)
  let runs (P : Finset ℕ) := (Finset.range n ×ˢ Finset.range n).filter
    (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))
  let score (P : Finset ℕ) := (runs P).sup cost
  change (q * q / 2) * (2 ^ ((n + d - 1) / d - 1 - 1) - 1) ≤
    WithTop.untopD 0 (feasible.image score).min
  have hd : 0 < d := Nat.pow_pos (by decide)
  have emptyFeasible : ∅ ∈ feasible :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by
      simp only [Finset.card_empty, Nat.zero_add]
      omega⟩
  obtain ⟨s, hs⟩ := Finset.min_of_mem (Finset.mem_image_of_mem score emptyFeasible)
  rw [hs]
  change _ ≤ s
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_min hs)
  obtain ⟨u, v, huv, hv, hcut, hwidth⟩ :=
    PEqualNP.Outside.L_meta_1349.ladder_run n d P (by dsimp [n]; omega) hd
      (Finset.mem_filter.mp hP).2
  have hmem : (u, v) ∈ runs P := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt huv hv),
      Finset.mem_range.mpr hv⟩, huv, hcut⟩
  calc
    _ ≤ (q * q / 2) * (2 ^ (v - u - 1) - 1) := by
      apply Nat.mul_le_mul_left
      apply Nat.sub_le_sub_right
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hwidth 1)
    _ ≤ cost (u, v) :=
      PEqualNP.Outside.L_meta_1349.ladderCost1349 h u v hh huv (by dsimp [n] at hv; omega)
    _ ≤ score P := Finset.le_sup (f := cost) hmem
