import Mathlib
import PEqualNP.Defs
-- The chart argument follows Gct.Helpers.LevelThree. The hyperbolic basis
-- and the finite cubic obstructions are computed over the field of five elements.
namespace PEqualNP.Outside.L_gct_226_aux
open Finset
abbrev K := ZMod 5
abbrev E := Fin 4 × Bool → K
abbrev M := Fin 3 × Fin 3 → K
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
theorem permanent_three (A : Matrix (Fin 3) (Fin 3) K) :
    A.permanent = A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 1 2 * A 2 1 + A 0 1 * A 1 0 * A 2 2 +
      A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 + A 0 2 * A 1 1 * A 2 0 := by
  have hu : (univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide
  unfold Matrix.permanent
  rw [hu, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [Fin.prod_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Equiv.Perm.one_apply]
  simp
  ring


def fm (x : E) (p : Fin 3 × Fin 3) : K := (![![-x (1, true) + (-2) * x (2, true) + 2 * x (3, false) + 2 * x (3, true), -x (0, true) + -x (2, false) + -x (2, true) + (-2) * x (3, false) + x (3, true), (-2) * x (2, true) + x (3, false) + -x (3, true)], ![x (3, false) + -x (3, true), x (2, false) + -x (2, true), 2 * x (3, false) + 2 * x (3, true)], ![x (1, false) + x (1, true) + x (2, false) + -x (2, true) + 2 * x (3, false) + 2 * x (3, true), x (0, false) + x (0, true) + 2 * x (1, true) + (-2) * x (3, false) + x (3, true), -x (0, false) + -x (1, false) + (-2) * x (1, true) + -x (2, false) + 2 * x (2, true) + x (3, false) + -x (3, true)]]) p.1 p.2

def fmap : E →ₗ[K] M where
  toFun := fm
  map_add' x y := by
    funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> simp [fm] <;> ring
  map_smul' a x := by
    funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> simp [fm] <;> ring

def pm (t : M) := Matrix.permanent (Matrix.of fun (i j : Fin 3) => t (i,j))
def cubic (x : E) := pm (fm x)
def atJ (t : M) := Matrix.permanent (Matrix.of fun (i j : Fin 3) => (1 : K) + t (i,j))
def mq (_ : Fin 4) : K := 1
theorem mq_ne_zero (i : Fin 4) : mq i ≠ 0 := by simp [mq]
def bil (x y : E) : K := ∑ i, mq i * (x (i, false) * y (i, true) + x (i, true) * y (i, false))

theorem bil_chart (S : Fin 4 → Bool) (x y : E) :
    bil x y = ∑ i, mq i * (x (i, S i) * y (i, !S i) + x (i, !S i) * y (i, S i)) := by
  unfold bil
  refine sum_congr rfl fun i _ => ?_
  cases S i
  · simp only [Bool.not_false]
  · simp only [Bool.not_true]
    ring


def zs (S : Fin 4 → Bool) : Submodule K E := by
  refine { carrier := {x | ∀ i, x (i, S i) = 0}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }
  · intro x y hx hy i
    have hx' : ∀ i, x (i,S i) = 0 := hx
    have hy' : ∀ i, y (i,S i) = 0 := hy
    simp [hx' i,hy' i]
  · exact fun _ => rfl
  · intro c x hx i
    have hx' : ∀ i, x (i,S i) = 0 := hx
    simp [hx' i]

theorem mem_zs (S : Fin 4 → Bool) (x : E) : x ∈ zs S ↔ ∀ i, x (i, S i) = 0 := Iff.rfl

set_option maxHeartbeats 2000000 in
theorem exists_chart_of (L : Submodule K E) (hiso : ∀ x ∈ L, ∀ y ∈ L, bil x y = 0) :
    ∀ n : ℕ, ∀ S : Fin 4 → Bool, Module.finrank K ↥(L ⊓ zs S) = n →
      ∃ S', L ⊓ zs S' = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    by_cases hb : L ⊓ zs S = ⊥
    · exact ⟨S, hb⟩
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hb
    have hyL : y ∈ L := hy.1
    have hyZ : ∀ i, y (i, S i) = 0 := hy.2
    obtain ⟨k, hk⟩ : ∃ k, y (k, !S k) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hy0
      funext ⟨i, b⟩
      by_cases hbS : b = S i
      · rw [hbS]; exact hyZ i
      · have hb' : b = !S i := by
          cases b <;> cases hS : S i <;> simp_all
        rw [hb']; exact hcon i
    have hlt : L ⊓ zs (Function.update S k (!S k)) < L ⊓ zs S := by
      refine lt_of_le_not_ge ?_ ?_
      · rintro x ⟨hxL, hxZ⟩
        have hxZ' : ∀ i, x (i, Function.update S k (!S k) i) = 0 := hxZ
        refine ⟨hxL, fun i => ?_⟩
        by_cases hik : i = k
        · subst hik
          have hB := hiso x hxL y hyL
          rw [bil_chart S, Finset.sum_eq_single i] at hB
          · rw [hyZ i, mul_zero, add_zero] at hB
            rcases mul_eq_zero.1 hB with h | h
            · exact absurd h (mq_ne_zero i)
            · rcases mul_eq_zero.1 h with h | h
              · exact h
              · exact absurd h hk
          · intro j _ hji
            have := hxZ' j
            rw [Function.update_of_ne hji] at this
            rw [this, hyZ j]
            ring
          · intro hi
            exact absurd (mem_univ i) hi
        · have := hxZ' i
          rwa [Function.update_of_ne hik] at this
      · intro hle
        have := (hle hy).2 k
        rw [Function.update_self] at this
        exact hk this
    exact ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl


theorem exists_chart (L : Submodule K E) (hiso : ∀ x ∈ L, ∀ y ∈ L, bil x y = 0) :
    ∃ S : Fin 4 → Bool, L ⊓ zs S = ⊥ :=
  exists_chart_of L hiso _ (fun _ => false) rfl


def pt (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K) (a : Fin 4 → K) : E :=
  fun q =>
  if q.2 = S q.1 then a q.1 else (∑ k, s q.1 k * a k) / mq q.1

theorem iso (L : Submodule K M) (h : ∀ t ∈ L, atJ t = 6)
    (x : E) (hx : fm x ∈ L) (y : E) (hy : fm y ∈ L) : bil x y = 0 := by
  have h1 := h _ (L.add_mem hx hy)
  have h2 := h _ (L.neg_mem (L.add_mem hx hy))
  have h3 := h _ (L.sub_mem hx hy)
  have h4 := h _ (L.neg_mem (L.sub_mem hx hy))
  simp only [atJ, permanent_three, Matrix.of_apply, Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at h1 h2 h3 h4
  simp [fm] at h1 h2 h3 h4
  simp only [bil, mq, one_mul, Fin.sum_univ_four]
  linear_combination (norm := (ring_nf <;> simp only [show (15 : K) = 0 from by decide, show (35 : K) = 0 from by decide, show (65 : K) = 0 from by decide, show (80 : K) = 0 from by decide, show (160 : K) = 0 from by decide, show (240 : K) = 0 from by decide, show (255 : K) = 0 from by decide, show (320 : K) = 0 from by decide, mul_zero, zero_mul, neg_zero, add_zero, sub_zero, zero_add, zero_sub] <;> ring)) 4 * (h1 + h2 - h3 - h4)

theorem vanish (L : Submodule K M) (h : ∀ t ∈ L, atJ t = 6) (x : E) (hx : fm x ∈ L) : cubic x = 0 := by
  have h1 := h _ hx
  have h2 := h _ (L.neg_mem hx)
  have h3 := h _ (L.smul_mem 2 hx)
  have h4 := h _ (L.smul_mem (-2) hx)
  simp only [atJ, permanent_three, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h1 h2 h3 h4
  simp only [cubic, pm, permanent_three, Matrix.of_apply]
  linear_combination (norm := (ring_nf <;> simp only [show (15 : K) = 0 from by decide, show (35 : K) = 0 from by decide, show (65 : K) = 0 from by decide, show (80 : K) = 0 from by decide, show (160 : K) = 0 from by decide, show (240 : K) = 0 from by decide, show (255 : K) = 0 from by decide, show (320 : K) = 0 from by decide, mul_zero, zero_mul, neg_zero, add_zero, sub_zero, zero_add, zero_sub] <;> ring)) 3*(h3 - h4 - 2*(h1-h2))

def detPlus (a b c d e f g h i : K) := a*e*i+a*f*h+b*d*i+b*f*g+c*d*h+c*e*g
def p0000_0 (a b c : K) : K := detPlus (a + (2)*b + (-2)*c) (b + (-c)) ((2)*b + c) (c) (b) ((-2)*c) ((-a) + b + (-2)*c) (1 + (-2)*a + (-c)) ((-1) + (2)*a + (-2)*b + c)
def p0000_1 (a d e : K) : K := detPlus ((2)*d + (-2)*e) ((-a) + d + (-e)) ((2)*d + e) (e) (d) ((-2)*e) (1 + d + (-2)*e) (a + (-e)) ((-1) + (-2)*d + e)
def p0000_2 (b d f : K) : K := detPlus ((-d) + (-2)*f) ((-1) + (-b) + (-f)) (f) (f) (1) ((-2)*f) (1 + d + (-2)*f) (b + (2)*d + (-f)) ((-1) + (-2)*d + f)
def p0000_3 (c e f : K) : K := detPlus (2 + (-e) + (-2)*f) ((-2) + (-c) + (-f)) (1 + (-2)*f) (1) ((-f)) (2) (2 + e + (-f)) ((-2) + c + (2)*e) (1 + (-2)*e + (2)*f)
def p0000_4 (a b c d e f : K) : K := detPlus (2 + a + (2)*b + (-2)*c + (-5)*e + (-10)*f) ((-6) + (-2)*a + (-3)*b + (-2)*c + (2)*d + (-2)*e + (-5)*f) (1 + (2)*b + c + (4)*d + (2)*e + (2)*f) (1 + c + (2)*e + (4)*f) (4 + b + (2)*d + (-f)) (2 + (-2)*c + (-4)*e + (-8)*f) (8 + (-a) + b + (-2)*c + (6)*d + (-3)*e + (-9)*f) ((-1) + (4)*b + (8)*d + (-4)*f) ((-6) + (2)*a + (-2)*b + c + (-12)*d + (6)*f)
def p0000_5 (b c d e f : K) : K := detPlus (2 + (-d) + (-e) + (-4)*f) ((-3) + (-b) + (-c) + (-2)*f) (1 + (-f)) (1 + f) (1 + (-f)) (2 + (-2)*f) (3 + d + e + (-3)*f) ((-2) + b + c + (2)*d + (2)*e + (-f)) ((-2)*d + (-2)*e + (3)*f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check0000 : ∀ a b c : K, p0000_0 a b c = 0 → ∀ d e : K, p0000_1 a d e = 0 → ∀ f : K, p0000_2 b d f = 0 → p0000_3 c e f = 0 → p0000_4 a b c d e f = 0 → p0000_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof0000 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = false)
    (h1 : S 1 = false)
    (h2 : S 2 = false)
    (h3 : S 3 = false)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check0000 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p0000_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p0000_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p0000_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p0000_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 2, 4, 1]) := by
        simp [p0000_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 1]) := by
        simp [p0000_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p0001_0 (a b c : K) : K := detPlus (a + (2)*b + (-2)*c) (b + (2)*c) ((2)*b + (-c)) ((-c)) (b) ((-2)*c) ((-a) + b + (-2)*c) (1 + (-2)*a + (2)*c) ((-1) + (2)*a + (-2)*b + (-c))
def p0001_1 (a d e : K) : K := detPlus ((2)*d + (-2)*e) ((-a) + d + (2)*e) ((2)*d + (-e)) ((-e)) (d) ((-2)*e) (1 + d + (-2)*e) (a + (2)*e) ((-1) + (-2)*d + (-e))
def p0001_2 (b d f : K) : K := detPlus ((-d) + (-2)*f) ((-1) + (-b) + (2)*f) ((-f)) ((-f)) (1) ((-2)*f) (1 + d + (-2)*f) (b + (2)*d + (2)*f) ((-1) + (-2)*d + (-f))
def p0001_3 (c e f : K) : K := detPlus (2 + (-e) + (-2)*f) (1 + (-c) + (-f)) ((-1) + (-2)*f) ((-1)) ((-f)) (2) (2 + e + (-f)) (1 + c + (2)*e) ((-1) + (-2)*e + (2)*f)
def p0001_4 (a b c d e f : K) : K := detPlus (8 + (-2)*d + (-6)*e + (-16)*f) ((-a) + (-4)*b + (-4)*c + d + (2)*e + (4)*f) ((-4) + (2)*d + (-e) + (-12)*f) ((-4) + (-e) + (-4)*f) (4 + d + (-4)*f) (8 + (-2)*e + (-8)*f) (13 + (5)*d + (2)*e + (-12)*f) (4 + a + (4)*b + (4)*c + (8)*d + (10)*e + (8)*f) ((-9) + (-10)*d + (-9)*e + (4)*f)
def p0001_5 (b c d e f : K) : K := detPlus (2 + (-d) + (-e) + (-4)*f) ((-b) + (-c) + f) ((-1) + (-3)*f) ((-1) + (-f)) (1 + (-f)) (2 + (-2)*f) (3 + d + e + (-3)*f) (1 + b + c + (2)*d + (2)*e + (2)*f) ((-2) + (-2)*d + (-2)*e + f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check0001 : ∀ a b c : K, p0001_0 a b c = 0 → ∀ d e : K, p0001_1 a d e = 0 → ∀ f : K, p0001_2 b d f = 0 → p0001_3 c e f = 0 → p0001_4 a b c d e f = 0 → p0001_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof0001 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = false)
    (h1 : S 1 = false)
    (h2 : S 2 = false)
    (h3 : S 3 = true)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check0001 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p0001_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p0001_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p0001_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p0001_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 4, 4]) := by
        simp [p0001_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 1]) := by
        simp [p0001_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p0010_0 (a b c : K) : K := detPlus (a + (-2)*c) (b + (-c)) (c) (c) ((-b)) ((-2)*c) ((-a) + (-b) + (-2)*c) (1 + (-2)*a + (-c)) ((-1) + (2)*a + b + c)
def p0010_1 (a d e : K) : K := detPlus ((-2)*e) ((-a) + d + (-e)) (e) (e) ((-d)) ((-2)*e) (1 + (-d) + (-2)*e) (a + (-e)) ((-1) + d + e)
def p0010_2 (b d f : K) : K := detPlus ((-2) + (-d) + (-2)*f) ((-1) + (-b) + (-f)) ((-2) + f) (f) ((-1)) ((-2)*f) ((-1) + d + (-2)*f) (b + (2)*d + (-f)) (2 + (-2)*d + f)
def p0010_3 (c e f : K) : K := detPlus (2 + (-e)) ((-2) + (-c) + (-f)) (1) (1) (f) (2) (2 + e + f) ((-2) + c + (2)*e) (1 + (-2)*e + (-f))
def p0010_4 (a c d e f : K) : K := detPlus (4 + (-4)*e) ((-4) + (-a) + (-2)*c + d + (-e) + (-2)*f) (2 + e) (2 + e) ((-d) + (2)*f) (4 + (-2)*e) (5 + (-d) + (2)*f) ((-4) + a + (2)*c + (3)*e) (1 + d + (-3)*e + (-2)*f)
def p0010_5 (a b c d e f : K) : K := detPlus (2 + (-d) + (-4)*e + (-2)*f) ((-5) + (-a) + (-b) + (-2)*c + d + (-e) + (-3)*f) (e + f) (2 + e + f) ((-1) + (-d) + (2)*f) (4 + (-2)*e + (-2)*f) (4) ((-4) + a + b + (2)*c + (2)*d + (3)*e + (-f)) (3 + (-d) + (-3)*e + (-f))
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check0010 : ∀ a b c : K, p0010_0 a b c = 0 → ∀ d e : K, p0010_1 a d e = 0 → ∀ f : K, p0010_2 b d f = 0 → p0010_3 c e f = 0 → p0010_4 a c d e f = 0 → p0010_5 a b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof0010 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = false)
    (h1 : S 1 = false)
    (h2 : S 2 = true)
    (h3 : S 3 = false)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check0010 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p0010_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p0010_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p0010_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p0010_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 2]) := by
        simp [p0010_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 1, 2]) := by
        simp [p0010_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p0011_0 (a b c : K) : K := detPlus (a + (-2)*c) (b + (2)*c) ((-c)) ((-c)) ((-b)) ((-2)*c) ((-a) + (-b) + (-2)*c) (1 + (-2)*a + (2)*c) ((-1) + (2)*a + b + (-c))
def p0011_1 (a d e : K) : K := detPlus ((-2)*e) ((-a) + d + (2)*e) ((-e)) ((-e)) ((-d)) ((-2)*e) (1 + (-d) + (-2)*e) (a + (2)*e) ((-1) + d + (-e))
def p0011_2 (b d f : K) : K := detPlus ((-2) + (-d) + (-2)*f) ((-1) + (-b) + (2)*f) ((-2) + (-f)) ((-f)) ((-1)) ((-2)*f) ((-1) + d + (-2)*f) (b + (2)*d + (2)*f) (2 + (-2)*d + (-f))
def p0011_3 (c e f : K) : K := detPlus (2 + (-e)) (1 + (-c) + (-f)) ((-1)) ((-1)) (f) (2) (2 + e + f) (1 + c + (2)*e) ((-1) + (-2)*e + (-f))
def p0011_4 (a b c d e f : K) : K := detPlus (8 + a + (-2)*c + (-6)*e) (4 + (-a) + b + (-2)*c + d + (2)*e + (-4)*f) ((-4) + (-c) + (-e)) ((-4) + (-c) + (-e)) ((-b) + (-d) + (4)*f) (8 + (-2)*c + (-2)*e) (9 + (-a) + (-b) + (-2)*c + (-d) + (2)*e + (4)*f) (5 + (-a) + (6)*c + (10)*e) ((-6) + (2)*a + b + (-c) + d + (-9)*e + (-4)*f)
def p0011_5 (a b c e f : K) : K := detPlus (2 + a + (-2)*c + (-e)) (1 + b + c + (-f)) ((-1) + (-c)) ((-1) + (-c)) ((-b) + f) (2 + (-2)*c) (2 + (-a) + (-b) + (-2)*c + e + f) (2 + (-2)*a + (3)*c + (2)*e) ((-2) + (2)*a + b + (-c) + (-2)*e + (-f))
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check0011 : ∀ a b c : K, p0011_0 a b c = 0 → ∀ d e : K, p0011_1 a d e = 0 → ∀ f : K, p0011_2 b d f = 0 → p0011_3 c e f = 0 → p0011_4 a b c d e f = 0 → p0011_5 a b c e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof0011 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = false)
    (h1 : S 1 = false)
    (h2 : S 2 = true)
    (h3 : S 3 = true)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check0011 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p0011_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p0011_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p0011_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p0011_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 1, 0, 4]) := by
        simp [p0011_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 0, 1]) := by
        simp [p0011_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p0100_0 (a b c : K) : K := detPlus ((2)*b + (-2)*c) (b + (-c)) ((2)*b + c) (c) (b) ((-2)*c) ((-a) + b + (-2)*c) (1 + (-c)) ((-1) + a + (-2)*b + c)
def p0100_1 (a d e : K) : K := detPlus ((-1) + (2)*d + (-2)*e) ((-a) + d + (-e)) ((2)*d + e) (e) (d) ((-2)*e) (1 + d + (-2)*e) (2 + a + (-e)) ((-2) + (-2)*d + e)
def p0100_2 (b d f : K) : K := detPlus ((-2)*f) ((-1) + (-b) + (-f)) (f) (f) (1) ((-2)*f) (1 + d + (-2)*f) (b + (-f)) ((-1) + (-d) + f)
def p0100_3 (c e f : K) : K := detPlus (2 + (-2)*f) ((-2) + (-c) + (-f)) (1 + (-2)*f) (1) ((-f)) (2) (2 + e + (-f)) ((-2) + c) (1 + (-e) + (2)*f)
def p0100_4 (a b c e f : K) : K := detPlus (8 + (2)*b + (-2)*c + (-8)*f) ((-8) + b + (-5)*c + (-4)*f) (4 + (2)*b + c + (-8)*f) (4 + c) (b + (-4)*f) (8 + (-2)*c) (8 + (-a) + b + (-2)*c + (4)*e + (-4)*f) ((-7) + (3)*c) (3 + a + (-2)*b + c + (-4)*e + (8)*f)
def p0100_5 (b c d e f : K) : K := detPlus (8 + (-10)*f) ((-9) + (-b) + (-4)*c + (-5)*f) (4 + (-7)*f) (4 + f) (1 + (-4)*f) (8 + (-2)*f) (9 + d + (4)*e + (-6)*f) ((-8) + b + (4)*c + (-f)) (3 + (-d) + (-4)*e + (9)*f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check0100 : ∀ a b c : K, p0100_0 a b c = 0 → ∀ d e : K, p0100_1 a d e = 0 → ∀ f : K, p0100_2 b d f = 0 → p0100_3 c e f = 0 → p0100_4 a b c e f = 0 → p0100_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof0100 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = false)
    (h1 : S 1 = true)
    (h2 : S 2 = false)
    (h3 : S 3 = false)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check0100 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p0100_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p0100_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p0100_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p0100_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 0, 4]) := by
        simp [p0100_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 4]) := by
        simp [p0100_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p0101_0 (a b c : K) : K := detPlus ((2)*b + (-2)*c) (b + (2)*c) ((2)*b + (-c)) ((-c)) (b) ((-2)*c) ((-a) + b + (-2)*c) (1 + (2)*c) ((-1) + a + (-2)*b + (-c))
def p0101_1 (a d e : K) : K := detPlus ((-1) + (2)*d + (-2)*e) ((-a) + d + (2)*e) ((2)*d + (-e)) ((-e)) (d) ((-2)*e) (1 + d + (-2)*e) (2 + a + (2)*e) ((-2) + (-2)*d + (-e))
def p0101_2 (b d f : K) : K := detPlus ((-2)*f) ((-1) + (-b) + (2)*f) ((-f)) ((-f)) (1) ((-2)*f) (1 + d + (-2)*f) (b + (2)*f) ((-1) + (-d) + (-f))
def p0101_3 (c e f : K) : K := detPlus (2 + (-2)*f) (1 + (-c) + (-f)) ((-1) + (-2)*f) ((-1)) ((-f)) (2) (2 + e + (-f)) (1 + c) ((-1) + (-e) + (2)*f)
def p0101_4 (a b c e f : K) : K := detPlus (4 + (2)*b + (-2)*c + (-4)*f) (2 + b + (-2)*f) ((-2) + (2)*b + (-c) + (-4)*f) ((-2) + (-c)) (b + (-2)*f) (4 + (-2)*c) (4 + (-a) + b + (-2)*c + (2)*e + (-2)*f) (3 + (4)*c) ((-3) + a + (-2)*b + (-c) + (-2)*e + (4)*f)
def p0101_5 (a b c d e f : K) : K := detPlus (8 + (2)*b + (-2)*c + (-16)*f) ((-3)*b + (-2)*c + (4)*f) ((-4) + (2)*b + (-c) + (-12)*f) ((-4) + (-c) + (-4)*f) (4 + b + (-4)*f) (8 + (-2)*c + (-8)*f) (12 + (-a) + b + (-2)*c + (4)*d + (4)*e + (-12)*f) (5 + (4)*b + (6)*c + (8)*f) ((-9) + a + (-2)*b + (-c) + (-4)*d + (-4)*e + (4)*f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check0101 : ∀ a b c : K, p0101_0 a b c = 0 → ∀ d e : K, p0101_1 a d e = 0 → ∀ f : K, p0101_2 b d f = 0 → p0101_3 c e f = 0 → p0101_4 a b c e f = 0 → p0101_5 a b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof0101 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = false)
    (h1 : S 1 = true)
    (h2 : S 2 = false)
    (h3 : S 3 = true)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check0101 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p0101_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p0101_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p0101_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p0101_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 0, 2]) := by
        simp [p0101_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 4, 4]) := by
        simp [p0101_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p0110_0 (a b c : K) : K := detPlus ((-2)*c) (b + (-c)) (c) (c) ((-b)) ((-2)*c) ((-a) + (-b) + (-2)*c) (1 + (-c)) ((-1) + a + b + c)
def p0110_1 (a d e : K) : K := detPlus ((-1) + (-2)*e) ((-a) + d + (-e)) (e) (e) ((-d)) ((-2)*e) (1 + (-d) + (-2)*e) (2 + a + (-e)) ((-2) + d + e)
def p0110_2 (b d f : K) : K := detPlus ((-2) + (-2)*f) ((-1) + (-b) + (-f)) ((-2) + f) (f) ((-1)) ((-2)*f) ((-1) + d + (-2)*f) (b + (-f)) (2 + (-d) + f)
def p0110_3 (c e f : K) : K := detPlus (2) ((-2) + (-c) + (-f)) (1) (1) (f) (2) (2 + e + f) ((-2) + c) (1 + (-e) + (-f))
def p0110_4 (a b c d e f : K) : K := detPlus ((-2)*c + (-8)*e + (-2)*f) ((-7) + (-4)*a + (-4)*c + (4)*d + (-4)*e + (-4)*f) (1 + c + (4)*e + f) (3 + c + (4)*e + f) ((-1) + (-b) + (-4)*d + (3)*f) (6 + (-2)*c + (-8)*e + (-2)*f) (9 + (-a) + (-b) + (-2)*c + (-3)*d + (-5)*e + f) (3 + (4)*a + b + (2)*c + (-4)*e + (-f)) ((-4) + a + b + c + (3)*d + e + (-2)*f)
def p0110_5 (b c d e f : K) : K := detPlus ((-2)*f) ((-3) + (-b) + (-c) + (-2)*f) ((-1) + f) (1 + f) ((-1) + f) (2 + (-2)*f) (1 + d + e + (-f)) ((-2) + b + c + (-f)) (3 + (-d) + (-e))
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check0110 : ∀ a b c : K, p0110_0 a b c = 0 → ∀ d e : K, p0110_1 a d e = 0 → ∀ f : K, p0110_2 b d f = 0 → p0110_3 c e f = 0 → p0110_4 a b c d e f = 0 → p0110_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof0110 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = false)
    (h1 : S 1 = true)
    (h2 : S 2 = true)
    (h3 : S 3 = false)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check0110 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p0110_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p0110_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p0110_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p0110_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 4, 1, 3]) := by
        simp [p0110_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 1]) := by
        simp [p0110_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p0111_0 (a b c : K) : K := detPlus ((-2)*c) (b + (2)*c) ((-c)) ((-c)) ((-b)) ((-2)*c) ((-a) + (-b) + (-2)*c) (1 + (2)*c) ((-1) + a + b + (-c))
def p0111_1 (a d e : K) : K := detPlus ((-1) + (-2)*e) ((-a) + d + (2)*e) ((-e)) ((-e)) ((-d)) ((-2)*e) (1 + (-d) + (-2)*e) (2 + a + (2)*e) ((-2) + d + (-e))
def p0111_2 (b d f : K) : K := detPlus ((-2) + (-2)*f) ((-1) + (-b) + (2)*f) ((-2) + (-f)) ((-f)) ((-1)) ((-2)*f) ((-1) + d + (-2)*f) (b + (2)*f) (2 + (-d) + (-f))
def p0111_3 (c e f : K) : K := detPlus (2) (1 + (-c) + (-f)) ((-1)) ((-1)) (f) (2) (2 + e + f) (1 + c) ((-1) + (-e) + (-f))
def p0111_4 (a b c e f : K) : K := detPlus (6 + (-2)*c) (3 + b + (-c) + (-3)*f) ((-3) + (-c)) ((-3) + (-c)) ((-b) + (3)*f) (6 + (-2)*c) (6 + (-a) + (-b) + (-2)*c + (3)*e + (3)*f) (4 + (5)*c) ((-4) + a + b + (-c) + (-3)*e + (-3)*f)
def p0111_5 (b c d e f : K) : K := detPlus ((-2)*f) ((-b) + (-c) + f) ((-3) + (-f)) ((-1) + (-f)) ((-1) + f) (2 + (-2)*f) (1 + d + e + (-f)) (1 + b + c + (2)*f) (1 + (-d) + (-e) + (-2)*f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check0111 : ∀ a b c : K, p0111_0 a b c = 0 → ∀ d e : K, p0111_1 a d e = 0 → ∀ f : K, p0111_2 b d f = 0 → p0111_3 c e f = 0 → p0111_4 a b c e f = 0 → p0111_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof0111 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = false)
    (h1 : S 1 = true)
    (h2 : S 2 = true)
    (h3 : S 3 = true)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check0111 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p0111_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p0111_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p0111_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p0111_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 0, 3]) := by
        simp [p0111_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 1]) := by
        simp [p0111_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p1000_0 (a b c : K) : K := detPlus (a + (2)*b + (-2)*c) ((-1) + b + (-c)) ((2)*b + c) (c) (b) ((-2)*c) ((-a) + b + (-2)*c) (1 + (-2)*a + (-c)) ((2)*a + (-2)*b + c)
def p1000_1 (a d e : K) : K := detPlus ((2)*d + (-2)*e) (d + (-e)) ((2)*d + e) (e) (d) ((-2)*e) (1 + d + (-2)*e) (a + (-e)) ((-1) + (-a) + (-2)*d + e)
def p1000_2 (b d f : K) : K := detPlus ((-d) + (-2)*f) ((-1) + (-f)) (f) (f) (1) ((-2)*f) (1 + d + (-2)*f) (b + (2)*d + (-f)) ((-1) + (-b) + (-2)*d + f)
def p1000_3 (c e f : K) : K := detPlus (2 + (-e) + (-2)*f) ((-2) + (-f)) (1 + (-2)*f) (1) ((-f)) (2) (2 + e + (-f)) ((-2) + c + (2)*e) (1 + (-c) + (-2)*e + (2)*f)
def p1000_4 (a b c d e f : K) : K := detPlus (2 + (-d) + (-3)*e + (-8)*f) ((-5) + d + (-e) + (-4)*f) (1 + (2)*d + e + f) (1 + e + (3)*f) (3 + d + (-f)) (2 + (-2)*e + (-6)*f) (6 + (4)*d + (-e) + (-7)*f) ((-2) + a + (3)*b + c + (6)*d + e + (-3)*f) ((-3) + (-a) + (-3)*b + (-c) + (-8)*d + (-e) + (5)*f)
def p1000_5 (b c d e f : K) : K := detPlus (4 + (-d) + (-2)*e + (-6)*f) ((-5) + (-3)*f) (2 + (-3)*f) (2 + f) (1 + (-2)*f) (4 + (-2)*f) (5 + d + (2)*e + (-4)*f) ((-4) + b + (2)*c + (2)*d + (4)*e + (-f)) (1 + (-b) + (-2)*c + (-2)*d + (-4)*e + (5)*f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check1000 : ∀ a b c : K, p1000_0 a b c = 0 → ∀ d e : K, p1000_1 a d e = 0 → ∀ f : K, p1000_2 b d f = 0 → p1000_3 c e f = 0 → p1000_4 a b c d e f = 0 → p1000_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof1000 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = true)
    (h1 : S 1 = false)
    (h2 : S 2 = false)
    (h3 : S 3 = false)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check1000 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p1000_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p1000_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p1000_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p1000_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 3, 1]) := by
        simp [p1000_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 2]) := by
        simp [p1000_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p1001_0 (a b c : K) : K := detPlus (a + (2)*b + (-2)*c) ((-1) + b + (2)*c) ((2)*b + (-c)) ((-c)) (b) ((-2)*c) ((-a) + b + (-2)*c) (1 + (-2)*a + (2)*c) ((2)*a + (-2)*b + (-c))
def p1001_1 (a d e : K) : K := detPlus ((2)*d + (-2)*e) (d + (2)*e) ((2)*d + (-e)) ((-e)) (d) ((-2)*e) (1 + d + (-2)*e) (a + (2)*e) ((-1) + (-a) + (-2)*d + (-e))
def p1001_2 (b d f : K) : K := detPlus ((-d) + (-2)*f) ((-1) + (2)*f) ((-f)) ((-f)) (1) ((-2)*f) (1 + d + (-2)*f) (b + (2)*d + (2)*f) ((-1) + (-b) + (-2)*d + (-f))
def p1001_3 (c e f : K) : K := detPlus (2 + (-e) + (-2)*f) (1 + (-f)) ((-1) + (-2)*f) ((-1)) ((-f)) (2) (2 + e + (-f)) (1 + c + (2)*e) ((-1) + (-c) + (-2)*e + (2)*f)
def p1001_4 (a b c d e f : K) : K := detPlus (4 + a + (2)*b + (-2)*c + (4)*d + (-6)*e + (-4)*f) (1 + b + (2)*c + (2)*d + (4)*e + (-2)*f) ((-2) + (2)*b + (-c) + (4)*d + (-2)*e + (-4)*f) ((-2) + (-c) + (-2)*e) (b + (2)*d + (-2)*f) (4 + (-2)*c + (-4)*e) (6 + (-a) + b + (-2)*c + (2)*d + (-2)*e + (-2)*f) (3 + (4)*c + (8)*e) ((-4) + (-2)*b + (-3)*c + (-4)*d + (-6)*e + (4)*f)
def p1001_5 (b c d e f : K) : K := detPlus (2 + (-d) + (-e) + (-4)*f) (f) ((-1) + (-3)*f) ((-1) + (-f)) (1 + (-f)) (2 + (-2)*f) (3 + d + e + (-3)*f) (1 + b + c + (2)*d + (2)*e + (2)*f) ((-2) + (-b) + (-c) + (-2)*d + (-2)*e + f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check1001 : ∀ a b c : K, p1001_0 a b c = 0 → ∀ d e : K, p1001_1 a d e = 0 → ∀ f : K, p1001_2 b d f = 0 → p1001_3 c e f = 0 → p1001_4 a b c d e f = 0 → p1001_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof1001 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = true)
    (h1 : S 1 = false)
    (h2 : S 2 = false)
    (h3 : S 3 = true)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check1001 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p1001_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p1001_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p1001_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p1001_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 2, 0, 2]) := by
        simp [p1001_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 1]) := by
        simp [p1001_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p1010_0 (a b c : K) : K := detPlus (a + (-2)*c) ((-1) + b + (-c)) (c) (c) ((-b)) ((-2)*c) ((-a) + (-b) + (-2)*c) (1 + (-2)*a + (-c)) ((2)*a + b + c)
def p1010_1 (a d e : K) : K := detPlus ((-2)*e) (d + (-e)) (e) (e) ((-d)) ((-2)*e) (1 + (-d) + (-2)*e) (a + (-e)) ((-1) + (-a) + d + e)
def p1010_2 (b d f : K) : K := detPlus ((-2) + (-d) + (-2)*f) ((-1) + (-f)) ((-2) + f) (f) ((-1)) ((-2)*f) ((-1) + d + (-2)*f) (b + (2)*d + (-f)) (2 + (-b) + (-2)*d + f)
def p1010_3 (c e f : K) : K := detPlus (2 + (-e)) ((-2) + (-f)) (1) (1) (f) (2) (2 + e + f) ((-2) + c + (2)*e) (1 + (-c) + (-2)*e + (-f))
def p1010_4 (a c d e f : K) : K := detPlus (4 + (-4)*e) ((-4) + d + (-e) + (-2)*f) (2 + e) (2 + e) ((-d) + (2)*f) (4 + (-2)*e) (5 + (-d) + (2)*f) ((-4) + a + (2)*c + (3)*e) (1 + (-a) + (-2)*c + d + (-3)*e + (-2)*f)
def p1010_5 (a b c e f : K) : K := detPlus (2 + a + (-2)*c + (-e)) ((-3) + b + (-c) + (-f)) (1 + c) (1 + c) ((-b) + f) (2 + (-2)*c) (2 + (-a) + (-b) + (-2)*c + e + f) ((-1) + (-2)*a + (2)*e) (1 + (2)*a + b + (-2)*e + (-f))
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check1010 : ∀ a b c : K, p1010_0 a b c = 0 → ∀ d e : K, p1010_1 a d e = 0 → ∀ f : K, p1010_2 b d f = 0 → p1010_3 c e f = 0 → p1010_4 a c d e f = 0 → p1010_5 a b c e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof1010 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = true)
    (h1 : S 1 = false)
    (h2 : S 2 = true)
    (h3 : S 3 = false)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check1010 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p1010_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p1010_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p1010_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p1010_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 2]) := by
        simp [p1010_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 0, 1]) := by
        simp [p1010_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p1011_0 (a b c : K) : K := detPlus (a + (-2)*c) ((-1) + b + (2)*c) ((-c)) ((-c)) ((-b)) ((-2)*c) ((-a) + (-b) + (-2)*c) (1 + (-2)*a + (2)*c) ((2)*a + b + (-c))
def p1011_1 (a d e : K) : K := detPlus ((-2)*e) (d + (2)*e) ((-e)) ((-e)) ((-d)) ((-2)*e) (1 + (-d) + (-2)*e) (a + (2)*e) ((-1) + (-a) + d + (-e))
def p1011_2 (b d f : K) : K := detPlus ((-2) + (-d) + (-2)*f) ((-1) + (2)*f) ((-2) + (-f)) ((-f)) ((-1)) ((-2)*f) ((-1) + d + (-2)*f) (b + (2)*d + (2)*f) (2 + (-b) + (-2)*d + (-f))
def p1011_3 (c e f : K) : K := detPlus (2 + (-e)) (1 + (-f)) ((-1)) ((-1)) (f) (2) (2 + e + f) (1 + c + (2)*e) ((-1) + (-c) + (-2)*e + (-f))
def p1011_4 (a b c d e f : K) : K := detPlus ((-2) + (-2)*d + (-3)*e + (-4)*f) ((-1) + d + (2)*e + (3)*f) ((-5) + (-e) + (-2)*f) ((-1) + (-e) + (-2)*f) ((-2) + (-d) + f) (2 + (-2)*e + (-4)*f) (1 + d + (-e) + (-3)*f) (1 + a + (2)*b + c + (4)*d + (4)*e + (4)*f) (2 + (-a) + (-2)*b + (-c) + (-3)*d + (-3)*e + (-3)*f)
def p1011_5 (b c d e f : K) : K := detPlus ((-d) + (-e) + (-2)*f) (f) ((-3) + (-f)) ((-1) + (-f)) ((-1) + f) (2 + (-2)*f) (1 + d + e + (-f)) (1 + b + c + (2)*d + (2)*e + (2)*f) (1 + (-b) + (-c) + (-2)*d + (-2)*e + (-2)*f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check1011 : ∀ a b c : K, p1011_0 a b c = 0 → ∀ d e : K, p1011_1 a d e = 0 → ∀ f : K, p1011_2 b d f = 0 → p1011_3 c e f = 0 → p1011_4 a b c d e f = 0 → p1011_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof1011 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = true)
    (h1 : S 1 = false)
    (h2 : S 2 = true)
    (h3 : S 3 = true)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check1011 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p1011_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p1011_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p1011_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p1011_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 2, 1]) := by
        simp [p1011_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 1]) := by
        simp [p1011_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p1100_0 (a b c : K) : K := detPlus ((2)*b + (-2)*c) ((-1) + b + (-c)) ((2)*b + c) (c) (b) ((-2)*c) ((-a) + b + (-2)*c) (1 + (-c)) (a + (-2)*b + c)
def p1100_1 (a d e : K) : K := detPlus ((-1) + (2)*d + (-2)*e) (d + (-e)) ((2)*d + e) (e) (d) ((-2)*e) (1 + d + (-2)*e) (2 + a + (-e)) ((-2) + (-a) + (-2)*d + e)
def p1100_2 (b d f : K) : K := detPlus ((-2)*f) ((-1) + (-f)) (f) (f) (1) ((-2)*f) (1 + d + (-2)*f) (b + (-f)) ((-1) + (-b) + (-d) + f)
def p1100_3 (c e f : K) : K := detPlus (2 + (-2)*f) ((-2) + (-f)) (1 + (-2)*f) (1) ((-f)) (2) (2 + e + (-f)) ((-2) + c) (1 + (-c) + (-e) + (2)*f)
def p1100_4 (a b c d e f : K) : K := detPlus ((-2) + (2)*b + (-2)*c + (4)*d + (-4)*e + (-8)*f) ((-5) + b + (-c) + (2)*d + (-2)*e + (-4)*f) ((2)*b + c + (4)*d + (2)*e + (4)*f) (c + (2)*e + (4)*f) (4 + b + (2)*d) ((-2)*c + (-4)*e + (-8)*f) (6 + (-a) + b + (-2)*c + (6)*d + (-4)*e + (-8)*f) (5 + (2)*a + (4)*b + (-c) + (-2)*e + (-4)*f) ((-8) + (-a) + (-6)*b + c + (-8)*d + (2)*e + (4)*f)
def p1100_5 (b c d e f : K) : K := detPlus (4 + (-6)*f) ((-5) + (-3)*f) (2 + (-3)*f) (2 + f) (1 + (-2)*f) (4 + (-2)*f) (5 + d + (2)*e + (-4)*f) ((-4) + b + (2)*c + (-f)) (1 + (-b) + (-2)*c + (-d) + (-2)*e + (5)*f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check1100 : ∀ a b c : K, p1100_0 a b c = 0 → ∀ d e : K, p1100_1 a d e = 0 → ∀ f : K, p1100_2 b d f = 0 → p1100_3 c e f = 0 → p1100_4 a b c d e f = 0 → p1100_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof1100 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = true)
    (h1 : S 1 = true)
    (h2 : S 2 = false)
    (h3 : S 3 = false)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check1100 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p1100_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p1100_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p1100_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p1100_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 2, 4, 0]) := by
        simp [p1100_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 2]) := by
        simp [p1100_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p1101_0 (a b c : K) : K := detPlus ((2)*b + (-2)*c) ((-1) + b + (2)*c) ((2)*b + (-c)) ((-c)) (b) ((-2)*c) ((-a) + b + (-2)*c) (1 + (2)*c) (a + (-2)*b + (-c))
def p1101_1 (a d e : K) : K := detPlus ((-1) + (2)*d + (-2)*e) (d + (2)*e) ((2)*d + (-e)) ((-e)) (d) ((-2)*e) (1 + d + (-2)*e) (2 + a + (2)*e) ((-2) + (-a) + (-2)*d + (-e))
def p1101_2 (b d f : K) : K := detPlus ((-2)*f) ((-1) + (2)*f) ((-f)) ((-f)) (1) ((-2)*f) (1 + d + (-2)*f) (b + (2)*f) ((-1) + (-b) + (-d) + (-f))
def p1101_3 (c e f : K) : K := detPlus (2 + (-2)*f) (1 + (-f)) ((-1) + (-2)*f) ((-1)) ((-f)) (2) (2 + e + (-f)) (1 + c) ((-1) + (-c) + (-e) + (2)*f)
def p1101_4 (a b c d e f : K) : K := detPlus (4 + (2)*b + (-2)*c + (-6)*f) (b + (2)*c) ((-2) + (2)*b + (-c) + (-5)*f) ((-2) + (-c) + (-f)) (1 + b + (-2)*f) (4 + (-2)*c + (-2)*f) (5 + (-a) + b + (-2)*c + d + (2)*e + (-4)*f) (3 + b + (4)*c + (2)*f) ((-3) + a + (-3)*b + (-3)*c + (-d) + (-2)*e + (3)*f)
def p1101_5 (b c d e f : K) : K := detPlus (2 + (-4)*f) (f) ((-1) + (-3)*f) ((-1) + (-f)) (1 + (-f)) (2 + (-2)*f) (3 + d + e + (-3)*f) (1 + b + c + (2)*f) ((-2) + (-b) + (-c) + (-d) + (-e) + f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check1101 : ∀ a b c : K, p1101_0 a b c = 0 → ∀ d e : K, p1101_1 a d e = 0 → ∀ f : K, p1101_2 b d f = 0 → p1101_3 c e f = 0 → p1101_4 a b c d e f = 0 → p1101_5 b c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof1101 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = true)
    (h1 : S 1 = true)
    (h2 : S 2 = false)
    (h3 : S 3 = true)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check1101 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p1101_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p1101_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p1101_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p1101_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 1, 2]) := by
        simp [p1101_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 1]) := by
        simp [p1101_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p1110_0 (a b c : K) : K := detPlus ((-2)*c) ((-1) + b + (-c)) (c) (c) ((-b)) ((-2)*c) ((-a) + (-b) + (-2)*c) (1 + (-c)) (a + b + c)
def p1110_1 (a d e : K) : K := detPlus ((-1) + (-2)*e) (d + (-e)) (e) (e) ((-d)) ((-2)*e) (1 + (-d) + (-2)*e) (2 + a + (-e)) ((-2) + (-a) + d + e)
def p1110_2 (b d f : K) : K := detPlus ((-2) + (-2)*f) ((-1) + (-f)) ((-2) + f) (f) ((-1)) ((-2)*f) ((-1) + d + (-2)*f) (b + (-f)) (2 + (-b) + (-d) + f)
def p1110_3 (c e f : K) : K := detPlus (2) ((-2) + (-f)) (1) (1) (f) (2) (2 + e + f) ((-2) + c) (1 + (-c) + (-e) + (-f))
def p1110_4 (a b c e f : K) : K := detPlus (6 + (-2)*c) ((-7) + b + (-c) + (-3)*f) (3 + c) (3 + c) ((-b) + (3)*f) (6 + (-2)*c) (6 + (-a) + (-b) + (-2)*c + (3)*e + (3)*f) ((-5) + (2)*c) (3 + a + b + (-2)*c + (-3)*e + (-3)*f)
def p1110_5 (a c d e f : K) : K := detPlus (1 + (-2)*e) ((-2) + d + (-e) + (-f)) (1 + e) (1 + e) ((-d) + f) (2 + (-2)*e) (3 + (-d) + (-e) + f) (a + c + (-e)) ((-1) + (-a) + (-c) + d + (-f))
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check1110 : ∀ a b c : K, p1110_0 a b c = 0 → ∀ d e : K, p1110_1 a d e = 0 → ∀ f : K, p1110_2 b d f = 0 → p1110_3 c e f = 0 → p1110_4 a b c e f = 0 → p1110_5 a c d e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof1110 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = true)
    (h1 : S 1 = true)
    (h2 : S 2 = true)
    (h3 : S 3 = false)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check1110 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p1110_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p1110_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p1110_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p1110_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 0, 3]) := by
        simp [p1110_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 1]) := by
        simp [p1110_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _

def p1111_0 (a b c : K) : K := detPlus ((-2)*c) ((-1) + b + (2)*c) ((-c)) ((-c)) ((-b)) ((-2)*c) ((-a) + (-b) + (-2)*c) (1 + (2)*c) (a + b + (-c))
def p1111_1 (a d e : K) : K := detPlus ((-1) + (-2)*e) (d + (2)*e) ((-e)) ((-e)) ((-d)) ((-2)*e) (1 + (-d) + (-2)*e) (2 + a + (2)*e) ((-2) + (-a) + d + (-e))
def p1111_2 (b d f : K) : K := detPlus ((-2) + (-2)*f) ((-1) + (2)*f) ((-2) + (-f)) ((-f)) ((-1)) ((-2)*f) ((-1) + d + (-2)*f) (b + (2)*f) (2 + (-b) + (-d) + (-f))
def p1111_3 (c e f : K) : K := detPlus (2) (1 + (-f)) ((-1)) ((-1)) (f) (2) (2 + e + f) (1 + c) ((-1) + (-c) + (-e) + (-f))
def p1111_4 (a b c d e f : K) : K := detPlus ((-6) + (-2)*c + (-8)*e + (-4)*f) ((-2) + b + (2)*c + (4)*d + (8)*e + (3)*f) ((-5) + (-c) + (-4)*e + (-2)*f) ((-1) + (-c) + (-4)*e + (-2)*f) ((-2) + (-b) + (-4)*d + f) (2 + (-2)*c + (-8)*e + (-4)*f) (4 + (-a) + (-b) + (-2)*c + (-2)*d + (-7)*e + (-3)*f) (10 + (4)*a + (2)*b + (3)*c + (8)*e + (4)*f) ((-5) + (-3)*a + (-b) + (-2)*c + (2)*d + (-5)*e + (-3)*f)
def p1111_5 (a b c e f : K) : K := detPlus (4 + (-2)*c) (1 + b + (2)*c + (-2)*f) ((-2) + (-c)) ((-2) + (-c)) ((-b) + (2)*f) (4 + (-2)*c) (4 + (-a) + (-b) + (-2)*c + (2)*e + (2)*f) (3 + (4)*c) ((-2) + a + b + (-3)*c + (-2)*e + (-2)*f)
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem check1111 : ∀ a b c : K, p1111_0 a b c = 0 → ∀ d e : K, p1111_1 a d e = 0 → ∀ f : K, p1111_2 b d f = 0 → p1111_3 c e f = 0 → p1111_4 a b c d e f = 0 → p1111_5 a b c e f = 0 → False := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem proof1111 (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i)
    (h0 : S 0 = true)
    (h1 : S 1 = true)
    (h2 : S 2 = true)
    (h3 : S 3 = true)
    (h : ∀ a : Fin 4 → K, cubic (pt S s a) = 0) : False := by
  have diag (i : Fin 4) : s i i = 0 := by
    have hz : (2:K)*s i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  refine check1111 (s 0 1) (s 0 2) (s 0 3) ?_ (s 1 2) (s 1 3) ?_ (s 2 3) ?_  ?_  ?_  ?_ 
  · calc
      _ = cubic (pt S s ![1, 0, 0, 0]) := by
        simp [p1111_0, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 1, 0, 0]) := by
        simp [p1111_1, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 1, 0]) := by
        simp [p1111_2, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![0, 0, 0, 1]) := by
        simp [p1111_3, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 4, 2, 1]) := by
        simp [p1111_4, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
  · calc
      _ = cubic (pt S s ![1, 0, 0, 2]) := by
        simp [p1111_5, detPlus, cubic, pm, permanent_three, fm, pt, mq, Fin.sum_univ_four, h0, h1, h2, h3, diag, e10, e20, e30, e21, e31, e32] <;> ring
      _ = 0 := h _
theorem excluded (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K)
    (hs : ∀ i k, s i k = -s k i) (h : ∀ a, cubic (pt S s a) = 0) : False := by
  cases h0 : S 0 <;> cases h1 : S 1 <;> cases h2 : S 2 <;> cases h3 : S 3
  · exact proof0000 S s hs h0 h1 h2 h3 h
  · exact proof0001 S s hs h0 h1 h2 h3 h
  · exact proof0010 S s hs h0 h1 h2 h3 h
  · exact proof0011 S s hs h0 h1 h2 h3 h
  · exact proof0100 S s hs h0 h1 h2 h3 h
  · exact proof0101 S s hs h0 h1 h2 h3 h
  · exact proof0110 S s hs h0 h1 h2 h3 h
  · exact proof0111 S s hs h0 h1 h2 h3 h
  · exact proof1000 S s hs h0 h1 h2 h3 h
  · exact proof1001 S s hs h0 h1 h2 h3 h
  · exact proof1010 S s hs h0 h1 h2 h3 h
  · exact proof1011 S s hs h0 h1 h2 h3 h
  · exact proof1100 S s hs h0 h1 h2 h3 h
  · exact proof1101 S s hs h0 h1 h2 h3 h
  · exact proof1110 S s hs h0 h1 h2 h3 h
  · exact proof1111 S s hs h0 h1 h2 h3 h
def back (t : M) (q : Fin 4 × Bool) : K := (![![2 * t (0, 0) + t (0, 1) + 2 * t (0, 2) + t (1, 0) + t (1, 1) + t (1, 2) + t (2, 1), -t (0, 1) + t (0, 2) + -t (1, 1) + t (1, 2)], ![t (0, 0) + -t (0, 2) + t (1, 0) + -t (1, 1) + (-2) * t (1, 2) + t (2, 0), -t (0, 0) + t (0, 2) + -t (1, 0) + t (1, 2)], ![2 * t (0, 2) + (-2) * t (1, 0) + t (1, 1), 2 * t (0, 2) + (-2) * t (1, 0)], ![(-2) * t (1, 0) + -t (1, 2), 2 * t (1, 0) + -t (1, 2)]]) q.1 (if q.2 then 1 else 0)
theorem invert (t : M) (ht : ∑ q, t q = 0) : fm (back t) = t := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three] at ht
  funext ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · apply sub_eq_zero.mp
    simp [fm, back]
    ring_nf <;> simp only [show (5 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring
  · apply sub_eq_zero.mp
    simp [fm, back]
    ring_nf <;> simp only [show (5 : K) = 0 from by decide, show (10 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring
  · apply sub_eq_zero.mp
    simp [fm, back]
    ring_nf <;> simp only [show (5 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring
  · apply sub_eq_zero.mp
    simp [fm, back]
    ring_nf <;> simp only [show (5 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring
  · apply sub_eq_zero.mp
    simp [fm, back]
    ring
  · apply sub_eq_zero.mp
    simp [fm, back]
    ring_nf <;> simp only [show (5 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring
  · apply sub_eq_zero.mp
    simp [fm, back]
    ring_nf <;> simp only [show (5 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring
  · apply sub_eq_zero.mp
    simp [fm, back]
    ring_nf <;> simp only [show (5 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring
  · apply sub_eq_zero.mp
    simp [fm, back]
    linear_combination (norm := (ring_nf <;> simp only [show (5 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring)) -ht
theorem sum_zero (L : Submodule K M) (h : ∀ t ∈ L, atJ t = 6) (t : M) (ht : t ∈ L) : ∑ q, t q = 0 := by
  have h1 := h _ ht
  have h2 := h _ (L.neg_mem ht)
  have h3 := h _ (L.smul_mem 2 ht)
  have h4 := h _ (L.smul_mem (-2) ht)
  simp only [atJ, permanent_three, Matrix.of_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
  linear_combination (norm := (ring_nf <;> simp only [show (95 : K) = 0 from by decide, mul_zero, zero_mul, add_zero, sub_zero, zero_add, zero_sub, neg_zero] <;> ring)) 4 * (8 * (h1-h2) - (h3-h4))
theorem finrank_le_three (L : Submodule K E) (no_chart : ∀ (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K), (∀ i k, s i k = -s k i) → (∀ a, cubic (pt S s a) = 0) → False)
    (hiso : ∀ x ∈ L, ∀ y ∈ L, bil x y = 0) (h : ∀ x ∈ L, cubic x = 0) :
    Module.finrank K L ≤ 3 := by
  by_contra hcon
  obtain ⟨S, hS⟩ := exists_chart L hiso
  let Φ : L →ₗ[K] (Fin 4 → K) :=
    { toFun := fun x i => x.1 (i, S i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦ : ∀ (x : L) (i : Fin 4), Φ x i = x.1 (i, S i) := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : x.1 ∈ L ⊓ zs S := ⟨x.2, fun i => congrFun hx i⟩
    rw [hS] at hx0
    exact Subtype.ext ((Submodule.mem_bot K).1 hx0)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have h44 : Module.finrank K (Fin 4 → K) = 4 := by simp
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)).1 hinj
  choose v hv using fun j : Fin 4 => hsurj (Pi.single j 1)
  have hv' : ∀ j i, (v j).1 (i, S i) = if i = j then 1 else 0 := by
    intro j i
    rw [← hΦ, hv, Pi.single_apply]
  have hskew : ∀ i k, mq i * (v k).1 (i, !S i) = -(mq k * (v i).1 (k, !S k)) := by
    intro i k
    have hB := hiso _ (v i).2 _ (v k).2
    rw [bil_chart S] at hB
    simp only [hv', ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, mul_add,
      sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hB
    linear_combination hB
  refine no_chart S (fun i k => mq i * (v k).1 (i, !S i)) hskew fun a => ?_
  have hmem : (∑ j, a j • (v j).1) ∈ L := L.sum_mem fun j _ => L.smul_mem _ (v j).2
  have hpt : pt S (fun i k => mq i * (v k).1 (i, !S i)) a = ∑ j, a j • (v j).1 := by
    funext ⟨i, b⟩
    simp only [pt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hbS : b = S i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hbS), hbS]
      simp [hv']
    · have hb' : b = !S i := by
        cases b <;> cases hS : S i <;> simp_all
      rw [ite_eq_right_of_eq_false _ _ (eq_false hbS), hb', div_eq_iff (mq_ne_zero i),
        Finset.sum_mul]
      exact sum_congr rfl fun k _ => by ring
  rw [hpt]
  exact h _ hmem

theorem endgame (no_chart : ∀ (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → K),
    (∀ i k, s i k = -s k i) → (∀ a, cubic (pt S s a) = 0) → False) :
    ¬ (∃ L : Submodule (ZMod 5) (Fin 3 × Fin 3 → ZMod 5), Module.finrank (ZMod 5) L = 4 ∧
      ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 3) => (1 : ZMod 5) + t (i,j)) = 6) := by
  rintro ⟨L,hr,h⟩
  have hle : L ≤ LinearMap.range fmap := fun t ht => ⟨back t, invert t (sum_zero L h t ht)⟩
  have hm : (L.comap fmap).map fmap = L := Submodule.map_comap_eq_of_le hle
  have hdim := Submodule.finrank_map_le fmap (L.comap fmap)
  have hl := finrank_le_three (L.comap fmap) no_chart (fun x hx y hy => iso L h x hx y hy)
    (fun x hx => vanish L h x hx)
  rw [hm,hr] at hdim
  omega
end PEqualNP.Outside.L_gct_226_aux

open PEqualNP.Outside.L_gct_226_aux in
theorem PEqualNP.Outside.L_gct_226 : ¬ (∃ L : Submodule (ZMod 5) (Fin 3 × Fin 3 → ZMod 5), Module.finrank (ZMod 5) L = 4 ∧ ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 3) => (1 : ZMod 5) + t (i, j)) = 6) := endgame excluded
