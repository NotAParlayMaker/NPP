import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1777

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem difp {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a h := by simp [h]

def fd {α : Type} (F : Gate → List α → α) (X : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [F g w]) X

theorem fd_snoc {α : Type} (F : Gate → List α → α) (X : List α) (gs : List Gate) (g : Gate) :
    fd F X (gs ++ [g]) = fd F X gs ++ [F g (fd F X gs)] := by
  simp [fd, List.foldl_append]

theorem fd_app {α : Type} (F : Gate → List α → α) (X : List α) (gs hs : List Gate) :
    fd F X (gs ++ hs) = fd F (fd F X gs) hs := by
  simp [fd, List.foldl_append]

def stpF : Gate → List Bool → Bool :=
  fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

def ldF : Gate → List ℕ → ℕ :=
  fun g d => g.lineDegree d

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = fd stpF x C.gates := rfl

theorem ld_eq (C : Circuit) (n : ℕ) (M : Finset ℕ) :
    C.lineDegrees n M = fd ldF ((List.range n).map fun i => if i ∈ M then 1 else 0) C.gates :=
  rfl

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ifn (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ifn (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem stp_or (a b : ℕ) (w : List Bool) :
    stpF ⟨GateOp.or, [a, b]⟩ w = (w.getD a false || w.getD b false) := by
  simp [stpF, GateOp.eval]

theorem stp_and (a b : ℕ) (w : List Bool) :
    stpF ⟨GateOp.and, [a, b]⟩ w = (w.getD a false && w.getD b false) := by
  simp [stpF, GateOp.eval]

theorem ld_or (a b : ℕ) (d : List ℕ) :
    ldF ⟨GateOp.or, [a, b]⟩ d = max (d.getD a 0) (d.getD b 0) := by
  simp [ldF, Gate.lineDegree]

theorem ld_and (a b : ℕ) (d : List ℕ) :
    ldF ⟨GateOp.and, [a, b]⟩ d = d.getD a 0 + d.getD b 0 := by
  unfold ldF Gate.lineDegree
  split_ifs with hc
  · simp
  · exact absurd rfl hc

def top (f K0 k : ℕ) : ℕ := if k = 0 then f else K0 + k - 1

def chain (f K0 : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => chain f K0 k ++ [⟨GateOp.or, [top f K0 k, f + k + 1]⟩]

theorem chain_len (f K0 : ℕ) : ∀ k, (chain f K0 k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [chain, ih]

theorem chain_mem (f K0 : ℕ) : ∀ k, ∀ g ∈ chain f K0 k,
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  intro k
  induction k with
  | zero => intro g hg; simp [chain] at hg
  | succ k ih =>
    intro g hg
    simp only [chain, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · subst hg
      exact ⟨rfl, rfl⟩

theorem top_lt (f K0 k : ℕ) (h : f < K0) : top f K0 k < K0 + k := by
  unfold top
  split_ifs <;> omega

theorem chain_gen {α : Type} (F : Gate → List α → α) (dflt : α) (f K0 : ℕ) (X : List α)
    (hX : X.length = K0) : ∀ k,
    (fd F X (chain f K0 k)).length = K0 + k ∧
    ∀ i, i < K0 → (fd F X (chain f K0 k)).getD i dflt = X.getD i dflt := by
  intro k
  induction k with
  | zero => exact ⟨by simp [fd, chain, hX], fun i _ => by simp [fd, chain]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [chain, fd_snoc]
      simp [h1]
      omega
    · intro i hi
      rw [chain, fd_snoc, getD_snoc, ifn (by omega)]
      exact h2 i hi

theorem chain_val (f K0 : ℕ) (X : List Bool) (hX : X.length = K0) : ∀ k, f + k < K0 →
    (fd stpF X (chain f K0 k)).getD (top f K0 k) false =
      decide (∃ t, t ≤ k ∧ X.getD (f + t) false = true) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [fd, chain, top]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    obtain ⟨h1, h2⟩ := chain_gen stpF false f K0 X hX k
    have ht : top f K0 (k + 1) = (fd stpF X (chain f K0 k)).length := by
      rw [h1]
      unfold top
      rw [ifn (by omega)]
      omega
    rw [chain, fd_snoc, getD_snoc, ifp ht, stp_or, ih', h2 _ (by omega)]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨t, ht1, ht2⟩ | h)
      · exact ⟨t, by omega, ht2⟩
      · exact ⟨k + 1, le_refl _, h⟩
    · rintro ⟨t, ht1, ht2⟩
      rcases Nat.lt_or_ge t (k + 1) with h | h
      · exact Or.inl ⟨t, by omega, ht2⟩
      · have : t = k + 1 := by omega
        subst this
        exact Or.inr ht2

theorem chain_deg (f K0 : ℕ) (X : List ℕ) (hX : X.length = K0) : ∀ k, f + k < K0 →
    (∀ t, t ≤ k → 0 < X.getD (f + t) 0) →
    0 < (fd ldF X (chain f K0 k)).getD (top f K0 k) 0 := by
  intro k
  induction k with
  | zero =>
    intro _ h
    have := h 0 (le_refl _)
    simpa [fd, chain, top] using this
  | succ k _ =>
    intro hk h
    obtain ⟨h1, h2⟩ := chain_gen ldF 0 f K0 X hX k
    have ht : top f K0 (k + 1) = (fd ldF X (chain f K0 k)).length := by
      rw [h1]
      unfold top
      rw [ifn (by omega)]
      omega
    rw [chain, fd_snoc, getD_snoc, ifp ht, ld_or, h2 (f + k + 1) (by omega)]
    have := h (k + 1) (le_refl _)
    rw [← Nat.add_assoc] at this
    exact lt_of_lt_of_le this (le_max_right _ _)

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem mark_getD (K : ℕ) (M : Finset ℕ) (i : ℕ) (hi : i < K) (hM : i ∈ M) :
    ((List.range K).map fun i => if i ∈ M then 1 else 0).getD i 0 = 1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp [hM]

def gl (a b : ℕ) : List Gate :=
  chain 0 (a + 1 + (b + 1)) a ++ chain (a + 1) (a + 1 + (b + 1) + a) b ++
    [⟨GateOp.and, [top 0 (a + 1 + (b + 1)) a, top (a + 1) (a + 1 + (b + 1) + a) b]⟩] ++
    [⟨GateOp.and, [a + 1 + (b + 1) + a + b, a + 1 + (b + 1) + a + b]⟩]

theorem gl_len (a b : ℕ) : (gl a b).length = a + b + 2 := by
  simp [gl, chain_len]
  omega

theorem gl_last (a b : ℕ) : (gl a b).getD (a + b + 1) ⟨GateOp.or, []⟩ =
    ⟨GateOp.and, [a + 1 + (b + 1) + a + b, a + 1 + (b + 1) + a + b]⟩ := by
  unfold gl
  rw [getD_snoc, ifp (by simp [chain_len]; omega)]

theorem gl_mono (a b : ℕ) : Monotone2 ⟨gl a b, a + 1 + (b + 1) + a + b + 1⟩ := by
  intro g hg
  simp only [gl, List.mem_append, List.mem_singleton] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · obtain ⟨h1, h2⟩ := chain_mem _ _ _ g hg
    exact ⟨Or.inr h1, h2.le⟩
  · obtain ⟨h1, h2⟩ := chain_mem _ _ _ g hg
    exact ⟨Or.inr h1, h2.le⟩
  · subst hg
    exact ⟨Or.inl rfl, le_refl _⟩
  · subst hg
    exact ⟨Or.inl rfl, le_refl _⟩

theorem gl_val (a b : ℕ) (X : List Bool) (hX : X.length = a + 1 + (b + 1)) :
    (fd stpF X (gl a b)).getD (a + 1 + (b + 1) + a + b + 1) false =
      (decide (∃ t, t ≤ a ∧ X.getD (0 + t) false = true) &&
        decide (∃ t, t ≤ b ∧ X.getD (a + 1 + t) false = true)) := by
  obtain ⟨p1, p2⟩ := chain_gen stpF false 0 (a + 1 + (b + 1)) X hX a
  have v1 := chain_val 0 (a + 1 + (b + 1)) X hX a (by omega)
  obtain ⟨q1, q2⟩ := chain_gen stpF false (a + 1) (a + 1 + (b + 1) + a)
    (fd stpF X (chain 0 (a + 1 + (b + 1)) a)) p1 b
  have v2 := chain_val (a + 1) (a + 1 + (b + 1) + a)
    (fd stpF X (chain 0 (a + 1 + (b + 1)) a)) p1 b (by omega)
  have e2 : (∃ t, t ≤ b ∧ (fd stpF X (chain 0 (a + 1 + (b + 1)) a)).getD (a + 1 + t) false = true)
      ↔ ∃ t, t ≤ b ∧ X.getD (a + 1 + t) false = true := by
    constructor
    · rintro ⟨t, ht, h⟩
      rw [p2 _ (by omega)] at h
      exact ⟨t, ht, h⟩
    · rintro ⟨t, ht, h⟩
      rw [← p2 _ (by omega)] at h
      exact ⟨t, ht, h⟩
  have hP := q2 (top 0 (a + 1 + (b + 1)) a) (by
    have := top_lt 0 (a + 1 + (b + 1)) a (by omega)
    omega)
  unfold gl
  rw [fd_snoc, fd_snoc, fd_app]
  have l3 : (fd stpF (fd stpF X (chain 0 (a + 1 + (b + 1)) a))
      (chain (a + 1) (a + 1 + (b + 1) + a) b)).length = a + 1 + (b + 1) + a + b := q1
  rw [getD_snoc, ifp (by simp [l3]), stp_and, getD_snoc, ifp (by simp [l3]), stp_and, hP, v1, v2,
    Bool.and_self, decide_eq_decide.mpr e2]

theorem gl_deg (a b : ℕ) (X : List ℕ) (hX : X.length = a + 1 + (b + 1))
    (hpos : ∀ t, t ≤ b → 0 < X.getD (a + 1 + t) 0) :
    0 < (fd ldF X (gl a b)).getD (a + 1 + (b + 1) + a + b) 0 := by
  obtain ⟨p1, p2⟩ := chain_gen ldF 0 0 (a + 1 + (b + 1)) X hX a
  obtain ⟨q1, q2⟩ := chain_gen ldF 0 (a + 1) (a + 1 + (b + 1) + a)
    (fd ldF X (chain 0 (a + 1 + (b + 1)) a)) p1 b
  have v2 := chain_deg (a + 1) (a + 1 + (b + 1) + a)
    (fd ldF X (chain 0 (a + 1 + (b + 1)) a)) p1 b (by omega) (by
      intro t ht
      rw [p2 _ (by omega)]
      exact hpos t ht)
  unfold gl
  rw [fd_snoc, fd_snoc, fd_app]
  have l3 : (fd ldF (fd ldF X (chain 0 (a + 1 + (b + 1)) a))
      (chain (a + 1) (a + 1 + (b + 1) + a) b)).length = a + 1 + (b + 1) + a + b := q1
  rw [getD_snoc, ifn (by simp [l3]), getD_snoc, ifp (by simp [l3]), ld_and]
  omega

theorem main (a b : ℕ) : ∃ C : Circuit, Monotone2 C ∧ C.size = a + 1 + (b + 1) ∧
    (∀ z : Fin (a + 1 + (b + 1)) → Bool, circuitFun (a + 1 + (b + 1)) C z =
      decide (∃ p : Fin (a + 1), ∃ j : Fin (b + 1),
        z (Fin.castAdd (b + 1) p) = true ∧ z (Fin.natAdd (a + 1) j) = true)) ∧
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ i ∈ (gateAt C j).inputs,
        0 < (C.lineDegrees (a + 1 + (b + 1)) (Finset.Ico (a + 1) (a + 1 + (b + 1)))).getD i 0 := by
  refine ⟨⟨gl a b, a + 1 + (b + 1) + a + b + 1⟩, gl_mono a b, ?_, ?_, ?_⟩
  · show (gl a b).length = _
    rw [gl_len]
    omega
  · intro z
    show (fd stpF (List.ofFn z) (gl a b)).getD (a + 1 + (b + 1) + a + b + 1) false = _
    rw [gl_val a b _ List.length_ofFn, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨t, ht, h1⟩, ⟨s, hs, h2⟩⟩
      rw [ofFn_getD, difp (by omega)] at h1 h2
      refine ⟨⟨t, by omega⟩, ⟨s, by omega⟩, ?_, ?_⟩
      · rw [← h1]
        congr 1
        apply Fin.ext
        simp
      · rw [← h2]
        congr 1
    · rintro ⟨p, j, h1, h2⟩
      refine ⟨⟨p.val, by omega, ?_⟩, ⟨j.val, by omega, ?_⟩⟩
      · rw [ofFn_getD, difp (by omega), ← h1]
        congr 1
        apply Fin.ext
        simp
      · rw [ofFn_getD, difp (by omega), ← h2]
        congr 1
  · refine ⟨a + b + 1, ?_, ?_⟩
    · show a + b + 1 < (gl a b).length
      rw [gl_len]
      omega
    · have hg : gateAt ⟨gl a b, a + 1 + (b + 1) + a + b + 1⟩ (a + b + 1) =
          ⟨GateOp.and, [a + 1 + (b + 1) + a + b, a + 1 + (b + 1) + a + b]⟩ := gl_last a b
      rw [hg]
      refine ⟨rfl, rfl, ?_⟩
      intro i hi
      have hi' : i = a + 1 + (b + 1) + a + b := by simpa using hi
      subst hi'
      rw [ld_eq]
      apply gl_deg a b _ (by simp)
      intro t ht
      rw [mark_getD _ _ _ (by omega) (by simp; omega)]
      exact Nat.one_pos

end PEqualNP.Outside.L_meta_1777

theorem PEqualNP.Outside.L_meta_1777 : ∀ n m : ℕ, 0 < n → 0 < m → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = n + m ∧ (∀ z : Fin (n + m) → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) C z = decide (∃ p : Fin n, ∃ j : Fin m, z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n j) = true)) ∧ ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 := by
  intro n m hn hm
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  exact PEqualNP.Outside.L_meta_1777.main a b
