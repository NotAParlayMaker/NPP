import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def codeFn (a b c d : ℕ) : ℕ :=
  (15 * Min.min a b + Max.max a b) * 225 + (15 * Min.min c d + Max.max c d)

def lift9 (σ : Equiv.Perm (Fin 14)) (w : Fin 15) : ℕ :=
  if (w : ℕ) < 14 then ↑(σ (Fin.ofNat 14 ↑w)) else 14

theorem lift9_lt (σ : Equiv.Perm (Fin 14)) (w : Fin 15) : lift9 σ w < 15 := by
  unfold lift9
  split_ifs with h
  · exact Nat.lt_trans (σ (Fin.ofNat 14 ↑w)).isLt (by decide)
  · decide

def liftFin (σ : Equiv.Perm (Fin 14)) (w : Fin 15) : Fin 15 :=
  ⟨lift9 σ w, lift9_lt σ w⟩

theorem ofNat14_eq {k : ℕ} (hk : k < 14) : Fin.ofNat 14 k = ⟨k, hk⟩ := by
  ext
  change k % 14 = k
  exact Nat.mod_eq_of_lt hk

theorem lift9_comp (σ π : Equiv.Perm (Fin 14)) (w : Fin 15) :
    lift9 π (liftFin σ w) = lift9 (σ.trans π) w := by
  unfold liftFin lift9
  by_cases hw : (w : ℕ) < 14
  · have hlt : ((σ (Fin.ofNat 14 ↑w)) : ℕ) < 14 := (σ (Fin.ofNat 14 ↑w)).isLt
    simp only [hw, ↓reduceIte, hlt, Equiv.trans_apply]
    congr 2
    exact ofNat14_eq hlt
  · simp [hw]

theorem liftFin_injective (σ : Equiv.Perm (Fin 14)) : Function.Injective (liftFin σ) := by
  intro w1 w2 h
  have hv : lift9 σ w1 = lift9 σ w2 := congrArg Fin.val h
  unfold lift9 at hv
  by_cases h1 : (w1 : ℕ) < 14 <;> by_cases h2 : (w2 : ℕ) < 14
  · simp only [h1, h2, ↓reduceIte] at hv
    have hinj := σ.injective (Fin.ext hv)
    rw [ofNat14_eq h1, ofNat14_eq h2] at hinj
    have hv12 : (w1 : ℕ) = (w2 : ℕ) := congrArg (@Fin.val 14) hinj
    exact Fin.ext hv12
  · simp only [h1, h2, ↓reduceIte] at hv
    exact absurd hv (Nat.ne_of_lt (σ _).isLt)
  · simp only [h1, h2, ↓reduceIte] at hv
    exact absurd hv.symm (Nat.ne_of_lt (σ _).isLt)
  · simp only [h1, h2, ↓reduceIte] at hv
    have hw1 : (w1 : ℕ) = 14 := by omega
    have hw2 : (w2 : ℕ) = 14 := by omega
    exact Fin.ext (hw1.trans hw2.symm)

theorem codeFn_swap_left (a b c d : ℕ) : codeFn b a c d = codeFn a b c d := by
  unfold codeFn; omega

theorem codeFn_swap_right (a b c d : ℕ) : codeFn a b d c = codeFn a b c d := by
  unfold codeFn; omega

theorem gateOp_comm {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or) (a b : Bool) :
    op.eval [a, b] = op.eval [b, a] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> rfl

def wmap (σ : Equiv.Perm (Fin 14)) (k : ℕ) : ℕ :=
  if hk : k < 14 then (σ ⟨k, hk⟩).val else k

def mapGate (σ : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap σ)⟩

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def RelW (σ : Equiv.Perm (Fin 14)) (W W' : List Bool) : Prop :=
  14 ≤ W.length ∧ W'.length = W.length ∧
    ∀ k : ℕ, W'.getD (wmap σ k) false = W.getD k false

theorem getD_snoc_lt {l : List Bool} (b : Bool) {k : ℕ} (hk : k < l.length) :
    (l ++ [b]).getD k false = l.getD k false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_snoc_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl l.length)]
  simp

theorem getD_snoc_eq_of_len {l : List Bool} (b : Bool) {k : ℕ} (hk : l.length = k) :
    (l ++ [b]).getD k false = b := by
  subst hk
  exact getD_snoc_eq l b

theorem relW_step (σ : Equiv.Perm (Fin 14)) {W W' : List Bool} (g : Gate)
    (hrel : RelW σ W W') :
    RelW σ (stepW W g) (stepW W' (mapGate σ g)) := by
  obtain ⟨h14, hlen, hget⟩ := hrel
  have hval : (mapGate σ g).op.eval ((mapGate σ g).inputs.map fun i => W'.getD i false) =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [mapGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hget k
  refine ⟨by simp [stepW]; omega, by simp [stepW, hlen], ?_⟩
  intro k
  dsimp only [stepW]
  rw [hval]
  rcases Nat.lt_trichotomy k W.length with hlt | heq | hgt
  · have hlt' : wmap σ k < W'.length := by
      unfold wmap
      split_ifs with hk
      · exact Nat.lt_of_lt_of_le (σ ⟨k, hk⟩).isLt (by omega)
      · omega
    rw [getD_snoc_lt _ hlt', getD_snoc_lt _ hlt, hget k]
  · subst heq
    have hw : wmap σ W.length = W'.length := by
      unfold wmap
      split_ifs with hk
      · omega
      · exact hlen.symm
    rw [hw, getD_snoc_eq, getD_snoc_eq]
  · have hgt' : W'.length + 1 ≤ wmap σ k := by
      unfold wmap
      split_ifs with hk <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

theorem relW_foldl (σ : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ {W W' : List Bool}, RelW σ W W' →
      RelW σ (gs.foldl stepW W) ((gs.map (mapGate σ)).foldl stepW W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih (relW_step σ g h)

theorem extract_two {l : List ℕ} (hlen : l.length = 2) (hnd : l.Nodup) :
    ∃ x y : ℕ, l = [x, y] ∧ x ≠ y := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp at hlen
  · simp at hlen
  · simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil, and_true] at hnd
    exact ⟨x, y, rfl, hnd.1⟩
  · simp at hlen

theorem min_max_pair_eval {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (V : Fin n → Bool) (p q : Fin n) :
    op.eval [V p, V q] = op.eval [V (min p q), V (max p q)] := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
  · rw [min_eq_right hqp, max_eq_left hqp, gateOp_comm hop]

theorem main_3010 :
    ∀ (f : (Fin 14 → Bool) → Bool) (C : Circuit),
      IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      2 ≤ C.size →
      C.size ≤ 26 →
      (∀ y : Fin 14 → Bool, C.eval (List.ofFn y) = f y) →
      ∃ (x10 x11 : Fin 14) (x12 x13 : Fin 15) (x14 x15 : GateOp) (x16 : Circuit),
        x10 < x11 ∧
        x12 < x13 ∧
        (x14 = GateOp.and ∨ x14 = GateOp.or) ∧
        (x15 = GateOp.and ∨ x15 = GateOp.or) ∧
        (∀ π : Equiv.Perm (Fin 14),
          (∀ y : Fin 14 → Bool, f (y ∘ ⇑π) = f y) →
          codeFn ↑x10 ↑x11 ↑x12 ↑x13 ≤
            codeFn (↑(π x10)) (↑(π x11)) (lift9 π x12) (lift9 π x13)) ∧
        Monotone2 x16 ∧
        x16.size ≤ 24 ∧
        ∀ y : Fin 14 → Bool,
          let w18 : List Bool := List.ofFn y ++ [x14.eval [y x10, y x11]]
          x16.eval (w18 ++ [x15.eval [w18.getD (↑x12) false, w18.getD (↑x13) false]]) = f y := by
  classical
  intro f C hao hnd hge2 hle26 heval
  obtain ⟨hao_ops, hrb, hlen2⟩ := hao
  rcases hgs : C.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · exfalso; change C.gates.length ≥ 2 at hge2; simp [hgs] at hge2
  · exfalso; change C.gates.length ≥ 2 at hge2; simp [hgs] at hge2
  have hrest_le : rest.length ≤ 24 := by
    change C.gates.length ≤ 26 at hle26
    rw [hgs] at hle26; simp at hle26; omega
  have hg0_mem : g0 ∈ C.gates := by simp [hgs]
  have hg1_mem : g1 ∈ C.gates := by simp [hgs]
  have hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or := hao_ops g0 hg0_mem
  have hop1 : g1.op = GateOp.and ∨ g1.op = GateOp.or := hao_ops g1 hg1_mem
  obtain ⟨u0n, v0n, hg0_in, huv0_ne⟩ := extract_two (hlen2 g0 hg0_mem) (hnd g0 hg0_mem)
  obtain ⟨a0n, b0n, hg1_in, hab0_ne⟩ := extract_two (hlen2 g1 hg1_mem) (hnd g1 hg1_mem)
  have hg0_at : gateAt C 0 = g0 := by simp [gateAt, hgs]
  have hg1_at : gateAt C 1 = g1 := by simp [gateAt, hgs]
  have h0_lt : 0 < C.gates.length := by simp [hgs]
  have h1_lt : 1 < C.gates.length := by simp [hgs]
  have hu0_lt : u0n < 14 := by
    have := hrb 0 h0_lt u0n (by rw [hg0_at, hg0_in]; simp)
    omega
  have hv0_lt : v0n < 14 := by
    have := hrb 0 h0_lt v0n (by rw [hg0_at, hg0_in]; simp)
    omega
  have ha0_lt : a0n < 15 := by
    have := hrb 1 h1_lt a0n (by rw [hg1_at, hg1_in]; simp)
    omega
  have hb0_lt : b0n < 15 := by
    have := hrb 1 h1_lt b0n (by rw [hg1_at, hg1_in]; simp)
    omega
  let u0 : Fin 14 := ⟨u0n, hu0_lt⟩
  let v0 : Fin 14 := ⟨v0n, hv0_lt⟩
  let a0 : Fin 15 := ⟨a0n, ha0_lt⟩
  let b0 : Fin 15 := ⟨b0n, hb0_lt⟩
  have huv0 : u0 ≠ v0 := fun h => huv0_ne (congrArg Fin.val h)
  have hab0 : a0 ≠ b0 := fun h => hab0_ne (congrArg Fin.val h)
  let score : Equiv.Perm (Fin 14) → ℕ :=
    fun σ => codeFn ↑(σ u0) ↑(σ v0) (lift9 σ a0) (lift9 σ b0)
  let A : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter (fun σ => ∀ y : Fin 14 → Bool, f (y ∘ ⇑σ) = f y)
  have h1_mem : (1 : Equiv.Perm (Fin 14)) ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    intro y; rfl
  obtain ⟨σ, hσA, hσ_min⟩ := Finset.exists_min_image A score ⟨1, h1_mem⟩
  have hσ_aut : ∀ y : Fin 14 → Bool, f (y ∘ ⇑σ) = f y :=
    (Finset.mem_filter.mp hσA).2
  let x10 : Fin 14 := min (σ u0) (σ v0)
  let x11 : Fin 14 := max (σ u0) (σ v0)
  let x12 : Fin 15 := min (liftFin σ a0) (liftFin σ b0)
  let x13 : Fin 15 := max (liftFin σ a0) (liftFin σ b0)
  have hx10_lt : x10 < x11 := by
    have hne : σ u0 ≠ σ v0 := σ.injective.ne huv0
    rcases lt_or_gt_of_ne hne with h | h
    · simpa [x10, x11, min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)] using h
    · simpa [x10, x11, min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)] using h
  have hx12_lt : x12 < x13 := by
    have hne : liftFin σ a0 ≠ liftFin σ b0 := (liftFin_injective σ).ne hab0
    rcases lt_or_gt_of_ne hne with h | h
    · simpa [x12, x13, min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)] using h
    · simpa [x12, x13, min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)] using h
  let D : Circuit := ⟨rest.map (mapGate σ), wmap σ C.output⟩
  have hD_mono : Monotone2 D := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have hg'_mem : g' ∈ C.gates := by simp [hgs, hg']
    refine ⟨?_, ?_⟩
    · simpa [mapGate] using hao_ops g' hg'_mem
    · simp [mapGate, hlen2 g' hg'_mem]
  have hD_sz : D.size ≤ 24 := by
    change (rest.map (mapGate σ)).length ≤ 24
    simpa using hrest_le
  have hscore_eq : codeFn ↑x10 ↑x11 ↑x12 ↑x13 = score σ := by
    dsimp only [score]
    have h1 : (x10 : ℕ) = Min.min ↑(σ u0) ↑(σ v0) ∧ (x11 : ℕ) = Max.max ↑(σ u0) ↑(σ v0) := by
      rcases le_total (σ u0) (σ v0) with h | h
      · have hv : (σ u0 : ℕ) ≤ (σ v0 : ℕ) := h
        simp [x10, x11, min_eq_left h, max_eq_right h, Nat.min_eq_left hv, Nat.max_eq_right hv]
      · have hv : (σ v0 : ℕ) ≤ (σ u0 : ℕ) := h
        simp [x10, x11, min_eq_right h, max_eq_left h, Nat.min_eq_right hv, Nat.max_eq_left hv]
    have h2 : (x12 : ℕ) = Min.min (lift9 σ a0) (lift9 σ b0) ∧
        (x13 : ℕ) = Max.max (lift9 σ a0) (lift9 σ b0) := by
      rcases le_total (liftFin σ a0) (liftFin σ b0) with h | h
      · have hv : lift9 σ a0 ≤ lift9 σ b0 := h
        simp [x12, x13, liftFin, min_eq_left h, max_eq_right h, Nat.min_eq_left hv, Nat.max_eq_right hv]
      · have hv : lift9 σ b0 ≤ lift9 σ a0 := h
        simp [x12, x13, liftFin, min_eq_right h, max_eq_left h, Nat.min_eq_right hv, Nat.max_eq_left hv]
    rw [h1.1, h1.2, h2.1, h2.2]
    unfold codeFn
    omega
  refine ⟨x10, x11, x12, x13, g0.op, g1.op, D, hx10_lt, hx12_lt, hop0, hop1, ?_, hD_mono, hD_sz, ?_⟩
  · intro π hπ
    rw [hscore_eq]
    let τ : Equiv.Perm (Fin 14) := σ.trans π
    have hτA : τ ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      intro y
      have hcomp : (y ∘ ⇑τ) = ((y ∘ ⇑π) ∘ ⇑σ) := rfl
      rw [hcomp, hσ_aut (y ∘ ⇑π), hπ y]
    have hle := hσ_min τ hτA
    suffices heq : score τ = codeFn (↑(π x10)) (↑(π x11)) (lift9 π x12) (lift9 π x13) by
      omega
    dsimp only [score, τ]
    have hL : ∀ c d : ℕ,
        codeFn (↑(π (σ u0))) (↑(π (σ v0))) c d = codeFn (↑(π x10)) (↑(π x11)) c d := by
      intro c d
      rcases le_total (σ u0) (σ v0) with h | h
      · simp [x10, x11, min_eq_left h, max_eq_right h]
      · simp [x10, x11, min_eq_right h, max_eq_left h]
        exact codeFn_swap_left _ _ _ _
    have hR : codeFn (↑(π x10)) (↑(π x11)) (lift9 (σ.trans π) a0) (lift9 (σ.trans π) b0) =
        codeFn (↑(π x10)) (↑(π x11)) (lift9 π x12) (lift9 π x13) := by
      rw [← lift9_comp σ π a0, ← lift9_comp σ π b0]
      rcases le_total (liftFin σ a0) (liftFin σ b0) with h | h
      · simp [x12, x13, min_eq_left h, max_eq_right h]
      · simp [x12, x13, min_eq_right h, max_eq_left h]
        exact codeFn_swap_right _ _ _ _
    simpa only [Equiv.trans_apply] using (hL _ _).trans hR
  · intro y
    dsimp only
    set w18 : List Bool := List.ofFn y ++ [g0.op.eval [y x10, y x11]]
    set W16D : List Bool := w18 ++ [g1.op.eval [w18.getD (↑x12) false, w18.getD (↑x13) false]]
    let x : Fin 14 → Bool := y ∘ ⇑σ
    let w0C : List Bool := List.ofFn x
    let w15C : List Bool := stepW w0C g0
    let W16C : List Bool := stepW w15C g1
    have hw0C_get : ∀ i : Fin 14, w0C.getD i.val false = y (σ i) := by
      intro i
      dsimp only [w0C, x]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [i.isLt]
    have hw18_lt14 : ∀ i : Fin 14, w18.getD i.val false = y i := by
      intro i
      dsimp only [w18]
      rw [getD_snoc_lt _ (by simp [i.isLt]), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [i.isLt]
    have hg0_val : g0.op.eval (g0.inputs.map fun i => w0C.getD i false) =
        g0.op.eval [y x10, y x11] := by
      rw [hg0_in]
      simp only [List.map]
      have hu : w0C.getD u0n false = y (σ u0) := hw0C_get u0
      have hv : w0C.getD v0n false = y (σ v0) := hw0C_get v0
      rw [hu, hv]
      exact min_max_pair_eval g0.op hop0 y (σ u0) (σ v0)
    have hw15_rel : ∀ w : Fin 15, w15C.getD w.val false = w18.getD (liftFin σ w).val false := by
      intro w
      dsimp only [w15C, stepW, liftFin, lift9]
      by_cases hw : (w : ℕ) < 14
      · simp only [hw, ↓reduceIte]
        rw [getD_snoc_lt _ (by simp [w0C, hw]), ofNat14_eq hw]
        rw [hw0C_get ⟨w.val, hw⟩, hw18_lt14 (σ ⟨w.val, hw⟩)]
      · have hw14 : (w : ℕ) = 14 := by omega
        rw [hw14]
        simp only [Nat.lt_irrefl, ↓reduceIte]
        rw [getD_snoc_eq_of_len _ (by simp [w0C]), hg0_val]
        dsimp only [w18]
        rw [getD_snoc_eq_of_len _ (by simp)]
    have hg1_val : g1.op.eval (g1.inputs.map fun i => w15C.getD i false) =
        g1.op.eval [w18.getD (↑x12) false, w18.getD (↑x13) false] := by
      rw [hg1_in]
      simp only [List.map]
      have ha : w15C.getD a0n false = w18.getD (liftFin σ a0).val false := hw15_rel a0
      have hb : w15C.getD b0n false = w18.getD (liftFin σ b0).val false := hw15_rel b0
      rw [ha, hb]
      exact min_max_pair_eval g1.op hop1 (fun z : Fin 15 => w18.getD z.val false)
        (liftFin σ a0) (liftFin σ b0)
    have hRel16 : RelW σ W16C W16D := by
      refine ⟨by simp [W16C, w15C, w0C, stepW], by simp [W16D, w18, W16C, w15C, w0C, stepW], ?_⟩
      intro k
      by_cases hk14 : k < 14
      · have hwmap : wmap σ k = (σ ⟨k, hk14⟩).val := by
          unfold wmap; split_ifs; rfl
        rw [hwmap]
        have hltD : (σ ⟨k, hk14⟩).val < w18.length := by
          simp [w18]; exact Nat.lt_trans (σ ⟨k, hk14⟩).isLt (by decide)
        have hltC1 : k < w15C.length := by simp [w15C, w0C, stepW]; omega
        have hltC0 : k < w0C.length := by simp [w0C]; exact hk14
        dsimp only [W16D, W16C, stepW]
        rw [getD_snoc_lt _ hltD, hw18_lt14 (σ ⟨k, hk14⟩), getD_snoc_lt _ hltC1]
        dsimp only [w15C, stepW]
        rw [getD_snoc_lt _ hltC0, hw0C_get ⟨k, hk14⟩]
      · have hwmap : wmap σ k = k := by
          unfold wmap; split_ifs; rfl
        rw [hwmap]
        by_cases hk15 : k = 14
        · subst hk15
          have hltD14 : 14 < w18.length := by simp [w18]
          have hltC14 : 14 < w15C.length := by simp [w15C, w0C, stepW]
          dsimp only [W16D, W16C, stepW]
          rw [getD_snoc_lt _ hltD14, getD_snoc_lt _ hltC14]
          dsimp only [w18, w15C, stepW]
          rw [getD_snoc_eq_of_len _ (by simp), getD_snoc_eq_of_len _ (by simp [w0C]), hg0_val]
        · by_cases hk16 : k = 15
          · subst hk16
            dsimp only [W16D, W16C, stepW]
            have hlD15 : w18.length = 15 := by simp [w18]
            have hlC15 : w15C.length = 15 := by simp [w15C, w0C, stepW]
            rw [getD_snoc_eq_of_len _ hlD15, getD_snoc_eq_of_len _ hlC15, hg1_val]
          · rw [List.getD_eq_default _ _ (by simp [W16D, w18]; omega),
              List.getD_eq_default _ _ (by simp [W16C, w15C, w0C, stepW]; omega)]
    have hRelFinal := relW_foldl σ rest hRel16
    have hevD : D.eval W16D = C.eval w0C := by
      change ((rest.map (mapGate σ)).foldl stepW W16D).getD (wmap σ C.output) false =
        (C.gates.foldl stepW w0C).getD C.output false
      rw [hgs, List.foldl_cons, List.foldl_cons]
      exact hRelFinal.2.2 C.output
    rw [hevD, heval x, hσ_aut y]

end PEqualNP.Outside.L_meta_3010

theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  exact PEqualNP.Outside.L_meta_3010.main_3010
