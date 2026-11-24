import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rho (σ : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ :=
  if h : i < 14 then (σ ⟨i, h⟩ : ℕ) else i

def gmap (σ : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rho σ)⟩

def Inv (σ : Equiv.Perm (Fin 14)) (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ 14 ≤ W.length ∧ ∀ i, W.getD i false = W'.getD (rho σ i) false

def code (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

lemma rho_pos (σ : Equiv.Perm (Fin 14)) (i : ℕ) (h : i < 14) : rho σ i = (σ ⟨i, h⟩ : ℕ) := by
  unfold rho
  split
  · rfl
  · contradiction

lemma rho_lt (σ : Equiv.Perm (Fin 14)) (i : ℕ) (h : i < 14) : rho σ i < 14 := by
  rw [rho_pos σ i h]
  exact (σ ⟨i, h⟩).isLt

lemma rho_ge (σ : Equiv.Perm (Fin 14)) (i : ℕ) (h : 14 ≤ i) : rho σ i = i := by
  unfold rho
  split
  · omega
  · rfl

lemma rho_val (σ : Equiv.Perm (Fin 14)) (p : Fin 14) : rho σ p.val = (σ p : ℕ) := by
  rw [rho_pos σ p.val p.isLt]

lemma rho_inj (σ : Equiv.Perm (Fin 14)) (i j : ℕ) (h : rho σ i = rho σ j) : i = j := by
  by_cases hi : i < 14 <;> by_cases hj : j < 14
  · rw [rho_pos σ i hi, rho_pos σ j hj] at h
    have h2 := σ.injective (Fin.ext h)
    exact congrArg Fin.val h2
  · have h1 := rho_lt σ i hi
    rw [rho_ge σ j (by omega)] at h
    omega
  · have h1 := rho_lt σ j hj
    rw [rho_ge σ i (by omega)] at h
    omega
  · rw [rho_ge σ i (by omega), rho_ge σ j (by omega)] at h
    exact h

lemma rho_mul (τ σ : Equiv.Perm (Fin 14)) (i : ℕ) : rho τ (rho σ i) = rho (τ * σ) i := by
  by_cases h : i < 14
  · rw [rho_pos σ i h, rho_val τ, rho_pos (τ * σ) i h]
    rfl
  · rw [rho_ge σ i (by omega), rho_ge τ i (by omega), rho_ge (τ * σ) i (by omega)]

lemma x9_eq (σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (if (i : ℕ) < 14 then ((σ (Fin.ofNat 14 (i : ℕ)) : Fin 14) : ℕ) else 14) = rho σ i.val := by
  by_cases h : (i : ℕ) < 14
  · have e : (Fin.ofNat 14 (i : ℕ) : Fin 14) = ⟨i.val, h⟩ := by
      apply Fin.ext
      show (i : ℕ) % 14 = i.val
      exact Nat.mod_eq_of_lt h
    rw [rho_pos σ i.val h]
    split
    · rw [e]
    · contradiction
  · rw [rho_ge σ i.val (by omega)]
    have := i.isLt
    split
    · contradiction
    · omega

lemma getD_ofFn (f : Fin 14 → Bool) (i : ℕ) (h : i < 14) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

lemma inv_base (σ : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) :
    Inv σ (List.ofFn (x ∘ ⇑σ)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < 14
  · rw [getD_ofFn _ i h, getD_ofFn _ (rho σ i) (rho_lt σ i h)]
    show x (σ ⟨i, h⟩) = x ⟨rho σ i, _⟩
    congr 1
    apply Fin.ext
    exact (rho_pos σ i h).symm
  · rw [rho_ge σ i (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma inv_snoc (σ : Equiv.Perm (Fin 14)) (W W' : List Bool) (u : Bool) (h : Inv σ W W') :
    Inv σ (W ++ [u]) (W' ++ [u]) := by
  obtain ⟨hl, h14, hv⟩ := h
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  by_cases hi : i < W.length
  · have hr : rho σ i < W'.length := by
      by_cases h : i < 14
      · have := rho_lt σ i h
        omega
      · rw [rho_ge σ i (by omega)]
        omega
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hr]
    exact hv i
  · have hr : rho σ i = i := rho_ge σ i (by omega)
    rw [hr, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

lemma inv_gate (σ : Equiv.Perm (Fin 14)) (W W' : List Bool) (g : Gate) (h : Inv σ W W') :
    (gmap σ g).op.eval ((gmap σ g).inputs.map fun i => W'.getD i false) =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
  unfold gmap
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (h.2.2 i).symm

lemma inv_step (σ : Equiv.Perm (Fin 14)) (W W' : List Bool) (g : Gate) (h : Inv σ W W') :
    Inv σ (stepW W g) (stepW W' (gmap σ g)) := by
  unfold stepW
  rw [inv_gate σ W W' g h]
  exact inv_snoc σ W W' _ h

lemma inv_fold (σ : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ W W' : List Bool, Inv σ W W' →
      Inv σ (gs.foldl stepW W) ((gs.map (gmap σ)).foldl stepW W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (inv_step σ W W' g h)

lemma eval_core (C : Circuit) (g0 g1 : Gate) (rest : List Gate)
    (hg : C.gates = g0 :: g1 :: rest) (a0 b0 a1 b1 : ℕ)
    (hi0 : g0.inputs = [a0, b0]) (hi1 : g1.inputs = [a1, b1])
    (ha0 : a0 < 14) (hb0 : b0 < 14)
    (σ : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) (v0 v1 : Bool)
    (hv0 : v0 = g0.op.eval [x (σ ⟨a0, ha0⟩), x (σ ⟨b0, hb0⟩)])
    (hv1 : v1 = g1.op.eval [(List.ofFn x ++ [v0]).getD (rho σ a1) false,
      (List.ofFn x ++ [v0]).getD (rho σ b1) false]) :
    (⟨rest.map (gmap σ), rho σ C.output⟩ : Circuit).eval ((List.ofFn x ++ [v0]) ++ [v1]) =
      C.eval (List.ofFn (x ∘ ⇑σ)) := by
  have I0 := inv_base σ x
  have e0 : stepW (List.ofFn (x ∘ ⇑σ)) g0 = List.ofFn (x ∘ ⇑σ) ++ [v0] := by
    unfold stepW
    rw [hi0, hv0]
    simp only [List.map_cons, List.map_nil]
    rw [getD_ofFn _ a0 ha0, getD_ofFn _ b0 hb0]
    rfl
  have I1 := inv_snoc σ _ _ v0 I0
  have e1 : stepW (List.ofFn (x ∘ ⇑σ) ++ [v0]) g1 = (List.ofFn (x ∘ ⇑σ) ++ [v0]) ++ [v1] := by
    unfold stepW
    rw [hi1, hv1]
    simp only [List.map_cons, List.map_nil]
    rw [I1.2.2 a1, I1.2.2 b1]
  have I2 := inv_snoc σ _ _ v1 I1
  have I3 := inv_fold σ rest _ _ I2
  show ((rest.map (gmap σ)).foldl stepW ((List.ofFn x ++ [v0]) ++ [v1])).getD (rho σ C.output) false =
    (C.gates.foldl stepW (List.ofFn (x ∘ ⇑σ))).getD C.output false
  rw [hg]
  simp only [List.foldl_cons]
  rw [e0, e1]
  exact (I3.2.2 C.output).symm

lemma op_comm (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or) (p q : Bool) :
    op.eval [p, q] = op.eval [q, p] := by
  rcases h with rfl | rfl <;> cases p <;> cases q <;> rfl

lemma code_swap1 (a b c d : ℕ) : code b a c d = code a b c d := by
  unfold code
  rw [min_comm b a, max_comm b a]

lemma code_swap2 (a b c d : ℕ) : code a b d c = code a b c d := by
  unfold code
  rw [min_comm d c, max_comm d c]

def Good (x1 : (Fin 14 → Bool) → Bool) (op0 op1 : GateOp) (X : Circuit)
    (p q : Fin 14) (c d : Fin 15) : Prop :=
  (∀ τ : Equiv.Perm (Fin 14), (∀ x : Fin 14 → Bool, x1 (x ∘ ⇑τ) = x1 x) →
      code ↑p ↑q ↑c ↑d ≤ code ↑(τ p) ↑(τ q) (rho τ c) (rho τ d)) ∧
  ∀ x : Fin 14 → Bool,
      X.eval ((List.ofFn x ++ [op0.eval [x p, x q]]) ++
        [op1.eval [(List.ofFn x ++ [op0.eval [x p, x q]]).getD ↑c false,
          (List.ofFn x ++ [op0.eval [x p, x q]]).getD ↑d false]]) = x1 x

lemma good_swap1 (x1 : (Fin 14 → Bool) → Bool) (op0 op1 : GateOp) (X : Circuit)
    (p q : Fin 14) (c d : Fin 15) (h0 : op0 = GateOp.and ∨ op0 = GateOp.or)
    (h : Good x1 op0 op1 X p q c d) : Good x1 op0 op1 X q p c d := by
  refine ⟨fun τ hτ => ?_, fun x => ?_⟩
  · rw [code_swap1, code_swap1 (↑(τ p))]
    exact h.1 τ hτ
  · rw [op_comm op0 h0 (x q) (x p)]
    exact h.2 x

lemma good_swap2 (x1 : (Fin 14 → Bool) → Bool) (op0 op1 : GateOp) (X : Circuit)
    (p q : Fin 14) (c d : Fin 15) (h1 : op1 = GateOp.and ∨ op1 = GateOp.or)
    (h : Good x1 op0 op1 X p q c d) : Good x1 op0 op1 X p q d c := by
  refine ⟨fun τ hτ => ?_, fun x => ?_⟩
  · rw [code_swap2, code_swap2 _ _ (rho τ c)]
    exact h.1 τ hτ
  · rw [op_comm op1 h1]
    exact h.2 x

lemma finish (x1 : (Fin 14 → Bool) → Bool) (op0 op1 : GateOp) (X : Circuit)
    (h0 : op0 = GateOp.and ∨ op0 = GateOp.or) (h1 : op1 = GateOp.and ∨ op1 = GateOp.or)
    (hX : Monotone2 X) (hs : X.size ≤ 24)
    (p q : Fin 14) (c d : Fin 15) (hpq : p < q) (hcd : c < d)
    (h : Good x1 op0 op1 X p q c d) :
    ∃ (x10 : Fin 14) (x11 : Fin 14) (x12 : Fin 15) (x13 : Fin 15) (x14 : GateOp) (x15 : GateOp)
      (x16 : Circuit),
      x10 < x11 ∧ x12 < x13 ∧ (x14 = GateOp.and ∨ x14 = GateOp.or) ∧
      (x15 = GateOp.and ∨ x15 = GateOp.or) ∧
      (∀ x17 : Equiv.Perm (Fin 14), (∀ x18 : Fin 14 → Bool, x1 (x18 ∘ ⇑x17) = x1 x18) →
        (15 * min (x10 : ℕ) (x11 : ℕ) + max (x10 : ℕ) (x11 : ℕ)) * 225 +
            (15 * min (x12 : ℕ) (x13 : ℕ) + max (x12 : ℕ) (x13 : ℕ)) ≤
          (15 * min ((x17 x10 : Fin 14) : ℕ) ((x17 x11 : Fin 14) : ℕ) +
              max ((x17 x10 : Fin 14) : ℕ) ((x17 x11 : Fin 14) : ℕ)) * 225 +
            (15 * min (if (x12 : ℕ) < 14 then ((x17 (Fin.ofNat 14 (x12 : ℕ)) : Fin 14) : ℕ) else 14)
                (if (x13 : ℕ) < 14 then ((x17 (Fin.ofNat 14 (x13 : ℕ)) : Fin 14) : ℕ) else 14) +
              max (if (x12 : ℕ) < 14 then ((x17 (Fin.ofNat 14 (x12 : ℕ)) : Fin 14) : ℕ) else 14)
                (if (x13 : ℕ) < 14 then ((x17 (Fin.ofNat 14 (x13 : ℕ)) : Fin 14) : ℕ) else 14))) ∧
      Monotone2 x16 ∧ x16.size ≤ 24 ∧
      ∀ x17 : Fin 14 → Bool,
        x16.eval ((List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]]) ++
          [x15.eval [(List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]]).getD ↑x12 false,
            (List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]]).getD ↑x13 false]]) = x1 x17 := by
  refine ⟨p, q, c, d, op0, op1, X, hpq, hcd, h0, h1, ?_, hX, hs, h.2⟩
  intro τ hτ
  rw [x9_eq τ c, x9_eq τ d]
  exact h.1 τ hτ

lemma main (x1 : (Fin 14 → Bool) → Bool) (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 14 C) (hnd : ∀ g ∈ C.gates, g.inputs.Nodup)
    (h2 : 2 ≤ C.size) (h26 : C.size ≤ 26)
    (hev : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = x1 x) :
    ∃ (x10 : Fin 14) (x11 : Fin 14) (x12 : Fin 15) (x13 : Fin 15) (x14 : GateOp) (x15 : GateOp)
      (x16 : Circuit),
      x10 < x11 ∧ x12 < x13 ∧ (x14 = GateOp.and ∨ x14 = GateOp.or) ∧
      (x15 = GateOp.and ∨ x15 = GateOp.or) ∧
      (∀ x17 : Equiv.Perm (Fin 14), (∀ x18 : Fin 14 → Bool, x1 (x18 ∘ ⇑x17) = x1 x18) →
        (15 * min (x10 : ℕ) (x11 : ℕ) + max (x10 : ℕ) (x11 : ℕ)) * 225 +
            (15 * min (x12 : ℕ) (x13 : ℕ) + max (x12 : ℕ) (x13 : ℕ)) ≤
          (15 * min ((x17 x10 : Fin 14) : ℕ) ((x17 x11 : Fin 14) : ℕ) +
              max ((x17 x10 : Fin 14) : ℕ) ((x17 x11 : Fin 14) : ℕ)) * 225 +
            (15 * min (if (x12 : ℕ) < 14 then ((x17 (Fin.ofNat 14 (x12 : ℕ)) : Fin 14) : ℕ) else 14)
                (if (x13 : ℕ) < 14 then ((x17 (Fin.ofNat 14 (x13 : ℕ)) : Fin 14) : ℕ) else 14) +
              max (if (x12 : ℕ) < 14 then ((x17 (Fin.ofNat 14 (x12 : ℕ)) : Fin 14) : ℕ) else 14)
                (if (x13 : ℕ) < 14 then ((x17 (Fin.ofNat 14 (x13 : ℕ)) : Fin 14) : ℕ) else 14))) ∧
      Monotone2 x16 ∧ x16.size ≤ 24 ∧
      ∀ x17 : Fin 14 → Bool,
        x16.eval ((List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]]) ++
          [x15.eval [(List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]]).getD ↑x12 false,
            (List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]]).getD ↑x13 false]]) = x1 x17 := by
  classical
  obtain ⟨hand, hrb, hlen⟩ := hAO
  obtain ⟨g0, g1, rest, hg⟩ : ∃ g0 g1 rest, C.gates = g0 :: g1 :: rest := by
    unfold Circuit.size at h2
    match hgs : C.gates with
    | [] => rw [hgs] at h2; simp at h2
    | [_] => rw [hgs] at h2; simp at h2
    | g0 :: g1 :: rest => exact ⟨g0, g1, rest, rfl⟩
  have hm0 : g0 ∈ C.gates := by rw [hg]; simp
  have hm1 : g1 ∈ C.gates := by rw [hg]; simp
  obtain ⟨a0, b0, hi0⟩ := List.length_eq_two.mp (hlen g0 hm0)
  obtain ⟨a1, b1, hi1⟩ := List.length_eq_two.mp (hlen g1 hm1)
  have hne0 : a0 ≠ b0 := by
    have h := hnd g0 hm0
    rw [hi0] at h
    simpa using h
  have hne1 : a1 ≠ b1 := by
    have h := hnd g1 hm1
    rw [hi1] at h
    simpa using h
  have hr0 := hrb 0 (by rw [hg]; simp)
  have hr1 := hrb 1 (by rw [hg]; simp)
  have e0 : NestedCover.gateAt C 0 = g0 := by simp [NestedCover.gateAt, hg]
  have e1 : NestedCover.gateAt C 1 = g1 := by simp [NestedCover.gateAt, hg]
  rw [e0, hi0] at hr0
  rw [e1, hi1] at hr1
  have ha0 : a0 < 14 := by have := hr0 a0 (by simp); omega
  have hb0 : b0 < 14 := by have := hr0 b0 (by simp); omega
  have ha1 : a1 < 15 := by have := hr1 a1 (by simp); omega
  have hb1 : b1 < 15 := by have := hr1 b1 (by simp); omega
  have hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or := hand g0 hm0
  have hop1 : g1.op = GateOp.and ∨ g1.op = GateOp.or := hand g1 hm1
  let κ : Equiv.Perm (Fin 14) → ℕ := fun σ => code (rho σ a0) (rho σ b0) (rho σ a1) (rho σ b1)
  let A : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter (fun σ => ∀ x : Fin 14 → Bool, x1 (x ∘ ⇑σ) = x1 x)
  have hA1 : (1 : Equiv.Perm (Fin 14)) ∈ A := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_⟩
    rfl
  obtain ⟨σ, hσA, hmin⟩ := A.exists_min_image κ ⟨1, hA1⟩
  have hσ : ∀ x : Fin 14 → Bool, x1 (x ∘ ⇑σ) = x1 x := (Finset.mem_filter.mp hσA).2
  let X : Circuit := ⟨rest.map (gmap σ), rho σ C.output⟩
  have hX : Monotone2 X := by
    intro g hgm
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hgm
    have hmem : g' ∈ C.gates := by rw [hg]; simp [hg']
    refine ⟨?_, ?_⟩
    · rcases hand g' hmem with h | h
      · show g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)
        rw [h]; simp
      · show g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)
        rw [h]; simp
    · show (g'.inputs.map (rho σ)).length ≤ 2
      rw [List.length_map, hlen g' hmem]
  have hXs : X.size ≤ 24 := by
    show (rest.map (gmap σ)).length ≤ 24
    unfold Circuit.size at h26
    rw [hg] at h26
    simp at h26 ⊢
    omega
  have hpq : σ ⟨a0, ha0⟩ ≠ σ ⟨b0, hb0⟩ := by
    intro h
    exact hne0 (congrArg Fin.val (σ.injective h))
  have hcd : (⟨rho σ a1, by
      by_cases h : a1 < 14
      · have := rho_lt σ a1 h; omega
      · rw [rho_ge σ a1 (by omega)]; exact ha1⟩ : Fin 15) ≠ ⟨rho σ b1, by
      by_cases h : b1 < 14
      · have := rho_lt σ b1 h; omega
      · rw [rho_ge σ b1 (by omega)]; exact hb1⟩ := by
    intro h
    exact hne1 (rho_inj σ a1 b1 (congrArg Fin.val h))
  have hG : Good x1 g0.op g1.op X (σ ⟨a0, ha0⟩) (σ ⟨b0, hb0⟩)
      ⟨rho σ a1, by
        by_cases h : a1 < 14
        · have := rho_lt σ a1 h; omega
        · rw [rho_ge σ a1 (by omega)]; exact ha1⟩
      ⟨rho σ b1, by
        by_cases h : b1 < 14
        · have := rho_lt σ b1 h; omega
        · rw [rho_ge σ b1 (by omega)]; exact hb1⟩ := by
    refine ⟨fun τ hτ => ?_, fun x => ?_⟩
    · have hmem : τ * σ ∈ A := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_⟩
        have e : x ∘ ⇑(τ * σ) = (x ∘ ⇑τ) ∘ ⇑σ := rfl
        rw [e, hσ, hτ]
      have hk := hmin (τ * σ) hmem
      show code ↑(σ ⟨a0, ha0⟩) ↑(σ ⟨b0, hb0⟩) (rho σ a1) (rho σ b1) ≤
        code ↑(τ (σ ⟨a0, ha0⟩)) ↑(τ (σ ⟨b0, hb0⟩)) (rho τ (rho σ a1)) (rho τ (rho σ b1))
      rw [rho_mul, rho_mul, ← rho_val τ (σ ⟨a0, ha0⟩), ← rho_val τ (σ ⟨b0, hb0⟩),
        ← rho_pos σ a0 ha0, ← rho_pos σ b0 hb0, rho_mul, rho_mul]
      exact hk
    · exact (eval_core C g0 g1 rest hg a0 b0 a1 b1 hi0 hi1 ha0 hb0 σ x _ _ rfl rfl).trans
        ((hev _).trans (hσ x))
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hcd with h2' | h2'
  · exact finish x1 g0.op g1.op X hop0 hop1 hX hXs _ _ _ _ h1 h2' hG
  · exact finish x1 g0.op g1.op X hop0 hop1 hX hXs _ _ _ _ h1 h2'
      (good_swap2 x1 _ _ X _ _ _ _ hop1 hG)
  · exact finish x1 g0.op g1.op X hop0 hop1 hX hXs _ _ _ _ h1 h2'
      (good_swap1 x1 _ _ X _ _ _ _ hop0 hG)
  · exact finish x1 g0.op g1.op X hop0 hop1 hX hXs _ _ _ _ h1 h2'
      (good_swap2 x1 _ _ X _ _ _ _ hop1 (good_swap1 x1 _ _ X _ _ _ _ hop0 hG))

end PEqualNP.Outside.L_meta_3010

theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro x1 x2 hAO hnd h2 h26 hev
  exact PEqualNP.Outside.L_meta_3010.main x1 x2 hAO hnd h2 h26 hev
