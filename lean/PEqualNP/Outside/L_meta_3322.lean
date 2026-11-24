import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_3322_aux

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih => rw [wiresFrom_cons, ih]; simp; omega

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons]
    rw [ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp; omega)]
    exact List.getD_append w _ _ _ h

def renameGate (rho : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map rho⟩

theorem wiresFrom_rename (rho : ℕ → ℕ) (hfix : ∀ i, 14 ≤ i → rho i = i)
    (hlt : ∀ i, i < 14 → rho i < 14) :
    ∀ (gs : List Gate) (U W : List Bool), U.length = W.length → 14 ≤ U.length →
      (∀ k < 14, W.getD (rho k) false = U.getD k false) →
      (∀ i, 14 ≤ i → i < U.length → W.getD i false = U.getD i false) →
      ∀ i < U.length + gs.length,
        (wiresFrom (gs.map (renameGate rho)) W).getD i false
          = if i < 14 then W.getD i false else (wiresFrom gs U).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro U W hlen h14 h1 h2 i hi
    by_cases hi14 : i < 14
    · rw [ite_eq_left hi14]
      exact getD_wiresFrom [] W i (by omega)
    · rw [ite_eq_right hi14]
      exact h2 i (by omega) (by simpa using hi)
  | cons g gs ih =>
    intro U W hlen h14 h1 h2 i hi
    have hbit : g.op.eval (g.inputs.map fun k => W.getD (rho k) false)
        = g.op.eval (g.inputs.map fun k => U.getD k false) := by
      congr 1
      refine List.map_congr_left ?_
      intro k hk
      by_cases hk14 : k < 14
      · exact h1 k hk14
      · rw [hfix k (by omega)]
        by_cases hkU : k < U.length
        · exact h2 k (by omega) hkU
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have hlen' : (U ++ [g.op.eval (g.inputs.map fun k => U.getD k false)]).length
        = (W ++ [g.op.eval (g.inputs.map fun k => W.getD (rho k) false)]).length := by
      simp [hlen]
    have h14' : 14 ≤ (U ++ [g.op.eval (g.inputs.map fun k => U.getD k false)]).length := by
      simp; omega
    have hinv1 : ∀ k < 14,
        (W ++ [g.op.eval (g.inputs.map fun k => W.getD (rho k) false)]).getD (rho k) false
          = (U ++ [g.op.eval (g.inputs.map fun k => U.getD k false)]).getD k false := by
      intro k hk
      have hkU : k < U.length := by omega
      have hr : rho k < U.length := by
        have := hlt k hk; omega
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hkU]
      exact h1 k hk
    have hinv2 : ∀ j, 14 ≤ j →
        j < (U ++ [g.op.eval (g.inputs.map fun k => U.getD k false)]).length →
        (W ++ [g.op.eval (g.inputs.map fun k => W.getD (rho k) false)]).getD j false
          = (U ++ [g.op.eval (g.inputs.map fun k => U.getD k false)]).getD j false := by
      intro j hj hjlen
      rw [List.length_append, List.length_singleton] at hjlen
      by_cases hjU : j < U.length
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hjU]
        exact h2 j hj hjU
      · have hjU' : j = U.length := by omega
        subst hjU'
        rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
        rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
        exact hbit
    have hi' : i < (U ++ [g.op.eval (g.inputs.map fun k => U.getD k false)]).length + gs.length := by
      simp only [List.length_append, List.length_cons] at hi ⊢
      omega
    have key := ih (U ++ [g.op.eval (g.inputs.map fun k => U.getD k false)])
      (W ++ [g.op.eval (g.inputs.map fun k => W.getD (rho k) false)]) hlen' h14' hinv1 hinv2 i hi'
    have hL' : wiresFrom ((g :: gs).map (renameGate rho)) W
        = wiresFrom (gs.map (renameGate rho))
            (W ++ [g.op.eval (g.inputs.map fun k => W.getD (rho k) false)]) := by
      rw [List.map_cons, wiresFrom_cons]
      congr 1
      simp [renameGate, List.map_map, Function.comp_def]
    rw [hL', key]
    by_cases hi14 : i < 14
    · rw [ite_eq_left hi14, ite_eq_left hi14]
      rw [List.getD_append _ _ _ _ (by omega)]
    · rw [ite_eq_right hi14, ite_eq_right hi14]
      rfl




def step1 (op : GateOp) (y : Fin 14 → Bool) (a b : Fin 14) : Bool := op.eval [y a, y b]

def wit (op : GateOp) (y : Fin 14 → Bool) (a b : Fin 14) : List Bool :=
  List.ofFn y ++ [step1 op y a b]

def step2 (op1 op2 : GateOp) (y : Fin 14 → Bool) (a b : Fin 14) (c d : Fin 15) : Bool :=
  op2.eval [(wit op1 y a b).getD (↑c) false, (wit op1 y a b).getD (↑d) false]

def full (op1 op2 : GateOp) (y : Fin 14 → Bool) (a b : Fin 14) (c d : Fin 15) : List Bool :=
  wit op1 y a b ++ [step2 op1 op2 y a b c d]

theorem eval_list2 (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or) (p q : Bool) :
    op.eval [p, q] = op.eval [q, p] := by
  rcases h with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

theorem full_swap12 (op1 op2 : GateOp) (h : op1 = GateOp.and ∨ op1 = GateOp.or)
    (y : Fin 14 → Bool) (a b : Fin 14) (c d : Fin 15) :
    full op1 op2 y b a c d = full op1 op2 y a b c d := by
  have hc : step1 op1 y b a = step1 op1 y a b := eval_list2 op1 h (y a) (y b) |>.symm
  simp [full, wit, step2, hc]

theorem full_swap34 (op1 op2 : GateOp) (h : op2 = GateOp.and ∨ op2 = GateOp.or)
    (y : Fin 14 → Bool) (a b : Fin 14) (c d : Fin 15) :
    full op1 op2 y a b d c = full op1 op2 y a b c d := by
  have hc : step2 op1 op2 y a b d c = step2 op1 op2 y a b c d := by
    simp only [step2]
    exact eval_list2 op2 h _ _
  simp [full, hc]

def Raw (f : (Fin 14 → Bool) → Bool) (q : Fin 14 × Fin 14 × Fin 15 × Fin 15) : Prop :=
  ∃ op1 op2 : GateOp, ∃ D : Circuit,
    (op1 = GateOp.and ∨ op1 = GateOp.or) ∧ (op2 = GateOp.and ∨ op2 = GateOp.or) ∧
      Monotone2 D ∧ D.size ≤ 24 ∧
        ∀ y : Fin 14 → Bool, D.eval (full op1 op2 y q.1 q.2.1 q.2.2.1 q.2.2.2) = f y

def key (q : Fin 14 × Fin 14 × Fin 15 × Fin 15) : ℕ :=
  (15 * min (↑q.1) (↑q.2.1) + max (↑q.1) (↑q.2.1)) * 225 +
    (15 * min (↑q.2.2.1) (↑q.2.2.2) + max (↑q.2.2.1) (↑q.2.2.2))

def permfun (σ : Equiv.Perm (Fin 14)) : ℕ → ℕ :=
  fun i => if i < 14 then ↑(σ (Fin.ofNat 14 i)) else i

theorem permfun_lt (σ : Equiv.Perm (Fin 14)) : ∀ i < 14, permfun σ i < 14 := by
  intro i hi
  simp [permfun, hi]

theorem permfun_fix (σ : Equiv.Perm (Fin 14)) : ∀ i, 14 ≤ i → permfun σ i = i := by
  intro i hi
  simp [permfun, by omega]

theorem permfun_val (σ : Equiv.Perm (Fin 14)) (k : ℕ) (hk : k < 14) :
    permfun σ k = ↑(σ (Fin.ofNat 14 k)) := by
  simp [permfun, hk]

theorem permfun_lt15 (σ : Equiv.Perm (Fin 14)) (c : Fin 15) : permfun σ ↑c < 15 := by
  by_cases h : ↑c < 14
  · have := permfun_lt σ ↑c h
    omega
  · rw [permfun_fix σ ↑c (by omega)]
    omega

theorem x9_eq (σ : Equiv.Perm (Fin 14)) (c : Fin 15) :
    (if c < (14 : Fin 15) then ↑(σ (Fin.ofNat 14 ↑c)) else 14) = permfun σ ↑c := by
  have h14 : (↑(14 : Fin 15) : ℕ) = 14 := by simp
  by_cases h : c < (14 : Fin 15)
  · rw [ite_eq_left h]
    have h' : ↑c < 14 := by simpa [h14] using h
    exact (permfun_val σ ↑c h').symm
  · rw [ite_eq_right h]
    have h' : ¬ ↑c < 14 := by simpa [h14] using h
    rw [permfun_fix σ ↑c (by omega)]
    omega

theorem key_swap12 (q : Fin 14 × Fin 14 × Fin 15 × Fin 15) :
    key (q.2.1, q.1, q.2.2.1, q.2.2.2) = key q := by
  simp [key, min_comm, max_comm]

theorem key_swap34 (q : Fin 14 × Fin 14 × Fin 15 × Fin 15) :
    key (q.1, q.2.1, q.2.2.2, q.2.2.1) = key q := by
  simp [key, min_comm, max_comm]



theorem ofFn_getD (z : Fin 14 → Bool) (k : ℕ) (hk : k < 14) :
    (List.ofFn z).getD k false = z ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hk]
  rfl

theorem ofNat_eq_mk (k : ℕ) (hk : k < 14) : (Fin.ofNat 14 k : Fin 14) = ⟨k, hk⟩ := by
  ext
  rw [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt hk

theorem permfun_inj (σ : Equiv.Perm (Fin 14)) (a b : ℕ) (ha : a < 15) (hb : b < 15)
    (h : permfun σ a = permfun σ b) : a = b := by
  by_cases ha14 : a < 14 <;> by_cases hb14 : b < 14
  · have hinj : σ (Fin.ofNat 14 a) = σ (Fin.ofNat 14 b) := by
      apply Fin.ext
      rw [permfun_val σ a ha14, permfun_val σ b hb14] at h
      exact h
    rw [ofNat_eq_mk a ha14, ofNat_eq_mk b hb14] at hinj
    simpa using congrArg Fin.val (σ.injective hinj)
  · have hb15 : b = 14 := by omega
    rw [permfun_val σ a ha14, hb15, permfun_fix σ 14 (le_refl 14)] at h
    have := permfun_lt σ a ha14
    omega
  · have ha15 : a = 14 := by omega
    rw [ha15, permfun_fix σ 14 (le_refl 14), permfun_val σ b hb14] at h
    have := permfun_lt σ b hb14
    omega
  · omega

theorem eval_of_getD (D : Circuit) (w : List Bool) (h : D.output < w.length) :
    D.eval w = w.getD D.output false := getD_wiresFrom D.gates w D.output h

theorem eval_lt14 (D : Circuit) (h : D.output < 14) (op1 op2 : GateOp) (y : Fin 14 → Bool)
    (a b : Fin 14) (c d : Fin 15) :
    D.eval (full op1 op2 y a b c d) = y ⟨D.output, h⟩ := by
  rw [eval_of_getD D _ (by simp [full, wit]; omega)]
  have htake : (full op1 op2 y a b c d).getD D.output false = (List.ofFn y).getD D.output false := by
    rw [full, wit]
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [htake, ofFn_getD y D.output h]

theorem getD_wit_lt (op : GateOp) (z : Fin 14 → Bool) (a b : Fin 14) (k : ℕ) (hk : k < 14) :
    (wit op z a b).getD k false = z ⟨k, hk⟩ := by
  rw [wit, List.getD_append _ _ _ _ (by simp; omega), ofFn_getD z k hk]

theorem getD_wit_eq (op : GateOp) (z : Fin 14 → Bool) (a b : Fin 14) :
    (wit op z a b).getD 14 false = step1 op z a b := by
  rw [wit, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem getD_fourteen (z : Fin 14 → Bool) (a b : Bool) :
    (List.ofFn z ++ [a, b]).getD 14 false = a := by
  rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self,
    List.getD_cons_zero]

theorem getD_fifteen (z : Fin 14 → Bool) (a b : Bool) :
    (List.ofFn z ++ [a, b]).getD 15 false = b := by
  rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
  simp

theorem Raw_swap12 (f : (Fin 14 → Bool) → Bool) (q : Fin 14 × Fin 14 × Fin 15 × Fin 15)
    (hq : Raw f q) : Raw f (q.2.1, q.1, q.2.2.1, q.2.2.2) := by
  obtain ⟨op1, op2, D, h1, h2, hm, hs, he⟩ := hq
  exact ⟨op1, op2, D, h1, h2, hm, hs,
    fun y => (full_swap12 op1 op2 h1 y q.1 q.2.1 q.2.2.1 q.2.2.2) ▸ he y⟩

theorem Raw_swap34 (f : (Fin 14 → Bool) → Bool) (q : Fin 14 × Fin 14 × Fin 15 × Fin 15)
    (hq : Raw f q) : Raw f (q.1, q.2.1, q.2.2.2, q.2.2.1) := by
  obtain ⟨op1, op2, D, h1, h2, hm, hs, he⟩ := hq
  exact ⟨op1, op2, D, h1, h2, hm, hs,
    fun y => (full_swap34 op1 op2 h2 y q.1 q.2.1 q.2.2.1 q.2.2.2) ▸ he y⟩



theorem base (f : (Fin 14 → Bool) → Bool) (C : Circuit) (hAO : IsAO2 14 C)
    (hnd : ∀ g ∈ C.gates, g.inputs.Nodup) (h2 : 2 ≤ C.size) (h26 : C.size ≤ 26)
    (hfun : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = f x) :
    ∃ a b : Fin 14, ∃ c d : Fin 15, a < b ∧ c < d ∧ Raw f (a, b, c, d) := by
  classical
  obtain ⟨hAndOr, hRB, hTwo⟩ := hAO
  obtain ⟨g0, g1, rest, hC⟩ : ∃ g0 g1 rest, C.gates = g0 :: g1 :: rest := by
    match h : C.gates with
    | [] => simp [Circuit.size, h] at h2
    | [_] => simp [Circuit.size, h] at h2
    | a :: b :: t => exact ⟨a, b, t, rfl⟩
  have hg0mem : g0 ∈ C.gates := by rw [hC]; simp
  have hg1mem : g1 ∈ C.gates := by rw [hC]; simp
  have hg0len : g0.inputs.length = 2 := hTwo g0 hg0mem
  have hg1len : g1.inputs.length = 2 := hTwo g1 hg1mem
  have hg0nd : g0.inputs.Nodup := hnd g0 hg0mem
  have hg1nd : g1.inputs.Nodup := hnd g1 hg1mem
  have hg0op : g0.op = GateOp.and ∨ g0.op = GateOp.or := hAndOr g0 hg0mem
  have hg1op : g1.op = GateOp.and ∨ g1.op = GateOp.or := hAndOr g1 hg1mem
  have hrb0 : ∀ i ∈ g0.inputs, i < 14 := by
    have h0 : 0 < C.gates.length := by rw [hC]; simp
    have := hRB 0 h0
    simpa [NestedCover.gateAt, hC] using this
  have hrb1 : ∀ i ∈ g1.inputs, i < 15 := by
    have h1 : 1 < C.gates.length := by rw [hC]; simp
    have := hRB 1 h1
    simpa [NestedCover.gateAt, hC] using this
  obtain ⟨i0, i1, hi01⟩ : ∃ i0 i1 : ℕ, g0.inputs = [i0, i1] := by
    match h : g0.inputs with
    | [] => simp [h] at hg0len
    | [_] => simp [h] at hg0len
    | [x, y] => exact ⟨x, y, rfl⟩
    | _ :: _ :: _ :: _ => simp [h] at hg0len
  obtain ⟨i2, i3, hi23⟩ : ∃ i2 i3 : ℕ, g1.inputs = [i2, i3] := by
    match h : g1.inputs with
    | [] => simp [h] at hg1len
    | [_] => simp [h] at hg1len
    | [x, y] => exact ⟨x, y, rfl⟩
    | _ :: _ :: _ :: _ => simp [h] at hg1len
  have hi0lt : i0 < 14 := hrb0 i0 (by rw [hi01]; simp)
  have hi1lt : i1 < 14 := hrb0 i1 (by rw [hi01]; simp)
  have hi2lt : i2 < 15 := hrb1 i2 (by rw [hi23]; simp)
  have hi3lt : i3 < 15 := hrb1 i3 (by rw [hi23]; simp)
  have hi0ne : i0 ≠ i1 := by
    have hn := hg0nd
    rw [hi01] at hn
    simpa using hn
  have hi2ne : i2 ≠ i3 := by
    have hn := hg1nd
    rw [hi23] at hn
    simpa using hn
  have hex0 : ∃ (a b : Fin 14), a < b ∧ (g0.inputs = [↑a, ↑b] ∨ g0.inputs = [↑b, ↑a]) := by
    rcases lt_or_gt_of_ne hi0ne with h | h
    · exact ⟨⟨i0, hi0lt⟩, ⟨i1, hi1lt⟩, h, Or.inl (by rw [hi01])⟩
    · exact ⟨⟨i1, hi1lt⟩, ⟨i0, hi0lt⟩, h, Or.inr (by rw [hi01])⟩
  obtain ⟨a, b, hab, hgo⟩ := hex0
  have hex1 : ∃ (c d : Fin 15), c < d ∧ (g1.inputs = [↑c, ↑d] ∨ g1.inputs = [↑d, ↑c]) := by
    rcases lt_or_gt_of_ne hi2ne with h | h
    · exact ⟨⟨i2, hi2lt⟩, ⟨i3, hi3lt⟩, h, Or.inl (by rw [hi23])⟩
    · exact ⟨⟨i3, hi3lt⟩, ⟨i2, hi2lt⟩, h, Or.inr (by rw [hi23])⟩
  obtain ⟨c, d, hcd, hgd⟩ := hex1
  let D : Circuit := ⟨rest, C.output⟩
  have hDsize : D.size ≤ 24 := by
    have h1 : C.gates.length = rest.length + 2 := by rw [hC]; simp
    simp only [Circuit.size, D] at h26 ⊢
    omega
  have hDmono : Monotone2 D := by
    intro g hg
    have hgC : g ∈ C.gates := by
      simp only [D] at hg
      rw [hC]
      simp [hg]
    have hlen := hTwo g hgC
    refine ⟨?_, by omega⟩
    rcases hAndOr g hgC with h | h <;> simp [h]
  refine ⟨a, b, c, d, hab, hcd, g0.op, g1.op, D, hg0op, hg1op, hDmono, hDsize, ?_⟩
  intro y
  rw [← hfun y]
  have hb0 : g0.op.eval (g0.inputs.map fun k => (List.ofFn y).getD k false)
      = step1 g0.op y a b := by
    rcases hgo with h | h
    · rw [h]
      simp only [List.map_cons, List.map_nil]
      rw [ofFn_getD y ↑a a.isLt, ofFn_getD y ↑b b.isLt, step1]
    · rw [h]
      simp only [List.map_cons, List.map_nil]
      rw [ofFn_getD y ↑b b.isLt, ofFn_getD y ↑a a.isLt, step1]
      show g0.op.eval [y b, y a] = g0.op.eval [y a, y b]
      exact eval_list2 g0.op hg0op (y b) (y a)
  have hb1 : g1.op.eval (g1.inputs.map fun k =>
        (List.ofFn y ++ [step1 g0.op y a b]).getD k false)
      = step2 g0.op g1.op y a b c d := by
    rcases hgd with h | h
    · rw [h]
      simp only [List.map_cons, List.map_nil, step2, wit]
    · rw [h]
      simp only [List.map_cons, List.map_nil, step2, wit]
      exact (eval_list2 g1.op hg1op _ _).symm
  have hw : wiresFrom C.gates (List.ofFn y) = wiresFrom rest (full g0.op g1.op y a b c d) := by
    rw [hC, wiresFrom_cons, wiresFrom_cons, hb0, hb1]
    simp [full, wit]
  calc D.eval (full g0.op g1.op y a b c d)
      = (wiresFrom rest (full g0.op g1.op y a b c d)).getD C.output false := rfl
    _ = (wiresFrom C.gates (List.ofFn y)).getD C.output false := by rw [hw]
    _ = C.eval (List.ofFn y) := rfl






theorem Raw_rename (f : (Fin 14 → Bool) → Bool) (q : Fin 14 × Fin 14 × Fin 15 × Fin 15)
    (σ : Equiv.Perm (Fin 14)) (hσ : ∀ z : Fin 14 → Bool, f (z ∘ ⇑σ) = f z)
    (hq : Raw f q) :
    Raw f (σ q.1, σ q.2.1, ⟨permfun σ ↑q.2.2.1, permfun_lt15 σ q.2.2.1⟩,
      ⟨permfun σ ↑q.2.2.2, permfun_lt15 σ q.2.2.2⟩) := by
  classical
  obtain ⟨op1, op2, D, hop1, hop2, hmono, hsize, hev⟩ := hq
  by_cases hshort : D.output < 14
  · refine ⟨op1, op2, D, hop1, hop2, hmono, hsize, fun y => ?_⟩
    have hfy : f y = y ⟨D.output, hshort⟩ := by
      rw [← hev y]
      exact eval_lt14 D hshort op1 op2 y q.1 q.2.1 q.2.2.1 q.2.2.2
    rw [hfy]
    exact eval_lt14 D hshort op1 op2 y (σ q.1) (σ q.2.1) _ _
  · have hge : 14 ≤ D.output := by omega
    set c' : Fin 15 := ⟨permfun σ ↑q.2.2.1, permfun_lt15 σ q.2.2.1⟩ with hc'
    set d' : Fin 15 := ⟨permfun σ ↑q.2.2.2, permfun_lt15 σ q.2.2.2⟩ with hd'
    have hc'v : (↑c' : ℕ) = permfun σ ↑q.2.2.1 := by rw [hc']
    have hd'v : (↑d' : ℕ) = permfun σ ↑q.2.2.2 := by rw [hd']
    refine ⟨op1, op2, ⟨D.gates.map (renameGate (permfun σ)), D.output⟩, hop1, hop2, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_map.mp hg with ⟨g', hg', rfl⟩
      obtain ⟨hm, hl⟩ := hmono g' hg'
      exact ⟨hm, by simpa [renameGate] using hl⟩
    · simpa [Circuit.size] using hsize
    · intro y
      set u : Fin 14 → Bool := fun j => y (σ j) with hu
      have hbit1 : step1 op1 y (σ q.1) (σ q.2.1) = step1 op1 u q.1 q.2.1 := rfl
      have hget1 : (wit op1 y (σ q.1) (σ q.2.1)).getD (↑c') false
          = (wit op1 u q.1 q.2.1).getD (↑q.2.2.1) false := by
        by_cases h : (↑q.2.2.1 : ℕ) < 14
        · have hc : (↑c' : ℕ) < 14 := by
            rw [hc'v]
            exact permfun_lt σ _ h
          rw [getD_wit_lt op1 y (σ q.1) (σ q.2.1) ↑c' hc,
            getD_wit_lt op1 u q.1 q.2.1 ↑q.2.2.1 h]
          show y ⟨↑c', hc⟩ = y (σ ⟨↑q.2.2.1, h⟩)
          congr 1
          ext
          show (↑c' : ℕ) = ↑(σ ⟨↑q.2.2.1, h⟩)
          rw [hc'v, permfun_val σ ↑q.2.2.1 h, ofNat_eq_mk ↑q.2.2.1 h]
        · have h14' : (↑q.2.2.1 : ℕ) = 14 := by omega
          have hc : (↑c' : ℕ) = 14 := by
            rw [hc'v, permfun_fix σ _ (by omega)]
            exact h14'
          rw [hc, h14', getD_wit_eq, getD_wit_eq]
          exact hbit1
      have hget2 : (wit op1 y (σ q.1) (σ q.2.1)).getD (↑d') false
          = (wit op1 u q.1 q.2.1).getD (↑q.2.2.2) false := by
        by_cases h : (↑q.2.2.2 : ℕ) < 14
        · have hc : (↑d' : ℕ) < 14 := by
            rw [hd'v]
            exact permfun_lt σ _ h
          rw [getD_wit_lt op1 y (σ q.1) (σ q.2.1) ↑d' hc,
            getD_wit_lt op1 u q.1 q.2.1 ↑q.2.2.2 h]
          show y ⟨↑d', hc⟩ = y (σ ⟨↑q.2.2.2, h⟩)
          congr 1
          ext
          show (↑d' : ℕ) = ↑(σ ⟨↑q.2.2.2, h⟩)
          rw [hd'v, permfun_val σ ↑q.2.2.2 h, ofNat_eq_mk ↑q.2.2.2 h]
        · have h14' : (↑q.2.2.2 : ℕ) = 14 := by omega
          have hc : (↑d' : ℕ) = 14 := by
            rw [hd'v, permfun_fix σ _ (by omega)]
            exact h14'
          rw [hc, h14', getD_wit_eq, getD_wit_eq]
          exact hbit1
      have hstep2 : step2 op1 op2 y (σ q.1) (σ q.2.1) c' d'
          = step2 op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2 := by
        simp only [step2]
        rw [hget1, hget2]
      have hW : full op1 op2 y (σ q.1) (σ q.2.1) c' d'
          = List.ofFn y ++ [step1 op1 u q.1 q.2.1,
              step2 op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2] := by
        show wit op1 y (σ q.1) (σ q.2.1) ++ [step2 op1 op2 y (σ q.1) (σ q.2.1) c' d'] = _
        rw [hstep2, wit, hbit1, List.append_assoc]
        rfl
      have hU : full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2
          = List.ofFn u ++ [step1 op1 u q.1 q.2.1,
              step2 op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2] := by
        show wit op1 u q.1 q.2.1 ++ [step2 op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2] = _
        rw [wit, List.append_assoc]
        rfl
      have hlen : (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2).length
          = (full op1 op2 y (σ q.1) (σ q.2.1) c' d').length := by
        rw [hU, hW]
        simp
      have h14 : 14 ≤ (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2).length := by
        rw [hU]
        simp
      have hinv1 : ∀ k < 14,
          (full op1 op2 y (σ q.1) (σ q.2.1) c' d').getD (permfun σ k) false
            = (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2).getD k false := by
        intro k hk
        rw [hW, hU]
        rw [List.getD_append _ _ _ _ (by simp; have := permfun_lt σ k hk; omega),
          List.getD_append _ _ _ _ (by simp; omega)]
        rw [ofFn_getD y (permfun σ k) (permfun_lt σ k hk), ofFn_getD u k hk]
        show y ⟨permfun σ k, permfun_lt σ k hk⟩ = y (σ ⟨k, hk⟩)
        congr 1
        ext
        show (permfun σ k : ℕ) = ↑(σ ⟨k, hk⟩)
        rw [permfun_val σ k hk, ofNat_eq_mk k hk]
      have hinv2 : ∀ i, 14 ≤ i →
          i < (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2).length →
          (full op1 op2 y (σ q.1) (σ q.2.1) c' d').getD i false
            = (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2).getD i false := by
        intro i hi hii
        rw [hU] at hii
        have hi2 : i = 14 ∨ i = 15 := by
          rw [List.length_append, List.length_cons, List.length_cons, List.length_nil,
            List.length_ofFn] at hii
          omega
        rcases hi2 with rfl | rfl
        · rw [hW, hU, getD_fourteen, getD_fourteen]
        · rw [hW, hU, getD_fifteen, getD_fifteen]
      have hren := wiresFrom_rename (permfun σ) (permfun_fix σ) (permfun_lt σ) D.gates
        (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2)
        (full op1 op2 y (σ q.1) (σ q.2.1) c' d') hlen h14 hinv1 hinv2
      by_cases hout : D.output <
          (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2).length + D.gates.length
      · have hkey := hren D.output hout
        calc (⟨D.gates.map (renameGate (permfun σ)), D.output⟩ : Circuit).eval
              (full op1 op2 y (σ q.1) (σ q.2.1) c' d')
            = (wiresFrom (D.gates.map (renameGate (permfun σ)))
                (full op1 op2 y (σ q.1) (σ q.2.1) c' d')).getD D.output false := rfl
          _ = (wiresFrom D.gates (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2)).getD
                D.output false := by
              rw [hkey, ite_eq_right (by omega)]
          _ = D.eval (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2) := rfl
          _ = f u := hev u
          _ = f y := hσ y
      · have hDfalse : D.eval (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2) = false := by
          show (wiresFrom D.gates (full op1 op2 u q.1 q.2.1 q.2.2.1 q.2.2.2)).getD
            D.output false = false
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; omega)
        have hD'false : (⟨D.gates.map (renameGate (permfun σ)), D.output⟩ : Circuit).eval
            (full op1 op2 y (σ q.1) (σ q.2.1) c' d') = false := by
          show (wiresFrom (D.gates.map (renameGate (permfun σ)))
            (full op1 op2 y (σ q.1) (σ q.2.1) c' d')).getD D.output false = false
          apply List.getD_eq_default
          rw [length_wiresFrom, List.length_map]
          have hout' := hout
          rw [hlen] at hout'
          omega
        have h1 : f u = false := by
          rw [← hev u]
          exact hDfalse
        have hfy : f y = false := by
          rw [← hσ y]
          exact h1
        rw [hD'false, hfy]















def sortq (q : Fin 14 × Fin 14 × Fin 15 × Fin 15) : Fin 14 × Fin 14 × Fin 15 × Fin 15 :=
  (min q.1 q.2.1, max q.1 q.2.1, min q.2.2.1 q.2.2.2, max q.2.2.1 q.2.2.2)

def Valid (f : (Fin 14 → Bool) → Bool) (q : Fin 14 × Fin 14 × Fin 15 × Fin 15) : Prop :=
  q.1 < q.2.1 ∧ q.2.2.1 < q.2.2.2 ∧ Raw f q

theorem min_lt_max_of_ne {α : Type} [LinearOrder α] {a b : α} (h : a ≠ b) : min a b < max a b := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [min_eq_left (le_of_lt h'), max_eq_right (le_of_lt h')]
    exact h'
  · rw [min_eq_right (le_of_lt h'), max_eq_left (le_of_lt h')]
    exact h'

theorem key_sortq (q : Fin 14 × Fin 14 × Fin 15 × Fin 15) : key (sortq q) = key q := by
  rcases le_total q.1 q.2.1 with hA | hA
  · rcases le_total q.2.2.1 q.2.2.2 with hB | hB
    · have h : sortq q = q := by
        simp [sortq, min_eq_left hA, max_eq_right hA, min_eq_left hB, max_eq_right hB]
      rw [h]
    · have h : sortq q = (q.1, q.2.1, q.2.2.2, q.2.2.1) := by
        simp [sortq, min_eq_left hA, max_eq_right hA, min_eq_right hB, max_eq_left hB]
      rw [h]
      exact key_swap34 q
  · rcases le_total q.2.2.1 q.2.2.2 with hB | hB
    · have h : sortq q = (q.2.1, q.1, q.2.2.1, q.2.2.2) := by
        simp [sortq, min_eq_right hA, max_eq_left hA, min_eq_left hB, max_eq_right hB]
      rw [h]
      exact key_swap12 q
    · have h : sortq q = (q.2.1, q.1, q.2.2.2, q.2.2.1) := by
        simp [sortq, min_eq_right hA, max_eq_left hA, min_eq_right hB, max_eq_left hB]
      rw [h]
      exact key_swap34 (q.2.1, q.1, q.2.2.1, q.2.2.2) |>.trans (key_swap12 q)

theorem Valid_sort (f : (Fin 14 → Bool) → Bool) (q : Fin 14 × Fin 14 × Fin 15 × Fin 15)
    (h12 : q.1 ≠ q.2.1) (h34 : q.2.2.1 ≠ q.2.2.2) (hq : Raw f q) :
    Valid f (sortq q) := by
  refine ⟨min_lt_max_of_ne h12, min_lt_max_of_ne h34, ?_⟩
  rcases le_total q.1 q.2.1 with hA | hA
  · rcases le_total q.2.2.1 q.2.2.2 with hB | hB
    · have h : sortq q = q := by
        simp [sortq, min_eq_left hA, max_eq_right hA, min_eq_left hB, max_eq_right hB]
      rw [h]
      exact hq
    · have h : sortq q = (q.1, q.2.1, q.2.2.2, q.2.2.1) := by
        simp [sortq, min_eq_left hA, max_eq_right hA, min_eq_right hB, max_eq_left hB]
      rw [h]
      exact Raw_swap34 f q hq
  · rcases le_total q.2.2.1 q.2.2.2 with hB | hB
    · have h : sortq q = (q.2.1, q.1, q.2.2.1, q.2.2.2) := by
        simp [sortq, min_eq_right hA, max_eq_left hA, min_eq_left hB, max_eq_right hB]
      rw [h]
      exact Raw_swap12 f q hq
    · have h : sortq q = (q.2.1, q.1, q.2.2.2, q.2.2.1) := by
        simp [sortq, min_eq_right hA, max_eq_left hA, min_eq_right hB, max_eq_left hB]
      rw [h]
      exact Raw_swap34 f (q.2.1, q.1, q.2.2.1, q.2.2.2) (Raw_swap12 f q hq)


end PEqualNP.Outside.L_meta_3322_aux

open PEqualNP.Outside.L_meta_3322_aux

theorem PEqualNP.Outside.L_meta_3322 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro x1 C hAO hnd h2 h26 hfun
  obtain ⟨a0, b0, c0, d0, hab0, hcd0, hraw0⟩ := base x1 C hAO hnd h2 h26 hfun
  have hne : ∃ n : ℕ, ∃ q : Fin 14 × Fin 14 × Fin 15 × Fin 15, Valid x1 q ∧ key q = n :=
    ⟨key (a0, b0, c0, d0), (a0, b0, c0, d0), ⟨hab0, hcd0, hraw0⟩, rfl⟩
  obtain ⟨q0, hq0, hkey0⟩ := Nat.find_spec hne
  have hmin : ∀ q : Fin 14 × Fin 14 × Fin 15 × Fin 15, Valid x1 q → key q0 ≤ key q := by
    intro q hq
    by_contra hcon
    have hlt : key q < Nat.find hne := by rw [← hkey0]; omega
    exact Nat.find_min hne hlt ⟨q, hq, rfl⟩
  obtain ⟨hlt1, hlt2, hraw⟩ := hq0
  have hrawkeep : Raw x1 q0 := hraw
  obtain ⟨op1, op2, D, hop1, hop2, hmono, hsize, hev⟩ := hraw
  refine ⟨q0.1, q0.2.1, q0.2.2.1, q0.2.2.2, op1, op2, D, hlt1, hlt2, hop1, hop2, ?_, hmono,
    hsize, ?_⟩
  · intro σ hσ
    have himg : Raw x1 (σ q0.1, σ q0.2.1, ⟨permfun σ ↑q0.2.2.1, permfun_lt15 σ q0.2.2.1⟩,
        ⟨permfun σ ↑q0.2.2.2, permfun_lt15 σ q0.2.2.2⟩) := Raw_rename x1 q0 σ hσ hrawkeep
    have hne12 : σ q0.1 ≠ σ q0.2.1 := fun h => absurd (σ.injective h) (ne_of_lt hlt1)
    have hne34 : (⟨permfun σ ↑q0.2.2.1, permfun_lt15 σ q0.2.2.1⟩ : Fin 15)
        ≠ ⟨permfun σ ↑q0.2.2.2, permfun_lt15 σ q0.2.2.2⟩ := by
      intro h
      have h' : permfun σ ↑q0.2.2.1 = permfun σ ↑q0.2.2.2 := by
        simpa using congrArg Fin.val h
      exact absurd (permfun_inj σ ↑q0.2.2.1 ↑q0.2.2.2 q0.2.2.1.isLt
        q0.2.2.2.isLt h') (ne_of_lt hlt2)
    have hle := hmin _ (Valid_sort x1 _ hne12 hne34 himg)
    rw [key_sortq] at hle
    simp only [key] at hle
    change (15 * min ↑q0.1 ↑q0.2.1 + max ↑q0.1 ↑q0.2.1) * 225 +
        (15 * min ↑q0.2.2.1 ↑q0.2.2.2 + max ↑q0.2.2.1 ↑q0.2.2.2) ≤
      (15 * min ↑(σ q0.1) ↑(σ q0.2.1) + max ↑(σ q0.1) ↑(σ q0.2.1)) * 225 +
        (15 * min (if q0.2.2.1 < (14 : Fin 15) then ↑(σ (Fin.ofNat (14 : ℕ) ↑q0.2.2.1)) else (14 : ℕ))
          (if q0.2.2.2 < (14 : Fin 15) then ↑(σ (Fin.ofNat (14 : ℕ) ↑q0.2.2.2)) else (14 : ℕ)) +
         max (if q0.2.2.1 < (14 : Fin 15) then ↑(σ (Fin.ofNat (14 : ℕ) ↑q0.2.2.1)) else (14 : ℕ))
          (if q0.2.2.2 < (14 : Fin 15) then ↑(σ (Fin.ofNat (14 : ℕ) ↑q0.2.2.2)) else (14 : ℕ)))
    rw [x9_eq, x9_eq]
    exact hle
  · intro y
    simpa [full, wit, step1, step2] using hev y

