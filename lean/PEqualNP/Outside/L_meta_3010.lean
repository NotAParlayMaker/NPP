import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

def rho (σ : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ := if h : i < 14 then ((σ ⟨i, h⟩ : Fin 14) : ℕ) else i

theorem rho_lt (σ : Equiv.Perm (Fin 14)) (i : ℕ) (h : i < 14) : rho σ i < 14 := by
  simp only [rho, h, dif_pos]
  exact Fin.is_lt _

theorem rho_ge (σ : Equiv.Perm (Fin 14)) (i : ℕ) (h : ¬ i < 14) : rho σ i = i := by
  simp only [rho, h, dif_neg, not_false_eq_true]

theorem rho_inj (σ : Equiv.Perm (Fin 14)) (i j : ℕ) (hij : rho σ i = rho σ j) : i = j := by
  by_cases hi : i < 14 <;> by_cases hj : j < 14
  · have h1 : σ ⟨i, hi⟩ = σ ⟨j, hj⟩ := by
      apply Fin.ext
      simpa only [rho, hi, hj, dif_pos] using hij
    have := congrArg Fin.val (σ.injective h1)
    simpa using this
  · have := rho_lt σ i hi
    rw [hij, rho_ge σ j hj] at this
    omega
  · have := rho_lt σ j hj
    rw [← hij, rho_ge σ i hi] at this
    omega
  · rwa [rho_ge σ i hi, rho_ge σ j hj] at hij

theorem rho_mul (τ σ : Equiv.Perm (Fin 14)) (i : ℕ) : rho τ (rho σ i) = rho (τ * σ) i := by
  by_cases hi : i < 14
  · simp only [rho, hi, dif_pos, Equiv.Perm.mul_apply, Fin.is_lt, Fin.eta]
  · rw [rho_ge σ i hi, rho_ge τ i hi, rho_ge (τ * σ) i hi]

def rl (σ : Equiv.Perm (Fin 14)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho σ)⟩

theorem getD_snoc (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then a else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    rw [hk]
    simp

theorem getD_ofFn {m : ℕ} (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < m then f ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

def Rel (σ : Equiv.Perm (Fin 14)) (w' w : List Bool) : Prop :=
  w'.length = w.length ∧ 14 ≤ w.length ∧ ∀ k, w'.getD (rho σ k) false = w.getD k false

theorem step_rel (σ : Equiv.Perm (Fin 14)) (g : Gate) (w' w : List Bool) (h : Rel σ w' w) :
    Rel σ (step w' (rl σ g)) (step w g) := by
  obtain ⟨hl, h14, hk⟩ := h
  have hval : (rl σ g).op.eval ((rl σ g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [rl, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hk i
  refine ⟨by simp [step, hl], by simp [step]; omega, fun k => ?_⟩
  simp only [step]
  rw [hval, getD_snoc, getD_snoc, hl]
  by_cases hk14 : k < 14
  · have h1 := rho_lt σ k hk14
    rw [if_pos (by omega), if_pos (by omega)]
    exact hk k
  · rw [rho_ge σ k hk14]
    split_ifs <;> first | rfl | exact hk14.elim (by omega) | skip
    have := hk k
    rwa [rho_ge σ k hk14] at this

theorem fold_rel (σ : Equiv.Perm (Fin 14)) (gs : List Gate) : ∀ w' w : List Bool, Rel σ w' w →
    Rel σ ((gs.map (rl σ)).foldl step w') (gs.foldl step w) := by
  induction gs with
  | nil => intro w' w h; exact h
  | cons g gs ih =>
    intro w' w h
    exact ih _ _ (step_rel σ g w' w h)

theorem rel_init (σ : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) :
    Rel σ (List.ofFn x) (List.ofFn (x ∘ σ)) := by
  refine ⟨by simp, by simp, fun k => ?_⟩
  rw [getD_ofFn, getD_ofFn]
  by_cases hk : k < 14
  · have h1 := rho_lt σ k hk
    rw [dif_pos h1, dif_pos hk]
    simp only [rho, hk, dif_pos, Function.comp_apply, Fin.eta]
  · rw [rho_ge σ k hk, dif_neg hk, dif_neg hk]

def keyf (a b c d : ℕ) : ℕ := (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

theorem keyf_swap1 (a b c d : ℕ) : keyf a b c d = keyf b a c d := by
  simp only [keyf, min_comm a b, max_comm a b]

theorem keyf_swap2 (a b c d : ℕ) : keyf a b c d = keyf a b d c := by
  simp only [keyf, min_comm c d, max_comm c d]

theorem key_mm (f : ℕ → ℕ) (p q r s : ℕ) :
    keyf (f (min p q)) (f (max p q)) (f (min r s)) (f (max r s)) = keyf (f p) (f q) (f r) (f s) := by
  rcases le_total p q with h | h <;> rcases le_total r s with h' | h'
  · rw [min_eq_left h, max_eq_right h, min_eq_left h', max_eq_right h']
  · rw [min_eq_left h, max_eq_right h, min_eq_right h', max_eq_left h', keyf_swap2]
  · rw [min_eq_right h, max_eq_left h, min_eq_left h', max_eq_right h', keyf_swap1]
  · rw [min_eq_right h, max_eq_left h, min_eq_right h', max_eq_left h', keyf_swap1, keyf_swap2]

theorem eval_sorted (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (f : ℕ → Bool)
    (p q : ℕ) : op.eval [f (min p q), f (max p q)] = op.eval [f p, f q] := by
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

end PEqualNP.Outside.L_meta_3010

theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro x1 x2 hAO hnd h2 h26 hf x8 x9
  obtain ⟨hAnd, hRB, hLen⟩ := hAO
  obtain ⟨g0, g1, rest, hg⟩ : ∃ g0 g1 rest, x2.gates = g0 :: g1 :: rest := by
    rcases hx : x2.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size, hx] at h2
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size, hx] at h2
    · exact ⟨g0, g1, rest, rfl⟩
  have hm0 : g0 ∈ x2.gates := by rw [hg]; simp
  have hm1 : g1 ∈ x2.gates := by rw [hg]; simp
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hLen g0 hm0)
  obtain ⟨c, d, hcd⟩ := List.length_eq_two.mp (hLen g1 hm1)
  have hlen : x2.gates.length = rest.length + 2 := by rw [hg]; simp
  have hga0 : PEqualNP.MetaComplexity.NestedCover.gateAt x2 0 = g0 := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hg]
  have hga1 : PEqualNP.MetaComplexity.NestedCover.gateAt x2 1 = g1 := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hg]
  have ha : a < 14 := by
    have := hRB 0 (by omega) a (by rw [hga0, hab]; simp)
    omega
  have hb : b < 14 := by
    have := hRB 0 (by omega) b (by rw [hga0, hab]; simp)
    omega
  have hc : c < 15 := by
    have := hRB 1 (by omega) c (by rw [hga1, hcd]; simp)
    omega
  have hd : d < 15 := by
    have := hRB 1 (by omega) d (by rw [hga1, hcd]; simp)
    omega
  have hne0 : a ≠ b := by
    have := hnd g0 hm0
    rw [hab] at this
    simpa using this
  have hne1 : c ≠ d := by
    have := hnd g1 hm1
    rw [hcd] at this
    simpa using this
  let S : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter (fun σ => ∀ y : Fin 14 → Bool, x1 (y ∘ ⇑σ) = x1 y)
  let K : Equiv.Perm (Fin 14) → ℕ := fun σ =>
    PEqualNP.Outside.L_meta_3010.keyf (PEqualNP.Outside.L_meta_3010.rho σ a)
      (PEqualNP.Outside.L_meta_3010.rho σ b) (PEqualNP.Outside.L_meta_3010.rho σ c)
      (PEqualNP.Outside.L_meta_3010.rho σ d)
  obtain ⟨σ, hσS, hmin⟩ := S.exists_min_image K ⟨1, by simp [S]⟩
  have hσ : ∀ y : Fin 14 → Bool, x1 (y ∘ ⇑σ) = x1 y := (Finset.mem_filter.mp hσS).2
  have hra := PEqualNP.Outside.L_meta_3010.rho_lt σ a ha
  have hrb := PEqualNP.Outside.L_meta_3010.rho_lt σ b hb
  have hr15 : ∀ v, v < 15 → PEqualNP.Outside.L_meta_3010.rho σ v < 15 := by
    intro v hv
    by_cases h : v < 14
    · have := PEqualNP.Outside.L_meta_3010.rho_lt σ v h
      omega
    · rw [PEqualNP.Outside.L_meta_3010.rho_ge σ v h]
      exact hv
  have hrc := hr15 c hc
  have hrd := hr15 d hd
  have hn0 : PEqualNP.Outside.L_meta_3010.rho σ a ≠ PEqualNP.Outside.L_meta_3010.rho σ b :=
    fun h => hne0 (PEqualNP.Outside.L_meta_3010.rho_inj σ _ _ h)
  have hn1 : PEqualNP.Outside.L_meta_3010.rho σ c ≠ PEqualNP.Outside.L_meta_3010.rho σ d :=
    fun h => hne1 (PEqualNP.Outside.L_meta_3010.rho_inj σ _ _ h)
  have hx8 : ∀ p q r s, x8 p q r s = PEqualNP.Outside.L_meta_3010.keyf p q r s :=
    fun _ _ _ _ => rfl
  have hx9 : ∀ (τ : Equiv.Perm (Fin 14)) (v : ℕ) (hv : v < 15),
      x9 τ ⟨v, hv⟩ = PEqualNP.Outside.L_meta_3010.rho τ v := by
    intro τ v hv
    show (if v < 14 then _ else _) = _
    split_ifs with h
    · simp [PEqualNP.Outside.L_meta_3010.rho, h, Fin.ofNat, Nat.mod_eq_of_lt h]
    · rw [PEqualNP.Outside.L_meta_3010.rho_ge τ v h]
      omega
  have hτv : ∀ (τ : Equiv.Perm (Fin 14)) (v : ℕ) (hv : v < 14),
      ((τ ⟨v, hv⟩ : Fin 14) : ℕ) = PEqualNP.Outside.L_meta_3010.rho τ v := by
    intro τ v hv
    simp [PEqualNP.Outside.L_meta_3010.rho, hv]
  refine ⟨⟨min (PEqualNP.Outside.L_meta_3010.rho σ a) (PEqualNP.Outside.L_meta_3010.rho σ b), by omega⟩,
    ⟨max (PEqualNP.Outside.L_meta_3010.rho σ a) (PEqualNP.Outside.L_meta_3010.rho σ b), by omega⟩,
    ⟨min (PEqualNP.Outside.L_meta_3010.rho σ c) (PEqualNP.Outside.L_meta_3010.rho σ d), by omega⟩,
    ⟨max (PEqualNP.Outside.L_meta_3010.rho σ c) (PEqualNP.Outside.L_meta_3010.rho σ d), by omega⟩,
    g0.op, g1.op, ⟨rest.map (PEqualNP.Outside.L_meta_3010.rl σ), PEqualNP.Outside.L_meta_3010.rho σ x2.output⟩,
    ?_, ?_, hAnd g0 hm0, hAnd g1 hm1, ?_, ?_, ?_, ?_⟩
  · rw [Fin.mk_lt_mk]
    omega
  · rw [Fin.mk_lt_mk]
    omega
  · intro τ hτ
    have hτσ : τ * σ ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro y
      show x1 ((y ∘ ⇑τ) ∘ ⇑σ) = x1 y
      rw [hσ, hτ]
    have hk := hmin (τ * σ) hτσ
    simp only [K] at hk
    rw [hx8, hx8, hx9, hx9, hτv, hτv]
    simp only [Fin.val_mk]
    rw [PEqualNP.Outside.L_meta_3010.key_mm (PEqualNP.Outside.L_meta_3010.rho τ)]
    have e := PEqualNP.Outside.L_meta_3010.key_mm id
      (PEqualNP.Outside.L_meta_3010.rho σ a) (PEqualNP.Outside.L_meta_3010.rho σ b)
      (PEqualNP.Outside.L_meta_3010.rho σ c) (PEqualNP.Outside.L_meta_3010.rho σ d)
    simp only [id] at e
    rw [e, PEqualNP.Outside.L_meta_3010.rho_mul, PEqualNP.Outside.L_meta_3010.rho_mul,
      PEqualNP.Outside.L_meta_3010.rho_mul, PEqualNP.Outside.L_meta_3010.rho_mul]
    exact hk
  · intro g hg'
    rw [List.mem_map] at hg'
    obtain ⟨g', hg'm, rfl⟩ := hg'
    have hm : g' ∈ x2.gates := by rw [hg]; simp [hg'm]
    refine ⟨?_, ?_⟩
    · rcases hAnd g' hm with h | h <;> simp [PEqualNP.Outside.L_meta_3010.rl, h]
    · simp [PEqualNP.Outside.L_meta_3010.rl, hLen g' hm]
  · show (rest.map _).length ≤ 24
    have : x2.gates.length ≤ 26 := h26
    simp only [List.length_map]
    omega
  · intro x17 x18
    have hrel := PEqualNP.Outside.L_meta_3010.fold_rel σ x2.gates _ _
      (PEqualNP.Outside.L_meta_3010.rel_init σ x17)
    have heval : x2.eval (List.ofFn (x17 ∘ ⇑σ)) = x1 x17 := by rw [hf, hσ]
    have hF : ∀ v (hv : v < 14), x17 ⟨v, hv⟩ = (List.ofFn x17).getD v false := by
      intro v hv
      rw [PEqualNP.Outside.L_meta_3010.getD_ofFn, dif_pos hv]
    have h18 : PEqualNP.Outside.L_meta_3010.step (List.ofFn x17)
        (PEqualNP.Outside.L_meta_3010.rl σ g0) = x18 := by
      show _ = List.ofFn x17 ++ [g0.op.eval [x17 _, x17 _]]
      rw [hF, hF]
      simp only [PEqualNP.Outside.L_meta_3010.step, PEqualNP.Outside.L_meta_3010.rl, hab,
        List.map_cons, List.map_nil]
      rw [PEqualNP.Outside.L_meta_3010.eval_sorted g0.op (hAnd g0 hm0)
        (fun v => (List.ofFn x17).getD v false)]
    have key : (x2.gates.map (PEqualNP.Outside.L_meta_3010.rl σ)).foldl
        PEqualNP.Outside.L_meta_3010.step (List.ofFn x17) =
        (rest.map (PEqualNP.Outside.L_meta_3010.rl σ)).foldl PEqualNP.Outside.L_meta_3010.step
          (x18 ++ [g1.op.eval [x18.getD (min (PEqualNP.Outside.L_meta_3010.rho σ c)
            (PEqualNP.Outside.L_meta_3010.rho σ d)) false,
            x18.getD (max (PEqualNP.Outside.L_meta_3010.rho σ c)
            (PEqualNP.Outside.L_meta_3010.rho σ d)) false]]) := by
      rw [hg]
      simp only [List.map_cons, List.foldl_cons]
      rw [h18]
      congr 1
      simp only [PEqualNP.Outside.L_meta_3010.step, PEqualNP.Outside.L_meta_3010.rl, hcd,
        List.map_cons, List.map_nil]
      rw [PEqualNP.Outside.L_meta_3010.eval_sorted g1.op (hAnd g1 hm1)
        (fun v => x18.getD v false)]
    show ((rest.map (PEqualNP.Outside.L_meta_3010.rl σ)).foldl PEqualNP.Outside.L_meta_3010.step _).getD
      (PEqualNP.Outside.L_meta_3010.rho σ x2.output) false = x1 x17
    rw [← key, hrel.2.2]
    exact heval
