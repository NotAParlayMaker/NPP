import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def score (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

def lift15 (π : Equiv.Perm (Fin 14)) (i : Fin 15) : ℕ :=
  if (i : ℕ) < 14 then (π (Fin.ofNat 14 (i : ℕ)) : ℕ) else 14

def liftNat (π : Equiv.Perm (Fin 14)) (w : ℕ) : ℕ :=
  if h : w < 14 then (π ⟨w, h⟩ : ℕ) else w

def mapGate (π : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (liftNat π)⟩

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma lift15_lt (π : Equiv.Perm (Fin 14)) (i : Fin 15) : lift15 π i < 15 := by
  unfold lift15
  split_ifs with h
  · exact Nat.lt_trans (π _).isLt (by decide)
  · decide

lemma lift15_inj (π : Equiv.Perm (Fin 14)) {i j : Fin 15} (hij : lift15 π i = lift15 π j) :
    i = j := by
  unfold lift15 at hij
  split_ifs at hij with hi hj
  · have h1 : Fin.ofNat 14 (i : ℕ) = Fin.ofNat 14 (j : ℕ) := by
      apply π.injective
      exact Fin.ext hij
    have hi' : (i : ℕ) % 14 = (j : ℕ) % 14 := congrArg Fin.val h1
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hi'
    exact Fin.ext hi'
  · exfalso
    have hlt := (π (Fin.ofNat 14 (i : ℕ))).isLt
    omega
  · exfalso
    have hlt := (π (Fin.ofNat 14 (j : ℕ))).isLt
    omega
  · exact Fin.ext (by omega)

lemma liftNat_eq_lift15 (π : Equiv.Perm (Fin 14)) (i : Fin 15) :
    liftNat π (i : ℕ) = lift15 π i := by
  unfold liftNat lift15
  split_ifs with h
  · congr 1
    exact Fin.ext (by simp [Fin.ofNat, Nat.mod_eq_of_lt h])
  · omega

lemma lift15_mul (σ π : Equiv.Perm (Fin 14)) (i : Fin 15) :
    lift15 σ ⟨lift15 π i, lift15_lt π i⟩ = lift15 (σ * π) i := by
  unfold lift15
  by_cases hi : (i : ℕ) < 14
  · simp [hi, (π (Fin.ofNat 14 (i : ℕ))).isLt, Fin.ofNat, Nat.mod_eq_of_lt, Equiv.Perm.mul_apply]
  · simp [hi]

lemma eval_comm_and_or (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : Bool) :
    op.eval [a, b] = op.eval [b, a] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> rfl

lemma foldl_mapGate (π : Equiv.Perm (Fin 14)) (gs : List Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length) (h14 : 14 ≤ w1.length)
    (hinv : ∀ i, w1.getD i false = w2.getD (liftNat π i) false) :
    ∀ i, (gs.foldl stepWire w1).getD i false =
      ((gs.map (mapGate π)).foldl stepWire w2).getD (liftNat π i) false := by
  induction gs generalizing w1 w2 with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    · simp [stepWire, hlen]
    · simp [stepWire]; omega
    · intro i
      have hev : g.op.eval (g.inputs.map fun k => w1.getD k false) =
          (mapGate π g).op.eval ((mapGate π g).inputs.map fun k => w2.getD k false) := by
        simp only [mapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro k _
        exact hinv k
      by_cases hi : i < w1.length
      · have hli : liftNat π i < w2.length := by
          unfold liftNat
          split_ifs with h
          · exact Nat.lt_of_lt_of_le (π _).isLt (by omega)
          · omega
        simp only [stepWire]
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hli]
        exact hinv i
      · have hge : w1.length ≤ i := Nat.le_of_not_lt hi
        have hli_ge : w2.length ≤ liftNat π i := by
          unfold liftNat
          split_ifs with h
          · omega
          · omega
        have hli_eq : liftNat π i = i := by
          unfold liftNat
          split_ifs with h
          · omega
          · rfl
        simp only [stepWire]
        rw [hli_eq]
        by_cases heq : i = w1.length
        · subst heq
          rw [List.getD_append_right _ _ _ _ (le_refl _),
              List.getD_append_right _ _ _ _ (by omega)]
          simp only [hlen, Nat.sub_self, List.getD_cons_zero]
          exact hev
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_3010

theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro f C hAO2 hNodup h2 h26 hEval x8 x9
  rcases hAO2 with ⟨hAndOr, hRB, hLen⟩
  have hgs : ∃ g0 g1 rest, C.gates = g0 :: g1 :: rest := by
    cases hg : C.gates with
    | nil => simp [PEqualNP.CircuitLowerBounds.Circuit.size, hg] at h2
    | cons g0 gs =>
      cases gs with
      | nil => simp [PEqualNP.CircuitLowerBounds.Circuit.size, hg] at h2
      | cons g1 rest => exact ⟨g0, g1, rest, rfl⟩
  obtain ⟨g0, g1, rest, hC⟩ := hgs
  have hg0_mem : g0 ∈ C.gates := by rw [hC]; simp
  have hg1_mem : g1 ∈ C.gates := by rw [hC]; simp
  have hg0_len : g0.inputs.length = 2 := hLen g0 hg0_mem
  have hg1_len : g1.inputs.length = 2 := hLen g1 hg1_mem
  have hg0_nd : g0.inputs.Nodup := hNodup g0 hg0_mem
  have hg1_nd : g1.inputs.Nodup := hNodup g1 hg1_mem
  have hg0_op : g0.op = .and ∨ g0.op = .or := hAndOr g0 hg0_mem
  have hg1_op : g1.op = .and ∨ g1.op = .or := hAndOr g1 hg1_mem
  have h0_pair : ∃ u0 v0, g0.inputs = [u0, v0] := by
    cases hi : g0.inputs with
    | nil => simp [hi] at hg0_len
    | cons u0 t0 =>
      cases t0 with
      | nil => simp [hi] at hg0_len
      | cons v0 t1 =>
        cases t1 with
        | nil => exact ⟨u0, v0, rfl⟩
        | cons _ _ => simp [hi] at hg0_len
  have h1_pair : ∃ u1 v1, g1.inputs = [u1, v1] := by
    cases hi : g1.inputs with
    | nil => simp [hi] at hg1_len
    | cons u1 t0 =>
      cases t0 with
      | nil => simp [hi] at hg1_len
      | cons v1 t1 =>
        cases t1 with
        | nil => exact ⟨u1, v1, rfl⟩
        | cons _ _ => simp [hi] at hg1_len
  obtain ⟨u0, v0, hg0_in⟩ := h0_pair
  obtain ⟨u1, v1, hg1_in⟩ := h1_pair
  have hu0v0 : u0 ≠ v0 := by rw [hg0_in] at hg0_nd; simpa using hg0_nd
  have hu1v1 : u1 ≠ v1 := by rw [hg1_in] at hg1_nd; simpa using hg1_nd
  have hu0_lt : u0 < 14 := by
    have := hRB 0 (by rw [hC]; simp) u0
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hC, hg0_in] at this
    exact this
  have hv0_lt : v0 < 14 := by
    have := hRB 0 (by rw [hC]; simp) v0
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hC, hg0_in] at this
    exact this
  have hu1_lt : u1 < 15 := by
    have := hRB 1 (by rw [hC]; simp) u1
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hC, hg1_in] at this
    exact this
  have hv1_lt : v1 < 15 := by
    have := hRB 1 (by rw [hC]; simp) v1
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hC, hg1_in] at this
    exact this
  let a0 : Fin 14 := ⟨u0, hu0_lt⟩
  let b0 : Fin 14 := ⟨v0, hv0_lt⟩
  let c0 : Fin 15 := ⟨u1, hu1_lt⟩
  let d0 : Fin 15 := ⟨v1, hv1_lt⟩
  have ha0b0 : a0 ≠ b0 := fun h => hu0v0 (congrArg Fin.val h)
  have hc0d0 : c0 ≠ d0 := fun h => hu1v1 (congrArg Fin.val h)
  classical
  let S : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter (fun π => ∀ x : Fin 14 → Bool, f (x ∘ ⇑π) = f x)
  have h1S : (1 : Equiv.Perm (Fin 14)) ∈ S := by
    simp [S]
  let scoreFn : Equiv.Perm (Fin 14) → ℕ :=
    fun π => PEqualNP.Outside.L_meta_3010.score (π a0 : ℕ) (π b0 : ℕ)
      (PEqualNP.Outside.L_meta_3010.lift15 π c0) (PEqualNP.Outside.L_meta_3010.lift15 π d0)
  let vals : Finset ℕ := S.image scoreFn
  have hvals_ne : vals.Nonempty := ⟨scoreFn 1, Finset.mem_image_of_mem scoreFn h1S⟩
  obtain ⟨π0, hπ0S, hπ0_min⟩ := Finset.mem_image.mp (Finset.min'_mem vals hvals_ne)
  have hπ0_pres : ∀ x : Fin 14 → Bool, f (x ∘ ⇑π0) = f x := (Finset.mem_filter.mp hπ0S).2
  have hmin_all : ∀ τ ∈ S, scoreFn π0 ≤ scoreFn τ := by
    intro τ hτ
    rw [hπ0_min]
    exact Finset.min'_le vals (scoreFn τ) (Finset.mem_image_of_mem scoreFn hτ)
  let x10 : Fin 14 := min (π0 a0) (π0 b0)
  let x11 : Fin 14 := max (π0 a0) (π0 b0)
  let p1 : Fin 15 := ⟨PEqualNP.Outside.L_meta_3010.lift15 π0 c0, PEqualNP.Outside.L_meta_3010.lift15_lt π0 c0⟩
  let p2 : Fin 15 := ⟨PEqualNP.Outside.L_meta_3010.lift15 π0 d0, PEqualNP.Outside.L_meta_3010.lift15_lt π0 d0⟩
  let x12 : Fin 15 := min p1 p2
  let x13 : Fin 15 := max p1 p2
  let x16 : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨rest.map (PEqualNP.Outside.L_meta_3010.mapGate π0),
     PEqualNP.Outside.L_meta_3010.liftNat π0 C.output⟩
  refine ⟨x10, x11, x12, x13, g0.op, g1.op, x16, ?_, ?_, hg0_op, hg1_op, ?_, ?_, ?_, ?_⟩
  · have hne : π0 a0 ≠ π0 b0 := fun h => ha0b0 (π0.injective h)
    rcases lt_trichotomy (π0 a0) (π0 b0) with h | h | h
    · simpa [x10, x11, min_eq_left h.le, max_eq_right h.le] using h
    · exact absurd h hne
    · simpa [x10, x11, min_eq_right h.le, max_eq_left h.le] using h
  · have hne : p1 ≠ p2 := fun h => hc0d0 (PEqualNP.Outside.L_meta_3010.lift15_inj π0 (congrArg Fin.val h))
    rcases lt_trichotomy p1 p2 with h | h | h
    · simpa [x12, x13, min_eq_left h.le, max_eq_right h.le] using h
    · exact absurd h hne
    · simpa [x12, x13, min_eq_right h.le, max_eq_left h.le] using h
  · intro σ hσ
    have hσπ0 : σ * π0 ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro x
      change f ((x ∘ ⇑σ) ∘ ⇑π0) = f x
      rw [hπ0_pres (x ∘ ⇑σ), hσ x]
    have hle := hmin_all (σ * π0) hσπ0
    have hx8_eq : x8 = PEqualNP.Outside.L_meta_3010.score := rfl
    have hx9_eq : ∀ τ i, x9 τ i = PEqualNP.Outside.L_meta_3010.lift15 τ i := fun _ _ => rfl
    rw [hx8_eq]
    have hab_eq : min (σ x10 : ℕ) (σ x11 : ℕ) = min ((σ * π0) a0 : ℕ) ((σ * π0) b0 : ℕ) ∧
        max (σ x10 : ℕ) (σ x11 : ℕ) = max ((σ * π0) a0 : ℕ) ((σ * π0) b0 : ℕ) := by
      rcases le_total (π0 a0) (π0 b0) with h | h
      · simp [x10, x11, min_eq_left h, max_eq_right h, Equiv.Perm.mul_apply]
      · simp [x10, x11, min_eq_right h, max_eq_left h, Equiv.Perm.mul_apply, min_comm, max_comm]
    have hcd_eq : min (x9 σ x12) (x9 σ x13) =
          min (PEqualNP.Outside.L_meta_3010.lift15 (σ * π0) c0) (PEqualNP.Outside.L_meta_3010.lift15 (σ * π0) d0) ∧
        max (x9 σ x12) (x9 σ x13) =
          max (PEqualNP.Outside.L_meta_3010.lift15 (σ * π0) c0) (PEqualNP.Outside.L_meta_3010.lift15 (σ * π0) d0) := by
      rcases le_total p1 p2 with h | h
      · simp only [x12, x13, min_eq_left h, max_eq_right h, hx9_eq]
        rw [PEqualNP.Outside.L_meta_3010.lift15_mul, PEqualNP.Outside.L_meta_3010.lift15_mul]
        exact ⟨rfl, rfl⟩
      · simp only [x12, x13, min_eq_right h, max_eq_left h, hx9_eq]
        rw [PEqualNP.Outside.L_meta_3010.lift15_mul, PEqualNP.Outside.L_meta_3010.lift15_mul]
        exact ⟨min_comm _ _, max_comm _ _⟩
    have h0_ab : min (x10 : ℕ) (x11 : ℕ) = min (π0 a0 : ℕ) (π0 b0 : ℕ) ∧
        max (x10 : ℕ) (x11 : ℕ) = max (π0 a0 : ℕ) (π0 b0 : ℕ) := by
      rcases le_total (π0 a0) (π0 b0) with h | h
      · simp [x10, x11, min_eq_left h, max_eq_right h]
      · simp [x10, x11, min_eq_right h, max_eq_left h, min_comm, max_comm]
    have h0_cd : min (x12 : ℕ) (x13 : ℕ) =
          min (PEqualNP.Outside.L_meta_3010.lift15 π0 c0) (PEqualNP.Outside.L_meta_3010.lift15 π0 d0) ∧
        max (x12 : ℕ) (x13 : ℕ) =
          max (PEqualNP.Outside.L_meta_3010.lift15 π0 c0) (PEqualNP.Outside.L_meta_3010.lift15 π0 d0) := by
      rcases le_total p1 p2 with h | h
      · simp [x12, x13, p1, p2, min_eq_left h, max_eq_right h]
      · simp [x12, x13, p1, p2, min_eq_right h, max_eq_left h, min_comm, max_comm]
    unfold PEqualNP.Outside.L_meta_3010.score at hle ⊢
    rw [h0_ab.1, h0_ab.2, h0_cd.1, h0_cd.2, hab_eq.1, hab_eq.2, hcd_eq.1, hcd_eq.2]
    exact hle
  · intro g hg
    simp only [x16, List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have hg'_mem : g' ∈ C.gates := by rw [hC]; simp [hg']
    refine ⟨?_, ?_⟩
    · rcases hAndOr g' hg'_mem with h | h <;> simp [PEqualNP.Outside.L_meta_3010.mapGate, h]
    · simp [PEqualNP.Outside.L_meta_3010.mapGate, hLen g' hg'_mem]
  · simp only [x16, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_map]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size, hC, List.length_cons] at h26
    omega
  · intro x x18
    let y : Fin 14 → Bool := x ∘ ⇑π0
    have hy_eval : C.eval (List.ofFn y) = f x := by
      rw [hEval y]
      exact hπ0_pres x
    rw [← hy_eval]
    let w1_0 : List Bool := PEqualNP.Outside.L_meta_3010.stepWire (List.ofFn y) g0
    let w1_1 : List Bool := PEqualNP.Outside.L_meta_3010.stepWire w1_0 g1
    let w2_1 : List Bool := x18 ++ [g1.op.eval [x18.getD (x12 : ℕ) false, x18.getD (x13 : ℕ) false]]
    have hg0_eq : g0.op.eval [y a0, y b0] = g0.op.eval [x x10, x x11] := by
      rcases le_total (π0 a0) (π0 b0) with h | h
      · simp [x10, x11, min_eq_left h, max_eq_right h, y]
      · simp only [x10, x11, min_eq_right h, max_eq_left h, y, Function.comp_apply]
        exact PEqualNP.Outside.L_meta_3010.eval_comm_and_or g0.op hg0_op _ _
    have hw10_eq : w1_0 = List.ofFn y ++ [g0.op.eval [y a0, y b0]] := by
      simp only [w1_0, PEqualNP.Outside.L_meta_3010.stepWire, hg0_in, List.map_cons, List.map_nil]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hu0_lt, hv0_lt, ↓reduceDIte, Option.getD_some]
      rfl
    have hinv0 : ∀ i, w1_0.getD i false = x18.getD (PEqualNP.Outside.L_meta_3010.liftNat π0 i) false := by
      intro i
      by_cases hi : i < 14
      · have hpi : (π0 ⟨i, hi⟩ : ℕ) < 14 := (π0 ⟨i, hi⟩).isLt
        have hln : PEqualNP.Outside.L_meta_3010.liftNat π0 i = (π0 ⟨i, hi⟩ : ℕ) := by
          simp [PEqualNP.Outside.L_meta_3010.liftNat, hi]
        rw [hln, hw10_eq, List.getD_append _ _ _ _ (by simp [hi]),
            List.getD_append _ _ _ _ (by simp [hpi])]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_ofFn, List.getElem?_ofFn]
        simp [hi, hpi, y]
      · have hln : PEqualNP.Outside.L_meta_3010.liftNat π0 i = i := by
          simp [PEqualNP.Outside.L_meta_3010.liftNat, hi]
        rw [hln, hw10_eq]
        by_cases hi14 : i = 14
        · subst hi14
          rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
          simp [x18, hg0_eq]
        · have hge15 : 15 ≤ i := by omega
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [x18]; omega)]
    have hg1_eq : g1.op.eval [w1_0.getD u1 false, w1_0.getD v1 false] =
        g1.op.eval [x18.getD (x12 : ℕ) false, x18.getD (x13 : ℕ) false] := by
      have hu1_e : w1_0.getD u1 false = x18.getD (p1 : ℕ) false := by
        rw [hinv0 u1]
        congr 1
        exact PEqualNP.Outside.L_meta_3010.liftNat_eq_lift15 π0 c0
      have hv1_e : w1_0.getD v1 false = x18.getD (p2 : ℕ) false := by
        rw [hinv0 v1]
        congr 1
        exact PEqualNP.Outside.L_meta_3010.liftNat_eq_lift15 π0 d0
      rw [hu1_e, hv1_e]
      rcases le_total p1 p2 with h | h
      · simp [x12, x13, min_eq_left h, max_eq_right h]
      · simp only [x12, x13, min_eq_right h, max_eq_left h]
        exact PEqualNP.Outside.L_meta_3010.eval_comm_and_or g1.op hg1_op _ _
    have hw11_eq : w1_1 = w1_0 ++ [g1.op.eval [w1_0.getD u1 false, w1_0.getD v1 false]] := by
      simp [w1_1, PEqualNP.Outside.L_meta_3010.stepWire, hg1_in]
    have hinv1 : ∀ i, w1_1.getD i false = w2_1.getD (PEqualNP.Outside.L_meta_3010.liftNat π0 i) false := by
      intro i
      by_cases hi : i < 15
      · have hpi : PEqualNP.Outside.L_meta_3010.liftNat π0 i < 15 := by
          rw [PEqualNP.Outside.L_meta_3010.liftNat_eq_lift15 π0 ⟨i, hi⟩]
          exact PEqualNP.Outside.L_meta_3010.lift15_lt π0 ⟨i, hi⟩
        rw [hw11_eq, List.getD_append _ _ _ _ (by simp [hw10_eq, hi]),
            List.getD_append _ _ _ _ (by simp [x18, hpi])]
        exact hinv0 i
      · have hln : PEqualNP.Outside.L_meta_3010.liftNat π0 i = i := by
          simp [PEqualNP.Outside.L_meta_3010.liftNat, show ¬ i < 14 by omega]
        rw [hln, hw11_eq]
        by_cases hi15 : i = 15
        · subst hi15
          have hw10_len : w1_0.length = 15 := by simp [hw10_eq]
          have hx18_len : x18.length = 15 := by simp [x18]
          rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega),
              hw10_len, hx18_len]
          simp only [Nat.sub_self, List.getD_cons_zero]
          exact hg1_eq
        · have hge16 : 16 ≤ i := by omega
          rw [List.getD_eq_default _ _ (by simp [hw10_eq]; omega),
              List.getD_eq_default _ _ (by simp [w2_1, x18]; omega)]
    have hlen1 : w1_1.length = w2_1.length := by
      simp [w1_1, w2_1, hw10_eq, x18, PEqualNP.Outside.L_meta_3010.stepWire]
    have h14_le : 14 ≤ w1_1.length := by
      simp [w1_1, hw10_eq, PEqualNP.Outside.L_meta_3010.stepWire]
    have hfold := PEqualNP.Outside.L_meta_3010.foldl_mapGate π0 rest w1_1 w2_1 hlen1 h14_le hinv1 C.output
    change (x16.wires w2_1).getD x16.output false = (C.wires (List.ofFn y)).getD C.output false
    have hCw : C.wires (List.ofFn y) = rest.foldl PEqualNP.Outside.L_meta_3010.stepWire w1_1 := by
      rw [PEqualNP.CircuitLowerBounds.Circuit.wires, hC]
      rfl
    have hx16w : x16.wires w2_1 = (rest.map (PEqualNP.Outside.L_meta_3010.mapGate π0)).foldl PEqualNP.Outside.L_meta_3010.stepWire w2_1 := rfl
    rw [hCw, hx16w]
    exact hfold.symm
