import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3322

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def key (u v p q : ℕ) : ℕ :=
  ((15 * min u v + max u v) * 225) + (15 * min p q + max p q)

def act15 (σ : Equiv.Perm (Fin 14)) (i : Fin 15) : ℕ :=
  if i < (14 : Fin 15) then ↑(σ (Fin.ofNat 14 ↑i)) else 14

def permWire (σ : Equiv.Perm (Fin 14)) (w : ℕ) : ℕ :=
  if h : w < 14 then (σ ⟨w, h⟩).val else w

def permFin15 (σ : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  if h : i.val < 14 then ⟨(σ ⟨i.val, h⟩).val, by have := (σ ⟨i.val, h⟩).isLt; omega⟩ else ⟨14, by omega⟩

def permGate (σ : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (permWire σ)⟩

def permCircuit (σ : Equiv.Perm (Fin 14)) (D : Circuit) : Circuit :=
  ⟨D.gates.map (permGate σ), permWire σ D.output⟩

lemma op_comm (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : Bool) :
    op.eval [a, b] = op.eval [b, a] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> rfl

lemma min_max_pair {α : Type*} [LinearOrder α] (x y : α) :
    (min x y = x ∧ max x y = y) ∨ (min x y = y ∧ max x y = x) := by
  rcases le_total x y with h | h
  · exact Or.inl ⟨min_eq_left h, max_eq_right h⟩
  · exact Or.inr ⟨min_eq_right h, max_eq_left h⟩

lemma op_eval_min_max {α : Type*} [LinearOrder α] (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (f : α → Bool) (x y : α) :
    op.eval [f (min x y), f (max x y)] = op.eval [f x, f y] := by
  rcases min_max_pair x y with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, op_comm op hop]

lemma key_swap1 (u v p q : ℕ) : key v u p q = key u v p q := by
  unfold key
  rw [Nat.min_comm, Nat.max_comm]

lemma key_swap2 (u v p q : ℕ) : key u v q p = key u v p q := by
  unfold key
  rw [Nat.min_comm p q, Nat.max_comm p q]

lemma key_min_max (u v p q : ℕ) :
    key (min u v) (max u v) (min p q) (max p q) = key u v p q := by
  rcases min_max_pair u v with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases min_max_pair p q with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h1, h2, h3, h4]
  · rw [h1, h2, h3, h4, key_swap2]
  · rw [h1, h2, h3, h4, key_swap1]
  · rw [h1, h2, h3, h4, key_swap1, key_swap2]

lemma fin_ofNat_14_eq (k : ℕ) (hk : k < 14) : Fin.ofNat 14 k = (⟨k, hk⟩ : Fin 14) := by
  apply Fin.ext
  change k % 14 = k
  exact Nat.mod_eq_of_lt hk

lemma act15_eq_permWire (σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    act15 σ i = permWire σ i.val := by
  unfold act15 permWire
  have hiff : (i < (14 : Fin 15)) ↔ i.val < 14 := Iff.rfl
  by_cases hi : i.val < 14
  · have hi' : i < (14 : Fin 15) := hi
    rw [if_pos hi', dif_pos hi, fin_ofNat_14_eq i.val hi]
  · have hi' : ¬ (i < (14 : Fin 15)) := hi
    have hval14 : i.val = 14 := by have := i.isLt; omega
    rw [if_neg hi', dif_neg hi, hval14]

lemma permFin15_val (σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (permFin15 σ i).val = act15 σ i := by
  unfold permFin15
  rw [act15_eq_permWire]
  unfold permWire
  by_cases hi : i.val < 14
  · rw [dif_pos hi, dif_pos hi]
  · have hval14 : i.val = 14 := by have := i.isLt; omega
    rw [dif_neg hi, dif_neg hi, hval14]

lemma permFin15_ne (σ : Equiv.Perm (Fin 14)) {i j : Fin 15} (hne : i ≠ j) :
    permFin15 σ i ≠ permFin15 σ j := by
  intro heq
  have hv := congrArg Fin.val heq
  unfold permFin15 at hv
  by_cases hi : i.val < 14 <;> by_cases hj : j.val < 14
  · simp only [hi, hj, dite_true] at hv
    have hσeq : σ ⟨i.val, hi⟩ = σ ⟨j.val, hj⟩ := Fin.ext hv
    have hinj := σ.injective hσeq
    have hinj_val : i.val = j.val := congrArg (@Fin.val 14) hinj
    exact hne (Fin.ext hinj_val)
  · simp only [hi, hj, dite_true, dite_false] at hv
    have := (σ ⟨i.val, hi⟩).isLt
    omega
  · simp only [hi, hj, dite_true, dite_false] at hv
    have := (σ ⟨j.val, hj⟩).isLt
    omega
  · have hi14 : i.val = 14 := by have := i.isLt; omega
    have hj14 : j.val = 14 := by have := j.isLt; omega
    exact hne (Fin.ext (hi14.trans hj14.symm))

lemma act15_permFin15 (τ σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    act15 τ (permFin15 σ i) = act15 (τ * σ) i := by
  rw [act15_eq_permWire, act15_eq_permWire]
  unfold permFin15 permWire
  by_cases hi : i.val < 14
  · have hσlt : (σ ⟨i.val, hi⟩).val < 14 := (σ ⟨i.val, hi⟩).isLt
    simp only [hi, dite_true, hσlt]
    rfl
  · have hi14 : i.val = 14 := by have := i.isLt; omega
    simp [hi, hi14]

lemma permWire_lt_of_lt (σ : Equiv.Perm (Fin 14)) {w len : ℕ} (hlen : 14 ≤ len) (hw : w < len) :
    permWire σ w < len := by
  unfold permWire
  by_cases h : w < 14
  · rw [dif_pos h]; exact Nat.lt_of_lt_of_le (σ ⟨w, h⟩).isLt hlen
  · rw [dif_neg h]; exact hw

lemma permWire_ge_14 (σ : Equiv.Perm (Fin 14)) {w : ℕ} (hw : 14 ≤ w) :
    permWire σ w = w := by
  unfold permWire
  rw [dif_neg (by omega)]

lemma getD_append_corr (σ : Equiv.Perm (Fin 14)) {u v : List Bool} (b : Bool)
    (h14 : 14 ≤ u.length) (hlen : u.length = v.length)
    (hcorr : ∀ w : ℕ, u.getD w false = v.getD (permWire σ w) false) :
    ∀ w : ℕ, (u ++ [b]).getD w false = (v ++ [b]).getD (permWire σ w) false := by
  intro w
  by_cases hlt : w < u.length
  · have hplt : permWire σ w < v.length := by rw [← hlen]; exact permWire_lt_of_lt σ h14 hlt
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hplt]
    exact hcorr w
  · by_cases heq : w = u.length
    · subst heq
      rw [permWire_ge_14 σ h14]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    · have hgt : u.length + 1 ≤ w := by omega
      have hp : permWire σ w = w := permWire_ge_14 σ (by omega)
      rw [hp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]

lemma foldl_permGate (σ : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ (u v : List Bool), 14 ≤ u.length → u.length = v.length →
      (∀ w : ℕ, u.getD w false = v.getD (permWire σ w) false) →
      ∀ w : ℕ, (gs.foldl step u).getD w false =
        ((gs.map (permGate σ)).foldl step v).getD (permWire σ w) false := by
  induction gs with
  | nil => intro u v _ _ hcorr w; exact hcorr w
  | cons g gs ih =>
    intro u v h14 hlen hcorr w
    simp only [List.map_cons, List.foldl_cons]
    have hbit : (permGate σ g).op.eval ((permGate σ g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => u.getD i false) := by
      unfold permGate
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (hcorr i).symm
    apply ih (step u g) (step v (permGate σ g))
    · simp [step]; omega
    · simp [step, hlen]
    · unfold step
      rw [hbit]
      exact getD_append_corr σ _ h14 hlen hcorr

lemma permCircuit_mono (σ : Equiv.Perm (Fin 14)) {D : Circuit} (hD : Monotone2 D) :
    Monotone2 (permCircuit σ D) := by
  intro g hg
  simp only [permCircuit, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨hop, hlen⟩ := hD g0 hg0
  exact ⟨hop, by simp [permGate, hlen]⟩

lemma permCircuit_size (σ : Equiv.Perm (Fin 14)) (D : Circuit) :
    (permCircuit σ D).size = D.size := by
  simp [permCircuit, Circuit.size]

lemma exists_min_nat {α : Type*} (P : α → Prop) (hP : ∃ x, P x) (f : α → ℕ) :
    ∃ m, P m ∧ ∀ x, P x → f m ≤ f x := by
  classical
  have hex : ∃ n : ℕ, ∃ x, P x ∧ f x = n := by
    obtain ⟨x0, hx0⟩ := hP
    exact ⟨f x0, x0, hx0, rfl⟩
  obtain ⟨m, hm, hfm⟩ := Nat.find_spec hex
  refine ⟨m, hm, fun x hx => ?_⟩
  rw [hfm]
  exact Nat.find_min' hex ⟨x, hx, rfl⟩

lemma peel_two
    (F : (Fin 14 → Bool) → Bool) (C : Circuit)
    (hAO : IsAO2 14 C) (hNodup : ∀ g ∈ C.gates, g.inputs.Nodup)
    (h2 : 2 ≤ C.size) (h26 : C.size ≤ 26)
    (hEval : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = F x) :
    ∃ (a0 b0 : Fin 14) (c0 d0 : Fin 15) (op1 op2 : GateOp) (D0 : Circuit),
      a0 < b0 ∧ c0 < d0 ∧
      (op1 = GateOp.and ∨ op1 = GateOp.or) ∧
      (op2 = GateOp.and ∨ op2 = GateOp.or) ∧
      Monotone2 D0 ∧ D0.size ≤ 24 ∧
      ∀ y : Fin 14 → Bool,
        let wy : List Bool := List.ofFn y ++ [op1.eval [y a0, y b0]]
        D0.eval (wy ++ [op2.eval [wy.getD c0.val false, wy.getD d0.val false]]) = F y := by
  obtain ⟨hAndOr, hRB, hLen2⟩ := hAO
  have hglen : 2 ≤ C.gates.length := h2
  rcases hgs : C.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp [hgs] at hglen
  · simp [hgs] at hglen
  · have hg0_mem : g0 ∈ C.gates := by simp [hgs]
    have hg1_mem : g1 ∈ C.gates := by simp [hgs]
    have hop1 : g0.op = GateOp.and ∨ g0.op = GateOp.or := hAndOr g0 hg0_mem
    have hop2 : g1.op = GateOp.and ∨ g1.op = GateOp.or := hAndOr g1 hg1_mem
    have hlen_g0 : g0.inputs.length = 2 := hLen2 g0 hg0_mem
    have hlen_g1 : g1.inputs.length = 2 := hLen2 g1 hg1_mem
    have hnd_g0 : g0.inputs.Nodup := hNodup g0 hg0_mem
    have hnd_g1 : g1.inputs.Nodup := hNodup g1 hg1_mem
    have hgate0 : gateAt C 0 = g0 := by simp [gateAt, hgs]
    have hgate1 : gateAt C 1 = g1 := by simp [gateAt, hgs]
    rcases hin0 : g0.inputs with _ | ⟨i0, _ | ⟨j0, _ | _⟩⟩
    · simp [hin0] at hlen_g0
    · simp [hin0] at hlen_g0
    · rcases hin1 : g1.inputs with _ | ⟨i1, _ | ⟨j1, _ | _⟩⟩
      · simp [hin1] at hlen_g1
      · simp [hin1] at hlen_g1
      · have hi0_lt : i0 < 14 := by
          have := hRB 0 (by simp [hgs]) i0 (by simp [hgate0, hin0]); omega
        have hj0_lt : j0 < 14 := by
          have := hRB 0 (by simp [hgs]) j0 (by simp [hgate0, hin0]); omega
        have hi1_lt : i1 < 15 := by
          have := hRB 1 (by simp [hgs]) i1 (by simp [hgate1, hin1]); omega
        have hj1_lt : j1 < 15 := by
          have := hRB 1 (by simp [hgs]) j1 (by simp [hgate1, hin1]); omega
        have hne0 : i0 ≠ j0 := by rw [hin0, List.nodup_cons] at hnd_g0; simp at hnd_g0; exact hnd_g0
        have hne1 : i1 ≠ j1 := by rw [hin1, List.nodup_cons] at hnd_g1; simp at hnd_g1; exact hnd_g1
        let u0 : Fin 14 := ⟨i0, hi0_lt⟩
        let v0 : Fin 14 := ⟨j0, hj0_lt⟩
        let u1 : Fin 15 := ⟨i1, hi1_lt⟩
        let v1 : Fin 15 := ⟨j1, hj1_lt⟩
        have huv0 : u0 ≠ v0 := fun h => hne0 (congrArg Fin.val h)
        have huv1 : u1 ≠ v1 := fun h => hne1 (congrArg Fin.val h)
        let a0 : Fin 14 := min u0 v0
        let b0 : Fin 14 := max u0 v0
        let c0 : Fin 15 := min u1 v1
        let d0 : Fin 15 := max u1 v1
        have hab0 : a0 < b0 := lt_of_le_of_ne (min_le_max) (by
          rcases min_max_pair u0 v0 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · dsimp only [a0, b0]; rw [e1, e2]; exact huv0
          · dsimp only [a0, b0]; rw [e1, e2]; exact huv0.symm)
        have hcd0 : c0 < d0 := lt_of_le_of_ne (min_le_max) (by
          rcases min_max_pair u1 v1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · dsimp only [c0, d0]; rw [e1, e2]; exact huv1
          · dsimp only [c0, d0]; rw [e1, e2]; exact huv1.symm)
        let D0 : Circuit := ⟨rest, C.output⟩
        have hMonoD0 : Monotone2 D0 := by
          intro g hg
          have hgC : g ∈ C.gates := by simp [hgs, D0] at hg ⊢; exact Or.inr (Or.inr hg)
          refine ⟨?_, ?_⟩
          · rcases hAndOr g hgC with h | h <;> simp [h]
          · have := hLen2 g hgC; omega
        have hSizeD0 : D0.size ≤ 24 := by
          have : C.size = rest.length + 2 := by simp [Circuit.size, hgs]
          change rest.length ≤ 24
          omega
        refine ⟨a0, b0, c0, d0, g0.op, g1.op, D0, hab0, hcd0, hop1, hop2, hMonoD0, hSizeD0, ?_⟩
        intro y
        dsimp only
        rw [← hEval y]
        unfold Circuit.eval Circuit.wires
        rw [hgs]
        simp only [List.foldl_cons, D0]
        have hbit0 : g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false) =
            g0.op.eval [y a0, y b0] := by
          rw [hin0]
          simp only [List.map]
          have get_u0 : (List.ofFn y).getD i0 false = y u0 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi0_lt),
                Option.getD_some, List.getElem_ofFn]
          have get_v0 : (List.ofFn y).getD j0 false = y v0 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hj0_lt),
                Option.getD_some, List.getElem_ofFn]
          rw [get_u0, get_v0]
          exact (op_eval_min_max g0.op hop1 y u0 v0).symm
        rw [hbit0]
        let wy := List.ofFn y ++ [g0.op.eval [y a0, y b0]]
        have hbit1 : g1.op.eval (g1.inputs.map fun i => wy.getD i false) =
            g1.op.eval [wy.getD c0.val false, wy.getD d0.val false] := by
          rw [hin1]
          simp only [List.map]
          exact (op_eval_min_max g1.op hop2 (fun z : Fin 15 => wy.getD z.val false) u1 v1).symm
        change (rest.foldl step (wy ++ [g1.op.eval [wy.getD c0.val false, wy.getD d0.val false]])).getD C.output false =
          (rest.foldl step (wy ++ [g1.op.eval (g1.inputs.map fun i => wy.getD i false)])).getD C.output false
        rw [hbit1]
      · simp [hin1] at hlen_g1
    · simp [hin0] at hlen_g0

end PEqualNP.Outside.L_meta_3322

theorem PEqualNP.Outside.L_meta_3322 :
    ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro F C hAO hNodup h2 h26 hEval
  dsimp only
  obtain ⟨a0, b0, c0, d0, op1, op2, D0, hab0, hcd0, hop1, hop2, hMono0, hSize0, hEv0⟩ :=
    PEqualNP.Outside.L_meta_3322.peel_two F C hAO hNodup h2 h26 hEval
  let IsStab : Equiv.Perm (Fin 14) → Prop :=
    fun σ => ∀ x : Fin 14 → Bool, F (x ∘ ⇑σ) = F x
  have h1Stab : IsStab 1 := fun _ => rfl
  let score : Equiv.Perm (Fin 14) → ℕ := fun σ =>
    PEqualNP.Outside.L_meta_3322.key (σ a0).val (σ b0).val
      (PEqualNP.Outside.L_meta_3322.act15 σ c0) (PEqualNP.Outside.L_meta_3322.act15 σ d0)
  obtain ⟨σ, hσStab, hσMin⟩ :=
    PEqualNP.Outside.L_meta_3322.exists_min_nat IsStab ⟨1, h1Stab⟩ score
  let u := σ a0
  let v := σ b0
  let p := PEqualNP.Outside.L_meta_3322.permFin15 σ c0
  let q := PEqualNP.Outside.L_meta_3322.permFin15 σ d0
  have huv : u ≠ v := fun h => (ne_of_lt hab0) (σ.injective h)
  have hpq : p ≠ q := PEqualNP.Outside.L_meta_3322.permFin15_ne σ (ne_of_lt hcd0)
  let a : Fin 14 := min u v
  let b : Fin 14 := max u v
  let c : Fin 15 := min p q
  let d : Fin 15 := max p q
  have hab : a < b := lt_of_le_of_ne min_le_max (by
    rcases PEqualNP.Outside.L_meta_3322.min_max_pair u v with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · dsimp only [a, b]; rw [e1, e2]; exact huv
    · dsimp only [a, b]; rw [e1, e2]; exact huv.symm)
  have hcd : c < d := lt_of_le_of_ne min_le_max (by
    rcases PEqualNP.Outside.L_meta_3322.min_max_pair p q with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · dsimp only [c, d]; rw [e1, e2]; exact hpq
    · dsimp only [c, d]; rw [e1, e2]; exact hpq.symm)
  let D := PEqualNP.Outside.L_meta_3322.permCircuit σ D0
  refine ⟨a, b, c, d, op1, op2, D, hab, hcd, hop1, hop2, ?_,
    PEqualNP.Outside.L_meta_3322.permCircuit_mono σ hMono0,
    by rw [PEqualNP.Outside.L_meta_3322.permCircuit_size]; exact hSize0, ?_⟩
  · intro τ hτ
    change PEqualNP.Outside.L_meta_3322.key a.val b.val c.val d.val ≤
      PEqualNP.Outside.L_meta_3322.key (τ a).val (τ b).val
        (PEqualNP.Outside.L_meta_3322.act15 τ c) (PEqualNP.Outside.L_meta_3322.act15 τ d)
    have hLHS : PEqualNP.Outside.L_meta_3322.key a.val b.val c.val d.val = score σ := by
      have ha_eq : a.val = min u.val v.val := rfl
      have hb_eq : b.val = max u.val v.val := rfl
      have hc_eq : c.val = min p.val q.val := rfl
      have hd_eq : d.val = max p.val q.val := rfl
      rw [ha_eq, hb_eq, hc_eq, hd_eq, PEqualNP.Outside.L_meta_3322.key_min_max]
      rw [PEqualNP.Outside.L_meta_3322.permFin15_val, PEqualNP.Outside.L_meta_3322.permFin15_val]
    have hRHS : PEqualNP.Outside.L_meta_3322.key (τ a).val (τ b).val
        (PEqualNP.Outside.L_meta_3322.act15 τ c) (PEqualNP.Outside.L_meta_3322.act15 τ d) =
        score (τ * σ) := by
      have h1 : ∀ r s : ℕ,
          PEqualNP.Outside.L_meta_3322.key (τ a).val (τ b).val r s =
            PEqualNP.Outside.L_meta_3322.key ((τ * σ) a0).val ((τ * σ) b0).val r s := by
        intro r s
        rcases PEqualNP.Outside.L_meta_3322.min_max_pair u v with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have ea : a = u := e1
          have eb : b = v := e2
          rw [ea, eb]; rfl
        · have ea : a = v := e1
          have eb : b = u := e2
          rw [ea, eb, PEqualNP.Outside.L_meta_3322.key_swap1]; rfl
      have h2 : PEqualNP.Outside.L_meta_3322.key ((τ * σ) a0).val ((τ * σ) b0).val
          (PEqualNP.Outside.L_meta_3322.act15 τ c) (PEqualNP.Outside.L_meta_3322.act15 τ d) =
            score (τ * σ) := by
        rcases PEqualNP.Outside.L_meta_3322.min_max_pair p q with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have ec : c = p := e1
          have ed : d = q := e2
          rw [ec, ed, PEqualNP.Outside.L_meta_3322.act15_permFin15,
              PEqualNP.Outside.L_meta_3322.act15_permFin15]
        · have ec : c = q := e1
          have ed : d = p := e2
          rw [ec, ed, PEqualNP.Outside.L_meta_3322.key_swap2,
              PEqualNP.Outside.L_meta_3322.act15_permFin15,
              PEqualNP.Outside.L_meta_3322.act15_permFin15]
      rw [h1, h2]
    have hCompStab : IsStab (τ * σ) := by
      intro x
      have hcomp : (x ∘ ⇑(τ * σ)) = ((x ∘ ⇑τ) ∘ ⇑σ) := rfl
      rw [hcomp, hσStab (x ∘ ⇑τ), hτ x]
    rw [hLHS, hRHS]
    exact hσMin (τ * σ) hCompStab
  · intro x
    let y : Fin 14 → Bool := x ∘ ⇑σ
    have hbit0 : op1.eval [x a, x b] = op1.eval [y a0, y b0] :=
      PEqualNP.Outside.L_meta_3322.op_eval_min_max op1 hop1 x u v
    let wx : List Bool := List.ofFn x ++ [op1.eval [x a, x b]]
    let wy : List Bool := List.ofFn y ++ [op1.eval [y a0, y b0]]
    have hcorr_w : ∀ w : ℕ, wy.getD w false = wx.getD (PEqualNP.Outside.L_meta_3322.permWire σ w) false := by
      have hcorr0 : ∀ w : ℕ, (List.ofFn y).getD w false =
          (List.ofFn x).getD (PEqualNP.Outside.L_meta_3322.permWire σ w) false := by
        intro w
        by_cases hw : w < 14
        · have hpw : PEqualNP.Outside.L_meta_3322.permWire σ w = (σ ⟨w, hw⟩).val := dif_pos hw
          rw [hpw]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hw),
              Option.getD_some, List.getElem_ofFn]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact (σ ⟨w, hw⟩).isLt),
              Option.getD_some, List.getElem_ofFn]
          rfl
        · have hpw : PEqualNP.Outside.L_meta_3322.permWire σ w = w :=
            PEqualNP.Outside.L_meta_3322.permWire_ge_14 σ (by omega)
          rw [hpw]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      dsimp only [wx, wy]
      rw [hbit0]
      exact PEqualNP.Outside.L_meta_3322.getD_append_corr σ _ (by simp) (by simp) hcorr0
    have hbit1 : op2.eval [wx.getD c.val false, wx.getD d.val false] =
        op2.eval [wy.getD c0.val false, wy.getD d0.val false] := by
      have heq_mm := PEqualNP.Outside.L_meta_3322.op_eval_min_max op2 hop2
        (fun z : Fin 15 => wx.getD z.val false) p q
      change op2.eval [wx.getD c.val false, wx.getD d.val false] = _
      rw [show c = min p q from rfl, show d = max p q from rfl, heq_mm]
      have hp_eq : wx.getD p.val false = wy.getD c0.val false := by
        rw [hcorr_w c0.val, ← PEqualNP.Outside.L_meta_3322.act15_eq_permWire,
            ← PEqualNP.Outside.L_meta_3322.permFin15_val]
      have hq_eq : wx.getD q.val false = wy.getD d0.val false := by
        rw [hcorr_w d0.val, ← PEqualNP.Outside.L_meta_3322.act15_eq_permWire,
            ← PEqualNP.Outside.L_meta_3322.permFin15_val]
      rw [hp_eq, hq_eq]
    let zx := wx ++ [op2.eval [wx.getD c.val false, wx.getD d.val false]]
    let zy := wy ++ [op2.eval [wy.getD c0.val false, wy.getD d0.val false]]
    have hcorr_z : ∀ w : ℕ, zy.getD w false = zx.getD (PEqualNP.Outside.L_meta_3322.permWire σ w) false := by
      dsimp only [zx, zy]
      rw [hbit1]
      exact PEqualNP.Outside.L_meta_3322.getD_append_corr σ _ (by simp [wy]) (by simp [wx, wy]) hcorr_w
    have hfold := PEqualNP.Outside.L_meta_3322.foldl_permGate σ D0.gates zy zx
      (by simp [zy, wy]) (by simp [zx, zy, wx, wy]) hcorr_z D0.output
    have hDeval : D.eval zx = D0.eval zy := hfold.symm
    change D.eval zx = F x
    rw [hDeval]
    exact (hEv0 y).trans (hσStab x)
