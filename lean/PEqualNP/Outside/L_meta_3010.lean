import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def score (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

def act15 (σ : Equiv.Perm (Fin 14)) (i : Fin 15) : ℕ :=
  if i.val < 14 then (σ (Fin.ofNat 14 i.val)).val else 14

def act15Fin (σ : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  ⟨act15 σ i, by unfold act15; split <;> omega⟩

def ρ (σ : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ :=
  if h : i < 14 then (σ ⟨i, h⟩).val else i

lemma act15_eq_ρ (σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    act15 σ i = ρ σ i.val := by
  unfold act15 ρ
  by_cases h : i.val < 14
  · simp only [h, ↓reduceIte, ↓reduceDIte]
    apply congrArg (fun p : Fin 14 => (σ p).val)
    ext; simp [Nat.mod_eq_of_lt h]
  · simp only [h, ↓reduceIte, ↓reduceDIte]
    omega

lemma act15_comp (τ σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    act15 τ (act15Fin σ i) = act15 (τ * σ) i := by
  unfold act15Fin act15
  by_cases h : i.val < 14
  · simp only [h, ↓reduceIte, Fin.is_lt, Equiv.Perm.mul_apply]
    congr 2; ext; simp
  · simp only [h, ↓reduceIte, lt_irrefl]

lemma act15Fin_inj (σ : Equiv.Perm (Fin 14)) : Function.Injective (act15Fin σ) := by
  intro a b hab
  have hv : act15 σ a = act15 σ b := congrArg Fin.val hab
  unfold act15 at hv
  by_cases ha : a.val < 14 <;> by_cases hb : b.val < 14
  · simp only [ha, hb, ↓reduceIte] at hv
    have heq : σ (Fin.ofNat 14 a.val) = σ (Fin.ofNat 14 b.val) := Fin.ext hv
    have heq' := σ.injective heq
    have hval := congrArg Fin.val heq'
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hval
    exact Fin.ext hval
  · simp only [ha, hb, ↓reduceIte] at hv; have := (σ (Fin.ofNat 14 a.val)).isLt; omega
  · simp only [ha, hb, ↓reduceIte] at hv; have := (σ (Fin.ofNat 14 b.val)).isLt; omega
  · ext; omega

lemma min_max_pair {α : Type*} [LinearOrder α] (f : α → ℕ) (u v : α) :
    min (f (min u v)) (f (max u v)) = min (f u) (f v) ∧
    max (f (min u v)) (f (max u v)) = max (f u) (f v) := by
  rcases le_total u v with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, min_comm, max_comm]

lemma op_eval_comm (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : Bool) :
    op.eval [a, b] = op.eval [b, a] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> rfl

lemma op_eval_min_max {α : Type*} [LinearOrder α] (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (f : α → Bool) (u v : α) :
    op.eval [f (min u v), f (max u v)] = op.eval [f u, f v] := by
  rcases le_total u v with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, op_eval_comm op hop]

lemma foldl_remap (σ : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      14 ≤ w2.length →
      (∀ i : ℕ, w1.getD (ρ σ i) false = w2.getD i false) →
      ∀ i : ℕ,
        ((gs.map fun g => Gate.mk g.op (g.inputs.map (ρ σ))).foldl step w1).getD (ρ σ i) false =
        (gs.foldl step w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ _ h0 i; exact h0 i
  | cons g rest ih =>
    intro w1 w2 hlen h14 h0 i
    simp only [List.map_cons, List.foldl_cons]
    have hbit :
        g.op.eval ((g.inputs.map (ρ σ)).map fun j => w1.getD j false) =
        g.op.eval (g.inputs.map fun j => w2.getD j false) := by
      congr 1; rw [List.map_map]; exact List.map_congr_left fun j _ => h0 j
    apply ih
    · simp [step, hlen]
    · simp [step]; omega
    · intro k
      simp only [step, hbit]
      by_cases hk : k < 14
      · have hr : ρ σ k < 14 := by simp [ρ, hk]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h0 k
      · have hr : ρ σ k = k := by simp [ρ, hk]
        rw [hr]
        rcases lt_trichotomy k w2.length with hlt | heq | hgt
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hlt]
          have := h0 k; rwa [hr] at this
        · subst heq
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (le_refl _)]
          simp [hlen]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma core (x1 : (Fin 14 → Bool) → Bool) (x2 : Circuit)
    (hao : IsAO2 14 x2)
    (hnodup : ∀ g ∈ x2.gates, g.inputs.Nodup)
    (hge2 : 2 ≤ x2.size)
    (hle26 : x2.size ≤ 26)
    (heval : ∀ x : Fin 14 → Bool, x2.eval (List.ofFn x) = x1 x) :
    ∃ (x10 x11 : Fin 14) (x12 x13 : Fin 15) (x14 x15 : GateOp) (x16 : Circuit),
      x10 < x11 ∧ x12 < x13 ∧
      (x14 = GateOp.and ∨ x14 = GateOp.or) ∧
      (x15 = GateOp.and ∨ x15 = GateOp.or) ∧
      (∀ (σ : Equiv.Perm (Fin 14)), (∀ x : Fin 14 → Bool, x1 (x ∘ σ) = x1 x) →
        score x10.val x11.val x12.val x13.val ≤
          score (σ x10).val (σ x11).val (act15 σ x12) (act15 σ x13)) ∧
      Monotone2 x16 ∧
      x16.size ≤ 24 ∧
      ∀ (x : Fin 14 → Bool),
        let w : List Bool := List.ofFn x ++ [x14.eval [x x10, x x11]]
        x16.eval (w ++ [x15.eval [w.getD x12.val false, w.getD x13.val false]]) = x1 x := by
  classical
  rcases hgates : x2.gates with _ | ⟨g0, _ | ⟨g1, tail⟩⟩
  · simp [Circuit.size, hgates] at hge2
  · simp [Circuit.size, hgates] at hge2
  have hg0_mem : g0 ∈ x2.gates := by simp [hgates]
  have hg1_mem : g1 ∈ x2.gates := by simp [hgates]
  have hop0 : g0.op = GateOp.and ∨ g0.op = GateOp.or := hao.1 g0 hg0_mem
  have hop1 : g1.op = GateOp.and ∨ g1.op = GateOp.or := hao.1 g1 hg1_mem
  have hlen0 : g0.inputs.length = 2 := hao.2.2 g0 hg0_mem
  have hlen1 : g1.inputs.length = 2 := hao.2.2 g1 hg1_mem
  rcases hi0 : g0.inputs with _ | ⟨a0, _ | ⟨b0, _ | ⟨_, _⟩⟩⟩ <;> simp [hi0] at hlen0
  rcases hi1 : g1.inputs with _ | ⟨c0, _ | ⟨d0, _ | ⟨_, _⟩⟩⟩ <;> simp [hi1] at hlen1
  have hab_ne : a0 ≠ b0 := by
    have := hnodup g0 hg0_mem; rw [hi0] at this; simp at this; exact this
  have hcd_ne : c0 ≠ d0 := by
    have := hnodup g1 hg1_mem; rw [hi1] at this; simp at this; exact this
  have ha0_lt : a0 < 14 := by
    have := hao.2.1 0 (by simp [hgates]) a0 (by simp [NestedCover.gateAt, hgates, hi0]); omega
  have hb0_lt : b0 < 14 := by
    have := hao.2.1 0 (by simp [hgates]) b0 (by simp [NestedCover.gateAt, hgates, hi0]); omega
  have hc0_lt : c0 < 15 := by
    have := hao.2.1 1 (by simp [hgates]) c0 (by simp [NestedCover.gateAt, hgates, hi1]); omega
  have hd0_lt : d0 < 15 := by
    have := hao.2.1 1 (by simp [hgates]) d0 (by simp [NestedCover.gateAt, hgates, hi1]); omega
  let fa0 : Fin 14 := ⟨a0, ha0_lt⟩
  let fb0 : Fin 14 := ⟨b0, hb0_lt⟩
  let fc0 : Fin 15 := ⟨c0, hc0_lt⟩
  let fd0 : Fin 15 := ⟨d0, hd0_lt⟩
  let aut : Finset (Equiv.Perm (Fin 14)) := Finset.univ.filter fun σ => ∀ x : Fin 14 → Bool, x1 (x ∘ σ) = x1 x
  have haut_ne : aut.Nonempty := ⟨1, by simp [aut]⟩
  let sc (σ : Equiv.Perm (Fin 14)) : ℕ := score (σ fa0).val (σ fb0).val (act15 σ fc0) (act15 σ fd0)
  obtain ⟨σ, hσ_mem, hσ_min⟩ := aut.exists_min_image sc haut_ne
  have hσ_aut : ∀ x : Fin 14 → Bool, x1 (x ∘ σ) = x1 x := (Finset.mem_filter.mp hσ_mem).2
  let u0 : Fin 14 := σ fa0
  let v0 : Fin 14 := σ fb0
  let u1 : Fin 15 := act15Fin σ fc0
  let v1 : Fin 15 := act15Fin σ fd0
  have huv0_ne : u0 ≠ v0 := fun h => hab_ne (congrArg Fin.val (σ.injective h))
  have huv1_ne : u1 ≠ v1 := fun h => hcd_ne (congrArg Fin.val (act15Fin_inj σ h))
  let x10 : Fin 14 := min u0 v0
  let x11 : Fin 14 := max u0 v0
  let x12 : Fin 15 := min u1 v1
  let x13 : Fin 15 := max u1 v1
  let x16 : Circuit := ⟨tail.map fun g => Gate.mk g.op (g.inputs.map (ρ σ)), ρ σ x2.output⟩
  refine ⟨x10, x11, x12, x13, g0.op, g1.op, x16, ?_, ?_, hop0, hop1, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (min_le_max) (fun h => huv0_ne (by
      dsimp only [x10, x11] at h
      rcases le_total u0 v0 with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at h; exact h
      · rw [min_eq_right hle, max_eq_left hle] at h; exact h.symm))
  · exact lt_of_le_of_ne (min_le_max) (fun h => huv1_ne (by
      dsimp only [x12, x13] at h
      rcases le_total u1 v1 with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at h; exact h
      · rw [min_eq_right hle, max_eq_left hle] at h; exact h.symm))
  · intro τ hτ
    have hcomp : τ * σ ∈ aut := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun x => ?_⟩
      change x1 ((x ∘ τ) ∘ σ) = x1 x
      rw [hσ_aut (x ∘ τ), hτ x]
    have hle := hσ_min (τ * σ) hcomp
    have h0a := min_max_pair (fun p : Fin 14 => p.val) u0 v0
    have h0b := min_max_pair (fun p : Fin 15 => p.val) u1 v1
    have h1a := min_max_pair (fun p : Fin 14 => (τ p).val) u0 v0
    have h1b := min_max_pair (fun p : Fin 15 => act15 τ p) u1 v1
    have hL : score x10.val x11.val x12.val x13.val = sc σ := by
      unfold score sc; rw [h0a.1, h0a.2, h0b.1, h0b.2]; rfl
    have hR : score (τ x10).val (τ x11).val (act15 τ x12) (act15 τ x13) = sc (τ * σ) := by
      unfold score sc
      rw [h1a.1, h1a.2, h1b.1, h1b.2, act15_comp, act15_comp]
      rfl
    rw [hL, hR]
    exact hle
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have hg'_mem : g' ∈ x2.gates := by simp [hgates, hg']
    exact ⟨hao.1 g' hg'_mem, by simp [hao.2.2 g' hg'_mem]⟩
  · simp only [Circuit.size, hgates, List.length_cons] at hle26
    simp only [x16, Circuit.size, List.length_map]; omega
  · intro x
    let y : Fin 14 → Bool := x ∘ σ
    have hy : x2.eval (List.ofFn y) = x1 x := (heval y).trans (hσ_aut x)
    rw [← hy]
    dsimp only
    rw [Circuit.eval, Circuit.eval, Circuit.wires, Circuit.wires, hgates]
    change (x16.gates.foldl step _).getD (ρ σ x2.output) false =
      ((g0 :: g1 :: tail).foldl step (List.ofFn y)).getD x2.output false
    have h0_eq : g0.op.eval [x x10, x x11] = g0.op.eval [y fa0, y fb0] :=
      op_eval_min_max g0.op hop0 x u0 v0
    have hw_init : ∀ i : ℕ, (List.ofFn x).getD (ρ σ i) false = (List.ofFn y).getD i false := by
      intro i
      by_cases hi : i < 14
      · simp only [ρ, hi, ↓reduceDIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [hi, y]
      · simp only [ρ, hi, ↓reduceDIte]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hg0_y : step (List.ofFn y) g0 = List.ofFn y ++ [g0.op.eval [y fa0, y fb0]] := by
      unfold step; rw [hi0]; simp only [List.map_cons, List.map_nil]
      have ha : (List.ofFn y).getD a0 false = y fa0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [ha0_lt, fa0]
      have hb : (List.ofFn y).getD b0 false = y fb0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [hb0_lt, fb0]
      rw [ha, hb]
    let w1 := List.ofFn x ++ [g0.op.eval [x x10, x x11]]
    let w2 := step (List.ofFn y) g0
    have hw12 : ∀ i : ℕ, w1.getD (ρ σ i) false = w2.getD i false := by
      intro i
      dsimp only [w1, w2]
      rw [hg0_y]
      by_cases hi : i < 14
      · have hr : ρ σ i < 14 := by simp [ρ, hi]
        rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
        exact hw_init i
      · have hr : ρ σ i = i := by simp [ρ, hi]
        rw [hr]
        by_cases hi14 : i = 14
        · subst hi14
          rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
          simp [h0_eq]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have h1_eq : g1.op.eval [w1.getD x12.val false, w1.getD x13.val false] =
        g1.op.eval [w2.getD c0 false, w2.getD d0 false] := by
      have hm := op_eval_min_max g1.op hop1 (fun p : Fin 15 => w1.getD p.val false) u1 v1
      rw [hm]
      have hu1 : w1.getD u1.val false = w2.getD c0 false := by
        have : u1.val = ρ σ c0 := act15_eq_ρ σ fc0
        rw [this]; exact hw12 c0
      have hv1 : w1.getD v1.val false = w2.getD d0 false := by
        have : v1.val = ρ σ d0 := act15_eq_ρ σ fd0
        rw [this]; exact hw12 d0
      rw [hu1, hv1]
    have hg1_y : step w2 g1 = w2 ++ [g1.op.eval [w2.getD c0 false, w2.getD d0 false]] := by
      unfold step; rw [hi1]; simp only [List.map_cons, List.map_nil]
    simp only [List.foldl_cons]
    have hl1 : w1.length = 15 := by simp [w1]
    have hl2 : w2.length = 15 := by dsimp only [w2]; rw [hg0_y]; simp
    have hstep_match : ∀ i : ℕ,
        (w1 ++ [g1.op.eval [w1.getD x12.val false, w1.getD x13.val false]]).getD (ρ σ i) false =
        (step w2 g1).getD i false := by
      intro i
      rw [hg1_y]
      by_cases hi : i < 15
      · have hr : ρ σ i < 15 := by
          unfold ρ; split
          · have := (σ ⟨i, ‹i < 14›⟩).isLt; omega
          · omega
        rw [List.getD_append w1 _ _ _ (by rw [hl1]; exact hr),
            List.getD_append w2 _ _ _ (by rw [hl2]; exact hi)]
        exact hw12 i
      · have hr : ρ σ i = i := by simp only [ρ, show ¬ i < 14 by omega, ↓reduceDIte]
        rw [hr]
        by_cases hi15 : i = 15
        · subst hi15
          rw [List.getD_append_right w1 _ _ _ (by rw [hl1]),
              List.getD_append_right w2 _ _ _ (by rw [hl2])]
          simp only [hl1, hl2, Nat.sub_self, List.getD_cons_zero]
          exact h1_eq
        · rw [List.getD_eq_default _ _ (by simp [hl1]; omega),
              List.getD_eq_default _ _ (by simp [hl2]; omega)]
    exact foldl_remap σ tail
      (w1 ++ [g1.op.eval [w1.getD x12.val false, w1.getD x13.val false]])
      (step w2 g1)
      (by simp [hl1, hg1_y, hl2])
      (by simp [hg1_y, hl2])
      hstep_match x2.output

end PEqualNP.Outside.L_meta_3010

theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 :=
  PEqualNP.Outside.L_meta_3010.core
