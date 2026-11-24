import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4003_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ren (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem getD_snoc_ne (l : List Bool) (v : Bool) (i : ℕ) (h : i ≠ l.length) :
    (l ++ [v]).getD i false = l.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem getD_snoc_eq (l : List Bool) (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem ofFnD (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]
  · exact getD_big _ _ (by simp; omega)

theorem evalcongr (g : Gate) (ρ : ℕ → ℕ) (a b : ℕ → Bool) (h : ∀ i ∈ eff g, a (ρ i) = b i) :
    (ren ρ g).op.eval ((ren ρ g).inputs.map a) = g.op.eval (g.inputs.map b) := by
  obtain ⟨op, ins⟩ := g
  cases op
  case not =>
    cases ins with
    | nil => simp [ren]
    | cons c t =>
      have := h c (by simp [eff])
      simp [ren, GateOp.eval, this]
  all_goals
    have e : (ins.map ρ).map a = ins.map b := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact h i hi
    simp only [ren]
    rw [e]

theorem eff_ren (ρ : ℕ → ℕ) (g : Gate) : eff (ren ρ g) = (eff g).map ρ := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [eff, ren, List.map_take]

theorem ren_id (B : List Gate) : B.map (ren id) = B := by
  have : ren id = id := by
    funext g
    cases g
    simp [ren]
  rw [this, List.map_id]

theorem sim (ρ : ℕ → ℕ) (bad : ℕ → Prop) : ∀ (B : List Gate) (w w' : List Bool),
    (∀ i, ¬ bad i → w'.getD (ρ i) false = w.getD i false) →
    (∀ g ∈ B, ∀ i ∈ eff g, ¬ bad i) →
    (∀ j, j < B.length → ρ (w.length + j) = w'.length + j) →
    (∀ i j, j < B.length → i ≠ w.length + j → ¬ bad i → ρ i ≠ w'.length + j) →
    ∀ i, ¬ bad i → ((B.map (ren ρ)).foldl step w').getD (ρ i) false
      = (B.foldl step w).getD i false := by
  intro B
  induction B with
  | nil =>
    intro w w' inv _ _ _ i hi
    exact inv i hi
  | cons g B ih =>
    intro w w' inv hb h1 h2
    simp only [List.map_cons, List.foldl_cons]
    have ev : (ren ρ g).op.eval ((ren ρ g).inputs.map fun k => w'.getD k false)
        = g.op.eval (g.inputs.map fun k => w.getD k false) :=
      evalcongr g ρ (fun k => w'.getD k false) (fun k => w.getD k false)
        (fun i hi => inv i (hb g (List.mem_cons_self) i hi))
    have l1 : (step w g).length = w.length + 1 := by simp [step]
    have l2 : (step w' (ren ρ g)).length = w'.length + 1 := by simp [step]
    apply ih
    · intro i hi
      unfold step
      rw [ev]
      by_cases hiw : i = w.length
      · subst hiw
        have := h1 0 (by simp)
        simp only [Nat.add_zero] at this
        rw [this, getD_snoc_eq, getD_snoc_eq]
      · have h3 := h2 i 0 (by simp) (by simpa using hiw) hi
        simp only [Nat.add_zero] at h3
        rw [getD_snoc_ne _ _ _ hiw, getD_snoc_ne _ _ _ h3, inv i hi]
    · intro g' hg'
      exact hb g' (List.mem_cons_of_mem _ hg')
    · intro j hj
      have := h1 (j + 1) (by simp; omega)
      rw [l1, l2, show w.length + 1 + j = w.length + (j + 1) by omega, this]
      omega
    · intro i j hj hne hi
      have := h2 i (j + 1) (by simp; omega) (by rw [l1] at hne; omega) hi
      rw [l2]
      omega

theorem len (B : List Gate) : ∀ w : List Bool, (B.foldl step w).length = w.length + B.length := by
  induction B with
  | nil => intro w; simp
  | cons g B ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem pre (B : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (B.foldl step w).getD i false = w.getD i false := by
  induction B with
  | nil => intro w i _; rfl
  | cons g B ih =>
    intro w i h
    rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
    exact getD_snoc_ne _ _ _ (by omega)

theorem mid (A B : List Gate) (G : Gate) (w0 : List Bool) :
    ((A ++ G :: B).foldl step w0).getD (A.foldl step w0).length false
      = G.op.eval (G.inputs.map fun i => (A.foldl step w0).getD i false) := by
  rw [List.foldl_append, List.foldl_cons, pre _ _ _ (by simp [step])]
  exact getD_snoc_eq _ _

theorem del (n : ℕ) (D : Circuit) (A B : List Gate) (G : Gate) (hD : D.gates = A ++ G :: B)
    (fan : FanInTwo D) (r : ℕ) (bad : ℕ → Prop)
    (hb1 : ∀ g ∈ B, ∀ i ∈ eff g, ¬ bad i) (hb2 : ¬ bad D.output)
    (hb4 : ¬ bad (n + A.length) → (r < n + A.length ∨ n + A.length + B.length ≤ r) ∧
      ∀ x : Fin n → Bool, (A.foldl step (List.ofFn x)).getD r false
        = G.op.eval (G.inputs.map fun i => (A.foldl step (List.ofFn x)).getD i false)) :
    ∃ D' : Circuit, FanInTwo D' ∧ D'.size + 1 = D.size ∧
      ∀ x : Fin n → Bool, D'.eval (List.ofFn x) = D.eval (List.ofFn x) := by
  let ρ : ℕ → ℕ := fun i => if i < n + A.length then i else if i = n + A.length then r else i - 1
  refine ⟨⟨A ++ B.map (ren ρ), ρ D.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact fan g (by rw [hD]; simp [h])
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := fan g0 (by rw [hD]; simp [hg0])
      simpa [ren] using this
  · simp [Circuit.size, hD]
    omega
  · intro x
    unfold Circuit.eval Circuit.wires
    rw [hD]
    show ((A ++ B.map (ren ρ)).foldl step (List.ofFn x)).getD (ρ D.output) false
      = ((A ++ G :: B).foldl step (List.ofFn x)).getD D.output false
    rw [List.foldl_append, List.foldl_append, List.foldl_cons]
    have hl : (A.foldl step (List.ofFn x)).length = n + A.length := by simp [len]
    have h4 := fun hi => (hb4 hi).2 x
    generalize A.foldl step (List.ofFn x) = wA at hl h4
    have l1 : (step wA G).length = n + A.length + 1 := by simp [step, hl]
    apply sim ρ bad B (step wA G) wA _ hb1 _ _ D.output hb2
    · intro i hi
      by_cases him : i = n + A.length
      · subst him
        have e : ρ (n + A.length) = r := by simp [ρ]
        rw [e, h4 hi]
        unfold step
        rw [← hl, getD_snoc_eq]
      · unfold step
        rw [getD_snoc_ne _ _ _ (by omega)]
        by_cases hlt : i < n + A.length
        · have e : ρ i = i := by simp [ρ, hlt]
          rw [e]
        · have e : ρ i = i - 1 := by simp [ρ, hlt, him]
          rw [e, getD_big _ _ (by omega), getD_big _ _ (by omega)]
    · intro j hj
      rw [l1, hl]
      simp only [ρ]
      split_ifs <;> omega
    · intro i j hj hne hi
      rw [l1] at hne
      rw [hl]
      simp only [ρ]
      split_ifs with h1 h2
      · omega
      · subst h2
        have := (hb4 hi).1
        omega
      · omega

theorem shrink (n : ℕ) (D : Circuit) (A B : List Gate) (G : Gate) (hD : D.gates = A ++ G :: B)
    (fan : FanInTwo D) (c : ℕ)
    (hv : ∀ x : Fin n → Bool,
      G.op.eval (G.inputs.map fun i => (A.foldl step (List.ofFn x)).getD i false)
        = (A.foldl step (List.ofFn x)).getD c false) :
    ∃ D' : Circuit, FanInTwo D' ∧ D'.size + 1 = D.size ∧
      ∀ x : Fin n → Bool, D'.eval (List.ofFn x) = D.eval (List.ofFn x) := by
  by_cases hc : c < n + A.length
  · exact del n D A B G hD fan c (fun _ => False) (fun _ _ _ _ => id) id
      (fun _ => ⟨Or.inl hc, fun x => (hv x).symm⟩)
  · refine del n D A B G hD fan (n + A.length + B.length) (fun _ => False) (fun _ _ _ _ => id) id
      (fun _ => ⟨Or.inr le_rfl, fun x => ?_⟩)
    have hl : (A.foldl step (List.ofFn x)).length = n + A.length := by simp [len]
    rw [hv x, getD_big _ _ (by omega), getD_big _ _ (by omega)]

theorem lvl2 {α : Type} (w : α → ℕ → Bool) (H : Gate)
    (hop : H.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : H.inputs.length ≤ 2) (t F : ℕ) (ht : ∀ x, w x t = true)
    (hF : ∀ x, w x F = false) (hm : t ∈ eff H) :
    ∃ c, ∀ x, H.op.eval (H.inputs.map fun i => w x i) = w x c := by
  obtain ⟨op, ins⟩ := H
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · match ins, hlen, hm with
    | [a], _, hm =>
      exact ⟨a, fun x => by simp [GateOp.eval]⟩
    | [a, b], _, hm =>
      simp only [eff, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨b, fun x => by simp [GateOp.eval, ht x]⟩
      · exact ⟨a, fun x => by simp [GateOp.eval, ht x]⟩
  · refine ⟨t, fun x => ?_⟩
    rw [ht x]
    simp only [GateOp.eval, List.any_map, List.any_eq_true]
    exact ⟨t, hm, ht x⟩
  · match ins, hm with
    | a :: l, hm =>
      simp only [eff, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      subst hm
      exact ⟨F, fun x => by simp [GateOp.eval, ht x, hF x]⟩

theorem lvl1 {α : Type} (w : α → ℕ → Bool) (H : Gate)
    (hop : H.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : H.inputs.length ≤ 2) (F : ℕ)
    (hF : ∀ x, w x F = false) (hm : F ∈ eff H) :
    (∃ c, ∀ x, H.op.eval (H.inputs.map fun i => w x i) = w x c) ∨
      ∀ x, H.op.eval (H.inputs.map fun i => w x i) = true := by
  obtain ⟨op, ins⟩ := H
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · left
    refine ⟨F, fun x => ?_⟩
    rw [hF x]
    simp only [GateOp.eval, List.all_map, List.all_eq_false]
    exact ⟨F, hm, by simp [hF x]⟩
  · left
    match ins, hlen, hm with
    | [a], _, hm =>
      exact ⟨a, fun x => by simp [GateOp.eval]⟩
    | [a, b], _, hm =>
      simp only [eff, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨b, fun x => by simp [GateOp.eval, hF x]⟩
      · exact ⟨a, fun x => by simp [GateOp.eval, hF x]⟩
  · right
    match ins, hm with
    | a :: l, hm =>
      simp only [eff, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      subst hm
      exact fun x => by simp [GateOp.eval, hF x]

theorem reduce (n : ℕ) (D : Circuit) (fan : FanInTwo D) (F : ℕ) (hF : n + D.gates.length ≤ F)
    (G0 : Gate) (hG : G0 ∈ D.gates) (hFe : F ∈ eff G0)
    (hnc : ∃ x y : Fin n → Bool, D.eval (List.ofFn x) ≠ D.eval (List.ofFn y)) :
    ∃ D' : Circuit, FanInTwo D' ∧ D'.size + 1 = D.size ∧
      ∀ x : Fin n → Bool, D'.eval (List.ofFn x) = D.eval (List.ofFn x) := by
  obtain ⟨A, B, hD⟩ := List.append_of_mem hG
  have hlen : D.gates.length = A.length + B.length + 1 := by simp [hD]; omega
  have hl : ∀ x : Fin n → Bool, (A.foldl step (List.ofFn x)).length = n + A.length := by
    intro x; simp [len]
  have hFw : ∀ x : Fin n → Bool, (A.foldl step (List.ofFn x)).getD F false = false := by
    intro x
    exact getD_big _ _ (by rw [hl x]; omega)
  rcases lvl1 (fun (x : Fin n → Bool) (i : ℕ) => (A.foldl step (List.ofFn x)).getD i false) G0 (fan G0 hG).1
    (fan G0 hG).2 F hFw hFe with ⟨c, hc⟩ | hT
  · exact shrink n D A B G0 hD fan c hc
  · by_cases hrd : ∃ H ∈ B, (n + A.length) ∈ eff H
    · obtain ⟨H, hH, hm⟩ := hrd
      obtain ⟨B1, B2, hB⟩ := List.append_of_mem hH
      have hD2 : D.gates = (A ++ G0 :: B1) ++ H :: B2 := by simp [hD, hB]
      have hHD : H ∈ D.gates := by rw [hD2]; simp
      have hl1 : ∀ x : Fin n → Bool, ((A ++ G0 :: B1).foldl step (List.ofFn x)).length
          = n + A.length + 1 + B1.length := by
        intro x; rw [len]; simp; omega
      have hlen2 : B.length = B1.length + B2.length + 1 := by simp [hB]; omega
      obtain ⟨c, hc⟩ := lvl2 (fun (x : Fin n → Bool) (i : ℕ) => ((A ++ G0 :: B1).foldl step (List.ofFn x)).getD i false) H
        (fan H hHD).1 (fan H hHD).2 (n + A.length) F
        (by
          intro x
          show ((A ++ G0 :: B1).foldl step (List.ofFn x)).getD (n + A.length) false = true
          rw [← hl x]
          exact (mid A B1 G0 _).trans (hT x))
        (by
          intro x
          exact getD_big _ _ (by rw [hl1 x]; omega))
        hm
      exact shrink n D (A ++ G0 :: B1) B2 H hD2 fan c hc
    · push Not at hrd
      by_cases hout : D.output = n + A.length
      · exfalso
        obtain ⟨x, y, hxy⟩ := hnc
        have ht : ∀ z : Fin n → Bool, D.eval (List.ofFn z) = true := by
          intro z
          unfold Circuit.eval Circuit.wires
          rw [hD, hout]
          show ((A ++ G0 :: B).foldl step (List.ofFn z)).getD (n + A.length) false = true
          rw [← hl z]
          exact (mid A B G0 _).trans (hT z)
        exact hxy (by rw [ht x, ht y])
      · exact del n D A B G0 hD fan 0 (fun i => i = n + A.length)
          (fun g hg i hi e => hrd g hg (e ▸ hi)) hout (fun h => absurd rfl h)

end PEqualNP.Outside.L_meta_4003_aux

open PEqualNP.Outside.L_meta_4003_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_4003 : (∀ (x1 : ℕ) (x2 : (Fin x1 → Bool) → Bool) (x3 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x2 x3 → ∀ (x5 : Fin x1), PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x6 : Fin x1 → Bool) => x2 x6 || x6 x5) (x3 + (1 : ℕ))) ∧ ∀ (x1 x2 : ℕ) (x3 : (Fin x1 → Bool) → Bool) (x4 : Fin x1), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x2 → (∃ (x6 : Fin x1 → Bool), x3 (Function.update x6 x4 Bool.false) ≠ x3 (Function.update x6 x4 Bool.true)) → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x3 (Function.update x7 x4 Bool.false) ≠ x3 (Function.update x8 x4 Bool.false)) → (1 : ℕ) ≤ x2 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x8 : Fin x1 → Bool) => x3 (Function.update x8 x4 Bool.false)) (x2 - (1 : ℕ)) := by
  constructor
  · rintro n f s ⟨C, fan, hsz, hev⟩ x5
    refine ⟨⟨C.gates ++ [Gate.mk GateOp.or [C.output, (x5 : ℕ)]], n + C.gates.length⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact fan g h
      · simp only [List.mem_singleton] at h
        subst h
        simp
    · simp only [Circuit.size, List.length_append, List.length_singleton]
      exact Nat.succ_le_succ hsz
    · intro x
      have hl : (C.gates.foldl step (List.ofFn x)).length = n + C.gates.length := by simp [len]
      unfold Circuit.eval Circuit.wires
      show ((C.gates ++ [Gate.mk GateOp.or [C.output, (x5 : ℕ)]]).foldl step (List.ofFn x)).getD
        (n + C.gates.length) false = _
      rw [← hl]
      refine (mid C.gates [] _ _).trans ?_
      show _ = (f x || x x5)
      rw [← hev x]
      have e5 : (C.gates.foldl step (List.ofFn x)).getD (x5 : ℕ) false = x x5 := by
        rw [pre _ _ _ (by simp), ofFnD]
        simp
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [e5]
      rfl
  · rintro n s f x4 ⟨C, fan, hsz, hev⟩ hdep hnc
    suffices h : ∃ D' : Circuit, FanInTwo D' ∧ D'.size + 1 ≤ s ∧
        ∀ x : Fin n → Bool, D'.eval (List.ofFn x) = f (Function.update x x4 false) by
      obtain ⟨D', f', s', e'⟩ := h
      exact ⟨by omega, D', f', by omega, e'⟩
    by_cases hread : ∃ g ∈ C.gates, (x4 : ℕ) ∈ eff g
    · obtain ⟨g0, hg0, hx4⟩ := hread
      let σ : ℕ → ℕ := fun i => if i = (x4 : ℕ) then n + C.gates.length else i
      have hDev : ∀ x : Fin n → Bool,
          (Circuit.mk (C.gates.map (ren σ)) (σ C.output)).eval (List.ofFn x)
            = f (Function.update x x4 false) := by
        intro x
        rw [← hev]
        unfold Circuit.eval Circuit.wires
        refine sim σ (fun _ => False) C.gates (List.ofFn (Function.update x x4 false))
          (List.ofFn x) ?_ (fun _ _ _ _ => id) ?_ ?_ C.output id
        · intro i _
          by_cases h : i = (x4 : ℕ)
          · subst h
            simp [σ, ofFnD]
          · simp only [σ, ite_eq_right h, ofFnD]
            split_ifs with hi
            · rw [Function.update_of_ne]
              intro e
              apply h
              rw [← e]
            · rfl
        · intro j _
          have := x4.isLt
          simp only [σ, List.length_ofFn]
          rw [ite_eq_right (by omega)]
        · intro i j hj hne _
          have := x4.isLt
          simp only [List.length_ofFn] at hne ⊢
          simp only [σ]
          split_ifs <;> omega
      obtain ⟨D', f', s', e'⟩ := reduce n (Circuit.mk (C.gates.map (ren σ)) (σ C.output))
        (by
          intro g hg
          obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
          simpa [ren] using fan g1 hg1)
        (n + C.gates.length) (by simp) (ren σ g0) (List.mem_map_of_mem hg0)
        (by
          rw [eff_ren]
          exact List.mem_map.2 ⟨(x4 : ℕ), hx4, by simp [σ]⟩)
        (by
          obtain ⟨x7, x8, h⟩ := hnc
          exact ⟨x7, x8, by rw [hDev, hDev]; exact h⟩)
      refine ⟨D', f', ?_, fun x => by rw [e' x, hDev x]⟩
      simp only [Circuit.size, List.length_map] at s'
      simp only [Circuit.size] at hsz ⊢
      omega
    · exfalso
      push Not at hread
      by_cases ho : C.output = (x4 : ℕ)
      · obtain ⟨x7, x8, h⟩ := hnc
        apply h
        rw [← hev, ← hev]
        unfold Circuit.eval Circuit.wires
        show (C.gates.foldl step _).getD _ false = (C.gates.foldl step _).getD _ false
        rw [ho, pre _ _ _ (by simp), pre _ _ _ (by simp), ofFnD, ofFnD]
        simp
      · obtain ⟨x6, h6⟩ := hdep
        have key := sim id (fun i => i = (x4 : ℕ)) C.gates
          (List.ofFn (Function.update x6 x4 false)) (List.ofFn (Function.update x6 x4 true))
          (by
            intro i hi
            simp only [id, ofFnD]
            split_ifs with h
            · rw [Function.update_of_ne, Function.update_of_ne]
              · intro e; apply hi; rw [← e]
              · intro e; apply hi; rw [← e]
            · rfl)
          (fun g hg i hi e => hread g hg (e ▸ hi))
          (by intro j _; simp)
          (by intro i j _ hne _; simpa using hne)
          C.output ho
        rw [ren_id] at key
        apply h6
        rw [← hev, ← hev]
        exact key.symm
