import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1725

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def F {α : Type} (φ : Gate → List α → α) (gs : List Gate) (u : List α) : List α :=
  gs.foldl (fun w g => w ++ [φ g w]) u

theorem F_append {α : Type} (φ : Gate → List α → α) (gs : List Gate) (g : Gate) (u : List α) :
    F φ (gs ++ [g]) u = F φ gs u ++ [φ g (F φ gs u)] := by
  simp [F, List.foldl_append]

theorem F_ext {α : Type} (φ : Gate → List α → α) (gs : List Gate) :
    ∀ u : List α, ∃ t, F φ gs u = u ++ t := by
  induction gs with
  | nil => intro u; exact ⟨[], by simp [F]⟩
  | cons g gs ih =>
    intro u
    obtain ⟨t, ht⟩ := ih (u ++ [φ g u])
    refine ⟨[φ g u] ++ t, ?_⟩
    simp only [F, List.foldl_cons] at ht ⊢
    rw [ht]; simp

theorem F_length {α : Type} (φ : Gate → List α → α) (gs : List Gate) :
    ∀ u : List α, (F φ gs u).length = u.length + gs.length := by
  induction gs with
  | nil => intro u; simp [F]
  | cons g gs ih =>
    intro u
    have := ih (u ++ [φ g u])
    simp only [F, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem F_prefix {α : Type} (φ : Gate → List α → α) (gs : List Gate) (u : List α) (j i : ℕ)
    (d : α) (hi : i < u.length + j) (hj : j ≤ gs.length) :
    (F φ gs u).getD i d = (F φ (gs.take j) u).getD i d := by
  have hsplit : F φ gs u = F φ (gs.drop j) (F φ (gs.take j) u) := by
    unfold F; rw [← List.foldl_append, List.take_append_drop]
  obtain ⟨t, ht⟩ := F_ext φ (gs.drop j) (F φ (gs.take j) u)
  have hl : i < (F φ (gs.take j) u).length := by
    rw [F_length, List.length_take]; omega
  rw [hsplit, ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hl,
    ← List.getD_eq_getElem?_getD]

theorem take_getD (gs : List Gate) (j : ℕ) (hj : j < gs.length) (g0 : Gate) :
    gs.take (j + 1) = gs.take j ++ [gs.getD j g0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rfl

theorem rel_fold {α β : Type} (R : α → β → Prop) (φ : Gate → List α → α)
    (ψ : Gate → List β → β) (g0 : Gate)
    (gs gs' : List Gate) (hl : gs'.length = gs.length) (u : List α) (u' : List β)
    (hu : u'.length = u.length) (da : α) (db : β) (hR0 : R da db)
    (hinit : ∀ i < u.length, R (u.getD i da) (u'.getD i db))
    (hstep : ∀ j < gs.length,
      (∀ i < u.length + j, R ((F φ (gs.take j) u).getD i da) ((F ψ (gs'.take j) u').getD i db)) →
      R (φ (gs.getD j g0) (F φ (gs.take j) u)) (ψ (gs'.getD j g0) (F ψ (gs'.take j) u'))) :
    ∀ i, R ((F φ gs u).getD i da) ((F ψ gs' u').getD i db) := by
  have key : ∀ k ≤ gs.length, ∀ i < u.length + k,
      R ((F φ (gs.take k) u).getD i da) ((F ψ (gs'.take k) u').getD i db) := by
    intro k
    induction k with
    | zero => intro _ i hi; simpa [F] using hinit i (by simpa using hi)
    | succ k ih =>
      intro hk i hi
      have hk' : k < gs.length := by omega
      have hlen : (F φ (gs.take k) u).length = u.length + k := by
        rw [F_length, List.length_take]; omega
      have hlen' : (F ψ (gs'.take k) u').length = u.length + k := by
        rw [F_length, List.length_take]; omega
      rw [take_getD gs k hk' g0, take_getD gs' k (by omega) g0, F_append, F_append]
      rcases Nat.lt_or_ge i (u.length + k) with h | h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD (l := _ ++ _),
          List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
        exact ih (by omega) i h
      · have hi' : i = u.length + k := by omega
        subst hi'
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
          List.getD_eq_getElem?_getD (l := _ ++ _), List.getElem?_append_right (by omega),
          hlen, hlen']
        simpa using hstep k hk' (ih (by omega))
  intro i
  rcases Nat.lt_or_ge i (u.length + gs.length) with h | h
  · have := key gs.length le_rfl i h
    have e1 : gs.take gs.length = gs := List.take_length
    have e2 : gs'.take gs.length = gs' := by rw [← hl]; exact List.take_length
    rwa [e1, e2] at this
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [F_length]; omega),
      List.getD_eq_getElem?_getD (l := F ψ gs' u'), List.getElem?_eq_none (by rw [F_length]; omega)]
    exact hR0

def W : Gate → List Bool → Bool := fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

def Ld : Gate → List ℕ → ℕ := fun g d => g.lineDegree d

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = F W C.gates x := rfl

theorem ld_eq (C : Circuit) (n : ℕ) (M : Finset ℕ) :
    C.lineDegrees n M = F Ld C.gates ((List.range n).map fun i => if i ∈ M then 1 else 0) := rfl

def pk (D : Circuit) (σ : ℕ → Bool) (j : ℕ) : ℕ :=
  if σ j then (gateAt D j).inputs.getD 1 0 else (gateAt D j).inputs.getD 0 0

def mg (D : Circuit) (B : Finset ℕ) (σ : ℕ → Bool) (j : ℕ) : Gate :=
  if j ∈ B then ⟨GateOp.or, [pk D σ j, pk D σ j]⟩ else gateAt D j

def Cs (D : Circuit) (B : Finset ℕ) (σ : ℕ → Bool) : Circuit :=
  ⟨(List.range D.gates.length).map (mg D B σ), D.output⟩

def KM (D : Circuit) (N j : ℕ) : Prop :=
  (∃ i ∈ (gateAt D j).inputs, (D.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
    (∀ h ∈ (gateAt D j).inputs, (D.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0)

theorem Cs_len (D : Circuit) (B : Finset ℕ) (σ : ℕ → Bool) :
    (Cs D B σ).gates.length = D.gates.length := by simp [Cs]

theorem Cs_getD (D : Circuit) (B : Finset ℕ) (σ : ℕ → Bool) (j : ℕ) (hj : j < D.gates.length) :
    (Cs D B σ).gates.getD j ⟨GateOp.or, []⟩ = mg D B σ j := by
  unfold Cs
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem gateAt_Cs (D : Circuit) (B : Finset ℕ) (σ : ℕ → Bool) (j : ℕ) (hj : j < D.gates.length) :
    gateAt (Cs D B σ) j = mg D B σ j := Cs_getD D B σ j hj

theorem gateAt_mem (D : Circuit) (j : ℕ) (hj : j < D.gates.length) : gateAt D j ∈ D.gates := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

theorem two (D : Circuit)
    (hD : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < D.gates.length) :
    ∃ a b, (gateAt D j).inputs = [a, b] ∧
      ((gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or) := by
  obtain ⟨h1, h2⟩ := hD _ (gateAt_mem D j hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  exact ⟨a, b, hab, h1⟩

theorem pk_mem (D : Circuit) (σ : ℕ → Bool) (j a b : ℕ) (hab : (gateAt D j).inputs = [a, b]) :
    pk D σ j = a ∨ pk D σ j = b := by
  unfold pk; rw [hab]; cases σ j <;> simp

theorem Cs_congr (D : Circuit) (B : Finset ℕ) (σ σ' : ℕ → Bool) (h : ∀ j ∈ B, σ j = σ' j) :
    Cs D B σ = Cs D B σ' := by
  unfold Cs
  congr 1
  apply List.map_congr_left
  intro j _
  unfold mg
  split_ifs with hj
  · simp [pk, h j hj]
  · rfl

theorem deg (D : Circuit) (B : Finset ℕ) (σ : ℕ → Bool) (n : ℕ) (M : Finset ℕ)
    (hD : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack n D) (hB : ∀ j ∈ B, (gateAt D j).op = GateOp.and) :
    ∀ i, ((Cs D B σ).lineDegrees n M).getD i 0 ≤ (D.lineDegrees n M).getD i 0 := by
  rw [ld_eq, ld_eq]
  refine rel_fold (fun a b => b ≤ a) Ld Ld ⟨GateOp.or, []⟩ D.gates (Cs D B σ).gates
    (Cs_len D B σ) _ _ rfl 0 0 le_rfl (fun i _ => le_rfl) ?_
  intro j hj ih
  simp only [List.length_map, List.length_range] at ih
  rw [Cs_getD D B σ j hj]
  obtain ⟨a, b, hab, hop⟩ := two D hD j hj
  have ha : a < n + j := hrb j hj a (by rw [hab]; simp)
  have hb : b < n + j := hrb j hj b (by rw [hab]; simp)
  have iha := ih a ha
  have ihb := ih b hb
  show Ld (mg D B σ j) _ ≤ Ld (gateAt D j) _
  by_cases hjB : j ∈ B
  · have hand := hB j hjB
    simp only [mg, hjB, ite_true]
    have hp := pk_mem D σ j a b hab
    have ihp := ih (pk D σ j) (by rcases hp with h | h <;> rw [h] <;> assumption)
    have hne : ¬ GateOp.or = GateOp.and := by intro h; cases h
    simp only [Ld, Gate.lineDegree, hab, hand, ite_true]
    rw [if_neg hne]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, max_self, Nat.add_zero]
    rcases hp with h | h <;> rw [h] at ihp ⊢ <;> omega
  · simp only [mg, hjB, ite_false]
    rcases hop with h | h
    · simp only [Ld, Gate.lineDegree, hab, h, ite_true]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, max_self, Nat.add_zero]
      omega
    · have hn : ¬ (gateAt D j).op = GateOp.and := by rw [h]; intro h; cases h
      simp only [Ld, Gate.lineDegree, hab]
      rw [if_neg hn, if_neg hn]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero, max_self, Nat.add_zero]
      exact max_le_max iha ihb

theorem mono (D : Circuit) (B : Finset ℕ) (σ : ℕ → Bool) (n : ℕ) (x : List Bool)
    (hx : x.length = n)
    (hD : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack n D) (hB : ∀ j ∈ B, (gateAt D j).op = GateOp.and) :
    ∀ i, (D.wires x).getD i false = true → ((Cs D B σ).wires x).getD i false = true := by
  rw [wires_eq, wires_eq]
  refine rel_fold (fun a b => a = true → b = true) W W ⟨GateOp.or, []⟩ D.gates (Cs D B σ).gates
    (Cs_len D B σ) _ _ rfl false false id (fun i _ => id) ?_
  intro j hj ih
  rw [Cs_getD D B σ j hj]
  obtain ⟨a, b, hab, hop⟩ := two D hD j hj
  have ha : a < x.length + j := by rw [hx]; exact hrb j hj a (by rw [hab]; simp)
  have hb : b < x.length + j := by rw [hx]; exact hrb j hj b (by rw [hab]; simp)
  have iha := ih a ha
  have ihb := ih b hb
  show W (gateAt D j) _ = true → W (mg D B σ j) _ = true
  by_cases hjB : j ∈ B
  · have hand := hB j hjB
    simp only [mg, hjB, ite_true]
    have hp := pk_mem D σ j a b hab
    simp only [W, hab, hand, GateOp.eval]
    intro h
    simp at h
    simp
    rcases hp with hp | hp <;> rw [hp] <;> tauto
  · simp only [mg, hjB, ite_false]
    rcases hop with h | h
    · simp only [W, hab, h, GateOp.eval]
      simp; tauto
    · simp only [W, hab, h, GateOp.eval]
      simp; tauto

theorem eqz (D : Circuit) (B : Finset ℕ) (n : ℕ) (x : List Bool)
    (hx : x.length = n)
    (hD : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack n D) (hB : ∀ j ∈ B, (gateAt D j).op = GateOp.and) :
    ∀ i, (D.wires x).getD i false =
      ((Cs D B (fun j => (D.wires x).getD ((gateAt D j).inputs.getD 0 0) false)).wires x).getD
        i false := by
  have hW : ∀ j, j ≤ D.gates.length → ∀ i < x.length + j,
      (F W D.gates x).getD i false = (F W (D.gates.take j) x).getD i false :=
    fun j hj i hi => F_prefix W D.gates x j i false hi hj
  rw [wires_eq, wires_eq]
  refine rel_fold (fun a b => a = b) W W ⟨GateOp.or, []⟩ D.gates _
    (Cs_len D B _) _ _ rfl false false rfl (fun i _ => rfl) ?_
  intro j hj ih
  rw [Cs_getD D B _ j hj]
  obtain ⟨a, b, hab, hop⟩ := two D hD j hj
  have ha : a < x.length + j := by rw [hx]; exact hrb j hj a (by rw [hab]; simp)
  have hb : b < x.length + j := by rw [hx]; exact hrb j hj b (by rw [hab]; simp)
  have iha := ih a ha
  have ihb := ih b hb
  have hwa := hW j hj.le a ha
  show W (gateAt D j) _ = W (mg D B _ j) _
  by_cases hjB : j ∈ B
  · have hand := hB j hjB
    simp only [mg, hjB, ite_true, pk, hab]
    simp only [W, hab, hand, GateOp.eval]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [hwa]
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons,
      List.any_nil, id]
    cases hc : (F W (List.take j D.gates) x).getD a false
    · simp only [Bool.false_eq_true, if_false, ← iha, hc]; simp
    · simp only [if_true, ← ihb]; simp
  · simp only [mg, hjB, ite_false]
    simp only [W, hab, List.map_cons, List.map_nil]
    rw [iha, ihb]

theorem km_transfer (D : Circuit) (B : Finset ℕ) (σ : ℕ → Bool) (N j : ℕ)
    (hD : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) D) (hB : ∀ j ∈ B, (gateAt D j).op = GateOp.and)
    (hj : j < D.gates.length) (hjB : j ∉ B) (hk : KM D N j) : KM (Cs D B σ) N j := by
  unfold KM at *
  rw [gateAt_Cs D B σ j hj]
  simp only [mg, hjB, ite_false]
  rcases hk with ⟨i, hi, h0⟩ | h
  · left
    have := deg D B σ (N + N) (Finset.Ico N (N + N)) hD hrb hB i
    exact ⟨i, hi, by omega⟩
  · right
    intro h' hh
    have := deg D B σ (N + N) (Finset.range N) hD hrb hB h'
    have := h h' hh
    omega

theorem main : (∀ (q111 N111 k111 v111 t111 : ℕ) (I111 : Fin N111 → Fin N111 → Prop) [DecidableRel I111] (Cs111 : Fin v111 → PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q111 → N111 = q111 ^ 2 + q111 + 1 → (∀ l111a : Fin N111, (Finset.univ.filter (fun p111a => I111 p111a l111a)).card = q111 + 1) → (∀ pa111 pb111 : Fin N111, pa111 ≠ pb111 → ∃! lb111 : Fin N111, I111 pa111 lb111 ∧ I111 pb111 lb111) → 8 ≤ q111 → 1 ≤ v111 → v111 ≤ k111 → 8 * v111 ≤ q111 → (∀ i111 : Fin v111, ((∀ g111 ∈ (Cs111 i111).gates, (g111.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g111.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g111.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N111 + N111) (Cs111 i111)) ∧ (∀ j111 < (Cs111 i111).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i111c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).inputs, ((Cs111 i111).lineDegrees (N111 + N111) (Finset.Ico N111 (N111 + N111))).getD i111c 0 = 0) ∨ (∀ h111 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).inputs, ((Cs111 i111).lineDegrees (N111 + N111) (Finset.range N111)).getD h111 0 = 0)) ∧ (Cs111 i111).size ≤ t111) → (∀ p111 l111 : Fin N111, I111 p111 l111 → ∀ i111a : Fin v111, PEqualNP.MetaComplexity.circuitFun (N111 + N111) (Cs111 i111a) (fun i111d => decide (i111d = Fin.castAdd N111 p111 ∨ i111d = Fin.natAdd N111 l111)) = true) → (∀ z111 : Fin (N111 + N111) → Bool, (Finset.univ.filter (fun l111b : Fin N111 => z111 (Fin.natAdd N111 l111b) = true)).card ≤ k111 → (¬ ∃ p111b l111c : Fin N111, I111 p111b l111c ∧ z111 (Fin.castAdd N111 p111b) = true ∧ z111 (Fin.natAdd N111 l111c) = true) → ∃ i111b : Fin v111, PEqualNP.MetaComplexity.circuitFun (N111 + N111) (Cs111 i111b) z111 = false) → N111 * (min k111 (q111 / 4) / v111) ≤ 20 * t111) → (∀ (N112 km112 : ℕ) (C112 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C112 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) C112 → Set.ncard {j112 : ℕ | j112 < C112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112 0 = 0) ∨ (∀ h112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112 0 = 0))} ≤ km112 → (∃ z112 z112a : Fin (N112 + N112) → Bool, PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112 ≠ PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112a) → ∃ D112 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g112 ∈ D112.gates, (g112.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g112.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g112.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) D112) ∧ Set.ncard {j112a : ℕ | j112a < D112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112a 0 = 0) ∨ (∀ h112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112a 0 = 0))} ≤ km112 ∧ D112.size ≤ C112.size ∧ PEqualNP.MetaComplexity.circuitFun (N112 + N112) D112 = PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112) → ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (km : ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → Set.ncard {j11 : ℕ | j11 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).inputs, (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i11 0 = 0) ∨ (∀ h11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).inputs, (C.lineDegrees (N + N) (Finset.range N)).getD h11 0 = 0))} ≤ km → 8 * 2 ^ km ≤ q → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * (min q (q / 4) / 2 ^ km) ≤ 20 * C.size := by
  intro H1 H2 q N I _ C km hq hN hline huniq hmono hrb hbad hpow hacc hrej
  have hN0 : 0 < N := by subst hN; positivity
  have hcard := hline ⟨0, hN0⟩
  obtain ⟨p0, hp0⟩ : ∃ p, I p ⟨0, hN0⟩ := by
    have : (Finset.univ.filter (fun p => I p ⟨0, hN0⟩)).Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    obtain ⟨p, hp⟩ := this
    exact ⟨p, by simpa using hp⟩
  have hfalse : circuitFun (N + N) C (fun _ => false) = false := hrej _ (by simp) (by simp)
  have hnc : ∃ z z' : Fin (N + N) → Bool, circuitFun (N + N) C z ≠ circuitFun (N + N) C z' :=
    ⟨fun k => decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N ⟨0, hN0⟩), fun _ => false,
      by rw [hacc p0 ⟨0, hN0⟩ hp0, hfalse]; simp⟩
  obtain ⟨D, ⟨hD, hrbD⟩, hbadD, hsize, hfun⟩ := H2 N km C hmono hrb hbad hnc
  classical
  let B : Finset ℕ := (Finset.range D.gates.length).filter
    (fun j => (gateAt D j).op = GateOp.and ∧ ¬ KM D N j)
  have hBset : {j | j < D.gates.length ∧ (gateAt D j).op = GateOp.and ∧ ¬ KM D N j} =
      (B : Set ℕ) := by
    ext j; simp [B]
  have hBk : B.card ≤ km := by
    rw [← Set.ncard_coe_finset, ← hBset]; exact hbadD
  have hBand : ∀ j ∈ B, (gateAt D j).op = GateOp.and := by
    intro j hj; simp only [B, Finset.mem_filter] at hj; exact hj.2.1
  let e := B.equivFin
  let σ : Fin (2 ^ B.card) → ℕ → Bool := fun i j =>
    if h : j ∈ B then decide ((finFunctionFinEquiv.symm i) (e ⟨j, h⟩) = 1) else false
  have hpowb : 2 ^ B.card ≤ 2 ^ km := Nat.pow_le_pow_right (by norm_num) hBk
  have h1 : 1 ≤ 2 ^ km := Nat.one_le_two_pow
  have hres := H1 q N q (2 ^ B.card) C.size I (fun i => Cs D B (σ i)) hq hN hline huniq
    (by omega) Nat.one_le_two_pow (by omega) (by omega) ?circ ?acc ?rej
  · calc N * (min q (q / 4) / 2 ^ km) ≤ N * (min q (q / 4) / 2 ^ B.card) :=
          Nat.mul_le_mul_left _ (Nat.div_le_div_left hpowb (by positivity))
      _ ≤ 20 * C.size := hres
  case circ =>
    intro i
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro g hg
      simp only [Cs, List.mem_map, List.mem_range] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      unfold mg
      split_ifs
      · simp
      · exact hD _ (gateAt_mem D j hj)
    · intro j hj i' hi'
      rw [Cs_len] at hj
      rw [gateAt_Cs D B _ j hj] at hi'
      unfold mg at hi'
      split_ifs at hi' with hjB
      · obtain ⟨a, b, hab, _⟩ := two D hD j hj
        have hi'' : i' = pk D (σ i) j := by simpa using hi'
        apply hrbD j hj
        rw [hab, hi'']
        rcases pk_mem D (σ i) j a b hab with h | h <;> rw [h] <;> simp
      · exact hrbD j hj i' hi'
    · intro j hj hand
      rw [Cs_len] at hj
      by_cases hjB : j ∈ B
      · rw [gateAt_Cs D B _ j hj] at hand
        simp only [mg, hjB, ite_true] at hand
        cases hand
      · have hDand : (gateAt D j).op = GateOp.and := by
          rw [gateAt_Cs D B _ j hj] at hand
          simpa only [mg, hjB, ite_false] using hand
        have hk : KM D N j := by
          by_contra h
          exact hjB (by simp only [B, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hDand, h⟩)
        exact km_transfer D B (σ i) N j hD hrbD hBand hj hjB hk
    · show (Cs D B (σ i)).gates.length ≤ C.gates.length
      rw [Cs_len]; exact hsize
  case acc =>
    intro p l hpl i
    have h := hacc p l hpl
    rw [← hfun] at h
    unfold circuitFun Circuit.eval at h ⊢
    exact mono D B (σ i) (N + N) _ (by simp) hD hrbD hBand D.output h
  case rej =>
    intro z hz1 hz2
    have hz := hrej z hz1 hz2
    rw [← hfun] at hz
    let σz : ℕ → Bool := fun j => (D.wires (List.ofFn z)).getD ((gateAt D j).inputs.getD 0 0) false
    let τ : Fin B.card → Fin 2 := fun r => if σz (e.symm r).val then 1 else 0
    refine ⟨finFunctionFinEquiv τ, ?_⟩
    have hc : Cs D B (σ (finFunctionFinEquiv τ)) = Cs D B σz := by
      apply Cs_congr
      intro j hj
      simp only [σ, hj, dite_true, Equiv.symm_apply_apply, τ]
      cases σz j <;> simp
    rw [hc]
    unfold circuitFun Circuit.eval at hz ⊢
    have hq := eqz D B (N + N) (List.ofFn z) (by simp) hD hrbD hBand D.output
    show ((Cs D B σz).wires (List.ofFn z)).getD D.output false = false
    rw [← hq]
    exact hz

end PEqualNP.Outside.L_meta_1725

theorem PEqualNP.Outside.L_meta_1725 : (∀ (q111 N111 k111 v111 t111 : ℕ) (I111 : Fin N111 → Fin N111 → Prop) [DecidableRel I111] (Cs111 : Fin v111 → PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q111 → N111 = q111 ^ 2 + q111 + 1 → (∀ l111a : Fin N111, (Finset.univ.filter (fun p111a => I111 p111a l111a)).card = q111 + 1) → (∀ pa111 pb111 : Fin N111, pa111 ≠ pb111 → ∃! lb111 : Fin N111, I111 pa111 lb111 ∧ I111 pb111 lb111) → 8 ≤ q111 → 1 ≤ v111 → v111 ≤ k111 → 8 * v111 ≤ q111 → (∀ i111 : Fin v111, ((∀ g111 ∈ (Cs111 i111).gates, (g111.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g111.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g111.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N111 + N111) (Cs111 i111)) ∧ (∀ j111 < (Cs111 i111).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i111c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).inputs, ((Cs111 i111).lineDegrees (N111 + N111) (Finset.Ico N111 (N111 + N111))).getD i111c 0 = 0) ∨ (∀ h111 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Cs111 i111) j111).inputs, ((Cs111 i111).lineDegrees (N111 + N111) (Finset.range N111)).getD h111 0 = 0)) ∧ (Cs111 i111).size ≤ t111) → (∀ p111 l111 : Fin N111, I111 p111 l111 → ∀ i111a : Fin v111, PEqualNP.MetaComplexity.circuitFun (N111 + N111) (Cs111 i111a) (fun i111d => decide (i111d = Fin.castAdd N111 p111 ∨ i111d = Fin.natAdd N111 l111)) = true) → (∀ z111 : Fin (N111 + N111) → Bool, (Finset.univ.filter (fun l111b : Fin N111 => z111 (Fin.natAdd N111 l111b) = true)).card ≤ k111 → (¬ ∃ p111b l111c : Fin N111, I111 p111b l111c ∧ z111 (Fin.castAdd N111 p111b) = true ∧ z111 (Fin.natAdd N111 l111c) = true) → ∃ i111b : Fin v111, PEqualNP.MetaComplexity.circuitFun (N111 + N111) (Cs111 i111b) z111 = false) → N111 * (min k111 (q111 / 4) / v111) ≤ 20 * t111) → (∀ (N112 km112 : ℕ) (C112 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C112 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) C112 → Set.ncard {j112 : ℕ | j112 < C112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112 0 = 0) ∨ (∀ h112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112 0 = 0))} ≤ km112 → (∃ z112 z112a : Fin (N112 + N112) → Bool, PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112 ≠ PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112a) → ∃ D112 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g112 ∈ D112.gates, (g112.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g112.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g112.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) D112) ∧ Set.ncard {j112a : ℕ | j112a < D112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112a 0 = 0) ∨ (∀ h112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112a 0 = 0))} ≤ km112 ∧ D112.size ≤ C112.size ∧ PEqualNP.MetaComplexity.circuitFun (N112 + N112) D112 = PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112) → ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (km : ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → Set.ncard {j11 : ℕ | j11 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).inputs, (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i11 0 = 0) ∨ (∀ h11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j11).inputs, (C.lineDegrees (N + N) (Finset.range N)).getD h11 0 = 0))} ≤ km → 8 * 2 ^ km ≤ q → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * (min q (q / 4) / 2 ^ km) ≤ 20 * C.size :=
  PEqualNP.Outside.L_meta_1725.main
