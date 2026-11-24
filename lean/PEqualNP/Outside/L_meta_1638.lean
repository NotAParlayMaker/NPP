import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1638

open PEqualNP.CircuitLowerBounds

def step (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

lemma length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [step, ih, Nat.add_comm, Nat.add_left_comm]

lemma old (gs : List Gate) (w : List Bool) (k : ℕ) (h : k < w.length) :
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ h]
    exact List.getElem_append_left h

def V {n : ℕ} (gs : List Gate) (k : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl step (List.ofFn x)).getD k false

lemma eval_gate {n : ℕ} (gs : List Gate) (j : ℕ) (h : j < gs.length) (x : Fin n → Bool) :
    V gs (n+j) x = gs[j].op.eval
      (gs[j].inputs.map fun k => if k < n+j then V gs k x else false) := by
  unfold V
  let w := (gs.take j).foldl step (List.ofFn x)
  have hw : w.length = n+j := by simp [w, length_run, Nat.min_eq_left (Nat.le_of_lt h)]
  have split : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons h]
  have fold : gs.foldl step (List.ofFn x) = (gs.drop (j+1)).foldl step (step w gs[j]) := by
    conv_lhs => rw [split, List.foldl_append, List.foldl_cons]
  have oldp (k : ℕ) (hk : k < n+j) : (gs.foldl step (List.ofFn x)).getD k false = w.getD k false := by
    conv_lhs => rw [split, List.foldl_append]
    exact old _ w _ (by rw [hw]; exact hk)
  calc
    _ = (step w gs[j]).getD w.length false := by
      rw [fold, old _ _ _ (by simp [step, hw]), hw]
    _ = gs[j].op.eval (gs[j].inputs.map fun k => w.getD k false) := by simp [step]
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro k _
      by_cases hk : k < n+j
      · rw [ite_eq_left hk, oldp k hk]
      · rw [ite_eq_right hk, List.getD_eq_default _ _ (by simpa [hw] using hk)]

lemma raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (h : k < n) :
    V gs k x = x ⟨k,h⟩ := by
  unfold V
  rw [old _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
  simp

lemma big {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (h : n + gs.length ≤ k) :
    V gs k x = false := by
  unfold V
  rw [List.getD_eq_default]
  rw [length_run]
  simpa using h

lemma gate_or {n : ℕ} (gs : List Gate) (i : Fin gs.length) (x : Fin n → Bool)
    (hop : (gs.get i).op = GateOp.or) (hw : ∀ w ∈ (gs.get i).inputs, w < n + (i : ℕ)) :
    V gs (n + (i : ℕ)) x = true ↔ ∃ e ∈ (gs.get i).inputs, V gs e x = true := by
  have h := eval_gate gs i.val i.isLt x
  have hg : gs[i.val] = gs.get i := rfl
  rw [h, hg, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨b, ⟨e, he, rfl⟩, hb⟩
    refine ⟨e, he, ?_⟩
    rw [ite_eq_left (hw e he)] at hb
    exact hb
  · rintro ⟨e, he, hv⟩
    refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
    rw [ite_eq_left (hw e he)]
    exact hv

lemma gate_and {n : ℕ} (gs : List Gate) (i : Fin gs.length) (x : Fin n → Bool)
    (hop : (gs.get i).op = GateOp.and) (hw : ∀ w ∈ (gs.get i).inputs, w < n + (i : ℕ)) :
    V gs (n + (i : ℕ)) x = true ↔ ∀ e ∈ (gs.get i).inputs, V gs e x = true := by
  have h := eval_gate gs i.val i.isLt x
  have hg : gs[i.val] = gs.get i := rfl
  rw [h, hg, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map]
  constructor
  · intro hall e he
    have h2 := hall _ ⟨e, he, rfl⟩
    rw [ite_eq_left (hw e he)] at h2
    exact h2
  · rintro hall b ⟨e, he, rfl⟩
    rw [ite_eq_left (hw e he)]
    exact hall e he

def Reach (N : ℕ) (gates : List Gate) (u Y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S →
    (gates.get i).op = GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → Y ∈ S

lemma main (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (gates : List Gate) (u : ℕ)
    (hops : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hw : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (hu : V gates u (fun v : Fin N => decide (v ∉ L i0)) = false) :
    (∀ Y : ℕ, Reach N gates u Y → V gates Y (fun v : Fin N => decide (v ∉ L i0)) = false) ∧
    (∀ p : Fin N, Reach N gates u (p : ℕ) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, V gates u (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true →
      Reach N gates u (r : ℕ) ∨ ∃ a : ℕ, Reach N gates u a ∧
        (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
        V gates a (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = GateOp.and →
      V gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
      c ∈ (gates.get a).inputs → V gates c (fun v : Fin N => decide (v ∉ L i0)) = false →
      ∀ r ∈ L i0 \ T0, V gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true →
        V gates c (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) := by
  have P1 : ∀ Y : ℕ, Reach N gates u Y →
      V gates Y (fun v : Fin N => decide (v ∉ L i0)) = false := by
    intro Y hY
    have h := hY {Y | V gates Y (fun v : Fin N => decide (v ∉ L i0)) = false} hu (by
      intro i hi hop e he
      have hi2 : V gates (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false := hi
      show V gates e (fun v : Fin N => decide (v ∉ L i0)) = false
      by_contra hne
      have ht : V gates e (fun v : Fin N => decide (v ∉ L i0)) = true := by
        simpa using hne
      have h3 := (gate_or gates i _ hop (hw i)).mpr ⟨e, he, ht⟩
      rw [hi2] at h3
      exact Bool.false_ne_true h3)
    exact h
  refine ⟨P1, ?_, ?_, ?_⟩
  · intro p hp
    have h1 := P1 _ hp
    rw [raw gates _ p.val p.isLt] at h1
    simpa using h1
  · intro r _ htrue
    have key : ∀ Y : ℕ, Reach N gates u Y →
        V gates Y (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true →
        Reach N gates u (r : ℕ) ∨ ∃ a : ℕ, Reach N gates u a ∧
          (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
          V gates a (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true := by
      intro Y
      induction Y using Nat.strong_induction_on with
      | _ Y ih =>
        intro hY hYt
        by_cases hlt : Y < N
        · left
          have h1 := P1 Y hY
          rw [raw gates _ Y hlt] at h1 hYt
          have h1b : (⟨Y, hlt⟩ : Fin N) ∈ L i0 := by simpa using h1
          have h2b : (⟨Y, hlt⟩ : Fin N) ∉ L i0 ∨ (⟨Y, hlt⟩ : Fin N) = r := by simpa using hYt
          have h3 : (⟨Y, hlt⟩ : Fin N) = r := h2b.resolve_left (fun h => h h1b)
          have h4 : Y = (r : ℕ) := by rw [← h3]
          rw [← h4]
          exact hY
        · by_cases hlt2 : Y < N + gates.length
          · obtain ⟨j, rfl⟩ : ∃ j, Y = N + j := ⟨Y - N, by omega⟩
            have hj : j < gates.length := by omega
            have hmem : gates.get ⟨j, hj⟩ ∈ gates := List.get_mem gates ⟨j, hj⟩
            rcases (hops _ hmem).1 with hand | hor
            · right
              exact ⟨N + j, hY, ⟨⟨j, hj⟩, rfl, hand⟩, hYt⟩
            · obtain ⟨e, he, het⟩ := (gate_or gates ⟨j, hj⟩ _ hor (hw ⟨j, hj⟩)).mp hYt
              have hel : e < N + j := hw ⟨j, hj⟩ e he
              have hRe : Reach N gates u e :=
                fun S hS hcl => hcl ⟨j, hj⟩ (hY S hS hcl) hor e he
              exact ih e hel hRe het
          · exfalso
            rw [big gates _ Y (by omega)] at hYt
            exact Bool.false_ne_true hYt
    exact key u (fun S hS _ => hS) htrue
  · intro a c hop _ hc _ r _ ht
    exact (gate_and gates a _ hop (hw a)).mp ht c hc

end PEqualNP.Outside.L_meta_1638

theorem PEqualNP.Outside.L_meta_1638 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hops _ hw hu
  exact PEqualNP.Outside.L_meta_1638.main N L i0 T0 gates u hops hw hu
