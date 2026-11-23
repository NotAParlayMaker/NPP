import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_216

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_prefix (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, step_length, List.length_cons]
    omega

lemma fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by rw [step_length]; omega)]
    exact step_prefix w g i hi

lemma fold_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      rw [fold_prefix gs (step w g) (w.length + 0) (by rw [step_length]; omega)]
      have h0 : (step w g).getD (w.length + 0) false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [h0]
      simp only [List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases h : i < w.length
      · have h' : i < w.length + 0 := by omega
        simp only [h', ite_true]
        rw [fold_prefix gs (step w g) i (by rw [step_length]; omega)]
        exact (step_prefix w g i h).symm
      · have h' : ¬ i < w.length + 0 := by omega
        simp only [h', ite_false]
        exact List.getD_eq_default _ _ (by omega)
    | succ j =>
      have h := ih (step w g) j (by simpa using hj)
      rw [step_length] at h
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact h

def val (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (t : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD t false

lemma val_in (gs : List Gate) (n : ℕ) (t : ℕ) (h : t < n) (x : Fin n → Bool) :
    val gs n x t = x ⟨t, h⟩ := by
  unfold val
  rw [fold_prefix _ _ t (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_out (gs : List Gate) (n : ℕ) (t : ℕ) (h : n + gs.length ≤ t) (x : Fin n → Bool) :
    val gs n x t = false := by
  unfold val
  apply List.getD_eq_default
  rw [fold_length, List.length_ofFn]
  exact h

def ent (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (t i : ℕ) : Bool :=
  if i < t then val gs n x i else false

lemma val_key (gs : List Gate) (n : ℕ) (j : ℕ) (hj : j < gs.length) (z : Fin n → Bool) :
    val gs n z (n + j) = (gs[j]).op.eval ((gs[j]).inputs.map (ent gs n z (n + j))) := by
  have h := fold_gate gs (List.ofFn z) j hj
  rw [List.length_ofFn] at h
  exact h

def firstval (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (j : ℕ) : Bool :=
  match gs[j]? with
  | some g =>
    match g.inputs with
    | u :: _ => ent gs n x (n + j) u
    | [] => false
  | none => false

lemma join_false (gs : List Gate) (n : ℕ) (A : Finset ℕ)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → j ∈ A)
    (x y : Fin n → Bool) (hσ : ∀ j ∈ A, firstval gs n x j = firstval gs n y j) :
    ∀ t, val gs n x t = false → val gs n y t = false →
      val gs n (fun i => x i || y i) t = false := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hx hy
    by_cases h1 : t < n
    · rw [val_in gs n t h1] at hx hy ⊢
      simp [hx, hy]
    · by_cases h2 : t < n + gs.length
      · obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
        have hj : j < gs.length := by omega
        have hent : ∀ i, ent gs n x (n + j) i = false → ent gs n y (n + j) i = false →
            ent gs n (fun i => x i || y i) (n + j) i = false := by
          intro i hxi hyi
          unfold ent at hxi hyi ⊢
          by_cases hlt : i < n + j
          · simp only [hlt, ↓reduceIte] at hxi hyi ⊢
            exact ih i hlt hxi hyi
          · simp only [hlt, ↓reduceIte]
        rw [val_key gs n j hj] at hx hy ⊢
        have hgj : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
        have hmj := hm _ (List.getElem_mem hj)
        rcases hmj.1 with hop | hop
        · have hjA : j ∈ A := hA j _ hgj hop
          have hs := hσ j hjA
          unfold firstval at hs
          rw [hgj] at hs
          simp only [] at hs
          rw [hop] at hx hy ⊢
          simp only [GateOp.eval] at hx hy ⊢
          have hlen := hmj.2
          rcases hin : (gs[j]).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩
          · rw [hin] at hx
            simp at hx
          · rw [hin] at hx hy
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
              Bool.and_true] at hx hy ⊢
            exact hent u hx hy
          · rw [hin] at hx hy hs
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
              Bool.and_true] at hx hy ⊢
            simp only [] at hs
            cases hux : ent gs n x (n + j) u
            · have huy : ent gs n y (n + j) u = false := by rw [← hs, hux]
              rw [hent u hux huy]
              rfl
            · have huy : ent gs n y (n + j) u = true := by rw [← hs, hux]
              rw [hux] at hx
              rw [huy] at hy
              simp only [Bool.true_and] at hx hy
              rw [hent v hx hy]
              simp
          · rw [hin] at hlen
            simp at hlen
        · rw [hop] at hx hy ⊢
          simp only [GateOp.eval] at hx hy ⊢
          rw [List.any_eq_false] at hx hy ⊢
          intro b hb
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
          have e1 := hx _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
          have e2 := hy _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
          simp only [id, Bool.not_eq_true] at e1 e2 ⊢
          exact hent i e1 e2
      · exact val_out gs n t (by omega) _

end PEqualNP.Outside.L_meta_216

theorem PEqualNP.Outside.L_meta_216 : ∀ (n k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∃ A : Finset ℕ, A.card ≤ k ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → {x : Fin n → Bool | C.eval (List.ofFn x) = false ∧ ∀ y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) → C.eval (List.ofFn y) = false → y = x}.ncard ≤ 2 ^ k := by
  intro n k C hmono hA
  obtain ⟨A, hAk, hA⟩ := hA
  classical
  have hm : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    simpa using h1
  have hinj : Set.InjOn (fun x : Fin n → Bool =>
      A.filter (fun j => PEqualNP.Outside.L_meta_216.firstval C.gates n x j = true))
      {x : Fin n → Bool | C.eval (List.ofFn x) = false ∧ ∀ y : Fin n → Bool,
        (∀ i : Fin n, x i = true → y i = true) → C.eval (List.ofFn y) = false → y = x} := by
    intro x hx y hy hxy
    have hσ : ∀ j ∈ A, PEqualNP.Outside.L_meta_216.firstval C.gates n x j = PEqualNP.Outside.L_meta_216.firstval C.gates n y j := by
      intro j hj
      have h1 : j ∈ A.filter (fun j => PEqualNP.Outside.L_meta_216.firstval C.gates n x j = true) ↔
          j ∈ A.filter (fun j => PEqualNP.Outside.L_meta_216.firstval C.gates n y j = true) := by
        rw [show A.filter (fun j => PEqualNP.Outside.L_meta_216.firstval C.gates n x j = true) =
          A.filter (fun j => PEqualNP.Outside.L_meta_216.firstval C.gates n y j = true) from hxy]
      simp only [Finset.mem_filter, hj, true_and] at h1
      cases hfx : PEqualNP.Outside.L_meta_216.firstval C.gates n x j <;> cases hfy : PEqualNP.Outside.L_meta_216.firstval C.gates n y j <;>
        simp [hfx, hfy] at h1 ⊢
    have hz : C.eval (List.ofFn (fun i => x i || y i)) = false :=
      PEqualNP.Outside.L_meta_216.join_false C.gates n A hm hA x y hσ C.output hx.1 hy.1
    have ex := hx.2 (fun i => x i || y i) (fun i hi => by simp [hi]) hz
    have ey := hy.2 (fun i => x i || y i) (fun i hi => by simp [hi]) hz
    exact ex.symm.trans ey
  have hmaps : ∀ x ∈ {x : Fin n → Bool | C.eval (List.ofFn x) = false ∧ ∀ y : Fin n → Bool,
      (∀ i : Fin n, x i = true → y i = true) → C.eval (List.ofFn y) = false → y = x},
      (fun x : Fin n → Bool => A.filter (fun j => PEqualNP.Outside.L_meta_216.firstval C.gates n x j = true)) x ∈
        (A.powerset : Set (Finset ℕ)) := by
    intro x _
    exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  have h1 := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_powerset] at h1
  exact h1.trans (Nat.pow_le_pow_right (by omega) hAk)
