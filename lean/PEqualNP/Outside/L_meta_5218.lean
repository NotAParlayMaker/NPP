import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5218

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem fold_len : ∀ (gs : List Gate) (l : List Bool),
    (gs.foldl step l).length = l.length + gs.length
  | [], l => by simp
  | g :: gs, l => by
    rw [List.foldl_cons, fold_len gs, step_len]; simp; omega

theorem fold_prefix : ∀ (gs : List Gate) (l : List Bool) (i : ℕ), i < l.length →
    (gs.foldl step l).getD i false = l.getD i false
  | [], l, i, _ => rfl
  | g :: gs, l, i, h => by
    rw [List.foldl_cons, fold_prefix gs _ i (by rw [step_len]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem fold_out (gs : List Gate) (l : List Bool) (i : ℕ) (h : l.length + gs.length ≤ i) :
    (gs.foldl step l).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [fold_len]; omega)]; rfl

theorem fold_gate : ∀ (gs : List Gate) (l : List Bool) (k : ℕ) (g : Gate), gs[k]? = some g →
    (gs.foldl step l).getD (l.length + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < l.length + k then (gs.foldl step l).getD i false else false)
  | [], l, k, g, h => by simp at h
  | g0 :: gs, l, 0, g, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.foldl_cons, Nat.add_zero, fold_prefix gs _ _ (by rw [step_len]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    congr 1
    apply List.map_congr_left
    intro i _
    split_ifs with hi
    · rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD,
        fold_prefix gs _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    · rw [List.getElem?_eq_none (by omega)]; rfl
  | g0 :: gs, l, k + 1, g, h => by
    simp only [List.getElem?_cons_succ] at h
    have := fold_gate gs (step l g0) k g h
    rw [step_len] at this
    rw [List.foldl_cons, show l.length + (k + 1) = l.length + 1 + k by omega]
    exact this

def W (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem W_in (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    W C n x i = x ⟨i, h⟩ := by
  unfold W Circuit.wires
  rw [show (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = step
    from rfl, fold_prefix _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem W_out (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ)
    (h : n + C.gates.length ≤ i) : W C n x i = false := by
  unfold W Circuit.wires
  rw [show (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = step
    from rfl, fold_out _ _ _ (by simpa using h)]

theorem W_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (h : C.gates[k]? = some g) :
    W C n x (n + k) = g.op.eval (g.inputs.map fun i =>
      if i < n + k then W C n x i else false) := by
  unfold W Circuit.wires
  rw [show (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = step
    from rfl]
  have := fold_gate C.gates (List.ofFn x) k g h
  simp only [List.length_ofFn] at this
  exact this

theorem gate_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (f f' : ℕ → Bool) (hf : ∀ j ∈ g.inputs, f j = true → f' j = true)
    (h : g.op.eval (g.inputs.map f) = true) : g.op.eval (g.inputs.map f') = true := by
  rcases hg with hg | hg <;> rw [hg] at h ⊢ <;>
    simp only [GateOp.eval, List.all_eq_true, List.any_eq_true, List.mem_map] at h ⊢
  · rintro b ⟨j, hj, rfl⟩
    exact hf j hj (h _ ⟨j, hj, rfl⟩)
  · obtain ⟨b, ⟨j, hj, rfl⟩, hb⟩ := h
    exact ⟨_, ⟨j, hj, rfl⟩, hf j hj hb⟩

theorem W_mono (C : Circuit) (n : ℕ) (hC : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ j, x j = true → y j = true) :
    ∀ i, W C n x i = true → W C n y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [W_in C n x i h1] at hi; rw [W_in C n y i h1]; exact hxy _ hi
    by_cases h2 : n + C.gates.length ≤ i
    · rw [W_out C n x i h2] at hi; exact absurd hi (by simp)
    obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hg : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
    rw [W_gate C n x k _ hg] at hi
    rw [W_gate C n y k _ hg]
    refine gate_mono _ (hC _ (List.getElem_mem hk)).1 _ _ ?_ hi
    intro j _ hj
    split_ifs at hj ⊢ with hjl
    · exact ih j hjl hj

def Flip (C : Circuit) (n : ℕ) (x : Fin n → Bool) (v : Fin n) (i : ℕ) : Prop :=
  W C n x i ≠ W C n (Function.update x v false) i

def E (C : Circuit) (n : ℕ) (x : Fin n → Bool) (v : Fin n) (p c : ℕ) : Prop :=
  n ≤ p ∧ (∃ g, C.gates[p - n]? = some g ∧ c ∈ g.inputs) ∧ Flip C n x v c

theorem flip_lt (C : Circuit) (n : ℕ) (x : Fin n → Bool) (v : Fin n) (i : ℕ)
    (h : Flip C n x v i) : i < n + C.gates.length := by
  by_contra h2
  exact h (by rw [W_out C n _ i (by omega), W_out C n _ i (by omega)])

theorem flip_path (C : Circuit) (n : ℕ) (x : Fin n → Bool) (v : Fin n) :
    ∀ i, Flip C n x v i → Relation.ReflTransGen (E C n x v) i v.val := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · have : (⟨i, h1⟩ : Fin n) = v := by
        by_contra hne
        apply hi
        rw [W_in C n _ i h1, W_in C n _ i h1, Function.update_of_ne hne]
      rw [← this]
    have h2 := flip_lt C n x v i hi
    obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hg : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
    have hex : ∃ j ∈ C.gates[k].inputs, j < n + k ∧ Flip C n x v j := by
      by_contra hne
      push_neg at hne
      apply hi
      rw [W_gate C n _ k _ hg, W_gate C n _ k _ hg]
      congr 1
      apply List.map_congr_left
      intro j hj
      split_ifs with hjl
      · by_contra hc; exact hne j hj hjl hc
      · rfl
    obtain ⟨j, hj, hjl, hjf⟩ := hex
    refine Relation.ReflTransGen.head ⟨by omega, ⟨_, by simpa using hg, hj⟩, hjf⟩ (ih j hjl hjf)

theorem flip_tail (C : Circuit) (n : ℕ) (x : Fin n → Bool) (v : Fin n) (a b : ℕ)
    (h : Relation.ReflTransGen (E C n x v) a b) (ha : Flip C n x v a) : Flip C n x v b := by
  induction h with
  | refl => exact ha
  | tail _ he _ => exact he.2.2

theorem flip_vals (C : Circuit) (n : ℕ) (hC : Monotone2 C) (x : Fin n → Bool) (v : Fin n)
    (i : ℕ) (h : Flip C n x v i) :
    W C n x i = true ∧ W C n (fun _ => false) i = false := by
  have hyx : ∀ j, Function.update x v false j = true → x j = true := by
    intro j hj
    by_cases hjv : j = v
    · subst hjv; simp at hj
    · rwa [Function.update_of_ne hjv] at hj
  have hy : W C n (Function.update x v false) i = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    exact h (by rw [hc, W_mono C n hC _ _ hyx i hc])
  refine ⟨?_, ?_⟩
  · by_contra hc
    simp only [Bool.not_eq_true] at hc
    exact h (by rw [hc, hy])
  · by_contra hc
    simp only [Bool.not_eq_false] at hc
    have := W_mono C n hC (fun _ => false) (Function.update x v false) (by simp) i hc
    rw [hy] at this; exact absurd this (by simp)

theorem main (n : ℕ) (C : Circuit) (X : Finset (Fin n → Bool)) (S : Finset (Fin n))
    (hC : Monotone2 C)
    (hS : ∀ v ∈ S, ∃ x ∈ X, circuitFun n C x ≠ circuitFun n C (Function.update x v false)) :
    S.card ≤ Fintype.card {k : Fin C.size //
      (C.wires (List.replicate n false)).getD (n + k) false = false ∧
      ∃ x ∈ X, EdgeOwnership.gateVal n C k x = true} + 1 := by
  classical
  choose! xs hxX hxf using hS
  have hflip : ∀ v ∈ S, Flip C n (xs v) v C.output := fun v hv => hxf v hv
  let D : Finset ℕ := (Finset.range (n + C.gates.length)).filter
    (fun w => ∃ v ∈ S, Relation.ReflTransGen (E C n (xs v) v) C.output w)
  let Dg : Finset (Fin C.size) := Finset.univ.filter (fun k => n + k.val ∈ D)
  let f : Fin C.size × Fin 2 → ℕ := fun p =>
    ((C.gates[p.1.val]?).map (fun g => g.inputs.getD p.2.val 0)).getD 0
  have memD : ∀ w, w ∈ D ↔ ∃ v ∈ S, Relation.ReflTransGen (E C n (xs v) v) C.output w := by
    intro w
    simp only [D, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    rintro ⟨v, hv, hp⟩
    exact flip_lt C n (xs v) v w (flip_tail C n _ v _ _ hp (hflip v hv))
  -- lower bound on |D|
  have h1 : S.card + Dg.card ≤ D.card := by
    have hdisj : Disjoint (S.image (fun v => v.val)) (Dg.image (fun k => n + k.val)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_image] at ha hb
      obtain ⟨v, _, rfl⟩ := ha
      obtain ⟨k, _, hk⟩ := hb
      have := v.2; omega
    have hsub : S.image (fun v => v.val) ∪ Dg.image (fun k => n + k.val) ⊆ D := by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
        exact (memD _).2 ⟨v, hv, flip_path C n _ v _ (hflip v hv)⟩
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ha
        exact (Finset.mem_filter.1 hk).2
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at this
    exact this
  -- upper bound on |D|
  have h2 : D.card ≤ 2 * Dg.card + 1 := by
    have hsub : D ⊆ insert C.output ((Dg ×ˢ (Finset.univ : Finset (Fin 2))).image f) := by
      intro d hd
      obtain ⟨v, hv, hp⟩ := (memD d).1 hd
      rcases Relation.ReflTransGen.cases_tail hp with rfl | ⟨p, hp1, hpd⟩
      · exact Finset.mem_insert_self _ _
      apply Finset.mem_insert_of_mem
      obtain ⟨hnp, ⟨g, hg, hdg⟩, _⟩ := hpd
      have hplt : p - n < C.gates.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hg; exact absurd hg (by simp)
      have hpD : p ∈ D := (memD p).2 ⟨v, hv, hp1⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hdg
      have hgm : g ∈ C.gates := List.mem_of_getElem? hg
      have hj2 : j < 2 := lt_of_lt_of_le hj (hC g hgm).2
      refine Finset.mem_image.2 ⟨(⟨p - n, hplt⟩, ⟨j, hj2⟩), ?_, ?_⟩
      · refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
          Finset.mem_univ _⟩
        show n + (p - n) ∈ D
        rwa [show n + (p - n) = p by omega]
      · simp only [f, hg, Option.map_some, Option.getD_some]
        simp [List.getD_eq_getElem?_getD, hj]
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have h3 := Finset.card_image_le (s := Dg ×ˢ (Finset.univ : Finset (Fin 2))) (f := f)
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h3
    omega
  -- Dg inside the counted set
  have h3 : Dg.card ≤ Fintype.card {k : Fin C.size //
      (C.wires (List.replicate n false)).getD (n + k) false = false ∧
      ∃ x ∈ X, EdgeOwnership.gateVal n C k x = true} := by
    rw [Fintype.card_subtype]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨v, hv, hp⟩ := (memD _).1 (Finset.mem_filter.1 hk).2
    have hv' := flip_vals C n hC _ v _ (flip_tail C n _ v _ _ hp (hflip v hv))
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, xs v, hxX v hv, hv'.1⟩
    have := hv'.2
    unfold W at this
    rwa [List.ofFn_const] at this
  omega

end PEqualNP.Outside.L_meta_5218

theorem PEqualNP.Outside.L_meta_5218 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1 → Bool)) (x4 : Finset (Fin x1)), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ x6 ∈ x4, ∃ x8 ∈ x3, PEqualNP.MetaComplexity.circuitFun x1 x2 x8 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x8 x6 Bool.false)) → x4.card ≤ Fintype.card { x7 : Fin x2.size // (x2.wires (List.replicate x1 Bool.false)).getD (x1 + ↑x7) Bool.false = Bool.false ∧ ∃ x8 ∈ x3, PEqualNP.EdgeOwnership.gateVal x1 x2 (↑x7) x8 = Bool.true } + (1 : ℕ) :=
  fun n C X S hC hS => PEqualNP.Outside.L_meta_5218.main n C X S hC hS
