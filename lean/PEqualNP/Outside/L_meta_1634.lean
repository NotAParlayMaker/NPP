import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1634

open PEqualNP.CircuitLowerBounds

lemma read_mono {xs ys : List Bool}
    (h : List.Forall₂ (fun a b => a = true → b = true) xs ys) (i : ℕ) :
    xs.getD i false = true → ys.getD i false = true := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero] using hab
    | succ i => simpa only [List.getD_cons_succ] using ih i

def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

lemma step_mono {xs ys : List Bool} {g : Gate}
    (h : List.Forall₂ (fun a b => a = true → b = true) xs ys)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    List.Forall₂ (fun a b => a = true → b = true) (step xs g) (step ys g) := by
  apply List.rel_append h
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro hx i hi
    exact read_mono h i (hx i hi)
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, read_mono h i hx⟩

lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (h : List.Forall₂ (fun a b => a = true → b = true) xs ys) :
    List.Forall₂ (fun a b => a = true → b = true) (gs.foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hgs k (List.mem_cons_of_mem g hk))
      (step_mono h (hgs g (List.mem_cons_self ..)))

lemma eval_mono {N : ℕ} (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin N → Bool) (hxy : ∀ i, x i = true → y i = true) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = true → Circuit.eval ⟨gs, w⟩ (List.ofFn y) = true := by
  apply read_mono (fold_mono gs hgs _) w
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp, ?_⟩
  intro i hx hy
  simpa only [List.get_eq_getElem, List.getElem_ofFn] using hxy ⟨i, by simpa using hx⟩

lemma points_to {N : ℕ} (A B : Finset (Fin N)) (test : Fin N → Fin N → Bool)
    (f : (Fin N → Bool) → Bool)
    (hmono : ∀ x y : Fin N → Bool, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hinter : (A ∩ B).card = 1) (hoff : f (fun v => decide (v ∉ B)) = false)
    (hcount : 2 ≤ (A.filter (fun p => f (test p) = true)).card) :
    ∃ p ∈ A \ B, ∃ v ∈ B, test p v = true := by
  have hlt : (A ∩ B).card < (A.filter (fun p => f (test p) = true)).card := by omega
  obtain ⟨p, hp, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hpA, htrue⟩ := Finset.mem_filter.mp hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hpA, fun hpB => hout (Finset.mem_inter.mpr ⟨hpA, hpB⟩)⟩, ?_⟩
  by_contra hmiss
  have hle (v : Fin N) (hv : test p v = true) : decide (v ∉ B) = true :=
    decide_eq_true (fun hB => hmiss ⟨v, hB, hv⟩)
  exact Bool.false_ne_true (hoff.symm.trans (hmono _ _ hle htrue))

end PEqualNP.Outside.L_meta_1634

theorem PEqualNP.Outside.L_meta_1634 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ (w : ℕ) (t u : Fin N), t ≠ u → ev w (fun v : Fin N => decide (v ∉ L t)) = false → ev w (fun v : Fin N => decide (v ∉ L u)) = false →
      2 ≤ ((L t).filter (fun p => ev w (T t p) = true)).card → 2 ≤ ((L u).filter (fun p => ev w (T u p) = true)).card →
      (∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) := by
  intro q N L i0 p0 p1 _ _ _ hinter _ _ _ _ T _ gs hgs _ _ ev hev w t u htu ht hu hct hcu
  have hmono (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
      ev w x = true → ev w y = true := by
    simp only [hev]
    exact PEqualNP.Outside.L_meta_1634.eval_mono gs (fun g hg => (hgs g hg).1) w x y hxy
  exact ⟨PEqualNP.Outside.L_meta_1634.points_to (L t) (L u) (T t) (ev w) hmono
      (hinter t u htu) hu hct,
    PEqualNP.Outside.L_meta_1634.points_to (L u) (L t) (T u) (ev w) hmono
      (hinter u t htu.symm) ht hcu⟩
