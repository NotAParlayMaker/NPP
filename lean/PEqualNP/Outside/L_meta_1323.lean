import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1323_aux

open PEqualNP.CircuitLowerBounds

def rd (gates : List Gate) (t : Fin gates.length) (z : List Bool) : Bool :=
  ((gates.get t).inputs.map (fun k : ℕ => (Circuit.wires ⟨gates.take t.val, 0⟩ z).getD k false)).headD false

def Rel (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ k, a.getD k false = true → b.getD k false = true

theorem wires_snoc (l : List Gate) (g : Gate) (z : List Bool) :
    Circuit.wires ⟨l ++ [g], 0⟩ z = Circuit.wires ⟨l, 0⟩ z ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨l, 0⟩ z).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem rel_snoc {a b : List Bool} {p q : Bool} (h : Rel a b) (hpq : p = true → q = true) :
    Rel (a ++ [p]) (b ++ [q]) := by
  obtain ⟨hl, hk⟩ := h
  refine ⟨by simp [hl], fun k hk' => ?_⟩
  rcases lt_trichotomy k a.length with h1 | h1 | h1
  · rw [List.getD_append _ _ _ _ h1] at hk'
    rw [List.getD_append _ _ _ _ (hl ▸ h1)]
    exact hk k hk'
  · subst h1
    simp_all
  · have h2 : a.length + 1 ≤ k := h1
    have h3 : (a ++ [p]).getD k false = false := by
      rw [List.getD_eq_default]
      simp
      omega
    rw [h3] at hk'
    exact absurd hk' (by simp)

theorem eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {f f' : ℕ → Bool}
    (h : ∀ k, f k = true → f' k = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with h1 | h1 <;> rw [h1] <;> simp [GateOp.eval]
  · intro hx k hk
    exact h k (hx k hk)
  · intro k hk hfk
    exact ⟨k, hk, h k hfk⟩

theorem wires_mono (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (x y : List Bool) (hxy : Rel x y) (t : ℕ) (ht : t ≤ gates.length)
    (hnot : ∀ u : Fin gates.length, u.val < t → (gates.get u).op = GateOp.not → rd gates u x = rd gates u y) :
    ∀ m, m ≤ t → Rel (Circuit.wires ⟨gates.take m, 0⟩ x) (Circuit.wires ⟨gates.take m, 0⟩ y) := by
  intro m
  induction m with
  | zero =>
    intro _
    simpa [Circuit.wires] using hxy
  | succ m ih =>
    intro hm
    have hm' : m < gates.length := by omega
    have ih' := ih (by omega)
    rw [List.take_add_one, List.getElem?_eq_getElem hm']
    simp only [Option.toList]
    rw [wires_snoc, wires_snoc]
    apply rel_snoc ih'
    have hmem : gates[m] ∈ gates := List.getElem_mem hm'
    rcases (hg _ hmem).1 with h1 | h1 | h1
    · exact eval_mono _ (Or.inl h1) ih'.2
    · exact eval_mono _ (Or.inr h1) ih'.2
    · have := hnot ⟨m, hm'⟩ (by simp; omega) (by simpa using h1)
      unfold rd at this
      simp only [List.get_eq_getElem] at this
      intro hp
      rw [h1] at hp ⊢
      simp only [GateOp.eval] at hp ⊢
      rw [← this]
      exact hp

end PEqualNP.Outside.L_meta_1323_aux

open PEqualNP.Outside.L_meta_1323_aux in
theorem PEqualNP.Outside.L_meta_1323 : ∀ (n s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → ∀ (r : ℕ) (x : ℕ → Fin n → Bool), (∀ i : ℕ, i < r → ∀ p : Fin n, x i p = true → x (i + 1) p = true) → (∀ i : ℕ, i < r → ∃ t : Fin gates.length, (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x i))).getD k false)).headD false ≠ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x (i + 1)))).getD k false)).headD false) → r + 1 ≤ 2 ^ s := by
  classical
  intro n s gates hg ⟨ι, hι⟩ r x hmono hchg
  let F : ℕ → Fin gates.length → Bool := fun i t =>
    if (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not then rd gates t (List.ofFn (x i)) else false
  have step : ∀ i, i < r → toLex (F i) < toLex (F (i + 1)) := by
    intro i hi
    obtain ⟨t0, h0⟩ := hchg i hi
    obtain ⟨t, ht, hmin⟩ := WellFounded.has_min wellFounded_lt
      {t : Fin gates.length | (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        rd gates t (List.ofFn (x i)) ≠ rd gates t (List.ofFn (x (i + 1)))} ⟨t0, h0⟩
    have hrel : Rel (List.ofFn (x i)) (List.ofFn (x (i + 1))) := by
      refine ⟨by simp, fun k hk => ?_⟩
      by_cases hkn : k < n
      · simp [List.getD_eq_getElem?_getD, hkn] at hk ⊢
        exact hmono i hi _ hk
      · simp [List.getD_eq_getElem?_getD, hkn] at hk
    have hw := wires_mono gates hg _ _ hrel t.val (le_of_lt t.2)
      (fun u hu hnu => by
        by_contra hne
        exact hmin u ⟨hnu, hne⟩ hu) t.val le_rfl
    have hread : rd gates t (List.ofFn (x i)) = true → rd gates t (List.ofFn (x (i + 1))) = true := by
      unfold rd
      cases (gates.get t).inputs with
      | nil => simp
      | cons k _ =>
        simp only [List.map_cons, List.headD_cons]
        exact hw.2 k
    have hf : rd gates t (List.ofFn (x i)) = false ∧ rd gates t (List.ofFn (x (i + 1))) = true := by
      have h2 := ht.2
      revert h2 hread
      cases rd gates t (List.ofFn (x i)) <;> cases rd gates t (List.ofFn (x (i + 1))) <;> simp
    refine ⟨t, fun u hu => ?_, ?_⟩
    · show F i u = F (i + 1) u
      simp only [F]
      split_ifs with hnu
      · by_contra hne
        exact hmin u ⟨hnu, hne⟩ hu
      · rfl
    · show F i t < F (i + 1) t
      simp only [F, ht.1, hf.1, hf.2]
      decide
  have chain : ∀ d i, i + d + 1 ≤ r → toLex (F i) < toLex (F (i + d + 1)) := by
    intro d
    induction d with
    | zero => intro i hi; exact step i (by omega)
    | succ d ih =>
      intro i hi
      have := ih i (by omega)
      have h2 := step (i + d + 1) (by omega)
      have h3 : i + (d + 1) + 1 = i + d + 1 + 1 := by omega
      rw [h3]
      exact lt_trans this h2
  let h : Fin (r + 1) → (Fin s → Bool) := fun i j => F i.val (ι j)
  have hinj : Function.Injective h := by
    intro a b hab
    have hF : F a.val = F b.val := by
      funext t
      by_cases hnt : (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not
      · obtain ⟨j, hj⟩ := hι t hnt
        have := congrFun hab j
        simp only [h] at this
        rw [hj] at this
        exact this
      · simp only [F]
        split_ifs
        rfl
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have := chain (b.val - a.val - 1) a.val (by omega)
      have e : a.val + (b.val - a.val - 1) + 1 = b.val := by omega
      rw [e, hF] at this
      exact lt_irrefl _ this
    · have := chain (a.val - b.val - 1) b.val (by omega)
      have e : b.val + (a.val - b.val - 1) + 1 = a.val := by omega
      rw [e, hF] at this
      exact lt_irrefl _ this
  have := Fintype.card_le_of_injective h hinj
  simpa using this
