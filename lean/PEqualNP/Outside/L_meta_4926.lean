import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4926

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def stepD (d : List ℕ) (g : Gate) : List ℕ := d ++ [g.lineDegree d]

def stepA (d : List ℕ) (g : Gate) : List ℕ :=
  d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + PEqualNP.MetaComplexity.SingleLevel.andLevel g]

def Good (v : Bool) (d a : ℕ) : Prop :=
  (a = 0 → d ≤ 1 ∧ (d = 1 → v = true)) ∧ (a ≤ 1 → 2 ≤ d → v = true)

theorem good_and (v1 v2 : Bool) (d1 d2 a1 a2 : ℕ) (h1 : Good v1 d1 a1) (h2 : Good v2 d2 a2) :
    Good (v1 && v2) (d1 + d2) (max a1 a2 + 1) := by
  obtain ⟨h1a, _⟩ := h1
  obtain ⟨h2a, _⟩ := h2
  refine ⟨fun h => by omega, fun ha hd => ?_⟩
  have e1 : a1 = 0 := by omega
  have e2 : a2 = 0 := by omega
  obtain ⟨b1, c1⟩ := h1a e1
  obtain ⟨b2, c2⟩ := h2a e2
  have f1 : d1 = 1 := by omega
  have f2 : d2 = 1 := by omega
  rw [c1 f1, c2 f2]
  rfl

theorem good_or (v1 v2 : Bool) (d1 d2 a1 a2 : ℕ) (h1 : Good v1 d1 a1) (h2 : Good v2 d2 a2) :
    Good (v1 || v2) (max d1 d2) (max a1 a2) := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨fun h => ?_, fun ha hd => ?_⟩
  · have e1 : a1 = 0 := by omega
    have e2 : a2 = 0 := by omega
    obtain ⟨b1, c1⟩ := h1a e1
    obtain ⟨b2, c2⟩ := h2a e2
    refine ⟨by omega, fun hm => ?_⟩
    rcases Nat.lt_or_ge d1 1 with hlt | hge
    · have f2 : d2 = 1 := by omega
      rw [c2 f2]
      simp
    · have f1 : d1 = 1 := by omega
      rw [c1 f1]
      simp
  · rcases Nat.lt_or_ge d1 2 with hlt | hge
    · have f2 : 2 ≤ d2 := by omega
      rw [h2b (by omega) f2]
      simp
    · rw [h1b (by omega) hge]
      simp

theorem inv (n : ℕ) (p : Fin n) : ∀ gs : List Gate,
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    (∀ j (h : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < n + j) →
    (gs.foldl stepW (List.ofFn fun q : Fin n => decide (q = p))).length = n + gs.length ∧
    (gs.foldl stepD ((List.range n).map fun i => if i ∈ ({(p : ℕ)} : Finset ℕ) then 1 else 0)).length
      = n + gs.length ∧
    (gs.foldl stepA (List.replicate n 0)).length = n + gs.length ∧
    ∀ i, i < n + gs.length →
      Good ((gs.foldl stepW (List.ofFn fun q : Fin n => decide (q = p))).getD i false)
        ((gs.foldl stepD ((List.range n).map fun i => if i ∈ ({(p : ℕ)} : Finset ℕ) then 1 else 0)).getD i 0)
        ((gs.foldl stepA (List.replicate n 0)).getD i 0) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro i hi
    have hi' : i < n := by simpa using hi
    have hv : (List.ofFn fun q : Fin n => decide (q = p)).getD i false = decide ((⟨i, hi'⟩ : Fin n) = p) := by
      simp [List.getD_eq_getElem?_getD, hi']
    have hd : ((List.range n).map fun i => if i ∈ ({(p : ℕ)} : Finset ℕ) then 1 else 0).getD i 0
        = if i = (p : ℕ) then 1 else 0 := by
      simp [List.getD_eq_getElem?_getD, hi']
    have ha : (List.replicate n 0).getD i 0 = 0 := by
      simp [List.getD_eq_getElem?_getD]
    simp only [List.foldl_nil]
    rw [hv, hd, ha]
    refine ⟨fun _ => ⟨by split_ifs <;> omega, fun h1 => ?_⟩, fun _ h2 => ?_⟩
    · have hip : i = (p : ℕ) := by
        by_contra hne
        simp only [hne, ite_false] at h1
        omega
      exact decide_eq_true (Fin.ext hip)
    · split_ifs at h2 <;> omega
  | append_singleton gs g ih =>
    intro hops hback
    have hops' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
      fun g' hg' => hops g' (List.mem_append_left _ hg')
    have hback' : ∀ j (h : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < n + j := by
      intro j h i hi
      have h2 : j < (gs ++ [g]).length := by simp; omega
      have := hback j h2 i (by rw [List.getElem_append_left h]; exact hi)
      exact this
    obtain ⟨hW, hD, hA, hG⟩ := ih hops' hback'
    have hg := hops g (by simp)
    have hgb : ∀ i ∈ g.inputs, i < n + gs.length := by
      intro i hi
      have h2 : gs.length < (gs ++ [g]).length := by simp
      have := hback gs.length h2 i (by simp; exact hi)
      exact this
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set W := gs.foldl stepW (List.ofFn fun q : Fin n => decide (q = p)) with hWdef
    set D := gs.foldl stepD ((List.range n).map fun i => if i ∈ ({(p : ℕ)} : Finset ℕ) then 1 else 0) with hDdef
    set A := gs.foldl stepA (List.replicate n 0) with hAdef
    refine ⟨by simp [stepW, hW]; omega, by simp [stepD, hD]; omega, by simp [stepA, hA]; omega, ?_⟩
    intro i hi
    have hi2 : i < n + gs.length + 1 := by simpa [Nat.add_assoc] using hi
    rcases Nat.lt_or_ge i (n + gs.length) with hlt | hge
    · have e1 : (stepW W g).getD i false = W.getD i false := by
        unfold stepW; rw [List.getD_append _ _ _ _ (by rw [hW]; exact hlt)]
      have e2 : (stepD D g).getD i 0 = D.getD i 0 := by
        unfold stepD; rw [List.getD_append _ _ _ _ (by rw [hD]; exact hlt)]
      have e3 : (stepA A g).getD i 0 = A.getD i 0 := by
        unfold stepA; rw [List.getD_append _ _ _ _ (by rw [hA]; exact hlt)]
      rw [e1, e2, e3]
      exact hG i hlt
    · have hieq : i = n + gs.length := by omega
      obtain ⟨hop, hlen⟩ := hg
      rcases hin : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, t⟩⟩⟩
      · rw [hin] at hlen; simp at hlen
      · rw [hin] at hlen; simp at hlen
      · have hu : u < n + gs.length := hgb u (by rw [hin]; simp)
        have hv : v < n + gs.length := hgb v (by rw [hin]; simp)
        have Gu := hG u hu
        have Gv := hG v hv
        have e1 : (stepW W g).getD i false = g.op.eval [W.getD u false, W.getD v false] := by
          unfold stepW
          rw [hieq, ← hW, List.getD_append_right _ _ _ _ (le_refl _)]
          simp [hin]
        have e2 : (stepD D g).getD i 0 = g.lineDegree D := by
          unfold stepD
          rw [hieq, ← hD, List.getD_append_right _ _ _ _ (le_refl _)]
          simp
        have e3 : (stepA A g).getD i 0 =
            max (A.getD u 0) (max (A.getD v 0) 0) + PEqualNP.MetaComplexity.SingleLevel.andLevel g := by
          unfold stepA
          rw [hieq, ← hA, List.getD_append_right _ _ _ _ (le_refl _)]
          simp [hin]
        rw [e1, e2, e3]
        rcases hop with hand | hor
        · have l1 : g.lineDegree D = D.getD u 0 + D.getD v 0 := by
            simp [Gate.lineDegree, hand, hin]
          have l2 : PEqualNP.MetaComplexity.SingleLevel.andLevel g = 1 := by
            simp [PEqualNP.MetaComplexity.SingleLevel.andLevel, hand, hin]
          have l3 : g.op.eval [W.getD u false, W.getD v false] = (W.getD u false && W.getD v false) := by
            simp [hand, GateOp.eval]
          rw [l1, l2, l3, Nat.max_zero]
          exact good_and _ _ _ _ _ _ Gu Gv
        · have l1 : g.lineDegree D = max (D.getD u 0) (D.getD v 0) := by
            simp [Gate.lineDegree, hor, hin]
          have l2 : PEqualNP.MetaComplexity.SingleLevel.andLevel g = 0 := by
            simp [PEqualNP.MetaComplexity.SingleLevel.andLevel, hor]
          have l3 : g.op.eval [W.getD u false, W.getD v false] = (W.getD u false || W.getD v false) := by
            simp [hor, GateOp.eval]
          rw [l1, l2, l3, Nat.max_zero, Nat.add_zero]
          exact good_or _ _ _ _ _ _ Gu Gv
      · rw [hin] at hlen; simp at hlen

end PEqualNP.Outside.L_meta_4926

theorem PEqualNP.Outside.L_meta_4926 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x2.eval (List.ofFn fun (x5 : Fin x1) => Decidable.decide (x5 = x3)) = Bool.false → (2 : ℕ) ≤ x2.lineDeg x1 {↑x3} → (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x2 x1).getD x2.output (0 : ℕ) := by
  intro n C p hC hev hdeg
  obtain ⟨hao, hrb, hlen⟩ := hC
  have hops : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hao g hg, hlen g hg⟩
  have hback : ∀ j (h : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < n + j := by
    intro j h i hi
    have := hrb j h i (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, h] using hi)
    exact this
  obtain ⟨hW, hD, hA, hG⟩ := PEqualNP.Outside.L_meta_4926.inv n p C.gates hops hback
  by_contra hcon
  have hlt : (PEqualNP.MetaComplexity.SingleLevel.andDepths C n).getD C.output 0 ≤ 1 := by omega
  rcases Nat.lt_or_ge C.output (n + C.gates.length) with ho | ho
  · have := (hG C.output ho).2 hlt hdeg
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval] at hev
    exact absurd (this.symm.trans hev) (by simp)
  · have hz : (C.lineDegrees n {(p : ℕ)}).getD C.output 0 = 0 := by
      apply List.getD_eq_default
      have : (C.lineDegrees n {(p : ℕ)}).length = n + C.gates.length := hD
      omega
    have : C.lineDeg n {(p : ℕ)} = 0 := hz
    omega
