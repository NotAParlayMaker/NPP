import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8195_aux

open PEqualNP.CircuitLowerBounds

theorem wires_len (G : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨G, o⟩ x).length = x.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton G g ih =>
    simp only [Circuit.wires] at ih ⊢
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append, ih,
      List.length_cons, List.length_nil]
    omega

theorem wires_app (G : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨G ++ [g], o⟩ x = Circuit.wires ⟨G, o⟩ x ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, o⟩ x).getD i false)] := by
  unfold Circuit.wires
  rw [List.foldl_append]
  rfl

theorem key {α β : Type} (R Ra Rb : Set (α × β)) (u1 u2 : α → Bool) (v1 v2 : β → Bool)
    (hR : ∀ p ∈ R, ∀ q ∈ R, (p.1, q.2) ∈ R) (hsub : R ⊆ Ra ∪ Rb)
    (h1 : ∀ p ∈ Ra, u1 p.1 = true ∧ v1 p.2 = false)
    (h2 : ∀ p ∈ Rb, u2 p.1 = true ∧ v2 p.2 = false) :
    (∀ p ∈ R, u1 p.1 = true ∧ v1 p.2 = false) ∨ (∀ p ∈ R, u2 p.1 = true ∧ v2 p.2 = false) ∨
    (∀ p ∈ R, (u1 p.1 && u2 p.1) = true ∧ (v1 p.2 && v2 p.2) = false) ∨
    (∀ p ∈ R, (u1 p.1 || u2 p.1) = true ∧ (v1 p.2 || v2 p.2) = false) := by
  have hp : ∀ p ∈ R, (u1 p.1 = true ∧ v1 p.2 = false) ∨ (u2 p.1 = true ∧ v2 p.2 = false) :=
    fun p hp => (hsub hp).elim (fun h => Or.inl (h1 p h)) (fun h => Or.inr (h2 p h))
  have and_ok : (∀ p ∈ R, u1 p.1 = true) → (∀ p ∈ R, u2 p.1 = true) →
      (∀ p ∈ R, (u1 p.1 && u2 p.1) = true ∧ (v1 p.2 && v2 p.2) = false) := by
    intro a1 a2 p hq
    rcases hp p hq with h | h <;> simp [a1 p hq, a2 p hq, h.2]
  have or_ok : (∀ p ∈ R, v1 p.2 = false) → (∀ p ∈ R, v2 p.2 = false) →
      (∀ p ∈ R, (u1 p.1 || u2 p.1) = true ∧ (v1 p.2 || v2 p.2) = false) := by
    intro b1 b2 p hq
    rcases hp p hq with h | h <;> simp [b1 p hq, b2 p hq, h.1]
  have f2_ok : (¬ ∀ p ∈ R, u1 p.1 = true) → (¬ ∀ p ∈ R, v1 p.2 = false) →
      (∀ p ∈ R, u2 p.1 = true ∧ v2 p.2 = false) := by
    intro a1 b1
    push Not at a1 b1
    obtain ⟨p, hpR, hp1⟩ := a1
    obtain ⟨q, hqR, hq1⟩ := b1
    intro r hr
    constructor
    · rcases hp _ (hR r hr q hqR) with h | h
      · exact absurd h.2 hq1
      · exact h.1
    · rcases hp _ (hR p hpR r hr) with h | h
      · exact absurd h.1 hp1
      · exact h.2
  have f1_ok : (¬ ∀ p ∈ R, u2 p.1 = true) → (¬ ∀ p ∈ R, v2 p.2 = false) →
      (∀ p ∈ R, u1 p.1 = true ∧ v1 p.2 = false) := by
    intro a1 b1
    push Not at a1 b1
    obtain ⟨p, hpR, hp1⟩ := a1
    obtain ⟨q, hqR, hq1⟩ := b1
    intro r hr
    constructor
    · rcases hp _ (hR r hr q hqR) with h | h
      · exact h.1
      · exact absurd h.2 hq1
    · rcases hp _ (hR p hpR r hr) with h | h
      · exact h.2
      · exact absurd h.1 hp1
  have mixed12 : (∀ p ∈ R, v2 p.2 = false) → (¬ ∀ p ∈ R, u2 p.1 = true) →
      (∀ p ∈ R, v1 p.2 = false) := by
    intro b2 a2
    push Not at a2
    obtain ⟨q, hqR, hq1⟩ := a2
    intro r hr
    rcases hp _ (hR q hqR r hr) with h | h
    · exact h.2
    · exact absurd h.1 hq1
  have mixed21 : (∀ p ∈ R, v1 p.2 = false) → (¬ ∀ p ∈ R, u1 p.1 = true) →
      (∀ p ∈ R, v2 p.2 = false) := by
    intro b2 a2
    push Not at a2
    obtain ⟨q, hqR, hq1⟩ := a2
    intro r hr
    rcases hp _ (hR q hqR r hr) with h | h
    · exact absurd h.1 hq1
    · exact h.2
  by_cases a1 : ∀ p ∈ R, u1 p.1 = true
  · by_cases a2 : ∀ p ∈ R, u2 p.1 = true
    · exact Or.inr (Or.inr (Or.inl (and_ok a1 a2)))
    · by_cases b2 : ∀ p ∈ R, v2 p.2 = false
      · exact Or.inr (Or.inr (Or.inr (or_ok (mixed12 b2 a2) b2)))
      · exact Or.inl (f1_ok a2 b2)
  · by_cases b1 : ∀ p ∈ R, v1 p.2 = false
    · have b2 := mixed21 b1 a1
      exact Or.inr (Or.inr (Or.inr (or_ok b1 b2)))
    · exact Or.inr (Or.inl (f2_ok a1 b1))

theorem build {x1 x2 : ℕ} {x3 x4 : Type} (x5 : x3 → Fin x1 → Bool) (x6 : x4 → Fin x1 → Bool)
    (x7 : ℕ → Set (x3 × x4))
    (h0 : ∀ (x8 : Fin x1), ∀ x9 ∈ x7 ↑x8, x5 x9.1 x8 = true ∧ x6 x9.2 x8 = false)
    (hs : ∀ x9 < x2, (∀ x11 ∈ x7 (x1 + x9), ∀ x13 ∈ x7 (x1 + x9), (x11.1, x13.2) ∈ x7 (x1 + x9)) ∧
      ∃ x11 < x1 + x9, ∃ x12 < x1 + x9, x7 (x1 + x9) ⊆ x7 x11 ∪ x7 x12) :
    ∀ m ≤ x2, ∃ G : List Gate, G.length = m ∧
      (∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      ∀ k < x1 + m, ∀ p ∈ x7 k, (Circuit.wires ⟨G, 0⟩ (List.ofFn (x5 p.1))).getD k false = true ∧
        (Circuit.wires ⟨G, 0⟩ (List.ofFn (x6 p.2))).getD k false = false := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], rfl, by simp, ?_⟩
    intro k hk p hp
    have hk2 : k < x1 := by omega
    have := h0 ⟨k, hk2⟩ p hp
    simpa [Circuit.wires, hk2] using this
  | succ m ih =>
    intro hm
    obtain ⟨G, hl, hmono, hsep⟩ := ih (by omega)
    obtain ⟨hR, a, ha, b, hb, hsub⟩ := hs m (by omega)
    have step : ∀ g : Gate, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) → g.inputs.length ≤ 2 →
        (∀ p ∈ x7 (x1 + m),
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, 0⟩ (List.ofFn (x5 p.1))).getD i false) = true ∧
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨G, 0⟩ (List.ofFn (x6 p.2))).getD i false) = false) →
        ∃ G : List Gate, G.length = m + 1 ∧
          (∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
          ∀ k < x1 + (m + 1), ∀ p ∈ x7 k, (Circuit.wires ⟨G, 0⟩ (List.ofFn (x5 p.1))).getD k false = true ∧
            (Circuit.wires ⟨G, 0⟩ (List.ofFn (x6 p.2))).getD k false = false := by
      intro g hg1 hg2 hg
      refine ⟨G ++ [g], by simp [hl], ?_, ?_⟩
      · intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h | h
        · exact hmono g' h
        · subst h
          exact ⟨hg1, hg2⟩
      · intro k hk p hp
        rw [wires_app, wires_app]
        have l1 := wires_len G 0 (List.ofFn (x5 p.1))
        have l2 := wires_len G 0 (List.ofFn (x6 p.2))
        simp only [List.length_ofFn, hl] at l1 l2
        rcases Nat.lt_or_ge k (x1 + m) with hk' | hk'
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact hsep k hk' p hp
        · have hkk : k = x1 + m := by omega
          subst hkk
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simpa [l1, l2] using hg p hp
    rcases key (x7 (x1 + m)) (x7 a) (x7 b)
      (fun s => (Circuit.wires ⟨G, 0⟩ (List.ofFn (x5 s))).getD a false)
      (fun s => (Circuit.wires ⟨G, 0⟩ (List.ofFn (x5 s))).getD b false)
      (fun s => (Circuit.wires ⟨G, 0⟩ (List.ofFn (x6 s))).getD a false)
      (fun s => (Circuit.wires ⟨G, 0⟩ (List.ofFn (x6 s))).getD b false)
      hR hsub (fun p hp => hsep a ha p hp) (fun p hp => hsep b hb p hp) with h | h | h | h
    · exact step ⟨GateOp.and, [a]⟩ (by simp) (by simp) (fun p hp => by simpa [GateOp.eval] using h p hp)
    · exact step ⟨GateOp.and, [b]⟩ (by simp) (by simp) (fun p hp => by simpa [GateOp.eval] using h p hp)
    · exact step ⟨GateOp.and, [a, b]⟩ (by simp) (by simp) (fun p hp => by simpa [GateOp.eval] using h p hp)
    · exact step ⟨GateOp.or, [a, b]⟩ (by simp) (by simp) (fun p hp => by simpa [GateOp.eval] using h p hp)

end PEqualNP.Outside.L_meta_8195_aux

open PEqualNP.Outside.L_meta_8195_aux in
theorem PEqualNP.Outside.L_meta_8195 : ∀ (x1 x2 : ℕ) (x3 x4 : Type) (x5 : x3 → Fin x1 → Bool) (x6 : x4 → Fin x1 → Bool) (x7 : ℕ → Set (x3 × x4)), (∀ (x8 : Fin x1), ∀ x9 ∈ x7 ↑x8, x5 x9.1 x8 = Bool.true ∧ x6 x9.2 x8 = Bool.false) → (∀ x9 < x2, (∀ x11 ∈ x7 (x1 + x9), ∀ x13 ∈ x7 (x1 + x9), (x11.1, x13.2) ∈ x7 (x1 + x9)) ∧ ∃ x11 < x1 + x9, ∃ x12 < x1 + x9, x7 (x1 + x9) ⊆ x7 x11 ∪ x7 x12) → ∀ x10 < x1 + x2, ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ x12.size ≤ x2 ∧ ∀ x13 ∈ x7 x10, x12.eval (List.ofFn (x5 x13.1)) = Bool.true ∧ x12.eval (List.ofFn (x6 x13.2)) = Bool.false := by
  intro x1 x2 x3 x4 x5 x6 x7 h0 hs x10 hx10
  obtain ⟨G, hl, hmono, hsep⟩ := build x5 x6 x7 h0 hs x2 le_rfl
  refine ⟨⟨G, x10⟩, hmono, by simp [PEqualNP.CircuitLowerBounds.Circuit.size, hl], ?_⟩
  intro p hp
  exact hsep x10 hx10 p hp
