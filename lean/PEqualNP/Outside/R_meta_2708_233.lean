import Mathlib
import PEqualNP.Defs

-- On the 21 edges and 37 maximal independent inputs, orient the operands by their
-- singleton values. The early-index bound 19 also appears in gperdigao's PR #8914.
-- KeishinTodate0712 (#5332) and stephenus (#7647) use the boundary inputs.
-- The proof of the structural child adapts the two-point part of HIIKA's L-meta-1483
-- (#3230), based on itay-raveh's L-meta-614 (#728).
-- The singleton cofactor uses Mads Anker Nielsen’s subdivided K4 lower bound
-- (#730) as carried in santahate’s L-meta-720 (#1083).
set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2708_233
    (structureBound : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C → a < 14+C.size → b < 14+C.size →
      let G := SimpleGraph.fromRel (fun u v : Fin 14 => u.val < 7 ∧ 7 ≤ v.val ∧
        (u.val + (v.val - 7)) % 7 ∈ ([0,1,3] : List ℕ))
      let f := fun x : Fin 14 → Bool => ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
      let w := fun (i : ℕ) (x : Fin 14 → Bool) => (C.wires (List.ofFn x)).getD i false
      let z := @PEqualNP.EdgeOwnership.pairInput 14
      let Q := fun (i j : ℕ) => 26 ≤ i ∧ 19 ≤ j ∧
        (∀ u v : Fin 14, w i (z u u) = true → w i (z v v) = true → u = v) ∧
        ((∃ u : Fin 14, w i (z u u) = true) → 31 ≤ j) ∧
        ((∃ u : Fin 14, w j (z u u) = true) → 31 ≤ i) ∧
        (j ≤ 25 → ∃ u : Fin 14, ∀ v : Fin 14, G.Adj u v → w j (z v v) = true) ∧
        (j ≤ 23 → 33 ≤ i ∧ ∀ u v : Fin 14, w i (z u v) = true ↔ G.Adj u v)
      (∀ x, f x → w a x = true ∧ w b x = true) →
      (∀ x, ¬f x → w a x = false ∨ w b x = false) →
      (∃ x, w a x = false) → (∃ x, w b x = false) →
      (∀ i, Monotone (w i)) ∧ (Q a b ∨ Q b a))
    (boundary : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C → a < 14+C.size → b < 14+C.size →
      let G := SimpleGraph.fromRel (fun u v : Fin 14 => u.val < 7 ∧ 7 ≤ v.val ∧
        (u.val + (v.val - 7)) % 7 ∈ ([0,1,3] : List ℕ))
      let f := fun x : Fin 14 → Bool => ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
      let w := fun (i : ℕ) (x : Fin 14 → Bool) => (C.wires (List.ofFn x)).getD i false
      let z := @PEqualNP.EdgeOwnership.pairInput 14
      let Q := fun (i j : ℕ) => 26 ≤ i ∧ 19 ≤ j ∧
        (∀ u v : Fin 14, w i (z u u) = true → w i (z v v) = true → u = v) ∧
        ((∃ u : Fin 14, w i (z u u) = true) → 31 ≤ j) ∧
        ((∃ u : Fin 14, w j (z u u) = true) → 31 ≤ i) ∧
        (j ≤ 25 → ∃ u : Fin 14, ∀ v : Fin 14, G.Adj u v → w j (z v v) = true) ∧
        (j ≤ 23 → 33 ≤ i ∧ ∀ u v : Fin 14, w i (z u v) = true ↔ G.Adj u v)
      Q a b → a ≠ b →
      (∀ u v : Fin 14, G.Adj u v → w a (z u v) = true ∧ w b (z u v) = true) →
      (∀ x, Maximal (fun t => ¬f t) x → w a x = false ∨ w b x = false) →
      (∃ x, Maximal (fun t => ¬f t) x ∧ w a x = false ∧ w b x = true) →
      (∃ x, Maximal (fun t => ¬f t) x ∧ w b x = false ∧ w a x = true) →
      26 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size := by
  intro C a b hc ha hb edges positive w pos neg aOff bOff
  let G := SimpleGraph.fromRel (fun u v : Fin 14 => u.val < 7 ∧ 7 ≤ v.val ∧
    (u.val + (v.val-7)) % 7 ∈ ([0,1,3] : List ℕ))
  let f := fun x : Fin 14 → Bool => ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  let z := @PEqualNP.EdgeOwnership.pairInput 14
  let Q := fun (i j : ℕ) => 26 ≤ i ∧ 19 ≤ j ∧
    (∀ u v : Fin 14, w i (z u u) = true → w i (z v v) = true → u = v) ∧
    ((∃ u : Fin 14, w i (z u u) = true) → 31 ≤ j) ∧
    ((∃ u : Fin 14, w j (z u u) = true) → 31 ≤ i) ∧
    (j ≤ 25 → ∃ u : Fin 14, ∀ v : Fin 14, G.Adj u v → w j (z v v) = true) ∧
    (j ≤ 23 → 33 ≤ i ∧ ∀ u v : Fin 14, w i (z u v) = true ↔ G.Adj u v)
  have adj (u v : Fin 14) : G.Adj u v ↔ (u.val,v.val) ∈ edges ∨ (v.val,u.val) ∈ edges := by
    dsimp only [G]
    rw [SimpleGraph.fromRel_adj]
    revert u v
    decide
  have equival (x) : f x ↔ positive x := by
    constructor
    · rintro ⟨u,v,h,hu,hv⟩
      rcases (adj u v).mp h with h|h
      · exact ⟨u,v,h,hu,hv⟩
      · exact ⟨v,u,h,hv,hu⟩
    · rintro ⟨u,v,h,hu,hv⟩
      exact ⟨u,v,(adj _ _).mpr (Or.inl h),hu,hv⟩
  have hp (x) (hx : f x) := pos x ((equival x).mp hx)
  have hn (x) (hx : ¬f x) := neg x (fun h => hx ((equival x).mpr h))
  obtain ⟨x,hx,ax,bx⟩ := aOff
  obtain ⟨y,hy,bhy,ahy⟩ := bOff
  have AB := structureBound C a b hc ha hb hp hn ⟨x,ax⟩ ⟨y,bhy⟩
  change (∀ i, Monotone (w i)) ∧ (Q a b ∨ Q b a) at AB
  have ne : a ≠ b := by intro h; subst b; exact Bool.noConfusion (ax.symm.trans bx)
  have edge (u v : Fin 14) (he : G.Adj u v) : w a (z u v) = true ∧ w b (z u v) = true := by
    apply hp
    refine ⟨u,v,he,?_,?_⟩
    · change decide (u = u ∨ u = v) = true
      exact decide_eq_true (Or.inl rfl)
    · change decide (v = u ∨ v = v) = true
      exact decide_eq_true (Or.inr rfl)
  have maxOff (i j : ℕ) (t : Fin 14 → Bool) (ht : ¬positive t) (htj : w j t = true)
      (both : ∀ v, ¬f v → w i v = false ∨ w j v = false) :
      ∃ t, Maximal (fun v => ¬f v) t ∧ w i t = false ∧ w j t = true := by
    obtain ⟨s,hts,hs⟩ := exists_maximal_ge_of_wellFoundedGT (fun v => ¬f v) t (fun h => ht ((equival t).mp h))
    have on : w j s = true := Bool.le_iff_imp.mp (AB.1 j hts) htj
    exact ⟨s,hs,(both s hs.1).resolve_right (fun h => Bool.noConfusion (h.symm.trans on)),on⟩
  have mx := maxOff a b x hx bx hn
  have my := maxOff b a y hy ahy (fun v h => (hn v h).symm)
  rcases AB.2 with h|h
  · exact boundary C a b hc ha hb h ne edge (fun v hv => hn v hv.1) mx my
  · exact boundary C b a hc hb ha h ne.symm (fun u v he => (edge u v he).symm)
      (fun v hv => (hn v hv.1).symm) my mx
