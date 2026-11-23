import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_093

open PEqualNP.ProofComplexity

-- A clause is available if some derivation produces it within the width bound.
def Available {V : Type} [DecidableEq V] (F : Set (Clause V)) (w : ℕ) (C : Clause V) : Prop :=
  ∃ π, IsDerivation F π ∧ C ∈ π ∧ ∀ D ∈ π, D.card ≤ w

lemma appendDer {V : Type} [DecidableEq V] {F : Set (Clause V)} {π σ : List (Clause V)}
    (hp : IsDerivation F π) (hs : IsDerivation F σ) : IsDerivation F (π ++ σ) := by
  induction hp with
  | nil => exact hs
  | ax _ ha ih => exact IsDerivation.ax ih ha
  | res _ hc hd hr ih =>
    exact IsDerivation.res ih (List.mem_append.mpr (.inl hc)) (List.mem_append.mpr (.inl hd)) hr

lemma fromAxiom {V : Type} [DecidableEq V] {F : Set (Clause V)} {w : ℕ} {C : Clause V}
    (h : C ∈ F) (hw : C.card ≤ w) : Available F w C := by
  refine ⟨[C], IsDerivation.ax IsDerivation.nil h, by simp, ?_⟩
  simpa using hw

lemma resolve {V : Type} [DecidableEq V] {F : Set (Clause V)} {w : ℕ} {C D R : Clause V}
    (v : V) (hC : Available F w C) (hD : Available F w D)
    (h : (v, true) ∈ C ∧ (v, false) ∈ D ∧ R = C.erase (v, true) ∪ D.erase (v, false) ∧
      R.card ≤ w) : Available F w R := by
  obtain ⟨π, hπ, hc, wπ⟩ := hC
  obtain ⟨σ, hσ, hd, wσ⟩ := hD
  obtain ⟨hp, hn, he, hw⟩ := h
  refine ⟨R :: (π ++ σ), IsDerivation.res (appendDer hπ hσ) (List.mem_append.mpr (.inl hc))
    (List.mem_append.mpr (.inr hd)) ⟨v, hp, hn, he⟩, by simp, ?_⟩
  intro E hE
  rcases List.mem_cons.mp hE with rfl | ha
  · exact hw
  · rcases List.mem_append.mp ha with ha | ha
    · exact wπ E ha
    · exact wσ E ha

lemma toRefutation {V : Type} [DecidableEq V] {F : Set (Clause V)} {w : ℕ}
    (h : Available F w ∅) : ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ w := by
  obtain ⟨π, hd, he, hw⟩ := h
  exact ⟨π, ⟨hd, he⟩, hw⟩

lemma resolventSat {V : Type} [DecidableEq V] (a : V → Bool) {C D R : Clause V}
    (h : IsResolvent C D R) (hc : ClauseSat a C) (hd : ClauseSat a D) : ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := h
  obtain ⟨l, hl, hal⟩ := hc
  obtain ⟨m, hm, ham⟩ := hd
  by_cases hp : l = (v, true)
  · subst l
    refine ⟨m, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hm⟩), ham⟩
    rintro rfl
    simp_all
  · exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hp, hl⟩), hal⟩

lemma narrowSound {V : Type} [DecidableEq V] {F : Set (Clause V)} {w : ℕ} (a : V → Bool)
    (ha : ∀ C ∈ F, C.card ≤ w → ClauseSat a C) {π : List (Clause V)} (hd : IsDerivation F π) :
    (∀ C ∈ π, C.card ≤ w) → ∀ C ∈ π, ClauseSat a C := by
  induction hd with
  | nil => simp
  | ax _ hm ih =>
    intro hw C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact ha _ hm (hw _ (by simp))
    · exact ih (fun E h => hw E (List.mem_cons_of_mem _ h)) C hC
  | res _ hp hn hr ih =>
    intro hw C hC
    have tailSat := ih (fun E h => hw E (List.mem_cons_of_mem _ h))
    rcases List.mem_cons.mp hC with rfl | hC
    · exact resolventSat a hr (tailSat _ hp) (tailSat _ hn)
    · exact tailSat C hC

lemma narrowLower {V : Type} [DecidableEq V] {F : Set (Clause V)} {w : ℕ} (a : V → Bool)
    (ha : ∀ C ∈ F, C.card ≤ w → ClauseSat a C) :
    ¬ ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ w := by
  rintro ⟨π, ⟨hd, he⟩, hw⟩
  obtain ⟨l, hl, _⟩ := narrowSound a ha hd hw ∅ he
  exact Finset.notMem_empty l hl

lemma labelCard {n k : ℕ} (g : Fin k → Fin n) :
    (Finset.univ.image (fun t : Fin k => ((Sum.inl (g t, t) : (Fin n × Fin k) ⊕ Fin n),
      true))).card = k := by
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact congrArg Prod.snd (Sum.inl.inj (Prod.mk.inj h).1)

abbrev V5 := (Fin 5 × Fin 3) ⊕ Fin 5

def formula5 : Set (Clause V5) :=
  {C6 | ∃ v7 : Fin 5, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 5 × Fin 3) ⊕ Fin 5), true))} ∪ {C9 | ∃ (u10 v11 : Fin 5) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (v11 = u10 + 1 ∨ u10 = v11 + 1) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 5 × Fin 3) ⊕ Fin 5), true))} ∪ {C14 | ∃ (e15 : Fin 5) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 5 × Fin 3) ⊕ Fin 5), false), ((Sum.inl (e15, t16) : (Fin 5 × Fin 3) ⊕ Fin 5), false), ((Sum.inl (e15 + 1, t16) : (Fin 5 × Fin 3) ⊕ Fin 5), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 5), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 5 => e19 ∉ S18 ∧ e19 + 1 ∉ S18)).image (fun e20 : Fin 5 => ((Sum.inr e20 : (Fin 5 × Fin 3) ⊕ Fin 5), true))}

abbrev x5 (v : Fin 5) (t : Fin 3) : V5 := Sum.inl (v, t)

abbrev e5 (e : Fin 5) : V5 := Sum.inr e

abbrev reachable5 := Available formula5 3

-- Setting the edge variables to true and the label variables to false
-- satisfies all axioms strictly narrower than the claimed minimum.
lemma lower5 : ¬ ∃ π, IsRefutation formula5 π ∧ ∀ D ∈ π, D.card ≤ 2 := by
  apply narrowLower (fun z : V5 => Sum.elim (fun _ => false) (fun _ => true) z)
  intro C hC hw
  rcases hC with (((⟨v, rfl⟩ | ⟨u, v, f, _, _, rfl⟩) | ⟨e, t, rfl⟩) | ⟨S, hs, rfl⟩)
  · have hc := labelCard (n := 5) (k := 3) (fun _ => v)
    omega
  · have hc := labelCard (n := 5) (k := 3) (fun t => if f t = true then v else u)
    omega
  · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), rfl⟩
  · have uncovered : ∀ T : Finset (Fin 5), T.card = 2 → ∃ e : Fin 5, e ∉ T ∧ e + 1 ∉ T := by
      decide
    obtain ⟨e, he⟩ := uncovered S hs
    exact ⟨_, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩, rfl⟩

-- Each edge below is the unique edge missed by an explicit set of vertices.

lemma unit5_0 : reachable5 {(e5 0, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{2, 4}, by decide, by decide⟩
  · decide

lemma edge5_0_0 : reachable5 {(x5 0 0, false), (x5 1 0, false)} := by
  have h : reachable5 {(e5 0, false), (x5 0 0, false), (x5 1 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨0, 0, by decide⟩)) (by decide)
  exact resolve (e5 0) unit5_0 h (by decide)

lemma edge5_0_1 : reachable5 {(x5 0 1, false), (x5 1 1, false)} := by
  have h : reachable5 {(e5 0, false), (x5 0 1, false), (x5 1 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨0, 1, by decide⟩)) (by decide)
  exact resolve (e5 0) unit5_0 h (by decide)

lemma edge5_0_2 : reachable5 {(x5 0 2, false), (x5 1 2, false)} := by
  have h : reachable5 {(e5 0, false), (x5 0 2, false), (x5 1 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨0, 2, by decide⟩)) (by decide)
  exact resolve (e5 0) unit5_0 h (by decide)

lemma unit5_1 : reachable5 {(e5 1, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{0, 3}, by decide, by decide⟩
  · decide

lemma edge5_1_0 : reachable5 {(x5 1 0, false), (x5 2 0, false)} := by
  have h : reachable5 {(e5 1, false), (x5 1 0, false), (x5 2 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨1, 0, by decide⟩)) (by decide)
  exact resolve (e5 1) unit5_1 h (by decide)

lemma edge5_1_1 : reachable5 {(x5 1 1, false), (x5 2 1, false)} := by
  have h : reachable5 {(e5 1, false), (x5 1 1, false), (x5 2 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨1, 1, by decide⟩)) (by decide)
  exact resolve (e5 1) unit5_1 h (by decide)

lemma edge5_1_2 : reachable5 {(x5 1 2, false), (x5 2 2, false)} := by
  have h : reachable5 {(e5 1, false), (x5 1 2, false), (x5 2 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨1, 2, by decide⟩)) (by decide)
  exact resolve (e5 1) unit5_1 h (by decide)

lemma unit5_3 : reachable5 {(e5 3, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{0, 2}, by decide, by decide⟩
  · decide

lemma edge5_3_0 : reachable5 {(x5 3 0, false), (x5 4 0, false)} := by
  have h : reachable5 {(e5 3, false), (x5 3 0, false), (x5 4 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨3, 0, by decide⟩)) (by decide)
  exact resolve (e5 3) unit5_3 h (by decide)

lemma edge5_3_1 : reachable5 {(x5 3 1, false), (x5 4 1, false)} := by
  have h : reachable5 {(e5 3, false), (x5 3 1, false), (x5 4 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨3, 1, by decide⟩)) (by decide)
  exact resolve (e5 3) unit5_3 h (by decide)

lemma edge5_3_2 : reachable5 {(x5 3 2, false), (x5 4 2, false)} := by
  have h : reachable5 {(e5 3, false), (x5 3 2, false), (x5 4 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨3, 2, by decide⟩)) (by decide)
  exact resolve (e5 3) unit5_3 h (by decide)

lemma unit5_4 : reachable5 {(e5 4, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{1, 3}, by decide, by decide⟩
  · decide

lemma edge5_4_0 : reachable5 {(x5 4 0, false), (x5 0 0, false)} := by
  have h : reachable5 {(e5 4, false), (x5 4 0, false), (x5 0 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨4, 0, by decide⟩)) (by decide)
  exact resolve (e5 4) unit5_4 h (by decide)

lemma edge5_4_1 : reachable5 {(x5 4 1, false), (x5 0 1, false)} := by
  have h : reachable5 {(e5 4, false), (x5 4 1, false), (x5 0 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨4, 1, by decide⟩)) (by decide)
  exact resolve (e5 4) unit5_4 h (by decide)

lemma edge5_4_2 : reachable5 {(x5 4 2, false), (x5 0 2, false)} := by
  have h : reachable5 {(e5 4, false), (x5 4 2, false), (x5 0 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨4, 2, by decide⟩)) (by decide)
  exact resolve (e5 4) unit5_4 h (by decide)

-- Consecutive vertices of this path give pairs of nonadjacent vertices.
-- The path visits 0, 2, 4, 1, 3 in order.
-- Earlier pairs have distinct labels. Each used label conflicts with an
-- endpoint of the next pair. Each unused label gives a new branch.

lemma branch5_0_1_2 : reachable5 {(x5 0 0, false), (x5 2 1, false), (x5 4 2, false)} := by
  have h0 : reachable5 {(x5 1 0, true), (x5 1 1, true), (x5 3 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 3, ![false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 0 0, false), (x5 1 1, true), (x5 3 2, true)} :=
    resolve (x5 1 0) h0 edge5_0_0 (by decide)
  have h2 : reachable5 {(x5 0 0, false), (x5 2 1, false), (x5 3 2, true)} :=
    resolve (x5 1 1) h1 edge5_1_1 (by decide)
  exact resolve (x5 3 2) h2 edge5_3_2 (by decide)

lemma branch5_0_1 : reachable5 {(x5 0 0, false), (x5 2 1, false)} := by
  have h0 : reachable5 {(x5 4 0, true), (x5 1 1, true), (x5 4 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 1, ![false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 0 0, false), (x5 1 1, true), (x5 4 2, true)} :=
    resolve (x5 4 0) h0 edge5_4_0 (by decide)
  have h2 : reachable5 {(x5 0 0, false), (x5 2 1, false), (x5 4 2, true)} :=
    resolve (x5 1 1) h1 edge5_1_1 (by decide)
  exact resolve (x5 4 2) h2 branch5_0_1_2 (by decide)

lemma branch5_0_2_1 : reachable5 {(x5 0 0, false), (x5 4 1, false), (x5 2 2, false)} := by
  have h0 : reachable5 {(x5 1 0, true), (x5 3 1, true), (x5 1 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 3, ![false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 0 0, false), (x5 3 1, true), (x5 1 2, true)} :=
    resolve (x5 1 0) h0 edge5_0_0 (by decide)
  have h2 : reachable5 {(x5 0 0, false), (x5 4 1, false), (x5 1 2, true)} :=
    resolve (x5 3 1) h1 edge5_3_1 (by decide)
  exact resolve (x5 1 2) h2 edge5_1_2 (by decide)

lemma branch5_0_2 : reachable5 {(x5 0 0, false), (x5 2 2, false)} := by
  have h0 : reachable5 {(x5 4 0, true), (x5 4 1, true), (x5 1 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 1, ![false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 0 0, false), (x5 4 1, true), (x5 1 2, true)} :=
    resolve (x5 4 0) h0 edge5_4_0 (by decide)
  have h2 : reachable5 {(x5 0 0, false), (x5 4 1, true), (x5 2 2, false)} :=
    resolve (x5 1 2) h1 edge5_1_2 (by decide)
  exact resolve (x5 4 1) h2 branch5_0_2_1 (by decide)

lemma branch5_0 : reachable5 {(x5 0 0, false)} := by
  have h0 : reachable5 {(x5 4 0, true), (x5 2 1, true), (x5 2 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 0 0, false), (x5 2 1, true), (x5 2 2, true)} :=
    resolve (x5 4 0) h0 edge5_4_0 (by decide)
  have h2 : reachable5 {(x5 0 0, false), (x5 2 2, true)} :=
    resolve (x5 2 1) h1 branch5_0_1 (by decide)
  exact resolve (x5 2 2) h2 branch5_0_2 (by decide)

lemma branch5_1_0_2 : reachable5 {(x5 2 0, false), (x5 0 1, false), (x5 4 2, false)} := by
  have h0 : reachable5 {(x5 1 0, true), (x5 1 1, true), (x5 3 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 3, ![false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 2 0, false), (x5 1 1, true), (x5 3 2, true)} :=
    resolve (x5 1 0) h0 edge5_1_0 (by decide)
  have h2 : reachable5 {(x5 2 0, false), (x5 0 1, false), (x5 3 2, true)} :=
    resolve (x5 1 1) h1 edge5_0_1 (by decide)
  exact resolve (x5 3 2) h2 edge5_3_2 (by decide)

lemma branch5_1_0 : reachable5 {(x5 2 0, false), (x5 0 1, false)} := by
  have h0 : reachable5 {(x5 1 0, true), (x5 4 1, true), (x5 4 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 1, ![true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 2 0, false), (x5 4 1, true), (x5 4 2, true)} :=
    resolve (x5 1 0) h0 edge5_1_0 (by decide)
  have h2 : reachable5 {(x5 2 0, false), (x5 0 1, false), (x5 4 2, true)} :=
    resolve (x5 4 1) h1 edge5_4_1 (by decide)
  exact resolve (x5 4 2) h2 branch5_1_0_2 (by decide)

lemma branch5_1_2_0 : reachable5 {(x5 4 0, false), (x5 0 1, false), (x5 2 2, false)} := by
  have h0 : reachable5 {(x5 3 0, true), (x5 1 1, true), (x5 1 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 4 0, false), (x5 1 1, true), (x5 1 2, true)} :=
    resolve (x5 3 0) h0 edge5_3_0 (by decide)
  have h2 : reachable5 {(x5 4 0, false), (x5 0 1, false), (x5 1 2, true)} :=
    resolve (x5 1 1) h1 edge5_0_1 (by decide)
  exact resolve (x5 1 2) h2 edge5_1_2 (by decide)

lemma branch5_1_2 : reachable5 {(x5 0 1, false), (x5 2 2, false)} := by
  have h0 : reachable5 {(x5 4 0, true), (x5 4 1, true), (x5 1 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 1, ![false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 4 0, true), (x5 0 1, false), (x5 1 2, true)} :=
    resolve (x5 4 1) h0 edge5_4_1 (by decide)
  have h2 : reachable5 {(x5 4 0, true), (x5 0 1, false), (x5 2 2, false)} :=
    resolve (x5 1 2) h1 edge5_1_2 (by decide)
  exact resolve (x5 4 0) h2 branch5_1_2_0 (by decide)

lemma branch5_1 : reachable5 {(x5 0 1, false)} := by
  have h0 : reachable5 {(x5 2 0, true), (x5 4 1, true), (x5 2 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 4, ![false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 2 0, true), (x5 0 1, false), (x5 2 2, true)} :=
    resolve (x5 4 1) h0 edge5_4_1 (by decide)
  have h2 : reachable5 {(x5 0 1, false), (x5 2 2, true)} :=
    resolve (x5 2 0) h1 branch5_1_0 (by decide)
  exact resolve (x5 2 2) h2 branch5_1_2 (by decide)

lemma branch5_2_0_1 : reachable5 {(x5 2 0, false), (x5 4 1, false), (x5 0 2, false)} := by
  have h0 : reachable5 {(x5 1 0, true), (x5 3 1, true), (x5 1 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 3, ![false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 2 0, false), (x5 3 1, true), (x5 1 2, true)} :=
    resolve (x5 1 0) h0 edge5_1_0 (by decide)
  have h2 : reachable5 {(x5 2 0, false), (x5 4 1, false), (x5 1 2, true)} :=
    resolve (x5 3 1) h1 edge5_3_1 (by decide)
  exact resolve (x5 1 2) h2 edge5_0_2 (by decide)

lemma branch5_2_0 : reachable5 {(x5 2 0, false), (x5 0 2, false)} := by
  have h0 : reachable5 {(x5 1 0, true), (x5 4 1, true), (x5 4 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 1, ![true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 2 0, false), (x5 4 1, true), (x5 4 2, true)} :=
    resolve (x5 1 0) h0 edge5_1_0 (by decide)
  have h2 : reachable5 {(x5 2 0, false), (x5 4 1, true), (x5 0 2, false)} :=
    resolve (x5 4 2) h1 edge5_4_2 (by decide)
  exact resolve (x5 4 1) h2 branch5_2_0_1 (by decide)

lemma branch5_2_1_0 : reachable5 {(x5 4 0, false), (x5 2 1, false), (x5 0 2, false)} := by
  have h0 : reachable5 {(x5 3 0, true), (x5 1 1, true), (x5 1 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 4 0, false), (x5 1 1, true), (x5 1 2, true)} :=
    resolve (x5 3 0) h0 edge5_3_0 (by decide)
  have h2 : reachable5 {(x5 4 0, false), (x5 2 1, false), (x5 1 2, true)} :=
    resolve (x5 1 1) h1 edge5_1_1 (by decide)
  exact resolve (x5 1 2) h2 edge5_0_2 (by decide)

lemma branch5_2_1 : reachable5 {(x5 2 1, false), (x5 0 2, false)} := by
  have h0 : reachable5 {(x5 4 0, true), (x5 1 1, true), (x5 4 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 1, ![false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 4 0, true), (x5 2 1, false), (x5 4 2, true)} :=
    resolve (x5 1 1) h0 edge5_1_1 (by decide)
  have h2 : reachable5 {(x5 4 0, true), (x5 2 1, false), (x5 0 2, false)} :=
    resolve (x5 4 2) h1 edge5_4_2 (by decide)
  exact resolve (x5 4 0) h2 branch5_2_1_0 (by decide)

lemma branch5_2 : reachable5 {(x5 0 2, false)} := by
  have h0 : reachable5 {(x5 2 0, true), (x5 2 1, true), (x5 4 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 4, ![false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 2 0, true), (x5 2 1, true), (x5 0 2, false)} :=
    resolve (x5 4 2) h0 edge5_4_2 (by decide)
  have h2 : reachable5 {(x5 2 1, true), (x5 0 2, false)} :=
    resolve (x5 2 0) h1 branch5_2_0 (by decide)
  exact resolve (x5 2 1) h2 branch5_2_1 (by decide)

lemma branch5_root : reachable5 ∅ := by
  have h0 : reachable5 {(x5 0 0, true), (x5 0 1, true), (x5 0 2, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨0, 2, ![false, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable5 {(x5 0 1, true), (x5 0 2, true)} :=
    resolve (x5 0 0) h0 branch5_0 (by decide)
  have h2 : reachable5 {(x5 0 2, true)} :=
    resolve (x5 0 1) h1 branch5_1 (by decide)
  exact resolve (x5 0 2) h2 branch5_2 (by decide)

abbrev V6 := (Fin 6 × Fin 4) ⊕ Fin 6

def formula6 : Set (Clause V6) :=
  {C26 | ∃ v27 : Fin 6, C26 = Finset.univ.image (fun t28 : Fin 4 => ((Sum.inl (v27, t28) : (Fin 6 × Fin 4) ⊕ Fin 6), true))} ∪ {C29 | ∃ (u30 v31 : Fin 6) (f32 : Fin 4 → Bool), u30 ≠ v31 ∧ ¬ (u30 ≠ v31 ∧ u30.val / 3 = v31.val / 3) ∧ C29 = Finset.univ.image (fun t33 : Fin 4 => ((Sum.inl (if f32 t33 = true then v31 else u30, t33) : (Fin 6 × Fin 4) ⊕ Fin 6), true))} ∪ {C34 | ∃ (e35 : Fin 6) (t36 : Fin 4), C34 = {((Sum.inr e35 : (Fin 6 × Fin 4) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e35).1, t36) : (Fin 6 × Fin 4) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e35).2, t36) : (Fin 6 × Fin 4) ⊕ Fin 6), false)}} ∪ {C37 | ∃ S38 : Finset (Fin 6), S38.card = 3 ∧ C37 = (Finset.univ.filter (fun e39 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e39).1 ∉ S38 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e39).2 ∉ S38)).image (fun e40 : Fin 6 => ((Sum.inr e40 : (Fin 6 × Fin 4) ⊕ Fin 6), true))}

abbrev x6 (v : Fin 6) (t : Fin 4) : V6 := Sum.inl (v, t)

abbrev e6 (e : Fin 6) : V6 := Sum.inr e

abbrev reachable6 := Available formula6 4

-- Setting the edge variables to true and the label variables to false
-- satisfies all axioms strictly narrower than the claimed minimum.
lemma lower6 : ¬ ∃ π, IsRefutation formula6 π ∧ ∀ D ∈ π, D.card ≤ 3 := by
  apply narrowLower (fun z : V6 => Sum.elim (fun _ => false) (fun _ => true) z)
  intro C hC hw
  rcases hC with (((⟨v, rfl⟩ | ⟨u, v, f, _, _, rfl⟩) | ⟨e, t, rfl⟩) | ⟨S, hs, rfl⟩)
  · have hc := labelCard (n := 6) (k := 4) (fun _ => v)
    omega
  · have hc := labelCard (n := 6) (k := 4) (fun t => if f t = true then v else u)
    omega
  · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), rfl⟩
  · have uncovered : ∀ T : Finset (Fin 6), T.card = 3 → ∃ e : Fin 6, ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e).1 ∉ T ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e).2 ∉ T := by
      decide
    obtain ⟨e, he⟩ := uncovered S hs
    exact ⟨_, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩, rfl⟩

-- Each edge below is the unique edge missed by an explicit set of vertices.

lemma unit6_0 : reachable6 {(e6 0, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{2, 3, 4}, by decide, by decide⟩
  · decide

lemma edge6_0_0 : reachable6 {(x6 0 0, false), (x6 1 0, false)} := by
  have h : reachable6 {(e6 0, false), (x6 0 0, false), (x6 1 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨0, 0, by decide⟩)) (by decide)
  exact resolve (e6 0) unit6_0 h (by decide)

lemma edge6_0_1 : reachable6 {(x6 0 1, false), (x6 1 1, false)} := by
  have h : reachable6 {(e6 0, false), (x6 0 1, false), (x6 1 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨0, 1, by decide⟩)) (by decide)
  exact resolve (e6 0) unit6_0 h (by decide)

lemma edge6_0_2 : reachable6 {(x6 0 2, false), (x6 1 2, false)} := by
  have h : reachable6 {(e6 0, false), (x6 0 2, false), (x6 1 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨0, 2, by decide⟩)) (by decide)
  exact resolve (e6 0) unit6_0 h (by decide)

lemma edge6_0_3 : reachable6 {(x6 0 3, false), (x6 1 3, false)} := by
  have h : reachable6 {(e6 0, false), (x6 0 3, false), (x6 1 3, false)} := fromAxiom
    (Or.inl (Or.inr ⟨0, 3, by decide⟩)) (by decide)
  exact resolve (e6 0) unit6_0 h (by decide)

lemma unit6_1 : reachable6 {(e6 1, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{0, 3, 4}, by decide, by decide⟩
  · decide

lemma edge6_1_0 : reachable6 {(x6 1 0, false), (x6 2 0, false)} := by
  have h : reachable6 {(e6 1, false), (x6 1 0, false), (x6 2 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨1, 0, by decide⟩)) (by decide)
  exact resolve (e6 1) unit6_1 h (by decide)

lemma edge6_1_1 : reachable6 {(x6 1 1, false), (x6 2 1, false)} := by
  have h : reachable6 {(e6 1, false), (x6 1 1, false), (x6 2 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨1, 1, by decide⟩)) (by decide)
  exact resolve (e6 1) unit6_1 h (by decide)

lemma edge6_1_2 : reachable6 {(x6 1 2, false), (x6 2 2, false)} := by
  have h : reachable6 {(e6 1, false), (x6 1 2, false), (x6 2 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨1, 2, by decide⟩)) (by decide)
  exact resolve (e6 1) unit6_1 h (by decide)

lemma edge6_1_3 : reachable6 {(x6 1 3, false), (x6 2 3, false)} := by
  have h : reachable6 {(e6 1, false), (x6 1 3, false), (x6 2 3, false)} := fromAxiom
    (Or.inl (Or.inr ⟨1, 3, by decide⟩)) (by decide)
  exact resolve (e6 1) unit6_1 h (by decide)

lemma unit6_2 : reachable6 {(e6 2, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{1, 3, 4}, by decide, by decide⟩
  · decide

lemma edge6_2_0 : reachable6 {(x6 0 0, false), (x6 2 0, false)} := by
  have h : reachable6 {(e6 2, false), (x6 0 0, false), (x6 2 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨2, 0, by decide⟩)) (by decide)
  exact resolve (e6 2) unit6_2 h (by decide)

lemma edge6_2_1 : reachable6 {(x6 0 1, false), (x6 2 1, false)} := by
  have h : reachable6 {(e6 2, false), (x6 0 1, false), (x6 2 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨2, 1, by decide⟩)) (by decide)
  exact resolve (e6 2) unit6_2 h (by decide)

lemma edge6_2_2 : reachable6 {(x6 0 2, false), (x6 2 2, false)} := by
  have h : reachable6 {(e6 2, false), (x6 0 2, false), (x6 2 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨2, 2, by decide⟩)) (by decide)
  exact resolve (e6 2) unit6_2 h (by decide)

lemma edge6_2_3 : reachable6 {(x6 0 3, false), (x6 2 3, false)} := by
  have h : reachable6 {(e6 2, false), (x6 0 3, false), (x6 2 3, false)} := fromAxiom
    (Or.inl (Or.inr ⟨2, 3, by decide⟩)) (by decide)
  exact resolve (e6 2) unit6_2 h (by decide)

lemma unit6_3 : reachable6 {(e6 3, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{0, 1, 5}, by decide, by decide⟩
  · decide

lemma edge6_3_0 : reachable6 {(x6 3 0, false), (x6 4 0, false)} := by
  have h : reachable6 {(e6 3, false), (x6 3 0, false), (x6 4 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨3, 0, by decide⟩)) (by decide)
  exact resolve (e6 3) unit6_3 h (by decide)

lemma edge6_3_1 : reachable6 {(x6 3 1, false), (x6 4 1, false)} := by
  have h : reachable6 {(e6 3, false), (x6 3 1, false), (x6 4 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨3, 1, by decide⟩)) (by decide)
  exact resolve (e6 3) unit6_3 h (by decide)

lemma edge6_3_2 : reachable6 {(x6 3 2, false), (x6 4 2, false)} := by
  have h : reachable6 {(e6 3, false), (x6 3 2, false), (x6 4 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨3, 2, by decide⟩)) (by decide)
  exact resolve (e6 3) unit6_3 h (by decide)

lemma edge6_3_3 : reachable6 {(x6 3 3, false), (x6 4 3, false)} := by
  have h : reachable6 {(e6 3, false), (x6 3 3, false), (x6 4 3, false)} := fromAxiom
    (Or.inl (Or.inr ⟨3, 3, by decide⟩)) (by decide)
  exact resolve (e6 3) unit6_3 h (by decide)

lemma unit6_4 : reachable6 {(e6 4, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{0, 1, 3}, by decide, by decide⟩
  · decide

lemma edge6_4_0 : reachable6 {(x6 4 0, false), (x6 5 0, false)} := by
  have h : reachable6 {(e6 4, false), (x6 4 0, false), (x6 5 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨4, 0, by decide⟩)) (by decide)
  exact resolve (e6 4) unit6_4 h (by decide)

lemma edge6_4_1 : reachable6 {(x6 4 1, false), (x6 5 1, false)} := by
  have h : reachable6 {(e6 4, false), (x6 4 1, false), (x6 5 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨4, 1, by decide⟩)) (by decide)
  exact resolve (e6 4) unit6_4 h (by decide)

lemma edge6_4_2 : reachable6 {(x6 4 2, false), (x6 5 2, false)} := by
  have h : reachable6 {(e6 4, false), (x6 4 2, false), (x6 5 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨4, 2, by decide⟩)) (by decide)
  exact resolve (e6 4) unit6_4 h (by decide)

lemma edge6_4_3 : reachable6 {(x6 4 3, false), (x6 5 3, false)} := by
  have h : reachable6 {(e6 4, false), (x6 4 3, false), (x6 5 3, false)} := fromAxiom
    (Or.inl (Or.inr ⟨4, 3, by decide⟩)) (by decide)
  exact resolve (e6 4) unit6_4 h (by decide)

lemma unit6_5 : reachable6 {(e6 5, true)} := by
  apply fromAxiom
  · exact Or.inr ⟨{0, 1, 4}, by decide, by decide⟩
  · decide

lemma edge6_5_0 : reachable6 {(x6 3 0, false), (x6 5 0, false)} := by
  have h : reachable6 {(e6 5, false), (x6 3 0, false), (x6 5 0, false)} := fromAxiom
    (Or.inl (Or.inr ⟨5, 0, by decide⟩)) (by decide)
  exact resolve (e6 5) unit6_5 h (by decide)

lemma edge6_5_1 : reachable6 {(x6 3 1, false), (x6 5 1, false)} := by
  have h : reachable6 {(e6 5, false), (x6 3 1, false), (x6 5 1, false)} := fromAxiom
    (Or.inl (Or.inr ⟨5, 1, by decide⟩)) (by decide)
  exact resolve (e6 5) unit6_5 h (by decide)

lemma edge6_5_2 : reachable6 {(x6 3 2, false), (x6 5 2, false)} := by
  have h : reachable6 {(e6 5, false), (x6 3 2, false), (x6 5 2, false)} := fromAxiom
    (Or.inl (Or.inr ⟨5, 2, by decide⟩)) (by decide)
  exact resolve (e6 5) unit6_5 h (by decide)

lemma edge6_5_3 : reachable6 {(x6 3 3, false), (x6 5 3, false)} := by
  have h : reachable6 {(e6 5, false), (x6 3 3, false), (x6 5 3, false)} := fromAxiom
    (Or.inl (Or.inr ⟨5, 3, by decide⟩)) (by decide)
  exact resolve (e6 5) unit6_5 h (by decide)

-- Consecutive vertices of this path give pairs of nonadjacent vertices.
-- The path visits 0, 3, 1, 4, 2, 5 in order.
-- Earlier pairs have distinct labels. Each used label conflicts with an
-- endpoint of the next pair. Each unused label gives a new branch.

lemma branch6_0_1_2_3 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 1 2, false), (x6 4 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 5 1, true), (x6 2 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 5 1, true), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 5 1) h1 edge6_5_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 1 2, false), (x6 5 3, true)} :=
    resolve (x6 2 2) h2 edge6_1_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_4_3 (by decide)

lemma branch6_0_1_2 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 1 2, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 4 1, true), (x6 2 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 4 1) h1 edge6_3_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 1 2, false), (x6 4 3, true)} :=
    resolve (x6 2 2) h2 edge6_1_2 (by decide)
  exact resolve (x6 4 3) h3 branch6_0_1_2_3 (by decide)

lemma branch6_0_1_3_2 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 4 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 5 1, true), (x6 5 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 5 1, true), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 5 1) h1 edge6_5_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 4 2, false), (x6 2 3, true)} :=
    resolve (x6 5 2) h2 edge6_4_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_1_3 (by decide)

lemma branch6_0_1_3 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 4 1, true), (x6 4 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 4 1) h1 edge6_3_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 4 2, true), (x6 1 3, false)} :=
    resolve (x6 2 3) h2 edge6_1_3 (by decide)
  exact resolve (x6 4 2) h3 branch6_0_1_3_2 (by decide)

lemma branch6_0_1 : reachable6 {(x6 0 0, false), (x6 3 1, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 4 1, true), (x6 1 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 1 2, true), (x6 1 3, true)} :=
    resolve (x6 1 0) h0 edge6_0_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 1 2, true), (x6 1 3, true)} :=
    resolve (x6 4 1) h1 edge6_3_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 3 1, false), (x6 1 3, true)} :=
    resolve (x6 1 2) h2 branch6_0_1_2 (by decide)
  exact resolve (x6 1 3) h3 branch6_0_1_3 (by decide)

lemma branch6_0_2_1_3 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 3 2, false), (x6 4 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 2 1, true), (x6 5 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, false, true, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 2 1, true), (x6 5 2, true), (x6 5 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 5 2, true), (x6 5 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 3 2, false), (x6 5 3, true)} :=
    resolve (x6 5 2) h2 edge6_5_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_4_3 (by decide)

lemma branch6_0_2_1 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 3 2, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 2 1, true), (x6 4 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 2 1, true), (x6 4 2, true), (x6 4 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 4 2, true), (x6 4 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 3 2, false), (x6 4 3, true)} :=
    resolve (x6 4 2) h2 edge6_3_2 (by decide)
  exact resolve (x6 4 3) h3 branch6_0_2_1_3 (by decide)

lemma branch6_0_2_3_1 : reachable6 {(x6 0 0, false), (x6 4 1, false), (x6 3 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 5 1, true), (x6 5 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 5 1, true), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 4 1, false), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 5 1) h1 edge6_4_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 4 1, false), (x6 3 2, false), (x6 2 3, true)} :=
    resolve (x6 5 2) h2 edge6_5_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_1_3 (by decide)

lemma branch6_0_2_3 : reachable6 {(x6 0 0, false), (x6 3 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 4 1, true), (x6 4 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 3 2, false), (x6 2 3, true)} :=
    resolve (x6 4 2) h1 edge6_3_2 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 3 2, false), (x6 1 3, false)} :=
    resolve (x6 2 3) h2 edge6_1_3 (by decide)
  exact resolve (x6 4 1) h3 branch6_0_2_3_1 (by decide)

lemma branch6_0_2 : reachable6 {(x6 0 0, false), (x6 3 2, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 4 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 1 1, true), (x6 4 2, true), (x6 1 3, true)} :=
    resolve (x6 1 0) h0 edge6_0_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 1 1, true), (x6 3 2, false), (x6 1 3, true)} :=
    resolve (x6 4 2) h1 edge6_3_2 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 3 2, false), (x6 1 3, true)} :=
    resolve (x6 1 1) h2 branch6_0_2_1 (by decide)
  exact resolve (x6 1 3) h3 branch6_0_2_3 (by decide)

lemma branch6_0_3_1_2 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 4 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 2 1, true), (x6 5 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, false, true, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 2 1, true), (x6 5 2, true), (x6 5 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 5 2, true), (x6 5 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 4 2, false), (x6 5 3, true)} :=
    resolve (x6 5 2) h2 edge6_4_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_5_3 (by decide)

lemma branch6_0_3_1 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 2 1, true), (x6 4 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 2 1, true), (x6 4 2, true), (x6 4 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 4 2, true), (x6 4 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 1 1, false), (x6 4 2, true), (x6 3 3, false)} :=
    resolve (x6 4 3) h2 edge6_3_3 (by decide)
  exact resolve (x6 4 2) h3 branch6_0_3_1_2 (by decide)

lemma branch6_0_3_2_1 : reachable6 {(x6 0 0, false), (x6 4 1, false), (x6 1 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 5 1, true), (x6 2 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 5 1, true), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 4 1, false), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 5 1) h1 edge6_4_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 4 1, false), (x6 1 2, false), (x6 5 3, true)} :=
    resolve (x6 2 2) h2 edge6_1_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_5_3 (by decide)

lemma branch6_0_3_2 : reachable6 {(x6 0 0, false), (x6 1 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 4 1, true), (x6 2 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 2 0) h0 edge6_2_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 1 2, false), (x6 4 3, true)} :=
    resolve (x6 2 2) h1 edge6_1_2 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 4 1, true), (x6 1 2, false), (x6 3 3, false)} :=
    resolve (x6 4 3) h2 edge6_3_3 (by decide)
  exact resolve (x6 4 1) h3 branch6_0_3_2_1 (by decide)

lemma branch6_0_3 : reachable6 {(x6 0 0, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 1 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 1 1, true), (x6 1 2, true), (x6 4 3, true)} :=
    resolve (x6 1 0) h0 edge6_0_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 1 1, true), (x6 1 2, true), (x6 3 3, false)} :=
    resolve (x6 4 3) h1 edge6_3_3 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 1 2, true), (x6 3 3, false)} :=
    resolve (x6 1 1) h2 branch6_0_3_1 (by decide)
  exact resolve (x6 1 2) h3 branch6_0_3_2 (by decide)

lemma branch6_0 : reachable6 {(x6 0 0, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 3 1, true), (x6 3 2, true), (x6 3 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨3, 1, ![true, false, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 0, false), (x6 3 1, true), (x6 3 2, true), (x6 3 3, true)} :=
    resolve (x6 1 0) h0 edge6_0_0 (by decide)
  have h2 : reachable6 {(x6 0 0, false), (x6 3 2, true), (x6 3 3, true)} :=
    resolve (x6 3 1) h1 branch6_0_1 (by decide)
  have h3 : reachable6 {(x6 0 0, false), (x6 3 3, true)} :=
    resolve (x6 3 2) h2 branch6_0_2 (by decide)
  exact resolve (x6 3 3) h3 branch6_0_3 (by decide)

lemma branch6_1_0_2_3 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 1 2, false), (x6 4 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 2 1, true), (x6 2 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 2 1, true), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 5 0) h0 edge6_5_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 1 2, false), (x6 5 3, true)} :=
    resolve (x6 2 2) h2 edge6_1_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_4_3 (by decide)

lemma branch6_1_0_2 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 1 2, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 2 1, true), (x6 2 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, true, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 2 1, true), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 1 2, false), (x6 4 3, true)} :=
    resolve (x6 2 2) h2 edge6_1_2 (by decide)
  exact resolve (x6 4 3) h3 branch6_1_0_2_3 (by decide)

lemma branch6_1_0_3_2 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 4 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 2 1, true), (x6 5 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 2 1, true), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 5 0) h0 edge6_5_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 4 2, false), (x6 2 3, true)} :=
    resolve (x6 5 2) h2 edge6_4_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_1_3 (by decide)

lemma branch6_1_0_3 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 2 1, true), (x6 4 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, true, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 2 1, true), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 4 2, true), (x6 1 3, false)} :=
    resolve (x6 2 3) h2 edge6_1_3 (by decide)
  exact resolve (x6 4 2) h3 branch6_1_0_3_2 (by decide)

lemma branch6_1_0 : reachable6 {(x6 3 0, false), (x6 0 1, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 1 1, true), (x6 1 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 1 1, true), (x6 1 2, true), (x6 1 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 1 2, true), (x6 1 3, true)} :=
    resolve (x6 1 1) h1 edge6_0_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 0 1, false), (x6 1 3, true)} :=
    resolve (x6 1 2) h2 branch6_1_0_2 (by decide)
  exact resolve (x6 1 3) h3 branch6_1_0_3 (by decide)

lemma branch6_1_2_0_3 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 3 2, false), (x6 4 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 2 1, true), (x6 5 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, false, true, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 2 1, true), (x6 5 2, true), (x6 5 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 5 2, true), (x6 5 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 3 2, false), (x6 5 3, true)} :=
    resolve (x6 5 2) h2 edge6_5_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_4_3 (by decide)

lemma branch6_1_2_0 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 3 2, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 2 1, true), (x6 4 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 2 1, true), (x6 4 2, true), (x6 4 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 4 2, true), (x6 4 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 3 2, false), (x6 4 3, true)} :=
    resolve (x6 4 2) h2 edge6_3_2 (by decide)
  exact resolve (x6 4 3) h3 branch6_1_2_0_3 (by decide)

lemma branch6_1_2_3_0 : reachable6 {(x6 4 0, false), (x6 0 1, false), (x6 3 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 2 1, true), (x6 5 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, false), (x6 2 1, true), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 5 0) h0 edge6_4_0 (by decide)
  have h2 : reachable6 {(x6 4 0, false), (x6 0 1, false), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 4 0, false), (x6 0 1, false), (x6 3 2, false), (x6 2 3, true)} :=
    resolve (x6 5 2) h2 edge6_5_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_1_3 (by decide)

lemma branch6_1_2_3 : reachable6 {(x6 0 1, false), (x6 3 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 2 1, true), (x6 4 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, true, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, true), (x6 0 1, false), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 2 1) h0 edge6_2_1 (by decide)
  have h2 : reachable6 {(x6 4 0, true), (x6 0 1, false), (x6 3 2, false), (x6 2 3, true)} :=
    resolve (x6 4 2) h1 edge6_3_2 (by decide)
  have h3 : reachable6 {(x6 4 0, true), (x6 0 1, false), (x6 3 2, false), (x6 1 3, false)} :=
    resolve (x6 2 3) h2 edge6_1_3 (by decide)
  exact resolve (x6 4 0) h3 branch6_1_2_3_0 (by decide)

lemma branch6_1_2 : reachable6 {(x6 0 1, false), (x6 3 2, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 4 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, true), (x6 0 1, false), (x6 4 2, true), (x6 1 3, true)} :=
    resolve (x6 1 1) h0 edge6_0_1 (by decide)
  have h2 : reachable6 {(x6 1 0, true), (x6 0 1, false), (x6 3 2, false), (x6 1 3, true)} :=
    resolve (x6 4 2) h1 edge6_3_2 (by decide)
  have h3 : reachable6 {(x6 0 1, false), (x6 3 2, false), (x6 1 3, true)} :=
    resolve (x6 1 0) h2 branch6_1_2_0 (by decide)
  exact resolve (x6 1 3) h3 branch6_1_2_3 (by decide)

lemma branch6_1_3_0_2 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 4 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 2 1, true), (x6 5 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, false, true, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 2 1, true), (x6 5 2, true), (x6 5 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 5 2, true), (x6 5 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 4 2, false), (x6 5 3, true)} :=
    resolve (x6 5 2) h2 edge6_4_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_5_3 (by decide)

lemma branch6_1_3_0 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 2 1, true), (x6 4 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 2 1, true), (x6 4 2, true), (x6 4 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 4 2, true), (x6 4 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 0 1, false), (x6 4 2, true), (x6 3 3, false)} :=
    resolve (x6 4 3) h2 edge6_3_3 (by decide)
  exact resolve (x6 4 2) h3 branch6_1_3_0_2 (by decide)

lemma branch6_1_3_2_0 : reachable6 {(x6 4 0, false), (x6 0 1, false), (x6 1 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 2 1, true), (x6 2 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, false), (x6 2 1, true), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 5 0) h0 edge6_4_0 (by decide)
  have h2 : reachable6 {(x6 4 0, false), (x6 0 1, false), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 2 1) h1 edge6_2_1 (by decide)
  have h3 : reachable6 {(x6 4 0, false), (x6 0 1, false), (x6 1 2, false), (x6 5 3, true)} :=
    resolve (x6 2 2) h2 edge6_1_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_5_3 (by decide)

lemma branch6_1_3_2 : reachable6 {(x6 0 1, false), (x6 1 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 2 1, true), (x6 2 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, true, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, true), (x6 0 1, false), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 2 1) h0 edge6_2_1 (by decide)
  have h2 : reachable6 {(x6 4 0, true), (x6 0 1, false), (x6 1 2, false), (x6 4 3, true)} :=
    resolve (x6 2 2) h1 edge6_1_2 (by decide)
  have h3 : reachable6 {(x6 4 0, true), (x6 0 1, false), (x6 1 2, false), (x6 3 3, false)} :=
    resolve (x6 4 3) h2 edge6_3_3 (by decide)
  exact resolve (x6 4 0) h3 branch6_1_3_2_0 (by decide)

lemma branch6_1_3 : reachable6 {(x6 0 1, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 1 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, true), (x6 0 1, false), (x6 1 2, true), (x6 4 3, true)} :=
    resolve (x6 1 1) h0 edge6_0_1 (by decide)
  have h2 : reachable6 {(x6 1 0, true), (x6 0 1, false), (x6 1 2, true), (x6 3 3, false)} :=
    resolve (x6 4 3) h1 edge6_3_3 (by decide)
  have h3 : reachable6 {(x6 0 1, false), (x6 1 2, true), (x6 3 3, false)} :=
    resolve (x6 1 0) h2 branch6_1_3_0 (by decide)
  exact resolve (x6 1 2) h3 branch6_1_3_2 (by decide)

lemma branch6_1 : reachable6 {(x6 0 1, false)} := by
  have h0 : reachable6 {(x6 3 0, true), (x6 1 1, true), (x6 3 2, true), (x6 3 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨3, 1, ![false, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, true), (x6 0 1, false), (x6 3 2, true), (x6 3 3, true)} :=
    resolve (x6 1 1) h0 edge6_0_1 (by decide)
  have h2 : reachable6 {(x6 0 1, false), (x6 3 2, true), (x6 3 3, true)} :=
    resolve (x6 3 0) h1 branch6_1_0 (by decide)
  have h3 : reachable6 {(x6 0 1, false), (x6 3 3, true)} :=
    resolve (x6 3 2) h2 branch6_1_2 (by decide)
  exact resolve (x6 3 3) h3 branch6_1_3 (by decide)

lemma branch6_2_0_1_3 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 0 2, false), (x6 4 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 2 1, true), (x6 2 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 2 1, true), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 5 0) h0 edge6_5_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 0 2, false), (x6 5 3, true)} :=
    resolve (x6 2 2) h2 edge6_2_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_4_3 (by decide)

lemma branch6_2_0_1 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 0 2, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 2 1, true), (x6 2 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, true, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 2 1, true), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 0 2, false), (x6 4 3, true)} :=
    resolve (x6 2 2) h2 edge6_2_2 (by decide)
  exact resolve (x6 4 3) h3 branch6_2_0_1_3 (by decide)

lemma branch6_2_0_3_1 : reachable6 {(x6 3 0, false), (x6 4 1, false), (x6 0 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 5 1, true), (x6 2 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 5 1, true), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 5 0) h0 edge6_5_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 4 1, false), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 5 1) h1 edge6_4_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 4 1, false), (x6 0 2, false), (x6 2 3, true)} :=
    resolve (x6 2 2) h2 edge6_2_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_1_3 (by decide)

lemma branch6_2_0_3 : reachable6 {(x6 3 0, false), (x6 0 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 4 1, true), (x6 2 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, false, true, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 4 1, true), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 4 1, true), (x6 0 2, false), (x6 2 3, true)} :=
    resolve (x6 2 2) h1 edge6_2_2 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 4 1, true), (x6 0 2, false), (x6 1 3, false)} :=
    resolve (x6 2 3) h2 edge6_1_3 (by decide)
  exact resolve (x6 4 1) h3 branch6_2_0_3_1 (by decide)

lemma branch6_2_0 : reachable6 {(x6 3 0, false), (x6 0 2, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 1 1, true), (x6 1 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 1 1, true), (x6 1 2, true), (x6 1 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 1 1, true), (x6 0 2, false), (x6 1 3, true)} :=
    resolve (x6 1 2) h1 edge6_0_2 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 0 2, false), (x6 1 3, true)} :=
    resolve (x6 1 1) h2 branch6_2_0_1 (by decide)
  exact resolve (x6 1 3) h3 branch6_2_0_3 (by decide)

lemma branch6_2_1_0_3 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 0 2, false), (x6 4 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 5 1, true), (x6 2 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 5 1, true), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 5 1) h1 edge6_5_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 0 2, false), (x6 5 3, true)} :=
    resolve (x6 2 2) h2 edge6_2_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_4_3 (by decide)

lemma branch6_2_1_0 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 0 2, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 4 1, true), (x6 2 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 4 1, true), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 4 1) h1 edge6_3_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 0 2, false), (x6 4 3, true)} :=
    resolve (x6 2 2) h2 edge6_2_2 (by decide)
  exact resolve (x6 4 3) h3 branch6_2_1_0_3 (by decide)

lemma branch6_2_1_3_0 : reachable6 {(x6 4 0, false), (x6 3 1, false), (x6 0 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 5 1, true), (x6 2 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, false), (x6 5 1, true), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 5 0) h0 edge6_4_0 (by decide)
  have h2 : reachable6 {(x6 4 0, false), (x6 3 1, false), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 5 1) h1 edge6_5_1 (by decide)
  have h3 : reachable6 {(x6 4 0, false), (x6 3 1, false), (x6 0 2, false), (x6 2 3, true)} :=
    resolve (x6 2 2) h2 edge6_2_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_1_3 (by decide)

lemma branch6_2_1_3 : reachable6 {(x6 3 1, false), (x6 0 2, false), (x6 1 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 4 1, true), (x6 2 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, false, true, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, true), (x6 3 1, false), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 4 1) h0 edge6_3_1 (by decide)
  have h2 : reachable6 {(x6 4 0, true), (x6 3 1, false), (x6 0 2, false), (x6 2 3, true)} :=
    resolve (x6 2 2) h1 edge6_2_2 (by decide)
  have h3 : reachable6 {(x6 4 0, true), (x6 3 1, false), (x6 0 2, false), (x6 1 3, false)} :=
    resolve (x6 2 3) h2 edge6_1_3 (by decide)
  exact resolve (x6 4 0) h3 branch6_2_1_3_0 (by decide)

lemma branch6_2_1 : reachable6 {(x6 3 1, false), (x6 0 2, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 4 1, true), (x6 1 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, true), (x6 3 1, false), (x6 1 2, true), (x6 1 3, true)} :=
    resolve (x6 4 1) h0 edge6_3_1 (by decide)
  have h2 : reachable6 {(x6 1 0, true), (x6 3 1, false), (x6 0 2, false), (x6 1 3, true)} :=
    resolve (x6 1 2) h1 edge6_0_2 (by decide)
  have h3 : reachable6 {(x6 3 1, false), (x6 0 2, false), (x6 1 3, true)} :=
    resolve (x6 1 0) h2 branch6_2_1_0 (by decide)
  exact resolve (x6 1 3) h3 branch6_2_1_3 (by decide)

lemma branch6_2_3_0_1 : reachable6 {(x6 1 0, false), (x6 4 1, false), (x6 0 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 5 1, true), (x6 2 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 5 1, true), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 4 1, false), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 5 1) h1 edge6_4_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 4 1, false), (x6 0 2, false), (x6 5 3, true)} :=
    resolve (x6 2 2) h2 edge6_2_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_5_3 (by decide)

lemma branch6_2_3_0 : reachable6 {(x6 1 0, false), (x6 0 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 4 1, true), (x6 2 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 4 1, true), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 4 1, true), (x6 0 2, false), (x6 4 3, true)} :=
    resolve (x6 2 2) h1 edge6_2_2 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 4 1, true), (x6 0 2, false), (x6 3 3, false)} :=
    resolve (x6 4 3) h2 edge6_3_3 (by decide)
  exact resolve (x6 4 1) h3 branch6_2_3_0_1 (by decide)

lemma branch6_2_3_1_0 : reachable6 {(x6 4 0, false), (x6 1 1, false), (x6 0 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 2 1, true), (x6 2 2, true), (x6 5 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, false), (x6 2 1, true), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 5 0) h0 edge6_4_0 (by decide)
  have h2 : reachable6 {(x6 4 0, false), (x6 1 1, false), (x6 2 2, true), (x6 5 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 4 0, false), (x6 1 1, false), (x6 0 2, false), (x6 5 3, true)} :=
    resolve (x6 2 2) h2 edge6_2_2 (by decide)
  exact resolve (x6 5 3) h3 edge6_5_3 (by decide)

lemma branch6_2_3_1 : reachable6 {(x6 1 1, false), (x6 0 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 2 1, true), (x6 2 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, true, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, true), (x6 1 1, false), (x6 2 2, true), (x6 4 3, true)} :=
    resolve (x6 2 1) h0 edge6_1_1 (by decide)
  have h2 : reachable6 {(x6 4 0, true), (x6 1 1, false), (x6 0 2, false), (x6 4 3, true)} :=
    resolve (x6 2 2) h1 edge6_2_2 (by decide)
  have h3 : reachable6 {(x6 4 0, true), (x6 1 1, false), (x6 0 2, false), (x6 3 3, false)} :=
    resolve (x6 4 3) h2 edge6_3_3 (by decide)
  exact resolve (x6 4 0) h3 branch6_2_3_1_0 (by decide)

lemma branch6_2_3 : reachable6 {(x6 0 2, false), (x6 3 3, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 1 2, true), (x6 4 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 0 2, false), (x6 4 3, true)} :=
    resolve (x6 1 2) h0 edge6_0_2 (by decide)
  have h2 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 0 2, false), (x6 3 3, false)} :=
    resolve (x6 4 3) h1 edge6_3_3 (by decide)
  have h3 : reachable6 {(x6 1 1, true), (x6 0 2, false), (x6 3 3, false)} :=
    resolve (x6 1 0) h2 branch6_2_3_0 (by decide)
  exact resolve (x6 1 1) h3 branch6_2_3_1 (by decide)

lemma branch6_2 : reachable6 {(x6 0 2, false)} := by
  have h0 : reachable6 {(x6 3 0, true), (x6 3 1, true), (x6 1 2, true), (x6 3 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨3, 1, ![false, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, true), (x6 3 1, true), (x6 0 2, false), (x6 3 3, true)} :=
    resolve (x6 1 2) h0 edge6_0_2 (by decide)
  have h2 : reachable6 {(x6 3 1, true), (x6 0 2, false), (x6 3 3, true)} :=
    resolve (x6 3 0) h1 branch6_2_0 (by decide)
  have h3 : reachable6 {(x6 0 2, false), (x6 3 3, true)} :=
    resolve (x6 3 1) h2 branch6_2_1 (by decide)
  exact resolve (x6 3 3) h3 branch6_2_3 (by decide)

lemma branch6_3_0_1_2 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 4 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 2 1, true), (x6 5 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 2 1, true), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 5 0) h0 edge6_5_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 4 2, false), (x6 2 3, true)} :=
    resolve (x6 5 2) h2 edge6_4_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_2_3 (by decide)

lemma branch6_3_0_1 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 2 1, true), (x6 4 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, true, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 2 1, true), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 1 1, false), (x6 4 2, true), (x6 0 3, false)} :=
    resolve (x6 2 3) h2 edge6_2_3 (by decide)
  exact resolve (x6 4 2) h3 branch6_3_0_1_2 (by decide)

lemma branch6_3_0_2_1 : reachable6 {(x6 3 0, false), (x6 4 1, false), (x6 1 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 5 1, true), (x6 2 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 5 1, true), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 5 0) h0 edge6_5_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 4 1, false), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 5 1) h1 edge6_4_1 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 4 1, false), (x6 1 2, false), (x6 2 3, true)} :=
    resolve (x6 2 2) h2 edge6_1_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_2_3 (by decide)

lemma branch6_3_0_2 : reachable6 {(x6 3 0, false), (x6 1 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 4 1, true), (x6 2 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, false, true, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 4 1, true), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 4 1, true), (x6 1 2, false), (x6 2 3, true)} :=
    resolve (x6 2 2) h1 edge6_1_2 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 4 1, true), (x6 1 2, false), (x6 0 3, false)} :=
    resolve (x6 2 3) h2 edge6_2_3 (by decide)
  exact resolve (x6 4 1) h3 branch6_3_0_2_1 (by decide)

lemma branch6_3_0 : reachable6 {(x6 3 0, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 1 1, true), (x6 1 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, false), (x6 1 1, true), (x6 1 2, true), (x6 1 3, true)} :=
    resolve (x6 4 0) h0 edge6_3_0 (by decide)
  have h2 : reachable6 {(x6 3 0, false), (x6 1 1, true), (x6 1 2, true), (x6 0 3, false)} :=
    resolve (x6 1 3) h1 edge6_0_3 (by decide)
  have h3 : reachable6 {(x6 3 0, false), (x6 1 2, true), (x6 0 3, false)} :=
    resolve (x6 1 1) h2 branch6_3_0_1 (by decide)
  exact resolve (x6 1 2) h3 branch6_3_0_2 (by decide)

lemma branch6_3_1_0_2 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 4 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 5 1, true), (x6 5 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 5 1, true), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 5 1) h1 edge6_5_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 4 2, false), (x6 2 3, true)} :=
    resolve (x6 5 2) h2 edge6_4_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_2_3 (by decide)

lemma branch6_3_1_0 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 4 1, true), (x6 4 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 4 1, true), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 4 1) h1 edge6_3_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 3 1, false), (x6 4 2, true), (x6 0 3, false)} :=
    resolve (x6 2 3) h2 edge6_2_3 (by decide)
  exact resolve (x6 4 2) h3 branch6_3_1_0_2 (by decide)

lemma branch6_3_1_2_0 : reachable6 {(x6 4 0, false), (x6 3 1, false), (x6 1 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 5 1, true), (x6 2 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, false), (x6 5 1, true), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 5 0) h0 edge6_4_0 (by decide)
  have h2 : reachable6 {(x6 4 0, false), (x6 3 1, false), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 5 1) h1 edge6_5_1 (by decide)
  have h3 : reachable6 {(x6 4 0, false), (x6 3 1, false), (x6 1 2, false), (x6 2 3, true)} :=
    resolve (x6 2 2) h2 edge6_1_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_2_3 (by decide)

lemma branch6_3_1_2 : reachable6 {(x6 3 1, false), (x6 1 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 4 1, true), (x6 2 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, false, true, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, true), (x6 3 1, false), (x6 2 2, true), (x6 2 3, true)} :=
    resolve (x6 4 1) h0 edge6_3_1 (by decide)
  have h2 : reachable6 {(x6 4 0, true), (x6 3 1, false), (x6 1 2, false), (x6 2 3, true)} :=
    resolve (x6 2 2) h1 edge6_1_2 (by decide)
  have h3 : reachable6 {(x6 4 0, true), (x6 3 1, false), (x6 1 2, false), (x6 0 3, false)} :=
    resolve (x6 2 3) h2 edge6_2_3 (by decide)
  exact resolve (x6 4 0) h3 branch6_3_1_2_0 (by decide)

lemma branch6_3_1 : reachable6 {(x6 3 1, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 4 1, true), (x6 1 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, true, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, true), (x6 3 1, false), (x6 1 2, true), (x6 1 3, true)} :=
    resolve (x6 4 1) h0 edge6_3_1 (by decide)
  have h2 : reachable6 {(x6 1 0, true), (x6 3 1, false), (x6 1 2, true), (x6 0 3, false)} :=
    resolve (x6 1 3) h1 edge6_0_3 (by decide)
  have h3 : reachable6 {(x6 3 1, false), (x6 1 2, true), (x6 0 3, false)} :=
    resolve (x6 1 0) h2 branch6_3_1_0 (by decide)
  exact resolve (x6 1 2) h3 branch6_3_1_2 (by decide)

lemma branch6_3_2_0_1 : reachable6 {(x6 1 0, false), (x6 4 1, false), (x6 3 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 5 1, true), (x6 5 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 5 1, true), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 4 1, false), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 5 1) h1 edge6_4_1 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 4 1, false), (x6 3 2, false), (x6 2 3, true)} :=
    resolve (x6 5 2) h2 edge6_5_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_2_3 (by decide)

lemma branch6_3_2_0 : reachable6 {(x6 1 0, false), (x6 3 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 2 0, true), (x6 4 1, true), (x6 4 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![true, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, false), (x6 4 1, true), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 2 0) h0 edge6_1_0 (by decide)
  have h2 : reachable6 {(x6 1 0, false), (x6 4 1, true), (x6 3 2, false), (x6 2 3, true)} :=
    resolve (x6 4 2) h1 edge6_3_2 (by decide)
  have h3 : reachable6 {(x6 1 0, false), (x6 4 1, true), (x6 3 2, false), (x6 0 3, false)} :=
    resolve (x6 2 3) h2 edge6_2_3 (by decide)
  exact resolve (x6 4 1) h3 branch6_3_2_0_1 (by decide)

lemma branch6_3_2_1_0 : reachable6 {(x6 4 0, false), (x6 1 1, false), (x6 3 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 5 0, true), (x6 2 1, true), (x6 5 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, false), (x6 2 1, true), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 5 0) h0 edge6_4_0 (by decide)
  have h2 : reachable6 {(x6 4 0, false), (x6 1 1, false), (x6 5 2, true), (x6 2 3, true)} :=
    resolve (x6 2 1) h1 edge6_1_1 (by decide)
  have h3 : reachable6 {(x6 4 0, false), (x6 1 1, false), (x6 3 2, false), (x6 2 3, true)} :=
    resolve (x6 5 2) h2 edge6_5_2 (by decide)
  exact resolve (x6 2 3) h3 edge6_2_3 (by decide)

lemma branch6_3_2_1 : reachable6 {(x6 1 1, false), (x6 3 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 4 0, true), (x6 2 1, true), (x6 4 2, true), (x6 2 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨4, 2, ![false, true, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 4 0, true), (x6 1 1, false), (x6 4 2, true), (x6 2 3, true)} :=
    resolve (x6 2 1) h0 edge6_1_1 (by decide)
  have h2 : reachable6 {(x6 4 0, true), (x6 1 1, false), (x6 3 2, false), (x6 2 3, true)} :=
    resolve (x6 4 2) h1 edge6_3_2 (by decide)
  have h3 : reachable6 {(x6 4 0, true), (x6 1 1, false), (x6 3 2, false), (x6 0 3, false)} :=
    resolve (x6 2 3) h2 edge6_2_3 (by decide)
  exact resolve (x6 4 0) h3 branch6_3_2_1_0 (by decide)

lemma branch6_3_2 : reachable6 {(x6 3 2, false), (x6 0 3, false)} := by
  have h0 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 4 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, false, true, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 3 2, false), (x6 1 3, true)} :=
    resolve (x6 4 2) h0 edge6_3_2 (by decide)
  have h2 : reachable6 {(x6 1 0, true), (x6 1 1, true), (x6 3 2, false), (x6 0 3, false)} :=
    resolve (x6 1 3) h1 edge6_0_3 (by decide)
  have h3 : reachable6 {(x6 1 1, true), (x6 3 2, false), (x6 0 3, false)} :=
    resolve (x6 1 0) h2 branch6_3_2_0 (by decide)
  exact resolve (x6 1 1) h3 branch6_3_2_1 (by decide)

lemma branch6_3 : reachable6 {(x6 0 3, false)} := by
  have h0 : reachable6 {(x6 3 0, true), (x6 3 1, true), (x6 3 2, true), (x6 1 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨3, 1, ![false, false, false, true], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 3 0, true), (x6 3 1, true), (x6 3 2, true), (x6 0 3, false)} :=
    resolve (x6 1 3) h0 edge6_0_3 (by decide)
  have h2 : reachable6 {(x6 3 1, true), (x6 3 2, true), (x6 0 3, false)} :=
    resolve (x6 3 0) h1 branch6_3_0 (by decide)
  have h3 : reachable6 {(x6 3 2, true), (x6 0 3, false)} :=
    resolve (x6 3 1) h2 branch6_3_1 (by decide)
  exact resolve (x6 3 2) h3 branch6_3_2 (by decide)

lemma branch6_root : reachable6 ∅ := by
  have h0 : reachable6 {(x6 0 0, true), (x6 0 1, true), (x6 0 2, true), (x6 0 3, true)} := fromAxiom
    (Or.inl (Or.inl (Or.inr ⟨0, 3, ![false, false, false, false], by decide, by decide, by decide⟩))) (by decide)
  have h1 : reachable6 {(x6 0 1, true), (x6 0 2, true), (x6 0 3, true)} :=
    resolve (x6 0 0) h0 branch6_0 (by decide)
  have h2 : reachable6 {(x6 0 2, true), (x6 0 3, true)} :=
    resolve (x6 0 1) h1 branch6_1 (by decide)
  have h3 : reachable6 {(x6 0 3, true)} :=
    resolve (x6 0 2) h2 branch6_2 (by decide)
  exact resolve (x6 0 3) h3 branch6_3 (by decide)

end PEqualNP.Outside.L_pcx_093

theorem PEqualNP.Outside.L_pcx_093 : (∀ F1 : Set (PEqualNP.ProofComplexity.Clause ((Fin 5 × Fin 3) ⊕ Fin 5)), F1 = {C6 | ∃ v7 : Fin 5, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 5 × Fin 3) ⊕ Fin 5), true))} ∪ {C9 | ∃ (u10 v11 : Fin 5) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (v11 = u10 + 1 ∨ u10 = v11 + 1) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 5 × Fin 3) ⊕ Fin 5), true))} ∪ {C14 | ∃ (e15 : Fin 5) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 5 × Fin 3) ⊕ Fin 5), false), ((Sum.inl (e15, t16) : (Fin 5 × Fin 3) ⊕ Fin 5), false), ((Sum.inl (e15 + 1, t16) : (Fin 5 × Fin 3) ⊕ Fin 5), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 5), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 5 => e19 ∉ S18 ∧ e19 + 1 ∉ S18)).image (fun e20 : Fin 5 => ((Sum.inr e20 : (Fin 5 × Fin 3) ⊕ Fin 5), true))} → (∃ π2, PEqualNP.ProofComplexity.IsRefutation F1 π2 ∧ ∀ D3 ∈ π2, D3.card ≤ 3) ∧ ¬ ∃ π4, PEqualNP.ProofComplexity.IsRefutation F1 π4 ∧ ∀ D5 ∈ π4, D5.card ≤ 2) ∧ (∀ F21 : Set (PEqualNP.ProofComplexity.Clause ((Fin 6 × Fin 4) ⊕ Fin 6)), F21 = {C26 | ∃ v27 : Fin 6, C26 = Finset.univ.image (fun t28 : Fin 4 => ((Sum.inl (v27, t28) : (Fin 6 × Fin 4) ⊕ Fin 6), true))} ∪ {C29 | ∃ (u30 v31 : Fin 6) (f32 : Fin 4 → Bool), u30 ≠ v31 ∧ ¬ (u30 ≠ v31 ∧ u30.val / 3 = v31.val / 3) ∧ C29 = Finset.univ.image (fun t33 : Fin 4 => ((Sum.inl (if f32 t33 = true then v31 else u30, t33) : (Fin 6 × Fin 4) ⊕ Fin 6), true))} ∪ {C34 | ∃ (e35 : Fin 6) (t36 : Fin 4), C34 = {((Sum.inr e35 : (Fin 6 × Fin 4) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e35).1, t36) : (Fin 6 × Fin 4) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e35).2, t36) : (Fin 6 × Fin 4) ⊕ Fin 6), false)}} ∪ {C37 | ∃ S38 : Finset (Fin 6), S38.card = 3 ∧ C37 = (Finset.univ.filter (fun e39 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e39).1 ∉ S38 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e39).2 ∉ S38)).image (fun e40 : Fin 6 => ((Sum.inr e40 : (Fin 6 × Fin 4) ⊕ Fin 6), true))} → (∃ π22, PEqualNP.ProofComplexity.IsRefutation F21 π22 ∧ ∀ D23 ∈ π22, D23.card ≤ 4) ∧ ¬ ∃ π24, PEqualNP.ProofComplexity.IsRefutation F21 π24 ∧ ∀ D25 ∈ π24, D25.card ≤ 3) := by
  constructor
  · intro F h
    change F = PEqualNP.Outside.L_pcx_093.formula5 at h
    subst F
    exact ⟨PEqualNP.Outside.L_pcx_093.toRefutation PEqualNP.Outside.L_pcx_093.branch5_root, PEqualNP.Outside.L_pcx_093.lower5⟩
  · intro F h
    change F = PEqualNP.Outside.L_pcx_093.formula6 at h
    subst F
    exact ⟨PEqualNP.Outside.L_pcx_093.toRefutation PEqualNP.Outside.L_pcx_093.branch6_root, PEqualNP.Outside.L_pcx_093.lower6⟩
