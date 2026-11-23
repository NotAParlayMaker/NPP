import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_100_aux
open PEqualNP.ProofComplexity

abbrev V := (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))
def M (Ymc : Finset (Fin 5)) : Prop := ((∀ umc ∈ Ymc, ∀ wmc ∈ Ymc, ¬ (wmc = umc + 1 ∨ umc = wmc + 1)) ∧ ∀ zmc : Fin 5, zmc ∉ Ymc → ∃ ymc ∈ Ymc, (zmc = ymc + 1 ∨ ymc = zmc + 1))
def Q (Yqc : Finset (Fin 5)) : Prop := ∃ Iqc : Finset (Fin 5), M Iqc ∧ ∃ wqc : Fin 5, wqc ∉ Iqc ∧ Yqc = insert wqc Iqc
def F : Set (Clause V) :=
  {C1c | ∃ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (M X1c ∨ Q X1c) ∧ j1c < i1c ∧ (C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), false)})} ∪
  {C2c | ∃ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (M X2c ∨ Q X2c) ∧ C2c = insert ((((5, X2c), ((i2c, e2c), (0, 0))) : V), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : V), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : V), true)))} ∪
  {C3c | ∃ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (M X3c ∨ Q X3c) ∧ v3c ∈ X3c ∧ C3c = {((((5, X3c), ((i3c, e3c), (0, 0))) : V), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : V), false)}} ∪
  {C4c | ∃ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (M X4c ∨ Q X4c) ∧ j4c < i4c ∧ C4c = {((((5, X4c), ((i4c, e4c), (0, 0))) : V), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : V), false)}} ∪
  {C5c | ∃ (X5c : Finset (Fin 5)) (i5c : Fin 2), (M X5c ∨ Q X5c) ∧ (C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, false), (0, 0))) : V), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), true), ((((5, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), false)})} ∪
  {C6c | ∃ (X6c : Finset (Fin 5)) (v6c : Fin 5), M X6c ∧ v6c ∈ X6c ∧ C6c = {((((2, ∅), ((0, false), (0, v6c))) : V), false)}} ∪
  {C7c | ∃ (X7c : Finset (Fin 5)) (i7c : Fin 2), M X7c ∧ C7c = {((((3, ∅), ((i7c, false), (0, 0))) : V), false), ((((6, X7c), ((i7c, false), (0, 0))) : V), false)}} ∪
  {C8c | ∃ (X8c : Finset (Fin 5)) (i8c : Fin 2), Q X8c ∧ (C8c = {((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((3, ∅), ((i8c, false), (0, 0))) : V), true)} ∨ C8c = {((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((6, X8c), ((i8c, false), (0, 0))) : V), true)})} ∪
  {C9c | ∃ X9c : Finset (Fin 5), Q X9c ∧ C9c = X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : V), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : V), true))}
def rho (z : V) : Option Bool := if z.1.1 = 2 then some false else none

-- Select the second gate and give its input and output variables the value of the triple test.
def assign (z : V) : Bool :=
  decide (z.2.1.1 = 1 ∧ (z.1.1 = 3 ∨ (z.1.1 = 5 ∨ z.1.1 = 6 ∨ z.1.1 = 7) ∧ z.1.2.card = 3))

def good (C : Clause V) : Bool :=
  match restrictClause rho C with
  | none => true
  | some D => decide (4 < D.card ∨ ∃ l ∈ D, assign l.1 = l.2)

lemma sat_of_good {C D : Clause V} (hg : good C = true)
    (hr : restrictClause rho C = some D) (hw : D.card ≤ 4) : ClauseSat assign D := by
  simpa [good, hr, Nat.not_lt.mpr hw, ClauseSat] using hg


set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma m_card : ∀ X, M X → X.card = 2 := by
  unfold M
  decide +kernel

lemma q_card (X) (h : Q X) : X.card = 3 := by
  obtain ⟨I, hI, w, hw, rfl⟩ := h
  rw [Finset.card_insert_of_notMem hw, m_card _ hI]

lemma mq_card (X) (h : M X ∨ Q X) : X.card = 2 ∨ X.card = 3 :=
  h.elim (fun hm => Or.inl (m_card X hm)) (fun hq => Or.inr (q_card X hq))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family1 (C : Clause V) (h : ∃ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (M X1c ∨ Q X1c) ∧ j1c < i1c ∧ (C = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), true)} ∨ C = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), true)} ∨ C = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), false)})) : good C = true := by
  rcases h with ⟨X, i, e, j, hrow, hj, eqn⟩
  have hsize := mq_card X hrow
  clear hrow
  rcases eqn with rfl | rfl | rfl <;> revert X i e j <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family2 (C : Clause V) (h : ∃ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (M X2c ∨ Q X2c) ∧ C = insert ((((5, X2c), ((i2c, e2c), (0, 0))) : V), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : V), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : V), true)))) : good C = true := by
  rcases h with ⟨X, i, e, hrow, eqn⟩
  have hsize := mq_card X hrow
  clear hrow
  rcases eqn with rfl <;> revert X i e <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family3 (C : Clause V) (h : ∃ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (M X3c ∨ Q X3c) ∧ v3c ∈ X3c ∧ C = {((((5, X3c), ((i3c, e3c), (0, 0))) : V), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : V), false)}) : good C = true := by
  rcases h with ⟨X, i, e, v, hrow, hv, eqn⟩
  have hsize := mq_card X hrow
  clear hrow
  rcases eqn with rfl <;> revert X i e v <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family4 (C : Clause V) (h : ∃ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (M X4c ∨ Q X4c) ∧ j4c < i4c ∧ C = {((((5, X4c), ((i4c, e4c), (0, 0))) : V), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : V), false)}) : good C = true := by
  rcases h with ⟨X, i, e, j, hrow, hj, eqn⟩
  have hsize := mq_card X hrow
  clear hrow
  rcases eqn with rfl <;> revert X i e j <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family5 (C : Clause V) (h : ∃ (X5c : Finset (Fin 5)) (i5c : Fin 2), (M X5c ∨ Q X5c) ∧ (C = {((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, false), (0, 0))) : V), true)} ∨ C = {((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), true)} ∨ C = {((((6, X5c), ((i5c, false), (0, 0))) : V), true), ((((5, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), false)})) : good C = true := by
  rcases h with ⟨X, i, hrow, eqn⟩
  have hsize := mq_card X hrow
  clear hrow
  rcases eqn with rfl | rfl | rfl <;> revert X i <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family6 (C : Clause V) (h : ∃ (X6c : Finset (Fin 5)) (v6c : Fin 5), M X6c ∧ v6c ∈ X6c ∧ C = {((((2, ∅), ((0, false), (0, v6c))) : V), false)}) : good C = true := by
  rcases h with ⟨X, v, hrow, hv, eqn⟩
  have hsize := m_card X hrow
  clear hrow
  rcases eqn with rfl <;> revert X v <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family7 (C : Clause V) (h : ∃ (X7c : Finset (Fin 5)) (i7c : Fin 2), M X7c ∧ C = {((((3, ∅), ((i7c, false), (0, 0))) : V), false), ((((6, X7c), ((i7c, false), (0, 0))) : V), false)}) : good C = true := by
  rcases h with ⟨X, i, hrow, eqn⟩
  have hsize := m_card X hrow
  clear hrow
  rcases eqn with rfl <;> revert X i <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family8 (C : Clause V) (h : ∃ (X8c : Finset (Fin 5)) (i8c : Fin 2), Q X8c ∧ (C = {((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((3, ∅), ((i8c, false), (0, 0))) : V), true)} ∨ C = {((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((6, X8c), ((i8c, false), (0, 0))) : V), true)})) : good C = true := by
  rcases h with ⟨X, i, hrow, eqn⟩
  have hsize := q_card X hrow
  clear hrow
  rcases eqn with rfl | rfl <;> revert X i <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8000 in
lemma family9 (C : Clause V) (h : ∃ X9c : Finset (Fin 5), Q X9c ∧ C = X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : V), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : V), true))) : good C = true := by
  rcases h with ⟨X, hrow, eqn⟩
  have hsize := q_card X hrow
  clear hrow
  rcases eqn with rfl <;> revert X <;> decide +kernel

lemma all_good (C : Clause V) (h : C ∈ F) : good C = true := by
  simp only [F, Set.mem_union, Set.mem_setOf_eq] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact family1 C h
  · exact family2 C h
  · exact family3 C h
  · exact family4 C h
  · exact family5 C h
  · exact family6 C h
  · exact family7 C h
  · exact family8 C h
  · exact family9 C h

-- An assignment satisfying both premises satisfies the resolvent.
theorem resolvent_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : Clause V}
    (h : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) : ClauseSat a R := by
  obtain ⟨v, -, -, rfl⟩ := h
  obtain ⟨l, hl, hal⟩ := hC
  obtain ⟨l', hl', hal'⟩ := hD
  by_cases h : l = (v, true)
  · subst h
    refine ⟨l', Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl'⟩), hal'⟩
    rintro rfl
    simp_all
  · exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩), hal⟩

-- Only axioms which actually occur in a narrow derivation must be satisfied.
lemma narrowSound {G : Set (Clause V)} (ha : ∀ C ∈ G, C.card ≤ 4 → ClauseSat assign C)
    {π : List (Clause V)} (h : IsDerivation G π) :
    (∀ C ∈ π, C.card ≤ 4) → ∀ C ∈ π, ClauseSat assign C := by
  induction h with
  | nil => simp
  | ax _ hCF ih =>
    intro w E he
    rcases List.mem_cons.mp he with rfl | he
    · exact ha _ hCF (w _ (List.mem_cons_self ..))
    · exact ih (fun C hc => w C (List.mem_cons_of_mem _ hc)) E he
  | res _ hC hD hR ih =>
    intro w E he
    have tailSat := ih (fun C hc => w C (List.mem_cons_of_mem _ hc))
    rcases List.mem_cons.mp he with rfl | he
    · exact resolvent_sound assign hR (tailSat _ hC) (tailSat _ hD)
    · exact tailSat E he

end PEqualNP.Outside.L_pcx_100_aux

open PEqualNP.Outside.L_pcx_100_aux PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_100 : ¬ (∀ Mc : Finset (Fin 5) → Prop, (∀ Ymc : Finset (Fin 5), Mc Ymc ↔ ((∀ umc ∈ Ymc, ∀ wmc ∈ Ymc, ¬ (wmc = umc + 1 ∨ umc = wmc + 1)) ∧ ∀ zmc : Fin 5, zmc ∉ Ymc → ∃ ymc ∈ Ymc, (zmc = ymc + 1 ∨ ymc = zmc + 1))) → ∀ Qc : Finset (Fin 5) → Prop, (∀ Yqc : Finset (Fin 5), Qc Yqc ↔ ∃ Iqc : Finset (Fin 5), Mc Iqc ∧ ∃ wqc : Fin 5, wqc ∉ Iqc ∧ Yqc = insert wqc Iqc) → ∀ Fc : Set (PEqualNP.ProofComplexity.Clause ((Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)))), Fc = {C1c | ∃ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (Mc X1c ∨ Qc X1c) ∧ j1c < i1c ∧ (C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X1c), ((j1c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X1c), ((j1c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)})} ∪ {C2c | ∃ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (Mc X2c ∨ Qc X2c) ∧ C2c = insert ((((5, X2c), ((i2c, e2c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)))} ∪ {C3c | ∃ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (Mc X3c ∨ Qc X3c) ∧ v3c ∈ X3c ∧ C3c = {((((5, X3c), ((i3c, e3c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C4c | ∃ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (Mc X4c ∨ Qc X4c) ∧ j4c < i4c ∧ C4c = {((((5, X4c), ((i4c, e4c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C5c | ∃ (X5c : Finset (Fin 5)) (i5c : Fin 2), (Mc X5c ∨ Qc X5c) ∧ (C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, true), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((5, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, true), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)})} ∪ {C6c | ∃ (X6c : Finset (Fin 5)) (v6c : Fin 5), Mc X6c ∧ v6c ∈ X6c ∧ C6c = {((((2, ∅), ((0, false), (0, v6c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C7c | ∃ (X7c : Finset (Fin 5)) (i7c : Fin 2), Mc X7c ∧ C7c = {((((3, ∅), ((i7c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X7c), ((i7c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C8c | ∃ (X8c : Finset (Fin 5)) (i8c : Fin 2), Qc X8c ∧ (C8c = {((((7, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((3, ∅), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C8c = {((((7, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)})} ∪ {C9c | ∃ X9c : Finset (Fin 5), Qc X9c ∧ C9c = X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true))} → ¬ (∃ πc1, PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.restrictCNF Fc (fun zc : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)) => if zc.1.1 = 2 then (some false : Option Bool) else none)) πc1 ∧ ∀ Dc1 ∈ πc1, Dc1.card ≤ 3) ∧ (∃ πc2, PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.restrictCNF Fc (fun zc : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)) => if zc.1.1 = 2 then (some false : Option Bool) else none)) πc2 ∧ ∀ Dc2 ∈ πc2, Dc2.card ≤ 4)) := by
  intro wrong
  obtain ⟨π, ⟨der, he⟩, hw⟩ := (wrong M (fun _ => Iff.rfl) Q (fun _ => Iff.rfl) F rfl).2
  have ax : ∀ C ∈ restrictCNF F rho, C.card ≤ 4 → ClauseSat assign C := by
    rintro D ⟨C, hC, hr⟩ hwD
    exact sat_of_good (all_good C hC) hr hwD
  simpa [ClauseSat] using narrowSound ax der hw ∅ he
