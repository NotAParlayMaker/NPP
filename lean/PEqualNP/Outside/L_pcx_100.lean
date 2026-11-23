import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_100
open PEqualNP.ProofComplexity

abbrev V := (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))

abbrev Mc (X : Finset (Fin 5)) : Prop :=
  (∀ u ∈ X, ∀ w ∈ X, ¬ (w = u + 1 ∨ u = w + 1)) ∧
  ∀ z : Fin 5, z ∉ X → ∃ y ∈ X, z = y + 1 ∨ y = z + 1

abbrev Qc (X : Finset (Fin 5)) : Prop := X.card = 3

abbrev mcDecidable : DecidablePred Mc := fun X => by
  unfold Mc
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma boundary : ∀ X, Qc X ↔ ∃ I : Finset (Fin 5), Mc I ∧
    ∃ w : Fin 5, w ∉ I ∧ X = insert w I := by
  let _ : DecidablePred Mc := mcDecidable
  decide

def restriction (v : V) : Option Bool :=
  if v.1.1 = 2 then some false else none

-- Use only the second gate at the output. On positive rows, its side and value
-- wires are true. Every selector and every wire of the first gate is false.
def model (v : V) : Bool :=
  decide (v.2.1.1 = 1 ∧ (v.1.1 = 3 ∨
    ((v.1.1 = 5 ∨ v.1.1 = 6 ∨ v.1.1 = 7) ∧ Qc v.1.2)))

def safe (C : Clause V) : Bool :=
  match restrictClause restriction C with
  | none => true
  | some D => decide (D.card ≤ 4 → ∃ l ∈ D, model l.1 = l.2)

lemma bounded_sound {F : Set (Clause V)} {π : List (Clause V)}
    (derivation : IsDerivation F π) (bounds : ∀ D ∈ π, D.card ≤ 4)
    (axioms : ∀ D ∈ F, D.card ≤ 4 → ClauseSat model D) :
    ∀ D ∈ π, ClauseSat model D := by
  induction derivation with
  | nil => simp
  | @ax π C prev hC ih =>
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact axioms _ hC (bounds _ (List.mem_cons_self ..))
      · exact ih (fun E hE => bounds E (List.mem_cons_of_mem _ hE)) D hD
  | @res π C D R prev hC hD hR ih =>
      intro E hE
      have keep := ih (fun K hK => bounds K (List.mem_cons_of_mem _ hK))
      rcases List.mem_cons.mp hE with rfl | hE
      · obtain ⟨v, _, _, rfl⟩ := hR
        cases hv : model v with
        | false =>
          obtain ⟨l, hl, ht⟩ := keep C hC
          refine ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hl⟩), ht⟩
          rintro rfl
          simp [hv] at ht
        | true =>
          obtain ⟨l, hl, ht⟩ := keep D hD
          refine ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl⟩), ht⟩
          rintro rfl
          simp [hv] at ht
      · exact keep E hE

def family1 : Set (Clause V) :=
  {C1c | ∃ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (Mc X1c ∨ Qc X1c) ∧ j1c < i1c ∧ (C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), false)})}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_1_1 : ∀ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (Mc X1c ∨ Qc X1c) ∧ j1c < i1c → safe ({((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), true)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_1_2 : ∀ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (Mc X1c ∨ Qc X1c) ∧ j1c < i1c → safe ({((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), true)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_1_3 : ∀ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (Mc X1c ∨ Qc X1c) ∧ j1c < i1c → safe ({((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), false)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family1_safe {C : Clause V} (h : C ∈ family1) : safe C = true := by
  obtain ⟨X1c, i1c, e1c, j1c, h⟩ := h
  obtain ⟨hr, hj, h⟩ := h
  rcases h with rfl | rfl | rfl
  · exact safe_1_1 X1c i1c e1c j1c ⟨hr, hj⟩
  · exact safe_1_2 X1c i1c e1c j1c ⟨hr, hj⟩
  · exact safe_1_3 X1c i1c e1c j1c ⟨hr, hj⟩

def family2 : Set (Clause V) :=
  {C2c | ∃ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (Mc X2c ∨ Qc X2c) ∧ C2c = insert ((((5, X2c), ((i2c, e2c), (0, 0))) : V), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : V), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : V), true)))}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_2_1 : ∀ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (Mc X2c ∨ Qc X2c) → safe (insert ((((5, X2c), ((i2c, e2c), (0, 0))) : V), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : V), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : V), true)))) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family2_safe {C : Clause V} (h : C ∈ family2) : safe C = true := by
  obtain ⟨X2c, i2c, e2c, h⟩ := h
  obtain ⟨hr, h⟩ := h
  subst C
  exact safe_2_1 X2c i2c e2c hr

def family3 : Set (Clause V) :=
  {C3c | ∃ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (Mc X3c ∨ Qc X3c) ∧ v3c ∈ X3c ∧ C3c = {((((5, X3c), ((i3c, e3c), (0, 0))) : V), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : V), false)}}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_3_1 : ∀ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (Mc X3c ∨ Qc X3c) ∧ v3c ∈ X3c → safe ({((((5, X3c), ((i3c, e3c), (0, 0))) : V), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : V), false)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family3_safe {C : Clause V} (h : C ∈ family3) : safe C = true := by
  obtain ⟨X3c, i3c, e3c, v3c, h⟩ := h
  obtain ⟨hr, hv, h⟩ := h
  subst C
  exact safe_3_1 X3c i3c e3c v3c ⟨hr, hv⟩

def family4 : Set (Clause V) :=
  {C4c | ∃ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (Mc X4c ∨ Qc X4c) ∧ j4c < i4c ∧ C4c = {((((5, X4c), ((i4c, e4c), (0, 0))) : V), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : V), false)}}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_4_1 : ∀ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (Mc X4c ∨ Qc X4c) ∧ j4c < i4c → safe ({((((5, X4c), ((i4c, e4c), (0, 0))) : V), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : V), false)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family4_safe {C : Clause V} (h : C ∈ family4) : safe C = true := by
  obtain ⟨X4c, i4c, e4c, j4c, h⟩ := h
  obtain ⟨hr, hj, h⟩ := h
  subst C
  exact safe_4_1 X4c i4c e4c j4c ⟨hr, hj⟩

def family5 : Set (Clause V) :=
  {C5c | ∃ (X5c : Finset (Fin 5)) (i5c : Fin 2), (Mc X5c ∨ Qc X5c) ∧ (C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, false), (0, 0))) : V), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), true), ((((5, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), false)})}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_5_1 : ∀ (X5c : Finset (Fin 5)) (i5c : Fin 2), (Mc X5c ∨ Qc X5c) → safe ({((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, false), (0, 0))) : V), true)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_5_2 : ∀ (X5c : Finset (Fin 5)) (i5c : Fin 2), (Mc X5c ∨ Qc X5c) → safe ({((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), true)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_5_3 : ∀ (X5c : Finset (Fin 5)) (i5c : Fin 2), (Mc X5c ∨ Qc X5c) → safe ({((((6, X5c), ((i5c, false), (0, 0))) : V), true), ((((5, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), false)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family5_safe {C : Clause V} (h : C ∈ family5) : safe C = true := by
  obtain ⟨X5c, i5c, h⟩ := h
  obtain ⟨hr, h⟩ := h
  rcases h with rfl | rfl | rfl
  · exact safe_5_1 X5c i5c hr
  · exact safe_5_2 X5c i5c hr
  · exact safe_5_3 X5c i5c hr

def family6 : Set (Clause V) :=
  {C6c | ∃ (X6c : Finset (Fin 5)) (v6c : Fin 5), Mc X6c ∧ v6c ∈ X6c ∧ C6c = {((((2, ∅), ((0, false), (0, v6c))) : V), false)}}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_6_1 : ∀ (X6c : Finset (Fin 5)) (v6c : Fin 5), Mc X6c ∧ v6c ∈ X6c → safe ({((((2, ∅), ((0, false), (0, v6c))) : V), false)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family6_safe {C : Clause V} (h : C ∈ family6) : safe C = true := by
  obtain ⟨X6c, v6c, h⟩ := h
  obtain ⟨hr, hj, h⟩ := h
  subst C
  exact safe_6_1 X6c v6c ⟨hr, hj⟩

def family7 : Set (Clause V) :=
  {C7c | ∃ (X7c : Finset (Fin 5)) (i7c : Fin 2), Mc X7c ∧ C7c = {((((3, ∅), ((i7c, false), (0, 0))) : V), false), ((((6, X7c), ((i7c, false), (0, 0))) : V), false)}}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_7_1 : ∀ (X7c : Finset (Fin 5)) (i7c : Fin 2), Mc X7c → safe ({((((3, ∅), ((i7c, false), (0, 0))) : V), false), ((((6, X7c), ((i7c, false), (0, 0))) : V), false)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family7_safe {C : Clause V} (h : C ∈ family7) : safe C = true := by
  obtain ⟨X7c, i7c, h⟩ := h
  obtain ⟨hr, h⟩ := h
  subst C
  exact safe_7_1 X7c i7c hr

def family8 : Set (Clause V) :=
  {C8c | ∃ (X8c : Finset (Fin 5)) (i8c : Fin 2), Qc X8c ∧ (C8c = {((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((3, ∅), ((i8c, false), (0, 0))) : V), true)} ∨ C8c = {((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((6, X8c), ((i8c, false), (0, 0))) : V), true)})}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_8_1 : ∀ (X8c : Finset (Fin 5)) (i8c : Fin 2), Qc X8c → safe ({((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((3, ∅), ((i8c, false), (0, 0))) : V), true)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_8_2 : ∀ (X8c : Finset (Fin 5)) (i8c : Fin 2), Qc X8c → safe ({((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((6, X8c), ((i8c, false), (0, 0))) : V), true)}) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family8_safe {C : Clause V} (h : C ∈ family8) : safe C = true := by
  obtain ⟨X8c, i8c, h⟩ := h
  obtain ⟨hr, h⟩ := h
  rcases h with rfl | rfl
  · exact safe_8_1 X8c i8c hr
  · exact safe_8_2 X8c i8c hr

def family9 : Set (Clause V) :=
  {C9c | ∃ X9c : Finset (Fin 5), Qc X9c ∧ C9c = X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : V), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : V), true))}

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma safe_9_1 : ∀ X9c : Finset (Fin 5), Qc X9c → safe (X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : V), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : V), true))) = true := by
  let _ : DecidablePred Mc := mcDecidable
  decide

lemma family9_safe {C : Clause V} (h : C ∈ family9) : safe C = true := by
  obtain ⟨X9c, h⟩ := h
  obtain ⟨hr, h⟩ := h
  subst C
  exact safe_9_1 X9c hr

def formula : Set (Clause V) := family1 ∪ family2 ∪ family3 ∪ family4 ∪ family5 ∪ family6 ∪ family7 ∪ family8 ∪ family9

lemma safety {C : Clause V} (h : C ∈ formula) : safe C = true := by
  simp only [formula, Set.mem_union, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h
  · exact family1_safe h
  · exact family2_safe h
  · exact family3_safe h
  · exact family4_safe h
  · exact family5_safe h
  · exact family6_safe h
  · exact family7_safe h
  · exact family8_safe h
  · exact family9_safe h

lemma axiom_sound (D : Clause V) (hD : D ∈ restrictCNF formula restriction)
    (hsize : D.card ≤ 4) : ClauseSat model D := by
  obtain ⟨C, hC, hres⟩ := hD
  have h := safety hC
  simp only [safe, hres, decide_eq_true_eq] at h
  exact h hsize

end PEqualNP.Outside.L_pcx_100

open PEqualNP.Outside.L_pcx_100

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_pcx_100 : ¬ (∀ Mc : Finset (Fin 5) → Prop, (∀ Ymc : Finset (Fin 5), Mc Ymc ↔ ((∀ umc ∈ Ymc, ∀ wmc ∈ Ymc, ¬ (wmc = umc + 1 ∨ umc = wmc + 1)) ∧ ∀ zmc : Fin 5, zmc ∉ Ymc → ∃ ymc ∈ Ymc, (zmc = ymc + 1 ∨ ymc = zmc + 1))) → ∀ Qc : Finset (Fin 5) → Prop, (∀ Yqc : Finset (Fin 5), Qc Yqc ↔ ∃ Iqc : Finset (Fin 5), Mc Iqc ∧ ∃ wqc : Fin 5, wqc ∉ Iqc ∧ Yqc = insert wqc Iqc) → ∀ Fc : Set (PEqualNP.ProofComplexity.Clause ((Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)))), Fc = {C1c | ∃ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (Mc X1c ∨ Qc X1c) ∧ j1c < i1c ∧ (C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X1c), ((j1c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X1c), ((j1c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)})} ∪ {C2c | ∃ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (Mc X2c ∨ Qc X2c) ∧ C2c = insert ((((5, X2c), ((i2c, e2c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)))} ∪ {C3c | ∃ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (Mc X3c ∨ Qc X3c) ∧ v3c ∈ X3c ∧ C3c = {((((5, X3c), ((i3c, e3c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C4c | ∃ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (Mc X4c ∨ Qc X4c) ∧ j4c < i4c ∧ C4c = {((((5, X4c), ((i4c, e4c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C5c | ∃ (X5c : Finset (Fin 5)) (i5c : Fin 2), (Mc X5c ∨ Qc X5c) ∧ (C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, true), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((5, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, true), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)})} ∪ {C6c | ∃ (X6c : Finset (Fin 5)) (v6c : Fin 5), Mc X6c ∧ v6c ∈ X6c ∧ C6c = {((((2, ∅), ((0, false), (0, v6c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C7c | ∃ (X7c : Finset (Fin 5)) (i7c : Fin 2), Mc X7c ∧ C7c = {((((3, ∅), ((i7c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X7c), ((i7c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C8c | ∃ (X8c : Finset (Fin 5)) (i8c : Fin 2), Qc X8c ∧ (C8c = {((((7, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((3, ∅), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C8c = {((((7, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)})} ∪ {C9c | ∃ X9c : Finset (Fin 5), Qc X9c ∧ C9c = X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true))} → ¬ (∃ πc1, PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.restrictCNF Fc (fun zc : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)) => if zc.1.1 = 2 then (some false : Option Bool) else none)) πc1 ∧ ∀ Dc1 ∈ πc1, Dc1.card ≤ 3) ∧ (∃ πc2, PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.restrictCNF Fc (fun zc : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)) => if zc.1.1 = 2 then (some false : Option Bool) else none)) πc2 ∧ ∀ Dc2 ∈ πc2, Dc2.card ≤ 4)) := by
  intro h

  have hw := h Mc (fun _ => Iff.rfl) Qc boundary formula rfl
  obtain ⟨π, hπ, hwidth⟩ := hw.2
  obtain ⟨l, hl, _⟩ := bounded_sound hπ.1 hwidth axiom_sound ∅ hπ.2
  exact Finset.notMem_empty l hl
