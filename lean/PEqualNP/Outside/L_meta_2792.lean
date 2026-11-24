import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2792

open PEqualNP.CircuitLowerBounds

lemma foldl_prefix (L : List Gate) (x : List Bool) :
    x <+: L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := by
  induction L generalizing x with
  | nil => exact List.prefix_refl x
  | cons g L ih => exact (List.prefix_append x _).trans (ih _)

lemma foldl_length (L : List Gate) (x : List Bool) :
    (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + L.length := by
  induction L generalizing x with
  | nil => simp
  | cons g L ih =>
    rw [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_cons,
      List.length_nil]
    omega

lemma wires_split (C : Circuit) (x : List Bool) (k : ℕ) (g : Gate)
    (h : C.gates[k]? = some g) :
    ∃ w tail : List Bool, w.length = x.length + k ∧
      C.wires x = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] ++ tail := by
  obtain ⟨hk, hg⟩ := List.getElem?_eq_some_iff.mp h
  have hsplit : C.gates = C.gates.take k ++ g :: C.gates.drop (k + 1) := by
    rw [← hg, List.getElem_cons_drop, List.take_append_drop]
  obtain ⟨tail, ht⟩ := foldl_prefix (C.gates.drop (k + 1))
    ((C.gates.take k).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x ++
      [g.op.eval (g.inputs.map fun i =>
        ((C.gates.take k).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)])
  refine ⟨(C.gates.take k).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x, tail, ?_, ?_⟩
  · rw [foldl_length, List.length_take, Nat.min_eq_left hk.le]
  · rw [ht]
    unfold Circuit.wires
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]

lemma val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  obtain ⟨t, ht⟩ := foldl_prefix C.gates x
  unfold Circuit.wires
  rw [← ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma val_out (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  apply List.getD_eq_default
  unfold Circuit.wires
  rw [foldl_length]
  exact hi

lemma val_gate (C : Circuit) (x : List Bool) (m k : ℕ) (g : Gate) (hm : x.length = m)
    (h : C.gates[k]? = some g) (hin : ∀ i ∈ g.inputs, i < m + k) :
    (C.wires x).getD (m + k) false
      = g.op.eval (g.inputs.map fun i => (C.wires x).getD i false) := by
  subst hm
  obtain ⟨w, tail, hw, he⟩ := wires_split C x k g h
  rw [he]
  have h1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] ++ tail).getD
      (x.length + k) false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    rw [← hw]
    simp [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < w.length := by rw [hw]; exact hin i hi
  simp [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left hlt]

lemma val_gate2 (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) (x : List Bool)
    (m k a b : ℕ) (g : Gate) (hm : x.length = m)
    (h : C.gates[k]? = some g) (hab : g.inputs = [a, b]) (ha : a < b) (hb : b < m + k) :
    (g.op = GateOp.and ∧ (C.wires x).getD (m + k) false
        = ((C.wires x).getD a false && (C.wires x).getD b false)) ∨
    (g.op = GateOp.or ∧ (C.wires x).getD (m + k) false
        = ((C.wires x).getD a false || (C.wires x).getD b false)) := by
  have hv := val_gate C x m k g hm h (by
    intro i hi
    rw [hab] at hi
    simp at hi
    omega)
  have hmem : g ∈ C.gates := List.mem_of_getElem? h
  rcases (hM g hmem).1 with hop | hop
  · left
    refine ⟨hop, ?_⟩
    rw [hv, hop, hab]
    simp [GateOp.eval]
  · right
    have hop' : g.op = GateOp.or := hop
    refine ⟨hop', ?_⟩
    rw [hv, hop', hab]
    simp [GateOp.eval]

lemma mono (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hI : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a < b ∧ b < n + n + k)
    (x x' : List Bool) (hl : x.length = n + n) (hl' : x'.length = n + n)
    (hle : ∀ i, x.getD i false = true → x'.getD i false = true) :
    ∀ i, (C.wires x).getD i false = true → (C.wires x').getD i false = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases h1 : i < n + n
    · rw [val_input C x i (by omega)] at h
      rw [val_input C x' i (by omega)]
      exact hle i h
    · by_cases h2 : i < n + n + C.gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + n + k := ⟨i - (n + n), by omega⟩
        have hk : k < C.gates.length := by omega
        have hg : C.gates[k]? = some (C.gates[k]) := List.getElem?_eq_getElem hk
        obtain ⟨a, b, hab, hlt, hb⟩ := hI k _ hg
        rcases val_gate2 C hM x (n + n) k a b _ hl hg hab hlt hb with ⟨hop, e⟩ | ⟨hop, e⟩
        · rcases val_gate2 C hM x' (n + n) k a b _ hl' hg hab hlt hb with ⟨_, e'⟩ | ⟨hop', _⟩
          · rw [e] at h
            rw [e']
            rw [Bool.and_eq_true] at h ⊢
            exact ⟨ih a (by omega) h.1, ih b (by omega) h.2⟩
          · rw [hop] at hop'
            cases hop'
        · rcases val_gate2 C hM x' (n + n) k a b _ hl' hg hab hlt hb with ⟨hop', _⟩ | ⟨_, e'⟩
          · rw [hop] at hop'
            cases hop'
          · rw [e] at h
            rw [e']
            rw [Bool.or_eq_true] at h ⊢
            rcases h with h | h
            · exact Or.inl (ih a (by omega) h)
            · exact Or.inr (ih b (by omega) h)
      · rw [val_out C x i (by omega)] at h
        cases h

lemma getD_app (n : ℕ) (x y : Fin n → Bool) (i : ℕ) :
    (List.ofFn x ++ List.ofFn y).getD i false =
      if h : i < n then x ⟨i, h⟩ else if h' : i - n < n then y ⟨i - n, h'⟩ else false := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, h]
  · by_cases h' : i - n < n
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h, h', Nat.le_of_not_lt h]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h, h', Nat.le_of_not_lt h]

lemma app_mono (n : ℕ) (x x' y y' : Fin n → Bool) (hx : ∀ j, x j = true → x' j = true)
    (hy : ∀ j, y j = true → y' j = true) (i : ℕ) :
    (List.ofFn x ++ List.ofFn y).getD i false = true →
      (List.ofFn x' ++ List.ofFn y').getD i false = true := by
  rw [getD_app, getD_app]
  by_cases h : i < n
  · simp only [h, dite_true]
    exact hx _
  · by_cases h' : i - n < n
    · simp only [h, h', dite_true, dite_false]
      exact hy _
    · simp [h, h']

lemma mono' (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hI : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a < b ∧ b < n + n + k)
    (x x' y y' : Fin n → Bool) (hx : ∀ j, x j = true → x' j = true)
    (hy : ∀ j, y j = true → y' j = true) (i : ℕ) :
    (C.wires (List.ofFn x ++ List.ofFn y)).getD i false = true →
      (C.wires (List.ofFn x' ++ List.ofFn y')).getD i false = true :=
  mono n C hM hI _ _ (by simp) (by simp) (app_mono n x x' y y' hx hy) i

lemma yindep (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hI : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a < b ∧ b < n + n + k)
    (c : ℕ)
    (hc : ∀ x : Fin n → Bool,
      ¬ (C.wires (List.ofFn x ++ List.replicate n false)).getD c false ≠
        (C.wires (List.ofFn x ++ List.replicate n true)).getD c false)
    (x y : Fin n → Bool) :
    ((C.wires (List.ofFn x ++ List.ofFn y)).getD c false = true ↔
      (C.wires (List.ofFn x ++ List.ofFn (fun _ : Fin n => false))).getD c false = true) := by
  have e := hc x
  rw [not_not, ← List.ofFn_const, ← List.ofFn_const] at e
  constructor
  · intro h
    rw [e]
    exact mono' n C hM hI x x y (fun _ => true) (fun _ hj => hj) (fun _ _ => rfl) c h
  · intro h
    exact mono' n C hM hI x x (fun _ => false) y (fun _ hj => hj)
      (fun _ hj => by cases hj) c h

lemma xindep (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hI : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a < b ∧ b < n + n + k)
    (c : ℕ)
    (hc : ∀ y : Fin n → Bool,
      ¬ (C.wires (List.replicate n false ++ List.ofFn y)).getD c false ≠
        (C.wires (List.replicate n true ++ List.ofFn y)).getD c false)
    (x y : Fin n → Bool) :
    ((C.wires (List.ofFn x ++ List.ofFn y)).getD c false = true ↔
      (C.wires (List.ofFn (fun _ : Fin n => false) ++ List.ofFn y)).getD c false = true) := by
  have e := hc y
  rw [not_not, ← List.ofFn_const, ← List.ofFn_const] at e
  constructor
  · intro h
    rw [e]
    exact mono' n C hM hI x (fun _ => true) y y (fun _ _ => rfl) (fun _ hj => hj) c h
  · intro h
    exact mono' n C hM hI (fun _ => false) x y y (fun _ hj => by cases hj)
      (fun _ hj => hj) c h

end PEqualNP.Outside.L_meta_2792

theorem PEqualNP.Outside.L_meta_2792 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 → ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x1 + x5) →       (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ∉ x3 → ¬((∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.false)).getD x11 Bool.false ≠ (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.true)).getD x11 Bool.false) ∨ ∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x13)).getD x11 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x13)).getD x11 Bool.false)) →         ∃ (x7 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),           (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.1 x8 = Bool.true} ∧ x7 (x1 + ↑x8) = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.2 x8 = Bool.true}) ∧             (∀ x8 < x2.size,                 ∃ x10 < x1 + x1 + x8,                   ∃ x11 < x1 + x1 + x8,                     have x12 : Set ((Fin x1 → Bool) × (Fin x1 → Bool)) := x7 (x1 + x1 + x8);                     x12 = x7 x10 ∪ x7 x11 ∨ x12 = x7 x10 ∨ x12 = ∅ ∨ x12 = x7 x10 ∩ x7 x11 ∧ (x8 ∈ x3 ∨ ∃ (x13 : Set (Fin x1 → Bool)) (x14 : Set (Fin x1 → Bool)), x7 x10 = x13 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x14)) ∧               ∀ (x8 x9 : Fin x1 → Bool), (x8, x9) ∈ x7 x2.output ↔ PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 (Fin.append x8 x9) = Bool.true := by
  intro n C S hM hI hS
  refine ⟨fun i => {p | (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD i false = true},
    ?_, ?_, ?_⟩
  · intro i
    constructor
    · ext p
      simp only [Set.mem_ofPred_eq]
      rw [PEqualNP.Outside.L_meta_2792.val_input C _ _ (by simp; omega),
        PEqualNP.Outside.L_meta_2792.getD_app]
      simp
    · ext p
      simp only [Set.mem_ofPred_eq]
      rw [PEqualNP.Outside.L_meta_2792.val_input C _ _ (by simp),
        PEqualNP.Outside.L_meta_2792.getD_app]
      simp
  · intro k hk
    have hk' : k < C.gates.length := hk
    have hg : C.gates[k]? = some (C.gates[k]) := List.getElem?_eq_getElem hk'
    obtain ⟨a, b, hab, hlt, hb⟩ := hI k _ hg
    have key := fun p : (Fin n → Bool) × (Fin n → Bool) =>
      PEqualNP.Outside.L_meta_2792.val_gate2 C hM (List.ofFn p.1 ++ List.ofFn p.2) (n + n) k a b
        _ (by simp) hg hab hlt hb
    by_cases hop : (C.gates[k]).op = PEqualNP.CircuitLowerBounds.GateOp.and
    · have keyA : ∀ p : (Fin n → Bool) × (Fin n → Bool),
          (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD (n + n + k) false =
            ((C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD a false &&
              (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD b false) := by
        intro p
        rcases key p with ⟨_, e⟩ | ⟨hop', _⟩
        · exact e
        · rw [hop] at hop'
          cases hop'
      by_cases hkS : k ∈ S
      · refine ⟨a, by omega, b, by omega, Or.inr (Or.inr (Or.inr ⟨?_, Or.inl hkS⟩))⟩
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
        rw [keyA p, Bool.and_eq_true]
      · have hneg := hS k _ hg hop hkS
        rw [not_or] at hneg
        obtain ⟨h1, h2⟩ := hneg
        rw [hab] at h1 h2
        push Not at h1 h2
        obtain ⟨c, hc, hcy⟩ := h1
        obtain ⟨d, hd, hdx⟩ := h2
        have hcy' := PEqualNP.Outside.L_meta_2792.yindep n C hM hI c
          (fun x => by rw [not_not]; exact hcy x)
        have hdx' := PEqualNP.Outside.L_meta_2792.xindep n C hM hI d
          (fun y => by rw [not_not]; exact hdx y)
        have hprodc : {p : (Fin n → Bool) × (Fin n → Bool) |
            (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD c false = true} =
            {x : Fin n → Bool | (C.wires (List.ofFn x ++
              List.ofFn (fun _ : Fin n => false))).getD c false = true} ×ˢ Set.univ := by
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
          exact hcy' p.1 p.2
        have hprodd : {p : (Fin n → Bool) × (Fin n → Bool) |
            (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD d false = true} =
            Set.univ ×ˢ {y : Fin n → Bool | (C.wires (List.ofFn (fun _ : Fin n => false) ++
              List.ofFn y)).getD d false = true} := by
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
          exact hdx' p.1 p.2
        by_cases hcd : c = d
        · subst hcd
          have hconst : ∀ p : (Fin n → Bool) × (Fin n → Bool),
              ((C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD c false = true ↔
                (C.wires (List.ofFn (fun _ : Fin n => false) ++
                  List.ofFn (fun _ : Fin n => false))).getD c false = true) := by
            intro p
            rw [hcy' p.1 p.2, hdx' p.1 (fun _ => false)]
          by_cases hv : (C.wires (List.ofFn (fun _ : Fin n => false) ++
                  List.ofFn (fun _ : Fin n => false))).getD c false = true
          · have hother : ∃ e, e < n + n + k ∧ ∀ p : (Fin n → Bool) × (Fin n → Bool),
                ((C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD (n + n + k) false = true ↔
                  (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD e false = true) := by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with rfl | rfl
              · refine ⟨b, by omega, fun p => ?_⟩
                rw [keyA p, Bool.and_eq_true]
                have := (hconst p).mpr hv
                tauto
              · refine ⟨a, by omega, fun p => ?_⟩
                rw [keyA p, Bool.and_eq_true]
                have := (hconst p).mpr hv
                tauto
            obtain ⟨e, he, hee⟩ := hother
            refine ⟨e, he, e, he, Or.inr (Or.inl ?_)⟩
            ext p
            simp only [Set.mem_ofPred_eq]
            exact hee p
          · refine ⟨a, by omega, b, by omega, Or.inr (Or.inr (Or.inl ?_))⟩
            ext p
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            rw [keyA p, Bool.and_eq_true]
            have hcf : ¬ (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD c false = true :=
              fun h => hv ((hconst p).mp h)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · tauto
            · tauto
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
          have hcd' : (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
            rcases hc with rfl | rfl
            · rcases hd with rfl | rfl
              · exact absurd rfl hcd
              · exact Or.inl ⟨rfl, rfl⟩
            · rcases hd with rfl | rfl
              · exact Or.inr ⟨rfl, rfl⟩
              · exact absurd rfl hcd
          have hc' : c < n + n + k := by
            rcases hc with rfl | rfl
            · omega
            · omega
          have hd' : d < n + n + k := by
            rcases hd with rfl | rfl
            · omega
            · omega
          refine ⟨c, hc', d, hd', Or.inr (Or.inr (Or.inr ⟨?_, Or.inr ⟨_, _, hprodc, hprodd⟩⟩))⟩
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
          rw [keyA p, Bool.and_eq_true]
          rcases hcd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Iff.rfl
          · exact and_comm
    · have keyO : ∀ p : (Fin n → Bool) × (Fin n → Bool),
          (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD (n + n + k) false =
            ((C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD a false ||
              (C.wires (List.ofFn p.1 ++ List.ofFn p.2)).getD b false) := by
        intro p
        rcases key p with ⟨hop', _⟩ | ⟨_, e⟩
        · exact absurd hop' hop
        · exact e
      refine ⟨a, by omega, b, by omega, Or.inl ?_⟩
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      rw [keyO p, Bool.or_eq_true]
  · intro x y
    simp only [Set.mem_ofPred_eq]
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [List.ofFn_fin_append]
