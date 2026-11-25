import Mathlib
import PEqualNP.Defs

/-!
Relabelling the inputs of a circuit along the two embeddings. The new circuit has the same
gates with every wire index i remapped by r: a point input e p goes to p, a line input f l
goes to a + l, a gate wire 2m + k goes to a + b + k, and every other index (an input outside
the images, which is off in the mapped input, or a missing wire) goes to a + b + L, a wire that
never exists and so reads false. By induction over the gates, the new wire r i always carries
the value of old wire i.
-/

namespace PEqualNP.Outside.L_meta_6567

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

def pre1 (e : Fin a ↪ Fin m) (i : ℕ) : Option (Fin a) :=
  (List.finRange a).find? (fun p => (e p : ℕ) == i)

def r (a b m L : ℕ) (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin m) (i : ℕ) : ℕ :=
  if i < m then (pre1 e i).elim (a + b + L) (fun p => p.val)
  else if i < 2 * m then (pre1 f (i - m)).elim (a + b + L) (fun l => a + l.val)
  else if i < 2 * m + L then i - 2 * m + (a + b) else a + b + L

def mapG (r : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map r }

variable {a b m L : ℕ} {e : Fin a ↪ Fin m} {f : Fin b ↪ Fin m}

theorem pre1_some {c : ℕ} {g : Fin c ↪ Fin m} {i : ℕ} {p : Fin c} (h : pre1 g i = some p) :
    (g p : ℕ) = i := by
  have := List.find?_some h
  simpa using this

theorem pre1_none {c : ℕ} {g : Fin c ↪ Fin m} {i : ℕ} (h : pre1 g i = none) (p : Fin c) :
    (g p : ℕ) ≠ i := by
  have := List.find?_eq_none.1 h p (List.mem_finRange p)
  simpa using this

theorem r_n1 (i : ℕ) (h : i < m) (hq : pre1 e i = none) : r a b m L e f i = a + b + L := by
  unfold r; rw [if_pos h, hq]; rfl

theorem r_s1 (i : ℕ) (h : i < m) (p : Fin a) (hq : pre1 e i = some p) :
    r a b m L e f i = p.val := by
  unfold r; rw [if_pos h, hq]; rfl

theorem r_n2 (i : ℕ) (h : ¬i < m) (h2 : i < 2 * m) (hq : pre1 f (i - m) = none) :
    r a b m L e f i = a + b + L := by
  unfold r; rw [if_neg h, if_pos h2, hq]; rfl

theorem r_s2 (i : ℕ) (h : ¬i < m) (h2 : i < 2 * m) (l : Fin b) (hq : pre1 f (i - m) = some l) :
    r a b m L e f i = a + l.val := by
  unfold r; rw [if_neg h, if_pos h2, hq]; rfl

theorem r_3 (i : ℕ) (h : 2 * m ≤ i) (h3 : i < 2 * m + L) : r a b m L e f i = i - 2 * m + (a + b) := by
  unfold r; rw [if_neg (by omega), if_neg (by omega), if_pos h3]

theorem r_4 (i : ℕ) (h : 2 * m + L ≤ i) : r a b m L e f i = a + b + L := by
  unfold r; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem r_cases (i : ℕ) : r a b m L e f i < a + b ∨ r a b m L e f i = a + b + L ∨
    (2 * m ≤ i ∧ i < 2 * m + L ∧ r a b m L e f i = i - 2 * m + (a + b)) := by
  by_cases h1 : i < m
  · rcases hq : pre1 e i with _ | p
    · rw [r_n1 i h1 hq]; omega
    · rw [r_s1 i h1 p hq]; have := p.isLt; omega
  · by_cases h2 : i < 2 * m
    · rcases hq : pre1 f (i - m) with _ | l
      · rw [r_n2 i h1 h2 hq]; omega
      · rw [r_s2 i h1 h2 l hq]; have := l.isLt; omega
    · by_cases h3 : i < 2 * m + L
      · rw [r_3 i (by omega) h3]; omega
      · rw [r_4 i (by omega)]; omega

theorem r_big (i : ℕ) (h : 2 * m ≤ i) : a + b ≤ r a b m L e f i := by
  by_cases h3 : i < 2 * m + L
  · rw [r_3 i h h3]; omega
  · rw [r_4 i (by omega)]; omega

theorem r_gate (k : ℕ) (hk : k < L) : r a b m L e f (2 * m + k) = a + b + k := by
  rw [r_3 _ (by omega) (by omega)]; omega

theorem getD_snoc (l : List Bool) (x : Bool) (j : ℕ) :
    (l ++ [x]).getD j false = if j = l.length then x else l.getD j false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2 h2
  · omega
  · rfl
  · subst h2; simp
  · obtain ⟨t, ht⟩ : ∃ t, j - l.length = t + 1 := ⟨j - l.length - 1, by omega⟩
    rw [ht, List.getElem?_eq_none (by omega : l.length ≤ j)]
    simp

theorem inc_len {n k : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin k)) :
    (incidenceInput X Y).length = n + k := by
  simp [incidenceInput]

theorem inc_lt {n k : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin k)) (i : ℕ) (h : i < n) :
    (incidenceInput X Y).getD i false = decide ((⟨i, h⟩ : Fin n) ∈ X) := by
  rw [List.getD_eq_getElem _ _ (by rw [inc_len]; omega)]
  unfold incidenceInput
  rw [List.getElem_append_left (by simp; omega)]
  simp

theorem inc_mid {n k : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin k)) (i : ℕ) (h1 : n ≤ i)
    (h2 : i < n + k) :
    (incidenceInput X Y).getD i false = decide ((⟨i - n, by omega⟩ : Fin k) ∈ Y) := by
  rw [List.getD_eq_getElem _ _ (by rw [inc_len]; omega)]
  unfold incidenceInput
  rw [List.getElem_append_right (by simp; omega)]
  simp

theorem inc_ge {n k : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin k)) (i : ℕ) (h : n + k ≤ i) :
    (incidenceInput X Y).getD i false = false :=
  List.getD_eq_default _ _ (by rw [inc_len]; omega)

theorem base (X : Finset (Fin a)) (Y : Finset (Fin b)) (i : ℕ) :
    (incidenceInput X Y).getD (r a b m L e f i) false =
      (incidenceInput (X.map e) (Y.map f)).getD i false := by
  by_cases h1 : i < m
  · rw [inc_lt _ _ i h1]
    rcases hq : pre1 e i with _ | p
    · rw [r_n1 i h1 hq, inc_ge _ _ _ (by omega)]
      symm
      rw [decide_eq_false_iff_not, Finset.mem_map]
      rintro ⟨p, _, hp⟩
      exact pre1_none hq p (by rw [hp])
    · rw [r_s1 i h1 p hq, inc_lt _ _ _ p.isLt]
      have he : (⟨i, h1⟩ : Fin m) = e p := Fin.ext (pre1_some hq).symm
      rw [he]; simp
  · by_cases h2 : i < 2 * m
    · rw [inc_mid _ _ i (by omega) (by omega)]
      rcases hq : pre1 f (i - m) with _ | l
      · rw [r_n2 i h1 h2 hq, inc_ge _ _ _ (by omega)]
        symm
        rw [decide_eq_false_iff_not, Finset.mem_map]
        rintro ⟨l, _, hl⟩
        exact pre1_none hq l (by rw [hl])
      · rw [r_s2 i h1 h2 l hq, inc_mid _ _ _ (by omega) (by have := l.isLt; omega)]
        have he : (⟨i - m, by omega⟩ : Fin m) = f l := Fin.ext (pre1_some hq).symm
        have hl2 : (⟨a + l.val - a, by have := l.isLt; omega⟩ : Fin b) = l := Fin.ext (by simp)
        rw [he, hl2]; simp
    · have h3 := r_big (L := L) (e := e) (f := f) (b := b) i (by omega)
      rw [inc_ge _ _ _ h3, inc_ge _ _ _ (by omega)]

theorem main_inv (L : ℕ) (gs : List Gate) : ∀ (W6 W8 : List Bool) (k : ℕ),
    W6.length = 2 * m + k → W8.length = a + b + k → k + gs.length = L →
    (∀ i, W8.getD (r a b m L e f i) false = W6.getD i false) →
    ∀ i, ((gs.map (mapG (r a b m L e f))).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W8).getD
        (r a b m L e f i) false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W6).getD
        i false := by
  induction gs with
  | nil => intro W6 W8 k _ _ _ h i; exact h i
  | cons g gs ih =>
    intro W6 W8 k h6 h8 hk h
    simp only [List.map_cons, List.foldl_cons]
    apply ih _ _ (k + 1) (by simp [h6]; omega) (by simp [h8]; omega)
      (by simp only [List.length_cons] at hk; omega)
    intro i
    have hv : (mapG (r a b m L e f) g).op.eval ((mapG (r a b m L e f) g).inputs.map
        fun j => W8.getD j false) = g.op.eval (g.inputs.map fun j => W6.getD j false) := by
      simp only [mapG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    rw [getD_snoc, getD_snoc, hv, h8, h6]
    have hkL : k < L := by simp only [List.length_cons] at hk; omega
    by_cases hi : i = 2 * m + k
    · subst hi
      rw [r_gate k hkL, if_pos rfl, if_pos rfl]
    · rw [if_neg hi, if_neg, h i]
      intro hc
      rcases r_cases (L := L) (e := e) (f := f) i with c | c | ⟨_, _, c⟩ <;> omega

end PEqualNP.Outside.L_meta_6567

theorem PEqualNP.Outside.L_meta_6567 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 ↪ Fin x3) (x5 : Fin x2 ↪ Fin x3) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size = x6.size ∧ ∀ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), x8.eval (PEqualNP.GenericRejection.incidenceInput x9 x10) = x6.eval (PEqualNP.GenericRejection.incidenceInput (Finset.map x4 x9) (Finset.map x5 x10)) := by
  intro a b m e f C hC
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_6567.mapG
    (PEqualNP.Outside.L_meta_6567.r a b m C.gates.length e f)),
    PEqualNP.Outside.L_meta_6567.r a b m C.gates.length e f C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := hC g0 hg0
    simpa [PEqualNP.Outside.L_meta_6567.mapG] using this
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro X Y
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    exact PEqualNP.Outside.L_meta_6567.main_inv C.gates.length C.gates _ _ 0
      (by rw [PEqualNP.Outside.L_meta_6567.inc_len]; omega)
      (by rw [PEqualNP.Outside.L_meta_6567.inc_len]; omega) (by omega)
      (PEqualNP.Outside.L_meta_6567.base X Y) C.output
