import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1961_aux

/- Source work/nested1962/Characterization.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover



def separates (C : Circuit) : Prop :=
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
      List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
  ∀ Q : Finset (Fin 13), Q.card = 4 →
    (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
    C.eval (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
      List.ofFn (fun v : Fin 13 => decide (∀ u ∈ Q, u - v ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false

def acceptable (C : Circuit) : Prop := Monotone2 C ∧ ReadsBack 26 C ∧ separates C

def onePair (C : Circuit) : Prop :=
  (∃ i j : ℕ, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ PEqualNP.EdgeOwnership.InCone 26 C i j) ∧
  (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) ∧
  PEqualNP.TopForm.andPairs 26 C ≤ 1

def postedClaim : Prop := ¬ (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → PEqualNP.TopForm.andPairs (26 : ℕ) x4 ≤ (1 : ℕ) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size)

theorem counterexample_is_minimal : postedClaim ↔
    ∃ C : Circuit, acceptable C ∧ C.size < 64 ∧ onePair C ∧
      ∀ D : Circuit, acceptable D → C.size ≤ D.size := by
  classical
  change (¬ ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → separates C → C.size < 64 →
    (∃ i j : ℕ, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ PEqualNP.EdgeOwnership.InCone 26 C i j) →
    (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
    PEqualNP.TopForm.andPairs 26 C ≤ 1 →
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ separates D ∧ D.size < C.size) ↔ _
  constructor
  · intro h
    by_contra noCandidate
    apply h
    intro C mono back sep small nested strict one
    by_contra noSmaller
    apply noCandidate
    refine ⟨C, ⟨mono, back, sep⟩, small, ⟨nested, strict, one⟩, ?_⟩
    rintro D ⟨trueMono, trueBack, trueSep⟩
    apply Nat.le_of_not_gt
    intro better
    exact noSmaller ⟨D, trueMono, trueBack, trueSep, better⟩
  · rintro ⟨C, ⟨mono, back, sep⟩, small, ⟨nested, strict, one⟩, least⟩ shrink
    obtain ⟨D, trueMono, trueBack, trueSep, better⟩ := shrink C mono back sep small nested strict one
    exact (Nat.not_lt_of_ge (least D ⟨trueMono, trueBack, trueSep⟩)) better

end OneNestedAnd

/- Source work/nested1962/NestedPairs.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem W_inp (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega)]; exact ih

theorem W_oob (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (W gs x).getD i false = false := by
  apply List.getD_eq_default; rw [W_len]; exact hi

theorem W_spec (gs : List Gate) (x : List Bool) : ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
    (W gs x).getD (x.length + k) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + k then (W gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro k g h; simp at h
  | append_singleton gs a ih =>
    intro k g h
    rw [W_snoc]
    rcases Nat.lt_or_ge k gs.length with hk | hk
    · rw [List.getElem?_append_left hk] at h
      rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih k g h]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < x.length + k
      · simp only [hi, if_true]
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
      · simp only [hi, if_false]
    · rcases Nat.lt_or_ge k (gs.length + 1) with hk1 | hk1
      · have hk2 : k = gs.length := by omega
        subst hk2
        have hag : a = g := by simpa using h
        subst hag
        rw [List.getD_append_right _ _ _ _ (by rw [W_len]), W_len]
        simp only [Nat.sub_self, List.getD_cons_zero]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + gs.length
        · simp only [hi, if_true]
          rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
        · simp only [hi, if_false]
          exact W_oob gs x i (by omega)
      · rw [List.getElem?_eq_none (by simp; omega)] at h
        cases h

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma gateAt_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  simp [gateAt, List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj]

lemma or_reader_true (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (k j : ℕ) (hk : k < j) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = .or) (reads : n + k ∈ (gateAt C j).inputs)
    (value : (C.wires x).getD (n + k) false = true) :
    (C.wires x).getD (n + j) false = true := by
  have spec := W_spec C.gates x j _ (gateAt_some C j hj)
  change (W C.gates x).getD (n + k) false = true at value
  change (W C.gates x).getD (n + j) false = true
  rw [hx, hop] at spec
  rw [spec]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
  refine ⟨true, ⟨n + k, reads, ?_⟩, rfl⟩
  rw [if_pos (Nat.add_lt_add_left hk n)]
  exact value

lemma and_between (n : ℕ) (C : Circuit) (mono : Monotone2 C) (i : ℕ)
    (x : List Bool) (hx : x.length = n)
    (value : (C.wires x).getD (n + i) false = true) :
    ∀ j, InCone n C i j → (C.wires x).getD (n + j) false = false →
      ∃ k, k < C.gates.length ∧ (gateAt C k).op = .and ∧ InCone n C i k := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro inj neg
    obtain ⟨hj, p, hp, reads, previous⟩ := (inCone_iff n C i j).mp inj
    have mem : gateAt C j ∈ C.gates := List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j hj⟩
    rcases (mono _ mem).1 with h | h
    · exact ⟨j, hj, h, inj⟩
    · have prior : (C.wires x).getD (n + p) false = false := by
        apply Bool.eq_false_iff.mpr
        intro positive
        have force := or_reader_true n C x hx p j hp hj h reads positive
        rw [neg] at force
        contradiction
      rcases previous with eq | ancestor
      · subst p
        rw [value] at prior
        contradiction
      · exact ih p hp ancestor prior

theorem live_negative_and_count (n : ℕ) (C : Circuit) (mono : Monotone2 C) (j : ℕ)
    (hout : C.output = n + j) (U : Finset ℕ)
    (hU : ∀ i ∈ U, i < C.gates.length ∧ (gateAt C i).op = .and ∧ InCone n C i j ∧
      ∃ x : List Bool, x.length = n ∧ (C.wires x).getD (n + i) false = true ∧ C.eval x = false) :
    U.card ≤ PEqualNP.TopForm.andPairs n C := by
  classical
  let pairs : Finset (ℕ × ℕ) := (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun p =>
    (gateAt C p.1).op = .and ∧ (gateAt C p.2).op = .and ∧ InCone n C p.1 p.2
  have count : pairs.card = PEqualNP.TopForm.andPairs n C := by
    unfold PEqualNP.TopForm.andPairs
    congr 1
    ext p
    simp [pairs]
  rw [← count]
  have included : U ⊆ pairs.image Prod.fst := by
    intro i hi
    obtain ⟨hi, hop, cone, x, hx, htrue, hfalse⟩ := hU i hi
    have outFalse : (C.wires x).getD (n + j) false = false := by
      simpa [Circuit.eval, hout] using hfalse
    obtain ⟨k, hk, other, c⟩ := and_between n C mono i x hx htrue j cone outFalse
    apply Finset.mem_image.mpr
    refine ⟨(i, k), ?_, rfl⟩
    simp [pairs, hi, hk, hop, other, c]
  exact (Finset.card_le_card included).trans Finset.card_image_le

lemma cone_trans (n : ℕ) (C : Circuit) (a b : ℕ) (ab : InCone n C a b) :
    ∀ c, InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro bc
    obtain ⟨bound, k, before, reads, hk⟩ := (inCone_iff n C b c).mp bc
    have ak : InCone n C a k := by
      rcases hk with eq | bk
      · rwa [← eq]
      · exact ih k before bk
    exact (inCone_iff n C a c).mpr ⟨bound, k, before, reads, Or.inr ak⟩

theorem unread_dead_slot (n : ℕ) (C : Circuit) (back : ReadsBack n C) (j : ℕ)
    (unreached : ∃ i < C.gates.length, i ≠ j ∧ ¬ InCone n C i j) :
    ∃ v < C.gates.length, v ≠ j ∧
      ∀ k < C.gates.length, n + v ∉ (gateAt C k).inputs := by
  classical
  let dead := (Finset.range C.gates.length).filter (fun i => i ≠ j ∧ ¬ InCone n C i j)
  have inhabited : dead.Nonempty := by
    obtain ⟨i, bound, diff, missing⟩ := unreached
    exact ⟨i, by simp [dead, bound, diff, missing]⟩
  let v := dead.max' inhabited
  have selected : v ∈ dead := dead.max'_mem inhabited
  have property : v < C.gates.length ∧ v ≠ j ∧ ¬ InCone n C v j := by
    simpa [dead] using selected
  refine ⟨v, property.1, property.2.1, ?_⟩
  intro k bound reads
  have before : v < k := by
    have := back k bound (n + v) reads
    omega
  have vk : InCone n C v k :=
    (inCone_iff n C v k).mpr ⟨bound, v, before, reads, Or.inl rfl⟩
  have different : k ≠ j := fun eq => property.2.2 (eq ▸ vk)
  have notAncestor : ¬ InCone n C k j := fun kj => property.2.2 (cone_trans n C v k vk j kj)
  have hk : k ∈ dead := by simp [dead, bound, different, notAncestor]
  have hkmax := dead.le_max' k hk
  change k ≤ v at hkmax
  omega

end OneNestedAnd

/- Source work/nested1962/OutputGate.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds

def incidenceRow (p l : Fin 13) : List Bool :=
  List.ofFn (fun u : Fin 13 => decide (u = p)) ++
    List.ofFn (fun v : Fin 13 => decide (v = l))

lemma row_length (p l : Fin 13) : (incidenceRow p l).length = 26 := by simp [incidenceRow]

lemma disjoint_raw_rows (i : Fin 26) :
    (incidenceRow 0 0).getD i.val false = false ∨ (incidenceRow 1 1).getD i.val false = false := by
  fin_cases i <;> decide

theorem output_gate (C : Circuit) (row0 : C.eval (incidenceRow 0 0) = true)
    (row1 : C.eval (incidenceRow 1 1) = true) : ∃ j < C.gates.length, C.output = 26 + j := by
  change (W C.gates (incidenceRow 0 0)).getD C.output false = true at row0
  change (W C.gates (incidenceRow 1 1)).getD C.output false = true at row1
  have lower : 26 ≤ C.output := by
    by_contra! bad
    rw [W_inp _ _ _ (by simpa only [row_length] using bad)] at row0 row1
    rcases disjoint_raw_rows ⟨C.output, bad⟩ with missing | missing
    · rw [row0] at missing
      contradiction
    · rw [row1] at missing
      contradiction
  have upper : C.output < 26 + C.gates.length := by
    by_contra! bad
    rw [W_oob _ _ _ (by simpa only [row_length] using bad)] at row0
    contradiction
  exact ⟨C.output - 26, by omega, by omega⟩

end OneNestedAnd

/- Source work/submit-L-meta-2022/lean/PEqualNP/Outside/L_meta_1751.lean -/
namespace PEqualNP.Outside.L_meta_1751

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]


def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wiresFrom gs x).getD w false

theorem eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

theorem V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

theorem gate_val_aux (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) :
    V gs x (26 + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (26 + pre.length)
      = g.op.eval (g.inputs.map fun w => (wiresFrom pre x).getD w false) :=
    wire_at 26 pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

theorem gate_val (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : Fin gs.length)
    (hw : ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ)) :
    V gs x (26 + (i : ℕ)) = (gs.get i).op.eval ((gs.get i).inputs.map (V gs x)) :=
  gate_val_aux gs x hx i (gs.get i) (by simp) hw

theorem or_val (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : Fin gs.length)
    (hw : ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ)) (hop : (gs.get i).op = GateOp.or) :
    V gs x (26 + (i : ℕ)) = true ↔ ∃ w ∈ (gs.get i).inputs, V gs x w = true := by
  rw [gate_val gs x hx i hw, hop]
  simp [GateOp.eval]


def inp (S R : Finset (Fin 13)) : List Bool :=
  List.ofFn (fun u : Fin 13 => decide (u ∈ S)) ++ List.ofFn (fun v : Fin 13 => decide (v ∈ R))

theorem inp_len (S R : Finset (Fin 13)) : (inp S R).length = 26 := by
  simp [inp]

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : ℕ) (h : j < m) :
    (List.ofFn F).getD j d = F ⟨j, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem V_point (gs : List Gate) (S R : Finset (Fin 13)) (w : ℕ) (h : w < 13) :
    V gs (inp S R) w = decide ((⟨w, h⟩ : Fin 13) ∈ S) := by
  unfold V
  rw [getD_wiresFrom _ _ _ (by rw [inp_len]; omega)]
  unfold inp
  rw [List.getD_append _ _ _ _ (by simp; exact h)]
  exact getD_ofFn 13 _ false w h

theorem V_line (gs : List Gate) (S R : Finset (Fin 13)) (w : ℕ) (h1 : 13 ≤ w) (h2 : w < 26) :
    V gs (inp S R) w = decide ((⟨w - 13, by omega⟩ : Fin 13) ∈ R) := by
  unfold V
  rw [getD_wiresFrom _ _ _ (by rw [inp_len]; omega)]
  unfold inp
  rw [List.getD_append_right _ _ _ _ (by simp; exact h1)]
  simp only [List.length_ofFn]
  exact getD_ofFn 13 _ false (w - 13) (by omega)

theorem orP (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0)) :
    ∀ w : ℕ, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0) →
      ∀ S R : Finset (Fin 13),
        (V gs (inp S R) w = true ↔ ∃ p ∈ S, V gs (inp {p} ∅) w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hP S R
    rcases hP with h | ⟨j, rfl, hj⟩
    · rw [V_point gs S R w h]
      constructor
      · intro hm
        exact ⟨⟨w, h⟩, by simpa using hm, by rw [V_point gs _ _ w h]; simp⟩
      · rintro ⟨p, hp, hv⟩
        rw [V_point gs _ _ w h] at hv
        simp at hv
        rw [hv]
        simpa using hp
    · obtain ⟨hop, hin⟩ := h0 j hj
      rw [or_val gs _ (inp_len S R) j (hwire j) hop]
      constructor
      · rintro ⟨w', hw', hv⟩
        obtain ⟨p, hp, hv'⟩ := (ih w' (hwire j w' hw') (hin w' hw') S R).1 hv
        exact ⟨p, hp, (or_val gs _ (inp_len _ _) j (hwire j) hop).2 ⟨w', hw', hv'⟩⟩
      · rintro ⟨p, hp, hv⟩
        obtain ⟨w', hw', hv'⟩ := (or_val gs _ (inp_len _ _) j (hwire j) hop).1 hv
        exact ⟨w', hw', (ih w' (hwire j w' hw') (hin w' hw') S R).2 ⟨p, hp, hv'⟩⟩

theorem orL (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1)) :
    ∀ w : ℕ, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1) →
      ∀ S R : Finset (Fin 13),
        (V gs (inp S R) w = true ↔ ∃ l ∈ R, V gs (inp ∅ {l}) w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hP S R
    rcases hP with h | ⟨j, rfl, hj⟩
    · rw [V_line gs S R w h.1 h.2]
      constructor
      · intro hm
        exact ⟨⟨w - 13, by omega⟩, by simpa using hm, by rw [V_line gs _ _ w h.1 h.2]; simp⟩
      · rintro ⟨p, hp, hv⟩
        rw [V_line gs _ _ w h.1 h.2] at hv
        simp at hv
        rw [hv]
        simpa using hp
    · obtain ⟨hop, hin⟩ := h1 j hj
      rw [or_val gs _ (inp_len S R) j (hwire j) hop]
      constructor
      · rintro ⟨w', hw', hv⟩
        obtain ⟨p, hp, hv'⟩ := (ih w' (hwire j w' hw') (hin w' hw') S R).1 hv
        exact ⟨p, hp, (or_val gs _ (inp_len _ _) j (hwire j) hop).2 ⟨w', hw', hv'⟩⟩
      · rintro ⟨p, hp, hv⟩
        obtain ⟨w', hw', hv'⟩ := (or_val gs _ (inp_len _ _) j (hwire j) hop).1 hv
        exact ⟨w', hw', (ih w' (hwire j w' hw') (hin w' hw') S R).2 ⟨p, hp, hv'⟩⟩


def PSw (gs : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => V gs (inp {p} ∅) w = true)

def LSw (gs : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => V gs (inp ∅ {l}) w = true)

theorem PSw_input (gs : List Gate) (w : ℕ) (h : w < 13) : (PSw gs w).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [PSw, Finset.mem_filter, Finset.mem_univ, true_and, V_point gs _ _ w h] at ha hb
  simp at ha hb
  rw [← ha, ← hb]

theorem LSw_input (gs : List Gate) (w : ℕ) (h1 : 13 ≤ w) (h2 : w < 26) : (LSw gs w).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [LSw, Finset.mem_filter, Finset.mem_univ, true_and, V_line gs _ _ w h1 h2] at ha hb
  simp at ha hb
  rw [← ha, ← hb]


def Piece {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (i : Fin N)
    (X : Finset (Fin 13)) : Prop :=
  X.card ≤ 1 ∨ ∃ j, j < i ∧ K j ∧ S j = X

def Built {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) : Prop :=
  ∀ i, K i → ∃ X Y, Piece K S i X ∧ Piece K S i Y ∧ S i = X ∪ Y

theorem split {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S) :
    ∀ (n : ℕ) (i : Fin N), (i : ℕ) = n → K i → 2 ≤ (S i).card →
      ∃ X Y : Finset (Fin 13), S i = X ∪ Y ∧ X ≠ S i ∧ Y ≠ S i ∧
        (X.card ≤ 1 ∨ ∃ j, K j ∧ S j = X) ∧ (Y.card ≤ 1 ∨ ∃ j, K j ∧ S j = Y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hK h2
    obtain ⟨X, Y, hX, hY, hXY⟩ := hB i hK
    by_cases hXe : X = S i
    · rcases hX with hX | ⟨j, hji, hKj, hSj⟩
      · rw [hXe] at hX; omega
      · have hSji : S j = S i := by rw [hSj, hXe]
        have := ih j (by rw [← hi]; exact hji) j rfl hKj (by rw [hSji]; exact h2)
        rw [hSji] at this
        exact this
    · by_cases hYe : Y = S i
      · rcases hY with hY | ⟨j, hji, hKj, hSj⟩
        · rw [hYe] at hY; omega
        · have hSji : S j = S i := by rw [hSj, hYe]
          have := ih j (by rw [← hi]; exact hji) j rfl hKj (by rw [hSji]; exact h2)
          rw [hSji] at this
          exact this
      · refine ⟨X, Y, hXY, hXe, hYe, ?_, ?_⟩
        · rcases hX with hX | ⟨j, _, hKj, hSj⟩
          · exact Or.inl hX
          · exact Or.inr ⟨j, hKj, hSj⟩
        · rcases hY with hY | ⟨j, _, hKj, hSj⟩
          · exact Or.inl hY
          · exact Or.inr ⟨j, hKj, hSj⟩

theorem card_lt_of_ne {X Z : Finset (Fin 13)} (h : X ⊆ Z) (hne : X ≠ Z) : X.card < Z.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩)

theorem cnt3 {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (i : Fin N) (hK : K i) (h3 : (S i).card = 3) :
    ∃ j, K j ∧ (S j).card = 2 ∧ S j ⊆ S i := by
  obtain ⟨X, Y, hXY, hXe, hYe, hX, hY⟩ := split K S hB i i rfl hK (by omega)
  have hXs : X ⊆ S i := by rw [hXY]; exact Finset.subset_union_left
  have hYs : Y ⊆ S i := by rw [hXY]; exact Finset.subset_union_right
  have hXc := card_lt_of_ne hXs hXe
  have hYc := card_lt_of_ne hYs hYe
  have hu : (S i).card ≤ X.card + Y.card := by rw [hXY]; exact Finset.card_union_le X Y
  by_cases hX2 : X.card = 2
  · rcases hX with hX | ⟨j, hKj, hSj⟩
    · omega
    · exact ⟨j, hKj, by rw [hSj]; exact hX2, by rw [hSj]; exact hXs⟩
  · have hY2 : Y.card = 2 := by omega
    rcases hY with hY | ⟨j, hKj, hSj⟩
    · omega
    · exact ⟨j, hKj, by rw [hSj]; exact hY2, by rw [hSj]; exact hYs⟩

theorem cnt {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (i : Fin N) (hK : K i) (h2 : 2 ≤ (S i).card) (h4 : (S i).card ≤ 4) :
    ∃ O' : Finset (Fin N), (∀ j ∈ O', K j ∧ 2 ≤ (S j).card ∧ S j ⊆ S i) ∧
      (S i).card ≤ O'.card + 1 := by
  classical
  obtain h | h | h : (S i).card = 2 ∨ (S i).card = 3 ∨ (S i).card = 4 := by omega
  · refine ⟨{i}, ?_, by simp; omega⟩
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨hK, h2, Finset.Subset.refl _⟩
  · obtain ⟨j, hKj, hj2, hjs⟩ := cnt3 K S hB i hK h
    have hne : i ≠ j := by intro e; rw [e] at h; omega
    refine ⟨{i, j}, ?_, by rw [Finset.card_pair hne]; omega⟩
    intro m hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact ⟨hK, h2, Finset.Subset.refl _⟩
    · exact ⟨hKj, by omega, hjs⟩
  · obtain ⟨X, Y, hXY, hXe, hYe, hX, hY⟩ := split K S hB i i rfl hK (by omega)
    have hXs : X ⊆ S i := by rw [hXY]; exact Finset.subset_union_left
    have hYs : Y ⊆ S i := by rw [hXY]; exact Finset.subset_union_right
    have hXc := card_lt_of_ne hXs hXe
    have hYc := card_lt_of_ne hYs hYe
    have hu : (S i).card ≤ X.card + Y.card := by rw [hXY]; exact Finset.card_union_le X Y
    have three : ∀ Z : Finset (Fin 13), Z ⊆ S i → Z.card = 3 → (Z.card ≤ 1 ∨ ∃ j, K j ∧ S j = Z) →
        ∃ O' : Finset (Fin N), (∀ j ∈ O', K j ∧ 2 ≤ (S j).card ∧ S j ⊆ S i) ∧
          (S i).card ≤ O'.card + 1 := by
      intro Z hZs hZ3 hZ
      rcases hZ with hZ | ⟨j, hKj, hSj⟩
      · omega
      · obtain ⟨j', hKj', hj'2, hj's⟩ := cnt3 K S hB j hKj (by rw [hSj]; exact hZ3)
        have hj3 : (S j).card = 3 := by rw [hSj]; exact hZ3
        have e1 : i ≠ j := by intro e; rw [e] at h; omega
        have e2 : i ≠ j' := by intro e; rw [e] at h; omega
        have e3 : j ≠ j' := by intro e; rw [e] at hj3; omega
        refine ⟨{i, j, j'}, ?_, ?_⟩
        · intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl
          · exact ⟨hK, h2, Finset.Subset.refl _⟩
          · exact ⟨hKj, by omega, by rw [hSj]; exact hZs⟩
          · exact ⟨hKj', by omega, fun x hx => hZs (hSj ▸ hj's hx)⟩
        · have : ({i, j, j'} : Finset (Fin N)).card = 3 :=
            Finset.card_eq_three.2 ⟨i, j, j', e1, e2, e3, rfl⟩
          omega
    by_cases hX3 : X.card = 3
    · exact three X hXs hX3 hX
    · by_cases hY3 : Y.card = 3
      · exact three Y hYs hY3 hY
      · have hX2 : X.card = 2 := by omega
        have hY2 : Y.card = 2 := by omega
        rcases hX with hX | ⟨j1, hK1, hS1⟩
        · omega
        · rcases hY with hY | ⟨j2, hK2, hS2⟩
          · omega
          · have e1 : i ≠ j1 := by intro e; rw [e, hS1] at h; omega
            have e2 : i ≠ j2 := by intro e; rw [e, hS2] at h; omega
            have e3 : j1 ≠ j2 := by
              intro e
              have hXYe : X = Y := by rw [← hS1, ← hS2, e]
              rw [hXY, hXYe, Finset.union_self] at h
              omega
            refine ⟨{i, j1, j2}, ?_, ?_⟩
            · intro m hm
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl
              · exact ⟨hK, h2, Finset.Subset.refl _⟩
              · exact ⟨hK1, by rw [hS1]; omega, by rw [hS1]; exact hXs⟩
              · exact ⟨hK2, by rw [hS2]; omega, by rw [hS2]; exact hYs⟩
            · have : ({i, j1, j2} : Finset (Fin N)).card = 3 :=
                Finset.card_eq_three.2 ⟨i, j1, j2, e1, e2, e3, rfl⟩
              omega

theorem arith (u k m : ℕ) (h4 : u ≤ 4) (hs : u ≤ k * (m + 1)) : 5 * u ≤ 4 * m + 8 * k := by
  obtain hk | hk | hk | hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  · subst hk; omega
  · subst hk; omega
  · subst hk; omega
  · omega

theorem group_bound {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (Lg : Finset (Fin 13)) (hL : Lg.card ≤ 4)
    (Tg : Finset (Fin N)) (Bs : Fin N → Finset (Fin 13)) (hsub : ∀ j ∈ Tg, Bs j ⊆ Lg)
    (hgate : ∀ j ∈ Tg, 2 ≤ (Bs j).card → ∃ i, K i ∧ S i = Bs j)
    (Og : Finset (Fin N)) (hOg : ∀ i, K i → 2 ≤ (S i).card → S i ⊆ Lg → i ∈ Og) :
    5 * (Tg.biUnion Bs).card ≤ 4 * Og.card + 8 * Tg.card := by
  have hu : (Tg.biUnion Bs).card ≤ 4 :=
    le_trans (Finset.card_le_card (Finset.biUnion_subset.2 hsub)) hL
  have hj : ∀ j ∈ Tg, (Bs j).card ≤ Og.card + 1 := by
    intro j hjT
    by_cases h2 : 2 ≤ (Bs j).card
    · obtain ⟨i, hKi, hSi⟩ := hgate j hjT h2
      have h4 : (S i).card ≤ 4 := by
        rw [hSi]; exact le_trans (Finset.card_le_card (hsub j hjT)) hL
      obtain ⟨O', hO', hc⟩ := cnt K S hB i hKi (by rw [hSi]; exact h2) h4
      have hsubO : O' ⊆ Og := fun j' hj' => hOg j' (hO' j' hj').1 (hO' j' hj').2.1
        (fun x hx => hsub j hjT (hSi ▸ (hO' j' hj').2.2 hx))
      have hcc := Finset.card_le_card hsubO
      rw [hSi] at hc
      omega
    · omega
  have hs : (Tg.biUnion Bs).card ≤ Tg.card * (Og.card + 1) := by
    calc (Tg.biUnion Bs).card ≤ ∑ j ∈ Tg, (Bs j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Tg, (Og.card + 1) := Finset.sum_le_sum hj
      _ = Tg.card * (Og.card + 1) := by simp
  exact arith _ _ _ hu hs


def E (gs : List Gate) (kind : Fin gs.length → Fin 4) (m i : Fin gs.length) : Prop :=
  kind i = 3 ∧ 26 + (m : ℕ) ∈ (gs.get i).inputs

theorem up (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or)
    (x : List Bool) (hx : x.length = 26) (j i : Fin gs.length)
    (hr : Relation.ReflTransGen (E gs kind) j i) (hv : V gs x (26 + (j : ℕ)) = true) :
    V gs x (26 + (i : ℕ)) = true := by
  induction hr with
  | refl => exact hv
  | tail _ hE ih => exact (or_val gs x hx _ (hwire _) (h3 _ hE.1)).2 ⟨_, hE.2, ih⟩

theorem down (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3))
    (x : List Bool) (hx : x.length = 26) :
    ∀ (n : ℕ) (i : Fin gs.length), (i : ℕ) = n → (kind i = 2 ∨ kind i = 3) →
      V gs x (26 + (i : ℕ)) = true →
      ∃ j, kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j i ∧ V gs x (26 + (j : ℕ)) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hk hv
    rcases hk with hk | hk
    · exact ⟨i, hk, Relation.ReflTransGen.refl, hv⟩
    · obtain ⟨hop, hin⟩ := h3 i hk
      obtain ⟨w, hw, hvw⟩ := (or_val gs x hx i (hwire i) hop).1 hv
      obtain ⟨m, rfl, hkm⟩ := hin w hw
      have hlt := hwire i _ hw
      obtain ⟨j, hj, hr, hvj⟩ := ih m (by omega) m rfl hkm hvw
      exact ⟨j, hj, hr.tail ⟨hk, hw⟩, hvj⟩

theorem reach_two (gs : List Gate) (kind : Fin gs.length → Fin 4) (j i : Fin gs.length)
    (hi : kind i = 2) (hr : Relation.ReflTransGen (E gs kind) j i) : j = i := by
  cases hr with
  | refl => rfl
  | tail _ hE =>
    have h := hE.1
    rw [hi] at h
    exact absurd h (by decide)

theorem reach_three (gs : List Gate) (kind : Fin gs.length → Fin 4) (j i : Fin gs.length)
    (hj : kind j = 2) (hi : kind i = 3) (hr : Relation.ReflTransGen (E gs kind) j i) :
    ∃ m : Fin gs.length, 26 + (m : ℕ) ∈ (gs.get i).inputs ∧ Relation.ReflTransGen (E gs kind) j m := by
  cases hr with
  | refl =>
    rw [hj] at hi
    exact absurd hi (by decide)
  | tail hr' hE => exact ⟨_, hE.2, hr'⟩


theorem count (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 →
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3)) :
    ∀ (k : ℕ) (I U : Finset (Fin gs.length)), (∀ i ∈ I, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3)) →
      (∀ j ∈ U, kind j = 2 ∧ ∃ i ∈ I, Relation.ReflTransGen (E gs kind) j i) →
      U.card ≤ I.card +
        (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card := by
  intro k
  induction k with
  | zero =>
    intro I U hI hU
    have hUe : U = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      obtain ⟨_, i, hi, _⟩ := hU j hj
      exact absurd (hI i hi).1 (by omega)
    simp [hUe]
  | succ k ih =>
    intro I U hI hU
    have hmono : (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card
        ≤ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).card := by
      apply Finset.card_le_card
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.1, by omega⟩
    by_cases hex : ∃ i0 ∈ I, (i0 : ℕ) = k
    · obtain ⟨i0, hi0, hi0k⟩ := hex
      have hIpos : 1 ≤ I.card := Finset.card_pos.2 ⟨i0, hi0⟩
      have hIe : (I.erase i0).card = I.card - 1 := Finset.card_erase_of_mem hi0
      have herase : ∀ i ∈ I.erase i0, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
        intro i hi
        obtain ⟨hne, hiI⟩ := Finset.mem_erase.1 hi
        have h1 := (hI i hiI).1
        have h2 : (i : ℕ) ≠ k := by
          intro e
          exact hne (Fin.ext (by omega))
        exact ⟨by omega, (hI i hiI).2⟩
      rcases (hI i0 hi0).2 with hk2 | hk3
      · have hU' : ∀ j ∈ U.erase i0, kind j = 2 ∧
            ∃ i ∈ I.erase i0, Relation.ReflTransGen (E gs kind) j i := by
          intro j hj
          obtain ⟨hne, hjU⟩ := Finset.mem_erase.1 hj
          obtain ⟨hj2, i, hiI, hr⟩ := hU j hjU
          refine ⟨hj2, i, Finset.mem_erase.2 ⟨?_, hiI⟩, hr⟩
          intro e
          subst e
          exact hne (reach_two gs kind j i hk2 hr)
        have h := ih (I.erase i0) (U.erase i0) herase hU'
        have hUc : U.card - 1 ≤ (U.erase i0).card := Finset.pred_card_le_card_erase
        omega
      · let J : Finset (Fin gs.length) :=
          Finset.univ.filter (fun m : Fin gs.length => 26 + (m : ℕ) ∈ (gs.get i0).inputs)
        have hJmem : ∀ m, m ∈ J ↔ 26 + (m : ℕ) ∈ (gs.get i0).inputs := by
          intro m
          simp [J]
        have hJc : J.card ≤ 2 := by
          have himg : (J.image (fun m : Fin gs.length => 26 + (m : ℕ))).card = J.card := by
            apply Finset.card_image_of_injective
            intro a b hab
            exact Fin.ext (by simpa using hab)
          have hsub : J.image (fun m : Fin gs.length => 26 + (m : ℕ)) ⊆ (gs.get i0).inputs.toFinset := by
            intro w hw
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hw
            exact List.mem_toFinset.2 ((hJmem m).1 hm)
          have h1 := Finset.card_le_card hsub
          have h2 := List.toFinset_card_le (gs.get i0).inputs
          have h3' := hlen i0
          omega
        have hI' : ∀ i ∈ I.erase i0 ∪ J, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
          intro i hi
          rcases Finset.mem_union.1 hi with hi | hi
          · exact herase i hi
          · have hin := (hJmem i).1 hi
            have hlt := hwire i0 _ hin
            obtain ⟨j, hj, hkj⟩ := h3 i0 hk3 _ hin
            have hji : j = i := Fin.ext (by omega)
            subst hji
            exact ⟨by omega, hkj⟩
        have hU' : ∀ j ∈ U, kind j = 2 ∧
            ∃ i ∈ I.erase i0 ∪ J, Relation.ReflTransGen (E gs kind) j i := by
          intro j hjU
          obtain ⟨hj2, i, hiI, hr⟩ := hU j hjU
          by_cases e : i = i0
          · subst e
            obtain ⟨m, hm, hr'⟩ := reach_three gs kind j i hj2 hk3 hr
            exact ⟨hj2, m, Finset.mem_union_right _ ((hJmem m).2 hm), hr'⟩
          · exact ⟨hj2, i, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hiI⟩), hr⟩
        have h := ih (I.erase i0 ∪ J) U hI' hU'
        have hcu := Finset.card_union_le (I.erase i0) J
        have hstep : (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card + 1
            ≤ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).card := by
          have hmem : i0 ∈ Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hk3, by omega⟩
          have hsub : Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)
              ⊆ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).erase i0 := by
            intro m hm
            rw [Finset.mem_filter] at hm
            refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨hm.1, hm.2.1, by omega⟩⟩
            intro e
            subst e
            omega
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_add_one hmem
          omega
        omega
    · have hI' : ∀ i ∈ I, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
        intro i hi
        have h1 := (hI i hi).1
        have h2 : (i : ℕ) ≠ k := fun e => hex ⟨i, hi, e⟩
        exact ⟨by omega, (hI i hi).2⟩
      have h := ih I U hI' hU
      omega


def Lp (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun l : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

def Pl (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun p : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

def TQ (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun v : Fin 13 => ∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13)))

def Q0 (d : Fin 13) : Finset (Fin 13) :=
  if d = 4 ∨ d = 5 ∨ d = 6 then {2, 4, 5, 6} else if d = 7 ∨ d = 8 then {2, 4, 7, 8} else {2, 10, 11, 12}

def Qf (p l : Fin 13) : Finset (Fin 13) := (Q0 (p - l)).image (fun q => q + l)

theorem geo_quad : ∀ p l : Fin 13, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
    (Qf p l).card = 4 ∧
    (∀ k : Fin 13, ((Qf p l).filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ Qf p l ∧ l ∈ TQ (Qf p l) := by
  decide +kernel

theorem geo_lines : ∀ p p' : Fin 13, p ≠ p' → (Lp p ∩ Lp p').card ≤ 1 := by
  decide +kernel

theorem geo_points : ∀ l l' : Fin 13, l ≠ l' → (Pl l ∩ Pl l').card ≤ 1 := by
  decide +kernel

theorem geo_Lp : ∀ p : Fin 13, (Lp p).card = 4 := by
  decide +kernel

theorem geo_Pl : ∀ l : Fin 13, (Pl l).card = 4 := by
  decide +kernel

theorem builtL (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1)) :
    Built (fun i : Fin gs.length => kind i = 1) (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) := by
  intro i hi
  obtain ⟨hop, hin⟩ := h1 i hi
  have hpiece : ∀ w ∈ (gs.get i).inputs, Piece (fun i : Fin gs.length => kind i = 1)
      (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) i (LSw gs w) := by
    intro w hw
    rcases hin w hw with h | ⟨j, rfl, hj⟩
    · exact Or.inl (LSw_input gs w h.1 h.2)
    · have hlt := hwire i _ hw
      exact Or.inr ⟨j, Fin.lt_def.2 (by omega), hj, rfl⟩
  have hmem : ∀ l, l ∈ LSw gs (26 + (i : ℕ)) ↔ ∃ w ∈ (gs.get i).inputs, l ∈ LSw gs w := by
    intro l
    simp only [LSw, Finset.mem_filter, Finset.mem_univ, true_and]
    exact or_val gs _ (inp_len _ _) i (hwire i) hop
  have hl := hlen i
  rcases hgi : (gs.get i).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · refine ⟨∅, ∅, Or.inl (by simp), Or.inl (by simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨LSw gs a, ∅, hpiece a (by rw [hgi]; simp), Or.inl (by simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨LSw gs a, LSw gs b, hpiece a (by rw [hgi]; simp), hpiece b (by rw [hgi]; simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · rw [hgi] at hl
    simp at hl

theorem builtP (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0)) :
    Built (fun i : Fin gs.length => kind i = 0) (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) := by
  intro i hi
  obtain ⟨hop, hin⟩ := h0 i hi
  have hpiece : ∀ w ∈ (gs.get i).inputs, Piece (fun i : Fin gs.length => kind i = 0)
      (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) i (PSw gs w) := by
    intro w hw
    rcases hin w hw with h | ⟨j, rfl, hj⟩
    · exact Or.inl (PSw_input gs w h)
    · have hlt := hwire i _ hw
      exact Or.inr ⟨j, Fin.lt_def.2 (by omega), hj, rfl⟩
  have hmem : ∀ l, l ∈ PSw gs (26 + (i : ℕ)) ↔ ∃ w ∈ (gs.get i).inputs, l ∈ PSw gs w := by
    intro l
    simp only [PSw, Finset.mem_filter, Finset.mem_univ, true_and]
    exact or_val gs _ (inp_len _ _) i (hwire i) hop
  have hl := hlen i
  rcases hgi : (gs.get i).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · refine ⟨∅, ∅, Or.inl (by simp), Or.inl (by simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨PSw gs a, ∅, hpiece a (by rw [hgi]; simp), Or.inl (by simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨PSw gs a, PSw gs b, hpiece a (by rw [hgi]; simp), hpiece b (by rw [hgi]; simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · rw [hgi] at hl
    simp at hl


theorem term_sets (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1))
    (h2 : ∀ i : Fin gs.length, kind i = 2 → (gs.get i).op = GateOp.and ∧
      ∃ a b : ℕ, ((gs.get i).inputs = [a, b] ∨ (gs.get i).inputs = [b, a]) ∧
        (a < 13 ∨ ∃ j : Fin gs.length, a = 26 + (j : ℕ) ∧ kind j = 0) ∧
        ((13 ≤ b ∧ b < 26) ∨ ∃ j : Fin gs.length, b = 26 + (j : ℕ) ∧ kind j = 1))
    (i : Fin gs.length) (hi : kind i = 2) :
    ∃ A B : Finset (Fin 13),
      (∀ S R : Finset (Fin 13), V gs (inp S R) (26 + (i : ℕ)) = true ↔
        (∃ p ∈ S, p ∈ A) ∧ (∃ l ∈ R, l ∈ B)) ∧
      (2 ≤ A.card → ∃ j : Fin gs.length, kind j = 0 ∧ PSw gs (26 + (j : ℕ)) = A) ∧
      (2 ≤ B.card → ∃ j : Fin gs.length, kind j = 1 ∧ LSw gs (26 + (j : ℕ)) = B) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := h2 i hi
  refine ⟨PSw gs a, LSw gs b, ?_, ?_, ?_⟩
  · intro S R
    have hv : V gs (inp S R) (26 + (i : ℕ)) = true ↔
        V gs (inp S R) a = true ∧ V gs (inp S R) b = true := by
      rw [gate_val gs _ (inp_len S R) i (hwire i), hop]
      rcases hin with hin | hin
      · rw [hin]; simp [GateOp.eval]
      · rw [hin]; simp [GateOp.eval, and_comm]
    rw [hv, orP gs kind hwire h0 a ha S R, orL gs kind hwire h1 b hb S R]
    simp [PSw, LSw]
  · intro hc
    rcases ha with h | ⟨j, rfl, hj⟩
    · have := PSw_input gs a h
      omega
    · exact ⟨j, hj, rfl⟩
  · intro hc
    rcases hb with h | ⟨j, rfl, hj⟩
    · have := LSw_input gs b h.1 h.2
      omega
    · exact ⟨j, hj, rfl⟩

theorem dbl {α β : Type} (s : Finset α) (t : Finset β) (r : α → β → Prop)
    [∀ a b, Decidable (r a b)] :
    ∑ a ∈ s, (t.filter (r a)).card = ∑ b ∈ t, (s.filter (fun a => r a b)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem main (gs : List Gate) (kind : Fin gs.length → Fin 4) (jo : Fin gs.length)
    (hop : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1))
    (h2 : ∀ i : Fin gs.length, kind i = 2 → (gs.get i).op = GateOp.and ∧
      ∃ a b : ℕ, ((gs.get i).inputs = [a, b] ∨ (gs.get i).inputs = [b, a]) ∧
        (a < 13 ∨ ∃ j : Fin gs.length, a = 26 + (j : ℕ) ∧ kind j = 0) ∧
        ((13 ≤ b ∧ b < 26) ∨ ∃ j : Fin gs.length, b = 26 + (j : ℕ) ∧ kind j = 1))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3))
    (hjo : kind jo = 2 ∨ kind jo = 3)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      V gs (inp {p} {l}) (26 + (jo : ℕ)) = true)
    (hrej : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      V gs (inp Q (TQ Q)) (26 + (jo : ℕ)) = false) :
    64 ≤ gs.length := by
  classical
  have hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2 :=
    fun i => (hop _ (List.get_mem gs i)).2
  have h3op : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or := fun i hi => (h3 i hi).1
  have hts : ∀ i : Fin gs.length, ∃ A B : Finset (Fin 13), kind i = 2 →
      ((∀ S R : Finset (Fin 13), V gs (inp S R) (26 + (i : ℕ)) = true ↔
        (∃ p ∈ S, p ∈ A) ∧ (∃ l ∈ R, l ∈ B)) ∧
      (2 ≤ A.card → ∃ j : Fin gs.length, kind j = 0 ∧ PSw gs (26 + (j : ℕ)) = A) ∧
      (2 ≤ B.card → ∃ j : Fin gs.length, kind j = 1 ∧ LSw gs (26 + (j : ℕ)) = B)) := by
    intro i
    by_cases hi : kind i = 2
    · obtain ⟨A, B, h⟩ := term_sets gs kind hwire h0 h1 h2 i hi
      exact ⟨A, B, fun _ => h⟩
    · exact ⟨∅, ∅, fun h => absurd h hi⟩
  choose A B hAB using hts
  obtain ⟨T, hTmem⟩ : ∃ T : Finset (Fin gs.length),
      ∀ j, j ∈ T ↔ (kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j jo) :=
    ⟨Finset.univ.filter (fun j => kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j jo), by simp⟩
  have hcov : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      ∃ j ∈ T, p ∈ A j ∧ l ∈ B j := by
    intro p l hpl
    obtain ⟨j, hj, hr, hv⟩ := down gs kind hwire h3 _ (inp_len _ _) jo jo rfl hjo (hacc p l hpl)
    obtain ⟨⟨p', hp', hpA⟩, ⟨l', hl', hlB⟩⟩ := ((hAB j hj).1 {p} {l}).1 hv
    rw [Finset.mem_singleton] at hp' hl'
    subst hp'
    subst hl'
    exact ⟨j, (hTmem j).2 ⟨hj, hr⟩, hpA, hlB⟩
  have hinc : ∀ j ∈ T, ∀ p ∈ A j, ∀ l ∈ B j, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    intro j hjT p hp l hl
    obtain ⟨hj, hr⟩ := (hTmem j).1 hjT
    by_contra hn
    obtain ⟨hc, hk, hpQ, hlQ⟩ := geo_quad p l hn
    have hv : V gs (inp (Qf p l) (TQ (Qf p l))) (26 + (j : ℕ)) = true :=
      ((hAB j hj).1 _ _).2 ⟨⟨p, hpQ, hp⟩, ⟨l, hlQ, hl⟩⟩
    have hup := up gs kind hwire h3op _ (inp_len _ _) j jo hr hv
    rw [hrej _ hc hk] at hup
    exact absurd hup (by simp)
  have hBsing : ∀ j ∈ T, 2 ≤ (A j).card → ∀ l ∈ B j, B j = {l} := by
    intro j hjT hc l hl
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨hl, ?_⟩
    intro l' hl'
    by_contra hne
    have hsub : A j ⊆ Pl l' ∩ Pl l := by
      intro p hp
      simp only [Finset.mem_inter, Pl, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hinc j hjT p hp l' hl', hinc j hjT p hp l hl⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := geo_points l' l hne
    omega
  have hAsing : ∀ j : Fin gs.length, ¬ 2 ≤ (A j).card → ∀ p ∈ A j, A j = {p} := by
    intro j hc p hp
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨hp, ?_⟩
    intro p' hp'
    exact Finset.card_le_one.1 (by omega) p' hp' p hp
  obtain ⟨Tp, hTp⟩ : ∃ Tp : Fin 13 → Finset (Fin gs.length),
      ∀ p j, j ∈ Tp p ↔ (j ∈ T ∧ A j = {p}) :=
    ⟨fun p => T.filter (fun j => A j = {p}), by simp⟩
  obtain ⟨Tl, hTl⟩ : ∃ Tl : Fin 13 → Finset (Fin gs.length),
      ∀ l j, j ∈ Tl l ↔ (j ∈ T ∧ 2 ≤ (A j).card ∧ B j = {l}) :=
    ⟨fun l => T.filter (fun j => 2 ≤ (A j).card ∧ B j = {l}), by simp⟩
  obtain ⟨Op, hOp⟩ : ∃ Op : Fin 13 → Finset (Fin gs.length),
      ∀ p i, i ∈ Op p ↔ (kind i = 1 ∧ 2 ≤ (LSw gs (26 + (i : ℕ))).card ∧ LSw gs (26 + (i : ℕ)) ⊆ Lp p) :=
    ⟨fun p => Finset.univ.filter (fun i : Fin gs.length =>
      kind i = 1 ∧ 2 ≤ (LSw gs (26 + (i : ℕ))).card ∧ LSw gs (26 + (i : ℕ)) ⊆ Lp p), by simp⟩
  obtain ⟨Ol, hOl⟩ : ∃ Ol : Fin 13 → Finset (Fin gs.length),
      ∀ l i, i ∈ Ol l ↔ (kind i = 0 ∧ 2 ≤ (PSw gs (26 + (i : ℕ))).card ∧ PSw gs (26 + (i : ℕ)) ⊆ Pl l) :=
    ⟨fun l => Finset.univ.filter (fun i : Fin gs.length =>
      kind i = 0 ∧ 2 ≤ (PSw gs (26 + (i : ℕ))).card ∧ PSw gs (26 + (i : ℕ)) ⊆ Pl l), by simp⟩
  
  have gp : ∀ p : Fin 13, 5 * ((Tp p).biUnion B).card ≤ 4 * (Op p).card + 8 * (Tp p).card := by
    intro p
    apply group_bound (fun i : Fin gs.length => kind i = 1)
      (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) (builtL gs kind hlen hwire h1) (Lp p)
      (le_of_eq (geo_Lp p)) (Tp p) B
    · intro j hj l hl
      obtain ⟨hjT, hA⟩ := (hTp p j).1 hj
      simp only [Lp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hinc j hjT p (by rw [hA]; simp) l hl
    · intro j hj hc
      obtain ⟨hjT, _⟩ := (hTp p j).1 hj
      exact (hAB j ((hTmem j).1 hjT).1).2.2 hc
    · intro i hK hc hs
      exact (hOp p i).2 ⟨hK, hc, hs⟩
  have gl : ∀ l : Fin 13, 5 * ((Tl l).biUnion A).card ≤ 4 * (Ol l).card + 8 * (Tl l).card := by
    intro l
    apply group_bound (fun i : Fin gs.length => kind i = 0)
      (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) (builtP gs kind hlen hwire h0) (Pl l)
      (le_of_eq (geo_Pl l)) (Tl l) A
    · intro j hj p hp
      obtain ⟨hjT, _, hBj⟩ := (hTl l j).1 hj
      simp only [Pl, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hinc j hjT p hp l (by rw [hBj]; simp)
    · intro j hj hc
      obtain ⟨hjT, _⟩ := (hTl l j).1 hj
      exact (hAB j ((hTmem j).1 hjT).1).2.1 hc
    · intro i hK hc hs
      exact (hOl l i).2 ⟨hK, hc, hs⟩
  
  have hcovp : ∀ p : Fin 13, 4 ≤ ((Tp p).biUnion B).card +
      (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A)).card := by
    intro p
    have hsub : Lp p ⊆ (Tp p).biUnion B ∪ Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A) := by
      intro l hl
      have hpl : p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
        simpa only [Lp, Finset.mem_filter, Finset.mem_univ, true_and] using hl
      obtain ⟨j, hjT, hpA, hlB⟩ := hcov p l hpl
      by_cases hc : 2 ≤ (A j).card
      · apply Finset.mem_union_right
        rw [Finset.mem_filter, Finset.mem_biUnion]
        exact ⟨Finset.mem_univ _, j, (hTl l j).2 ⟨hjT, hc, hBsing j hjT hc l hlB⟩, hpA⟩
      · apply Finset.mem_union_left
        rw [Finset.mem_biUnion]
        exact ⟨j, (hTp p j).2 ⟨hjT, hAsing j hc p hpA⟩, hlB⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le ((Tp p).biUnion B)
      (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A))
    have hc3 := geo_Lp p
    omega
  have hswap : ∑ p : Fin 13, (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A)).card
      = ∑ l : Fin 13, ((Tl l).biUnion A).card := by
    rw [dbl Finset.univ Finset.univ (fun (p l : Fin 13) => p ∈ (Tl l).biUnion A)]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    ext p
    simp
  have hC : 52 ≤ ∑ p : Fin 13, ((Tp p).biUnion B).card + ∑ l : Fin 13, ((Tl l).biUnion A).card := by
    rw [← hswap, ← Finset.sum_add_distrib]
    calc 52 = ∑ _p : Fin 13, 4 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p _ => hcovp p)
  have hG1 : 5 * ∑ p : Fin 13, ((Tp p).biUnion B).card
      ≤ 4 * ∑ p : Fin 13, (Op p).card + 8 * ∑ p : Fin 13, (Tp p).card := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun p _ => gp p)
  have hG2 : 5 * ∑ l : Fin 13, ((Tl l).biUnion A).card
      ≤ 4 * ∑ l : Fin 13, (Ol l).card + 8 * ∑ l : Fin 13, (Tl l).card := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun l _ => gl l)
  
  have hO1 : ∑ p : Fin 13, (Op p).card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 1)).card := by
    have hd : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Op := by
      intro p _ p' _ hne
      show Disjoint (Op p) (Op p')
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨_, hc, hs⟩ := (hOp p i).1 hi
      obtain ⟨_, _, hs'⟩ := (hOp p' i).1 hi'
      have hc1 := Finset.card_le_card (Finset.subset_inter hs hs')
      have hc2 := geo_lines p p' hne
      omega
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hOp p i).1 hp).1⟩
  have hO2 : ∑ l : Fin 13, (Ol l).card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 0)).card := by
    have hd : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Ol := by
      intro l _ l' _ hne
      show Disjoint (Ol l) (Ol l')
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨_, hc, hs⟩ := (hOl l i).1 hi
      obtain ⟨_, _, hs'⟩ := (hOl l' i).1 hi'
      have hc1 := Finset.card_le_card (Finset.subset_inter hs hs')
      have hc2 := geo_points l l' hne
      omega
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hOl l i).1 hl).1⟩
  have hTT : ∑ p : Fin 13, (Tp p).card + ∑ l : Fin 13, (Tl l).card ≤ T.card := by
    have hd1 : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Tp := by
      intro p _ p' _ hne
      show Disjoint (Tp p) (Tp p')
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := ((hTp p j).1 hj).2
      have e2 := ((hTp p' j).1 hj').2
      rw [e1] at e2
      exact hne (Finset.singleton_inj.1 e2)
    have hd2 : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Tl := by
      intro l _ l' _ hne
      show Disjoint (Tl l) (Tl l')
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := ((hTl l j).1 hj).2.2
      have e2 := ((hTl l' j).1 hj').2.2
      rw [e1] at e2
      exact hne (Finset.singleton_inj.1 e2)
    rw [← Finset.card_biUnion hd1, ← Finset.card_biUnion hd2]
    have hint : (Finset.univ.biUnion Tp) ∩ (Finset.univ.biUnion Tl) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_inter.1 hj
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hj1
      obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hj2
      have e1 := ((hTp p j).1 hp).2
      have e2 := ((hTl l j).1 hl).2.1
      rw [e1, Finset.card_singleton] at e2
      omega
    have hun := Finset.card_union_add_card_inter (Finset.univ.biUnion Tp) (Finset.univ.biUnion Tl)
    rw [hint, Finset.card_empty] at hun
    have hsub : (Finset.univ.biUnion Tp) ∪ (Finset.univ.biUnion Tl) ⊆ T := by
      intro j hj
      rcases Finset.mem_union.1 hj with hj | hj
      · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hj
        exact ((hTp p j).1 hp).1
      · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hj
        exact ((hTl l j).1 hl).1
    have hc := Finset.card_le_card hsub
    omega
  
  have hT2 : T.card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 2)).card := by
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hTmem j).1 hj).1⟩
  have hT3 : T.card ≤ 1 + (Finset.univ.filter (fun i : Fin gs.length => kind i = 3)).card := by
    have h := count gs kind hlen hwire (fun i hi => (h3 i hi).2) gs.length {jo} T
      (by
        intro i hi
        rw [Finset.mem_singleton] at hi
        subst hi
        exact ⟨i.2, hjo⟩)
      (by
        intro j hj
        obtain ⟨a, b⟩ := (hTmem j).1 hj
        exact ⟨a, jo, Finset.mem_singleton_self _, b⟩)
    have hsub : Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < gs.length)
        ⊆ Finset.univ.filter (fun i : Fin gs.length => kind i = 3) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.1⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h
    omega
  have hN : (Finset.univ.filter (fun i : Fin gs.length => kind i = 0)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 1)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 2)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 3)).card = gs.length := by
    have h := Finset.card_eq_sum_card_fiberwise (f := kind) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Fin.sum_univ_four, Finset.card_univ, Fintype.card_fin] at h
    omega
  omega




open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

theorem V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wiresFrom _ _ _ h, getD_wiresFrom _ _ _ h]

theorem V_gate_some (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ)
    (h : V gs x (26 + i) = true) : ∃ g, gs[i]? = some g := by
  have hi : i < gs.length := by
    by_contra hi
    rw [V_out gs x (26 + i) (by rw [hx]; omega)] at h
    exact Bool.false_ne_true h
  exact ⟨gs[i], List.getElem?_eq_getElem hi⟩

theorem orN (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) (hop : g.op = GateOp.or) :
    V gs x (26 + i) = true ↔ ∃ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

theorem andN (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) (hop : g.op = GateOp.and) :
    V gs x (26 + i) = true ↔ ∀ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

def side0 (c : ℕ → ℕ) (w : ℕ) : Prop := w < 13 ∨ (26 ≤ w ∧ c (w - 26) = 0)

def side1 (c : ℕ → ℕ) (w : ℕ) : Prop := (13 ≤ w ∧ w < 26) ∨ (26 ≤ w ∧ c (w - 26) = 1)

def sideT (c : ℕ → ℕ) (w : ℕ) : Prop := 26 ≤ w ∧ (c (w - 26) = 2 ∨ c (w - 26) = 3)

def lowW (c : ℕ → ℕ) (w : ℕ) : Prop := w < 26 ∨ (26 ≤ w ∧ (c (w - 26) = 0 ∨ c (w - 26) = 1))

def newGate (c : ℕ → ℕ) (j : ℕ) (g : Gate) : Gate :=
  if c j = 0 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide (w < 13 ∨ (26 ≤ w ∧ c (w - 26) = 0)))⟩
  else if c j = 1 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide ((13 ≤ w ∧ w < 26) ∨ (26 ≤ w ∧ c (w - 26) = 1)))⟩
  else if c j = 2 then g
  else if c j = 3 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide (26 ≤ w ∧ (c (w - 26) = 2 ∨ c (w - 26) = 3)))⟩
  else ⟨GateOp.or, []⟩

def newGates (c : ℕ → ℕ) (gs : List Gate) : List Gate := gs.mapIdx (fun j g => newGate c j g)

theorem newGates_len (c : ℕ → ℕ) (gs : List Gate) : (newGates c gs).length = gs.length := by
  simp [newGates]

theorem newGates_get (c : ℕ → ℕ) (gs : List Gate) (i : ℕ) (g : Gate) (hg : gs[i]? = some g) :
    (newGates c gs)[i]? = some (newGate c i g) := by
  simp [newGates, List.getElem?_mapIdx, hg]

theorem newGates_inv (c : ℕ → ℕ) (gs : List Gate) (i : ℕ) (g' : Gate)
    (hg : (newGates c gs)[i]? = some g') : ∃ g, gs[i]? = some g ∧ g' = newGate c i g := by
  have hi : i < gs.length := by
    have := (List.getElem?_eq_some_iff.1 hg).1
    rw [newGates_len] at this
    exact this
  refine ⟨gs[i], List.getElem?_eq_getElem hi, ?_⟩
  have h2 := newGates_get c gs i gs[i] (List.getElem?_eq_getElem hi)
  rw [hg] at h2
  exact Option.some.inj h2

theorem mem0 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 0) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ side0 c w := by
  simp [newGate, h, side0]

theorem mem1 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 1) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ side1 c w := by
  simp [newGate, h, side1]

theorem eq2 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : c i = 2) : newGate c i g = g := by
  simp [newGate, h]

theorem mem3 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 3) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ sideT c w := by
  simp [newGate, h, sideT]

theorem eq4 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : 4 ≤ c i) : newGate c i g = ⟨GateOp.or, []⟩ := by
  have h0 : c i ≠ 0 := by omega
  have h1 : c i ≠ 1 := by omega
  have h2 : c i ≠ 2 := by omega
  have h3 : c i ≠ 3 := by omega
  simp [newGate, h0, h1, h2, h3]

theorem newGate_or (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : c i ≠ 2) :
    (newGate c i g).op = GateOp.or := by
  unfold newGate
  split_ifs <;> rfl

theorem newGate_sub (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : w ∈ (newGate c i g).inputs) :
    w ∈ g.inputs := by
  unfold newGate at h
  split_ifs at h
  · exact (List.mem_filter.1 h).1
  · exact (List.mem_filter.1 h).1
  · exact h
  · exact (List.mem_filter.1 h).1
  · simp at h

theorem newGate_len (c : ℕ → ℕ) (i : ℕ) (g : Gate) :
    (newGate c i g).inputs.length ≤ g.inputs.length := by
  unfold newGate
  split_ifs
  · exact List.length_filter_le _ _
  · exact List.length_filter_le _ _
  · exact le_refl _
  · exact List.length_filter_le _ _
  · simp

def Hyp (gs : List Gate) (c : ℕ → ℕ) : Prop :=
  ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧ ∀ w ∈ g.inputs, w < 26 + i) ∧
    (c i = 0 ∨ c i = 1 → g.op = GateOp.or ∧ ∀ w ∈ g.inputs, lowW c w) ∧
    (c i = 2 → g.op = GateOp.and ∧
      ∃ a b, (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧ side0 c a ∧ side1 c b) ∧
    (c i = 3 → g.op = GateOp.or) ∧
    (4 ≤ c i → g.op = GateOp.and ∧ (∀ w ∈ g.inputs, lowW c w) ∧
      ¬ ∃ a b, (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧ side0 c a ∧ side1 c b) ∧
    (c i = 1 → ∀ p : Fin 13, V gs (inp {p} ∅) (26 + i) = false) ∧
    (c i = 0 → ∀ l : Fin 13, V gs (inp ∅ {l}) (26 + i) = true →
      ∃ p : Fin 13, V gs (inp {p} ∅) (26 + i) = true)


theorem monoC (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c)
    (S R S' R' : Finset (Fin 13)) (hS : S ⊆ S') (hR : R ⊆ R') :
    ∀ w, V gs (inp S R) w = true → V gs (inp S' R') w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h13 : w < 13
    · rw [V_point gs _ _ w h13] at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      exact hS h
    by_cases h26 : w < 26
    · rw [V_line gs _ _ w (by omega) h26] at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      exact hR h
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨⟨ho, _, hb⟩, _⟩ := H j g hg
    rcases ho with ho | ho
    · rw [andN gs _ (inp_len _ _) j g hg hb ho] at h ⊢
      intro u hu
      exact ih u (hb u hu) (h u hu)
    · rw [orN gs _ (inp_len _ _) j g hg hb ho] at h ⊢
      obtain ⟨u, hu, hv⟩ := h
      exact ⟨u, hu, ih u (hb u hu) hv⟩


theorem dom (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (x : List Bool) (hx : x.length = 26) :
    ∀ w, V (newGates c gs) x w = true → V gs x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h26 : w < 26
    · rw [V_in gs (newGates c gs) x w (by omega)]
      exact h
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g', hg'⟩ := V_gate_some _ x hx j h
    obtain ⟨g, hg, rfl⟩ := newGates_inv c gs j g' hg'
    obtain ⟨⟨ho, _, hb⟩, h01, h2, h3, h4, _⟩ := H j g hg
    have hbd : ∀ u ∈ (newGate c j g).inputs, u < 26 + j := fun u hu => hb u (newGate_sub c j g u hu)
    by_cases hc2 : c j = 2
    · have hand := (h2 hc2).1
      have e := eq2 c j g hc2
      rw [e] at hg'
      rw [andN _ x hx j g hg' hb hand] at h
      rw [andN gs x hx j g hg hb hand]
      intro u hu
      exact ih u (hb u hu) (h u hu)
    · rw [orN _ x hx j _ hg' hbd (newGate_or c j g hc2)] at h
      obtain ⟨u, hu, hv⟩ := h
      have hor : g.op = GateOp.or := by
        by_cases hc4 : 4 ≤ c j
        · rw [eq4 c j g hc4] at hu
          simp at hu
        · have : c j = 0 ∨ c j = 1 ∨ c j = 3 := by omega
          rcases this with h' | h' | h'
          · exact (h01 (Or.inl h')).1
          · exact (h01 (Or.inr h')).1
          · exact h3 h'
      rw [orN gs x hx j g hg hb hor]
      exact ⟨u, newGate_sub c j g u hu, ih u (hbd u hu) hv⟩


theorem lowP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13)
    (S R : Finset (Fin 13)) (hp : p ∈ S) :
    ∀ i, c i = 0 → V gs (inp {p} ∅) (26 + i) = true →
      V (newGates c gs) (inp S R) (26 + i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc hv
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) i hv
    obtain ⟨⟨_, _, hb⟩, h01, _, _, _, _, _⟩ := H i g hg
    obtain ⟨hor, hlow⟩ := h01 (Or.inl hc)
    rw [orN gs _ (inp_len _ _) i g hg hb hor] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    rw [orN _ _ (inp_len _ _) i _ (newGates_get c gs i g hg)
      (fun u hu => hb u (newGate_sub c i g u hu)) (newGate_or c i g (by omega))]
    have hbw := hb w hw
    rcases hlow w hw with h | ⟨h26, hcw⟩
    · by_cases h13 : w < 13
      · refine ⟨w, (mem0 c i g w hc).2 ⟨hw, Or.inl h13⟩, ?_⟩
        rw [V_point gs _ _ w h13] at hvw
        rw [V_point _ _ _ w h13]
        simp only [decide_eq_true_eq, Finset.mem_singleton] at hvw ⊢
        rw [hvw]; exact hp
      · rw [V_line gs _ _ w (by omega) h] at hvw
        simp at hvw
    · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      rw [Nat.add_sub_cancel_left] at hcw
      rcases hcw with hcw | hcw
      · refine ⟨26 + j, (mem0 c i g _ hc).2 ⟨hw, Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hcw⟩⟩, ?_⟩
        exact ih j (by omega) hcw hvw
      · obtain ⟨gj, hgj⟩ := V_gate_some gs _ (inp_len _ _) j hvw
        obtain ⟨_, _, _, _, _, hs1, _⟩ := H j gj hgj
        rw [hs1 hcw p] at hvw
        exact absurd hvw Bool.false_ne_true

theorem lowL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13)
    (S R : Finset (Fin 13)) (hl : l ∈ R) :
    ∀ i, c i = 1 → V gs (inp ∅ {l}) (26 + i) = true →
      V (newGates c gs) (inp S R) (26 + i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc hv
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) i hv
    obtain ⟨⟨_, _, hb⟩, h01, _, _, _, hs1i, _⟩ := H i g hg
    obtain ⟨hor, hlow⟩ := h01 (Or.inr hc)
    rw [orN gs _ (inp_len _ _) i g hg hb hor] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    rw [orN _ _ (inp_len _ _) i _ (newGates_get c gs i g hg)
      (fun u hu => hb u (newGate_sub c i g u hu)) (newGate_or c i g (by omega))]
    have hbw := hb w hw
    rcases hlow w hw with h | ⟨h26, hcw⟩
    · by_cases h13 : w < 13
      · rw [V_point gs _ _ w h13] at hvw
        simp at hvw
      · refine ⟨w, (mem1 c i g w hc).2 ⟨hw, Or.inl ⟨by omega, h⟩⟩, ?_⟩
        rw [V_line gs _ _ w (by omega) h] at hvw
        rw [V_line _ _ _ w (by omega) h]
        simp only [decide_eq_true_eq, Finset.mem_singleton] at hvw ⊢
        rw [hvw]; exact hl
    · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      rw [Nat.add_sub_cancel_left] at hcw
      rcases hcw with hcw | hcw
      · obtain ⟨gj, hgj⟩ := V_gate_some gs _ (inp_len _ _) j hvw
        obtain ⟨_, _, _, _, _, _, hs0⟩ := H j gj hgj
        obtain ⟨p0, hp0⟩ := hs0 hcw l hvw
        have hi : V gs (inp {p0} ∅) (26 + i) = true :=
          (orN gs _ (inp_len _ _) i g hg hb hor).2 ⟨26 + j, hw, hp0⟩
        rw [hs1i hc p0] at hi
        exact absurd hi Bool.false_ne_true
      · refine ⟨26 + j, (mem1 c i g _ hc).2 ⟨hw, Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hcw⟩⟩, ?_⟩
        exact ih j (by omega) hcw hvw


theorem addLow (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p l : Fin 13) :
    ∀ w, lowW c w → V gs (inp {p} {l}) w = true →
      V gs (inp {p} ∅) w = true ∨ V gs (inp ∅ {l}) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hlw hv
    by_cases h13 : w < 13
    · left
      rw [V_point gs _ _ w h13] at hv ⊢
      exact hv
    by_cases h26 : w < 26
    · right
      rw [V_line gs _ _ w (by omega) h26] at hv ⊢
      exact hv
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    have hcj : c j = 0 ∨ c j = 1 := by
      rcases hlw with h | ⟨_, h⟩
      · omega
      · rw [Nat.add_sub_cancel_left] at h; exact h
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j hv
    obtain ⟨⟨_, _, hb⟩, h01, _⟩ := H j g hg
    obtain ⟨hor, hlow⟩ := h01 hcj
    rw [orN gs _ (inp_len _ _) j g hg hb hor] at hv
    obtain ⟨u, hu, hvu⟩ := hv
    rcases ih u (hb u hu) (hlow u hu) hvu with h | h
    · left
      exact (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, h⟩
    · right
      exact (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, h⟩


def Q1 (d : Fin 13) : Finset (Fin 13) :=
  if d = 3 then {0, 2, 3, 4} else if d = 4 then {0, 1, 4, 6} else if d = 6 then {0, 1, 2, 6}
  else if d = 7 then {0, 1, 2, 7} else if d = 8 then {0, 1, 4, 8} else if d = 9 then {0, 2, 4, 9}
  else if d = 10 then {0, 1, 5, 10} else if d = 11 then {0, 1, 2, 11}
  else if d = 12 then {0, 1, 4, 12} else {0, 1, 2, 5}

def QP (p p' : Fin 13) : Finset (Fin 13) := (Q1 (p' - p)).image (fun q => q + p)

def Q2 (d : Fin 13) : Finset (Fin 13) :=
  if d = 1 then {5, 6, 7, 11} else if d = 2 then {4, 6, 7, 8} else if d = 3 then {2, 5, 7, 8}
  else if d = 4 then {2, 6, 8, 10} else if d = 5 then {2, 4, 7, 11} else if d = 6 then {4, 5, 8, 10}
  else if d = 8 then {2, 5, 6, 10} else if d = 9 then {2, 4, 6, 8} else if d = 10 then {2, 4, 5, 8}
  else if d = 12 then {4, 5, 6, 10} else {2, 4, 5, 6}

def QL (l l' : Fin 13) : Finset (Fin 13) := (Q2 (l' - l)).image (fun q => q + l)

theorem geoPP : ∀ p p' : Fin 13,
    (QP p p').card = 4 ∧
    (∀ k : Fin 13, ((QP p p').filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ QP p p' ∧ p' ∈ QP p p' := by
  decide +kernel

theorem geoLL : ∀ l l' : Fin 13,
    (QL l l').card = 4 ∧
    (∀ k : Fin 13, ((QL l l').filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    l ∈ TQ (QL l l') ∧ l' ∈ TQ (QL l l') := by
  decide +kernel


def Bad (gs : List Gate) (w : ℕ) : Prop :=
  ∃ Q : Finset (Fin 13), Q.card = 4 ∧
    (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    V gs (inp Q (TQ Q)) w = true

theorem badPP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p p' : Fin 13) (w : ℕ)
    (h : V gs (inp {p, p'} ∅) w = true) : Bad gs w := by
  obtain ⟨h1, h2, h3, h4⟩ := geoPP p p'
  refine ⟨QP p p', h1, h2, monoC gs c H _ _ _ _ ?_ (Finset.empty_subset _) w h⟩
  intro q hq
  rcases Finset.mem_insert.1 hq with rfl | hq
  · exact h3
  · rw [Finset.mem_singleton.1 hq]; exact h4

theorem badLL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l l' : Fin 13) (w : ℕ)
    (h : V gs (inp ∅ {l, l'}) w = true) : Bad gs w := by
  obtain ⟨h1, h2, h3, h4⟩ := geoLL l l'
  refine ⟨QL l l', h1, h2, monoC gs c H _ _ _ _ (Finset.empty_subset _) ?_ w h⟩
  intro q hq
  rcases Finset.mem_insert.1 hq with rfl | hq
  · exact h3
  · rw [Finset.mem_singleton.1 hq]; exact h4

theorem badP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (h : V gs (inp {p} ∅) w = true) : Bad gs w :=
  badPP gs c H p p w (monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) w h)

theorem badL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13) (w : ℕ)
    (h : V gs (inp ∅ {l}) w = true) : Bad gs w :=
  badLL gs c H l l w (monoC gs c H _ _ _ _ (Finset.empty_subset _) (by simp) w h)


theorem firesP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (hl : lowW c w) (h : V gs (inp {p} ∅) w = true) : side0 c w := by
  by_cases h13 : w < 13
  · exact Or.inl h13
  by_cases h26 : w < 26
  · rw [V_line gs _ _ w (by omega) h26] at h
    simp at h
  obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
  rcases hl with hl | ⟨_, hl⟩
  · omega
  rw [Nat.add_sub_cancel_left] at hl
  rcases hl with hl | hl
  · exact Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hl⟩
  · obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, hs1, _⟩ := H j g hg
    rw [hs1 hl p] at h
    exact absurd h Bool.false_ne_true


theorem firesL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13) (w : ℕ)
    (hl : lowW c w) (h : V gs (inp ∅ {l}) w = true) :
    side1 c w ∨ ∃ p0 : Fin 13, V gs (inp {p0} ∅) w = true := by
  by_cases h13 : w < 13
  · rw [V_point gs _ _ w h13] at h
    simp at h
  by_cases h26 : w < 26
  · exact Or.inl (Or.inl ⟨by omega, h26⟩)
  obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
  rcases hl with hl | ⟨_, hl⟩
  · omega
  rw [Nat.add_sub_cancel_left] at hl
  rcases hl with hl | hl
  · obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, _, hs0⟩ := H j g hg
    exact Or.inr (hs0 hl l h)
  · exact Or.inl (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hl⟩)


theorem side0D (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13)
    (S R : Finset (Fin 13)) (hp : p ∈ S) (w : ℕ) (hs : side0 c w)
    (h : V gs (inp {p} ∅) w = true) : V (newGates c gs) (inp S R) w = true := by
  rcases hs with h13 | ⟨h26, hc⟩
  · rw [V_point gs _ _ w h13] at h
    rw [V_point _ _ _ w h13]
    simp only [decide_eq_true_eq, Finset.mem_singleton] at h ⊢
    rw [h]; exact hp
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    exact lowP gs c H p S R hp j hc h

theorem side1D (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13)
    (S R : Finset (Fin 13)) (hl : l ∈ R) (w : ℕ) (hs : side1 c w)
    (h : V gs (inp ∅ {l}) w = true) : V (newGates c gs) (inp S R) w = true := by
  rcases hs with ⟨h13, h26⟩ | ⟨h26, hc⟩
  · rw [V_line gs _ _ w h13 h26] at h
    rw [V_line _ _ _ w h13 h26]
    simp only [decide_eq_true_eq, Finset.mem_singleton] at h ⊢
    rw [h]; exact hl
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    exact lowL gs c H l S R hl j hc h

theorem side0_low (c : ℕ → ℕ) (w : ℕ) (h : side0 c w) : lowW c w := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨h, Or.inl h'⟩

theorem side1_low (c : ℕ → ℕ) (w : ℕ) (h : side1 c w) : lowW c w := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h.2
  · exact Or.inr ⟨h, Or.inr h'⟩


theorem side1_noP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (hs : side1 c w) (h : V gs (inp {p} ∅) w = true) : False := by
  rcases hs with ⟨h13, h26⟩ | ⟨h26, hc⟩
  · rw [V_line gs _ _ w h13 h26] at h
    simp at h
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, hs1, _⟩ := H j g hg
    rw [hs1 hc p] at h
    exact absurd h Bool.false_ne_true



theorem top (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p l : Fin 13) :
    ∀ w, V gs (inp {p} {l}) w = true →
      (sideT c w ∧ V (newGates c gs) (inp {p} {l}) w = true) ∨ Bad gs w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    have hlowcase : lowW c w → Bad gs w := by
      intro hlw
      rcases addLow gs c H p l w hlw hv with h | h
      · exact badP gs c H p w h
      · exact badL gs c H l w h
    by_cases h26 : w < 26
    · exact Or.inr (hlowcase (Or.inl h26))
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j hv
    obtain ⟨⟨ho, hlen, hb⟩, h01, h2, h3, h4, _⟩ := H j g hg
    have hgd := newGates_get c gs j g hg
    have hbd : ∀ u ∈ (newGate c j g).inputs, u < 26 + j := fun u hu => hb u (newGate_sub c j g u hu)
    have hsT : ∀ hh : c j = 2 ∨ c j = 3, sideT c (26 + j) := fun hh =>
      ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hh⟩
    by_cases hc01 : c j = 0 ∨ c j = 1
    · exact Or.inr (hlowcase (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hc01⟩))
    by_cases hc2 : c j = 2
    · obtain ⟨hand, a, b, hsh, ha, hbb⟩ := h2 hc2
      have hall := (andN gs _ (inp_len _ _) j g hg hb hand).1 hv
      have hma : a ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
      have hmb : b ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
      have hbl : V gs (inp ∅ {l}) b = true := by
        rcases addLow gs c H p l b (side1_low c b hbb) (hall b hmb) with h | h
        · exact (side1_noP gs c H p b hbb h).elim
        · exact h
      rcases addLow gs c H p l a (side0_low c a ha) (hall a hma) with h | h
      · left
        refine ⟨hsT (Or.inl hc2), ?_⟩
        have e := eq2 c j g hc2
        rw [e] at hgd
        rw [andN _ _ (inp_len _ _) j g hgd hb hand]
        intro u hu
        have hu' : u = a ∨ u = b := by
          rcases hsh with e | e
          · rw [e] at hu; simpa using hu
          · rw [e] at hu; simpa [or_comm] using hu
        rcases hu' with rfl | rfl
        · exact side0D gs c H p _ _ (by simp) _ ha h
        · exact side1D gs c H l _ _ (by simp) _ hbb hbl
      · right
        apply badL gs c H l
        rw [andN gs _ (inp_len _ _) j g hg hb hand]
        intro u hu
        have hu' : u = a ∨ u = b := by
          rcases hsh with e | e
          · rw [e] at hu; simpa using hu
          · rw [e] at hu; simpa [or_comm] using hu
        rcases hu' with rfl | rfl
        · exact h
        · exact hbl
    by_cases hc3 : c j = 3
    · have hor := h3 hc3
      obtain ⟨u, hu, hvu⟩ := (orN gs _ (inp_len _ _) j g hg hb hor).1 hv
      rcases ih u (hb u hu) hvu with ⟨hT, hd⟩ | ⟨Q, hQ1, hQ2, hQ3⟩
      · left
        refine ⟨hsT (Or.inr hc3), ?_⟩
        rw [orN _ _ (inp_len _ _) j _ hgd hbd (newGate_or c j g hc2)]
        exact ⟨u, (mem3 c j g u hc3).2 ⟨hu, hT⟩, hd⟩
      · right
        exact ⟨Q, hQ1, hQ2, (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, hQ3⟩⟩
    have hc4 : 4 ≤ c j := by omega
    obtain ⟨hand, hlow, hnsh⟩ := h4 hc4
    have hall := (andN gs _ (inp_len _ _) j g hg hb hand).1 hv
    right
    have key : ∀ S R : Finset (Fin 13), (∀ u ∈ g.inputs, V gs (inp S R) u = true) →
        V gs (inp S R) (26 + j) = true := fun S R hh =>
      (andN gs _ (inp_len _ _) j g hg hb hand).2 hh
    have hsplit : ∀ u ∈ g.inputs, V gs (inp {p} ∅) u = true ∨ V gs (inp ∅ {l}) u = true :=
      fun u hu => addLow gs c H p l u (hlow u hu) (hall u hu)
    by_cases hallP : ∀ u ∈ g.inputs, V gs (inp {p} ∅) u = true
    · exact badP gs c H p _ (key _ _ hallP)
    by_cases hallL : ∀ u ∈ g.inputs, V gs (inp ∅ {l}) u = true
    · exact badL gs c H l _ (key _ _ hallL)
    
    obtain ⟨a, ha, haP⟩ : ∃ a ∈ g.inputs, V gs (inp {p} ∅) a = true ∧ ¬ V gs (inp ∅ {l}) a = true := by
      by_contra hne
      apply hallL
      intro u hu
      by_contra hul
      rcases hsplit u hu with h | h
      · exact hne ⟨u, hu, h, hul⟩
      · exact hul h
    obtain ⟨b, hbm, hbL⟩ : ∃ b ∈ g.inputs, V gs (inp ∅ {l}) b = true ∧ ¬ V gs (inp {p} ∅) b = true := by
      by_contra hne
      apply hallP
      intro u hu
      by_contra hup
      rcases hsplit u hu with h | h
      · exact hup h
      · exact hne ⟨u, hu, h, hup⟩
    have hab : a ≠ b := by
      rintro rfl
      exact hbL.2 haP.1
    have hshape : g.inputs = [a, b] ∨ g.inputs = [b, a] := by
      match hgi : g.inputs, hlen, ha, hbm with
      | [], _, ha', _ => simp at ha'
      | [u], _, ha', hb' =>
        simp at ha' hb'
        exact absurd (ha'.trans hb'.symm) hab
      | [u, v], _, ha', hb' =>
        simp at ha' hb'
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd rfl hab
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl hab
      | _ :: _ :: _ :: _, hl', _, _ => simp at hl'
    have hs0 := firesP gs c H p a (hlow a ha) haP.1
    rcases firesL gs c H l b (hlow b hbm) hbL.1 with hs1 | ⟨p0, hp0⟩
    · exact (hnsh ⟨a, b, hshape, hs0, hs1⟩).elim
    · apply badPP gs c H p p0
      apply key
      intro u hu
      have hu' : u = a ∨ u = b := by
        rcases hshape with e | e
        · rw [e] at hu; simpa using hu
        · rw [e] at hu; simpa [or_comm] using hu
      rcases hu' with rfl | rfl
      · exact monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) _ haP.1
      · exact monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) _ hp0


lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h



theorem newGate_op (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (newGate c i g).op = GateOp.and ∨ (newGate c i g).op = GateOp.or := by
  by_cases h2 : c i = 2
  · rw [eq2 c i g h2]; exact h
  · exact Or.inr (newGate_or c i g h2)

theorem core (gs : List Gate) (out : ℕ)
    (hmon : Monotone2 ⟨gs, out⟩) (hback : ReadsBack 26 ⟨gs, out⟩)
    (hnn : ¬ ∃ i j : ℕ, (gateAt ⟨gs, out⟩ i).op = GateOp.and ∧
      (gateAt ⟨gs, out⟩ j).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ i j)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      V gs (inp {p} {l}) out = true)
    (hrej : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      V gs (inp Q (TQ Q)) out = false) : 64 ≤ gs.length := by
  classical
  have hgat : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → gateAt (⟨gs, out⟩ : Circuit) i = g := by
    intro i g hg
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hg
    exact gateAt_eq ⟨gs, out⟩ i hi
  have hG : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 ∧ ∀ w ∈ g.inputs, w < 26 + i := by
    intro i g hg
    have e := hgat i g hg
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hg
    have hm := hmon gs[i] (List.getElem_mem hi)
    refine ⟨by simpa using hm.1, hm.2, ?_⟩
    have hb := hback i hi
    rw [e] at hb
    exact hb
  obtain ⟨Top, hTop⟩ : ∃ Top : ℕ → Prop, ∀ j, Top j ↔
      ((gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∨
        ∃ k, (gateAt (⟨gs, out⟩ : Circuit) k).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ k j) :=
    ⟨_, fun j => Iff.rfl⟩
  have hread : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ w ∈ g.inputs, 26 ≤ w → Top (w - 26) →
      ∃ k, (gateAt (⟨gs, out⟩ : Circuit) k).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ k j := by
    intro j g hg w hw h26 hT
    have hj : j < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hbw := (hG j g hg).2.2 w hw
    have hw' : w ∈ (gateAt (⟨gs, out⟩ : Circuit) j).inputs := by rw [hgat j g hg]; exact hw
    rcases (hTop _).1 hT with h | ⟨k, hk, hkc⟩
    · exact ⟨w - 26, h, (inCone_iff 26 ⟨gs, out⟩ _ j hj).2 ⟨w, hw', h26, hbw, Or.inl rfl⟩⟩
    · exact ⟨k, hk, (inCone_iff 26 ⟨gs, out⟩ _ j hj).2 ⟨w, hw', h26, hbw, Or.inr hkc⟩⟩
  have hreadA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ w ∈ g.inputs, 26 ≤ w →
      ¬ Top (w - 26) := by
    intro j g hg hop w hw h26 hT
    obtain ⟨k, hk, hkc⟩ := hread j g hg w hw h26 hT
    exact hnn ⟨k, j, hk, by rw [hgat j g hg]; exact hop, hkc⟩
  have hsex : ∀ j : ℕ, ∃ v : ℕ,
      (v = 1 ∧ (∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true) ∨
      (v = 0 ∧ ¬ ((∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true)) := by
    intro j
    by_cases h : ((∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true)
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, h⟩⟩
  choose s hs using hsex
  have hs01 : ∀ j, s j = 0 ∨ s j = 1 := by
    intro j
    rcases hs j with h | h
    · exact Or.inr h.1
    · exact Or.inl h.1
  obtain ⟨shape, hshape⟩ : ∃ shape : ℕ → Prop, ∀ j, shape j ↔
      ∃ a b, ((gateAt (⟨gs, out⟩ : Circuit) j).inputs = [a, b] ∨
        (gateAt (⟨gs, out⟩ : Circuit) j).inputs = [b, a]) ∧ side0 s a ∧ side1 s b :=
    ⟨_, fun j => Iff.rfl⟩
  have hcex : ∀ j : ℕ, ∃ v : ℕ,
      (¬ Top j ∧ v = s j) ∨
      (Top j ∧ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ shape j ∧ v = 2) ∨
      (Top j ∧ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ ¬ shape j ∧ v = 4) ∨
      (Top j ∧ ¬ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ v = 3) := by
    intro j
    by_cases hT : Top j
    · by_cases ha : (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and
      · by_cases hsj : shape j
        · exact ⟨2, Or.inr (Or.inl ⟨hT, ha, hsj, rfl⟩)⟩
        · exact ⟨4, Or.inr (Or.inr (Or.inl ⟨hT, ha, hsj, rfl⟩))⟩
      · exact ⟨3, Or.inr (Or.inr (Or.inr ⟨hT, ha, rfl⟩))⟩
    · exact ⟨s j, Or.inl ⟨hT, rfl⟩⟩
  choose c hc using hcex
  have hcs : ∀ j, ¬ Top j → c j = s j := by
    intro j hT
    rcases hc j with h | h | h | h
    · exact h.2
    · exact absurd h.1 hT
    · exact absurd h.1 hT
    · exact absurd h.1 hT
  
  have tr0 : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ a ∈ g.inputs,
      (side0 s a ↔ side0 c a) := by
    intro j g hg hop a ha
    unfold side0
    constructor
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [← hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
  have tr1 : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ a ∈ g.inputs,
      (side1 s a ↔ side1 c a) := by
    intro j g hg hop a ha
    unfold side1
    constructor
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [← hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
  have H : Hyp gs c := by
    intro i g hg
    have hga := hgat i g hg
    have hs01i := hs01 i
    refine ⟨hG i g hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h01
      have hnT : ¬ Top i := by
        intro hT
        rcases hc i with h | h | h | h
        · exact h.1 hT
        · obtain ⟨_, _, _, e⟩ := h; omega
        · obtain ⟨_, _, _, e⟩ := h; omega
        · obtain ⟨_, _, e⟩ := h; omega
      have hor : g.op = GateOp.or := by
        rcases (hG i g hg).1 with h | h
        · exact absurd ((hTop i).2 (Or.inl (by rw [hga]; exact h))) hnT
        · exact h
      refine ⟨hor, fun w hw => ?_⟩
      by_cases h26 : w < 26
      · exact Or.inl h26
      · have hnTw : ¬ Top (w - 26) := fun hT =>
          hnT ((hTop i).2 (Or.inr (hread i g hg w hw (by omega) hT)))
        refine Or.inr ⟨by omega, ?_⟩
        rw [hcs _ hnTw]
        exact hs01 _
    · intro h2
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, hand, hsh, _⟩ := h
        rw [hga] at hand
        obtain ⟨a, b, hab, ha, hb⟩ := (hshape i).1 hsh
        rw [hga] at hab
        have hma : a ∈ g.inputs := by rcases hab with e | e <;> simp [e]
        have hmb : b ∈ g.inputs := by rcases hab with e | e <;> simp [e]
        exact ⟨hand, a, b, hab, (tr0 i g hg hand a hma).1 ha, (tr1 i g hg hand b hmb).1 hb⟩
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h3
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, hna, _⟩ := h
        rw [hga] at hna
        rcases (hG i g hg).1 with h' | h'
        · exact absurd h' hna
        · exact h'
    · intro h4
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, hand, hnsh, _⟩ := h
        rw [hga] at hand
        refine ⟨hand, fun w hw => ?_, ?_⟩
        · by_cases h26 : w < 26
          · exact Or.inl h26
          · refine Or.inr ⟨by omega, ?_⟩
            rw [hcs _ (hreadA i g hg hand w hw (by omega))]
            exact hs01 _
        · rintro ⟨a, b, hab, ha, hb⟩
          apply hnsh
          have hma : a ∈ g.inputs := by rcases hab with e | e <;> simp [e]
          have hmb : b ∈ g.inputs := by rcases hab with e | e <;> simp [e]
          exact (hshape i).2 ⟨a, b, by rw [hga]; exact hab,
            (tr0 i g hg hand a hma).2 ha, (tr1 i g hg hand b hmb).2 hb⟩
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h1 p
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h
        rcases hs i with h' | h'
        · exact h'.2.1 p
        · obtain ⟨e', _⟩ := h'; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h0 l hl
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h
        rcases hs i with h' | h'
        · obtain ⟨e', _⟩ := h'; omega
        · by_contra hne
          apply h'.2
          refine ⟨fun p => ?_, l, hl⟩
          by_contra hp
          exact hne ⟨p, by simpa using hp⟩
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
  have h00 : V gs (inp {0} {0}) out = true := hacc 0 0 (by decide)
  have hBadOut : ¬ Bad gs out := by
    rintro ⟨Q, h1, h2, h3⟩
    rw [hrej Q h1 h2] at h3
    exact Bool.false_ne_true h3
  have hT0 : sideT c out := by
    rcases top gs c H 0 0 out h00 with ⟨h, _⟩ | h
    · exact h
    · exact absurd h hBadOut
  obtain ⟨h26, hco⟩ := hT0
  obtain ⟨jo, rfl⟩ : ∃ j, out = 26 + j := ⟨out - 26, by omega⟩
  rw [Nat.add_sub_cancel_left] at hco
  have hjo : jo < gs.length := by
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) jo h00
    exact (List.getElem?_eq_some_iff.1 hg).1
  have hkex : ∀ i : ℕ, ∃ v : Fin 4, (c i = 1 ∧ v = 1) ∨ (c i = 2 ∧ v = 2) ∨ (c i = 3 ∧ v = 3) ∨
      (c i ≠ 1 ∧ c i ≠ 2 ∧ c i ≠ 3 ∧ v = 0) := by
    intro i
    by_cases h1 : c i = 1
    · exact ⟨1, Or.inl ⟨h1, rfl⟩⟩
    by_cases h2 : c i = 2
    · exact ⟨2, Or.inr (Or.inl ⟨h2, rfl⟩)⟩
    by_cases h3 : c i = 3
    · exact ⟨3, Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))⟩
    exact ⟨0, Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, rfl⟩))⟩
  choose kd hkd using hkex
  have k0 : ∀ i, kd i = 0 ↔ (c i = 0 ∨ 4 ≤ c i) := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k1 : ∀ i, kd i = 1 ↔ c i = 1 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k2 : ∀ i, kd i = 2 ↔ c i = 2 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k3 : ∀ i, kd i = 3 ↔ c i = 3 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have hlenD := newGates_len c gs
  have hD : ∀ i : Fin (newGates c gs).length,
      ∃ g, gs[(i : ℕ)]? = some g ∧ (newGates c gs).get i = newGate c i g := by
    intro i
    exact newGates_inv c gs i _ (by simp)
  have toFin : ∀ (i : Fin (newGates c gs).length) (w : ℕ), w < 26 + (i : ℕ) → 26 ≤ w →
      ∀ P : Fin 4 → Prop, P (kd (w - 26)) →
      ∃ j : Fin (newGates c gs).length, w = 26 + (j : ℕ) ∧ P (kd j) := by
    intro i w hw h26 P hP
    have hi := i.2
    refine ⟨⟨w - 26, by omega⟩, ?_, hP⟩
    show w = 26 + (w - 26)
    omega
  have hfin : 64 ≤ (newGates c gs).length → 64 ≤ gs.length := fun h => by rw [hlenD] at h; exact h
  apply hfin
  refine main (newGates c gs) (fun i => kd i) ⟨jo, by rw [hlenD]; exact hjo⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨g0, hg0, e⟩ := newGates_inv c gs i _ (List.getElem?_eq_getElem hi)
    rw [e]
    obtain ⟨⟨ho, hl, _⟩, _⟩ := H i g0 hg0
    exact ⟨newGate_op c i g0 ho, le_trans (newGate_len c i g0) hl⟩
  · intro i w hw
    obtain ⟨g, hg, e⟩ := hD i
    rw [e] at hw
    exact (H i g hg).1.2.2 w (newGate_sub c i g w hw)
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    rcases (k0 i).1 hk with h | h
    · refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
      obtain ⟨hw1, hw2⟩ := (mem0 c i g w h).1 hw
      rcases hw2 with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 0)
          ((k0 _).2 (Or.inl hcw)))
    · rw [eq4 c i g h]
      exact ⟨rfl, fun w hw => by simp at hw⟩
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k1 i).1 hk
    refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := (mem1 c i g w h).1 hw
    rcases hw2 with h13 | ⟨h26, hcw⟩
    · exact Or.inl h13
    · exact Or.inr (toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 1) ((k1 _).2 hcw))
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k2 i).1 hk
    rw [eq2 c i g h]
    obtain ⟨hand, a, b, hsh, ha, hb⟩ := (H i g hg).2.2.1 h
    have hma : a ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
    have hmb : b ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
    refine ⟨hand, a, b, hsh, ?_, ?_⟩
    · rcases ha with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i a ((H i g hg).1.2.2 a hma) h26 (fun v => v = 0)
          ((k0 _).2 (Or.inl hcw)))
    · rcases hb with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i b ((H i g hg).1.2.2 b hmb) h26 (fun v => v = 1) ((k1 _).2 hcw))
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k3 i).1 hk
    refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
    obtain ⟨hw1, h26, hcw⟩ := (mem3 c i g w h).1 hw
    refine toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 2 ∨ v = 3) ?_
    rcases hcw with hcw | hcw
    · exact Or.inl ((k2 _).2 hcw)
    · exact Or.inr ((k3 _).2 hcw)
  · rcases hco with hco | hco
    · exact Or.inl ((k2 _).2 hco)
    · exact Or.inr ((k3 _).2 hco)
  · intro p l hpl
    rcases top gs c H p l _ (hacc p l hpl) with ⟨_, h⟩ | h
    · exact h
    · exact absurd h hBadOut
  · intro Q h1 h2
    by_contra hne
    have ht : V (newGates c gs) (inp Q (TQ Q)) (26 + jo) = true := by simpa using hne
    have h3 := dom gs c H _ (inp_len _ _) _ ht
    rw [hrej Q h1 h2] at h3
    exact Bool.false_ne_true h3

end PEqualNP.Outside.L_meta_1751

theorem PEqualNP.Outside.L_meta_1751 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → ¬x3 x4 → (64 : ℕ) ≤ x4.size := by
  intro x1 x2 x3 C hmon hback hsound hnn
  obtain ⟨gs, out⟩ := C
  have hacc := hsound.1
  have hrej := hsound.2
  refine PEqualNP.Outside.L_meta_1751.core gs out hmon hback hnn ?_ ?_
  · intro p l hpl
    have he : PEqualNP.Outside.L_meta_1751.inp {p} {l}
        = List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l)) := by
      unfold PEqualNP.Outside.L_meta_1751.inp
      simp only [Finset.mem_singleton]
    rw [← PEqualNP.Outside.L_meta_1751.eval_eq, he]
    exact hacc p l hpl
  · intro Q hc hk
    have he : PEqualNP.Outside.L_meta_1751.inp Q (PEqualNP.Outside.L_meta_1751.TQ Q)
        = List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 =>
            decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) := by
      unfold PEqualNP.Outside.L_meta_1751.inp PEqualNP.Outside.L_meta_1751.TQ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← PEqualNP.Outside.L_meta_1751.eval_eq, he]
    exact hrej Q hc hk

/- Source work/submit-L-meta-2022/lean/PEqualNP/Outside/L_meta_2061.lean -/
namespace PEqualNP.Outside.L_meta_2061

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def sk (N i : ℕ) : ℕ := if i < N then i else i - 1

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

theorem sk_lt (N M i : ℕ) (hN0 : 0 < N) (hM : N ≤ M) (hi : i < M + 1) : sk N i < M := by
  unfold sk
  split_ifs <;> omega

theorem getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem getD_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (i : ℕ) (hi : i ≠ N) :
    (A ++ E).getD (sk N i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold sk
  by_cases h : i < A.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    have h1 : A.length ≤ i - 1 := by omega
    have h2 : A.length ≤ i := by omega
    have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.getElem?_append_right h2]
    rw [h3, List.getElem?_cons_succ]

theorem getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  by_cases h : i = N
  · have e : rn N a N = a := by
      unfold rn
      rw [if_neg (lt_irrefl _), if_pos rfl]
    have ha' : a < A.length := by omega
    rw [h, getD_mid A E b N hN, e, ← hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · have e : rn N a i = sk N i := by
      unfold rn sk
      by_cases h' : i < N
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h, if_neg h']
    rw [e]
    exact getD_sk A E b N hN i h

theorem surg (T : Gate → Gate) (A : List Bool) (b : Bool) :
    ∀ (post : List Gate) (E : List Bool),
      (∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false)) →
      ∃ E2 : List Bool, wf post (A ++ b :: E) = A ++ b :: E2 ∧
        wf (post.map T) (A ++ E) = A ++ E2 := by
  intro post
  induction post with
  | nil => intro E _; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E hT
    have e := hT h (List.mem_cons.mpr (Or.inl rfl)) E
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        (fun h' hh' E' => hT h' (List.mem_cons.mpr (Or.inr hh')) E')
    refine ⟨E2, ?_, ?_⟩
    · rw [wf_cons, List.append_assoc, List.cons_append]
      exact h1
    · rw [List.map_cons, wf_cons, ← e, List.append_assoc]
      exact h2

theorem ev (pre post : List Gate) (g : Gate) (T : Gate → Gate) (x : List Bool) (b : Bool)
    (hb : g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) = b)
    (hT : ∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (wf pre x ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (wf pre x ++ E').getD i false)) :
    ∃ E2 : List Bool, wf (pre ++ g :: post) x = wf pre x ++ b :: E2 ∧
      wf (pre ++ post.map T) x = wf pre x ++ E2 := by
  obtain ⟨E2, h1, h2⟩ := surg T (wf pre x) b post [] hT
  rw [List.append_nil] at h2
  refine ⟨E2, ?_, ?_⟩
  · rw [wf_append, wf_cons, hb]
    exact h1
  · rw [wf_append]
    exact h2

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

def Tt (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.and => ⟨GateOp.and, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.and, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

def Tf (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.or => ⟨GateOp.or, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.or, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

theorem Tt_and (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.and, ins⟩
    = ⟨GateOp.and, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tt_or (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.or, ins⟩
    = if N ∈ ins then ⟨GateOp.and, []⟩ else ⟨GateOp.or, ins.map (sk N)⟩ := rfl

theorem Tf_or (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.or, ins⟩
    = ⟨GateOp.or, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tf_and (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.and, ins⟩
    = if N ∈ ins then ⟨GateOp.or, []⟩ else ⟨GateOp.and, ins.map (sk N)⟩ := rfl

theorem map_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (ins : List ℕ)
    (hni : N ∉ ins) :
    (ins.map (sk N)).map (fun i => (A ++ E).getD i false)
      = ins.map (fun i => (A ++ b :: E).getD i false) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact getD_sk A E b N hN i (fun e => hni (by rw [← e]; exact hi))

theorem all_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = true) : ∀ ins : List ℕ,
    (ins.map f).all id = ((ins.filter (fun i => decide (i ≠ N))).map f).all id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.all_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.all_cons, ih]

theorem any_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = false) : ∀ ins : List ℕ,
    (ins.map f).any id = ((ins.filter (fun i => decide (i ≠ N))).map f).any id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.any_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.any_cons, ih]

theorem sound_c (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (h : Gate) :
    h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
      = (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) := by
  have e : (h.inputs.map (rn N a)).map (fun i => (A ++ E).getD i false)
      = h.inputs.map fun i => (A ++ b :: E).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_rn A E b N hN a ha hb i
  show h.op.eval _ = h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false)
  rw [e]

theorem sound_t (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ true :: E).getD i false)
      = (Tt N h).op.eval ((Tt N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ true :: E).getD N false = true := getD_mid A E true N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    show (ins.map fun i => (A ++ true :: E).getD i false).all id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).all id
    rw [map_sk A E true N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact all_drop _ N hf ins
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id = true
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨N, hm, rfl⟩, hf⟩
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).any id
      rw [map_sk A E true N hN ins hm]

theorem sound_f (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ false :: E).getD i false)
      = (Tf N h).op.eval ((Tf N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ false :: E).getD N false = false := getD_mid A E false N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id = false
      cases hall : (ins.map fun i => (A ++ false :: E).getD i false).all id with
      | false => rfl
      | true =>
        have t := List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨N, hm, rfl⟩)
        have t2 : (A ++ false :: E).getD N false = true := t
        rw [hf] at t2
        exact Bool.noConfusion t2
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).all id
      rw [map_sk A E false N hN ins hm]
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    show (ins.map fun i => (A ++ false :: E).getD i false).any id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).any id
    rw [map_sk A E false N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact any_drop _ N hf ins

theorem Tc_legal (N a : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tc N a h).op = GateOp.and ∨ (Tc N a h).op = GateOp.or) ∧ (Tc N a h).inputs.length ≤ 2 := by
  refine ⟨hl.1, ?_⟩
  show (h.inputs.map (rn N a)).length ≤ 2
  rw [List.length_map]
  exact hl.2

theorem Tc_rb (N a : ℕ) (ha : a < N) (h : Gate) (M : ℕ) (hM : N ≤ M)
    (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tc N a h).inputs, i < M := by
  intro i hi'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  have := hi j hj
  unfold rn
  split_ifs <;> omega

theorem Tt_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tt N h).op = GateOp.and ∨ (Tt N h).op = GateOp.or) ∧ (Tt N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    refine ⟨Or.inl rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inl rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inr rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'

theorem Tf_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tf N h).op = GateOp.and ∨ (Tf N h).op = GateOp.or) ∧ (Tf N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inr rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inl rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    refine ⟨Or.inr rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'

theorem Tt_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tt N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)

theorem Tf_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tf N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)

theorem assemble (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hev : ∀ x : List Bool, x.length = 26 →
      Circuit.eval ⟨pre ++ post.map T, o'⟩ x = C.eval x) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  refine ⟨⟨pre ++ post.map T, o'⟩, ?_, ?_, hev, ?_⟩
  · intro g' hg'
    have hg2 : g' ∈ pre ∨ g' ∈ post.map T := List.mem_append.mp hg'
    rcases hg2 with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := hTm h (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))))
      refine ⟨?_, hl.2⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map T, o'⟩ j = gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp only [List.length_append, List.length_cons]; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map T, o'⟩ j = T (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      have hmem : post[j - pre.length] ∈ C.gates := by
        rw [hC]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.getElem_mem hjk))))
      have hold : ∀ i ∈ (post[j - pre.length]).inputs, i < (26 + j) + 1 := by
        intro i hi2
        have := hrb (j + 1) (by rw [hC]; simp only [List.length_append, List.length_cons]; omega)
          i (by rw [e2]; exact hi2)
        omega
      exact hTr _ (legal _ hmem) (26 + j) (by omega) hold i hi
  · show (pre ++ post.map T).length < C.gates.length
    rw [hC]
    simp

theorem copy_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (a : ℕ)
    (ha : a < 26 + pre.length)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = A.getD a false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  apply assemble C pre post g hC (Tc (26 + pre.length) a) (rn (26 + pre.length) a C.output)
    hmono hrb
  · intro h hl
    exact Tc_legal _ _ h hl
  · intro h _ M hM hi
    exact Tc_rb _ _ ha h M hM hi
  · intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    obtain ⟨E2, h1, h2⟩ := ev pre post g (Tc (26 + pre.length) a) x _ (hb (wf pre x))
      (fun h _ E' => sound_c (wf pre x) E' _ (26 + pre.length) hlen a ha rfl h)
    show (wf (pre ++ post.map (Tc (26 + pre.length) a)) x).getD
        (rn (26 + pre.length) a C.output) false = (wf C.gates x).getD C.output false
    rw [h2, hC, h1]
    exact getD_rn (wf pre x) E2 _ (26 + pre.length) hlen a ha rfl C.output

theorem const_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (T : Gate → Gate)
    (b : Bool)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = b)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hs : ∀ h : Gate, (h.op = GateOp.and ∨ h.op = GateOp.or) → ∀ (A E : List Bool),
      A.length = 26 + pre.length →
      h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
        = (T h).op.eval ((T h).inputs.map fun i => (A ++ E).getD i false))
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  have key : ∀ x : List Bool, x.length = 26 → ∃ E2 : List Bool,
      wf C.gates x = wf pre x ++ b :: E2 ∧ wf (pre ++ post.map T) x = wf pre x ++ E2 := by
    intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    have hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
      intro h hh
      exact (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh))))).1
    rw [hC]
    exact ev pre post g T x b (hb (wf pre x))
      (fun h hh E' => hs h (hpost h hh) (wf pre x) E' hlen)
  have hout : C.output ≠ 26 + pre.length := by
    intro ho
    obtain ⟨x, y, hx, hy, ex, ey⟩ := hne
    obtain ⟨E2, h1, _⟩ := key x hx
    obtain ⟨E3, h3, _⟩ := key y hy
    have vx : C.eval x = b := by
      show (wf C.gates x).getD C.output false = b
      rw [h1, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hx])
    have vy : C.eval y = b := by
      show (wf C.gates y).getD C.output false = b
      rw [h3, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hy])
    rw [vx] at ex
    rw [vy, ex] at ey
    exact Bool.noConfusion ey
  apply assemble C pre post g hC T (sk (26 + pre.length) C.output) hmono hrb hTm hTr
  intro x hx
  obtain ⟨E2, h1, h2⟩ := key x hx
  show (wf (pre ++ post.map T) x).getD (sk (26 + pre.length) C.output) false
    = (wf C.gates x).getD C.output false
  rw [h2, h1]
  exact getD_sk _ _ _ _ (by rw [wf_len, hx]) _ hout

theorem copy_val (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (v : Bool) :
    op.eval [v] = v ∧ op.eval [v, v] = v := by
  rcases hop with rfl | rfl <;> cases v <;> exact ⟨rfl, rfl⟩

theorem len26 (f g : Fin 13 → Bool) : (List.ofFn f ++ List.ofFn g).length = 26 := by
  simp

theorem short_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false)
    (hdeg : ∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
    obtain ⟨g, hg, hd⟩ := hdeg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    obtain ⟨pre, post, gj, hC, hpl, hgj⟩ := split_gates C.gates k hk
    have hgg : gj = g := by rw [← hgj, hgk]
    rw [hgg] at hC
    have hl := legal_of C hmono g hg
    have hin : ∀ i ∈ g.inputs, i < 26 + pre.length := by
      intro i hi
      have := hrb k hk i (by rw [gateAt_eq C k hk, hgk]; exact hi)
      omega
    obtain ⟨op, ins⟩ := g
    have hop : op = GateOp.and ∨ op = GateOp.or := hl.1
    have hlen : ins.length ≤ 2 := hl.2
    have hd' : ins.length < 2 ∨ ins.getD 0 0 = ins.getD 1 0 := hd
    have hin' : ∀ i ∈ ins, i < 26 + pre.length := hin
    rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, r⟩⟩⟩
    · rcases hop with hop | hop
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tt (26 + pre.length)) true (fun _ => rfl)
          (fun h hl => Tt_legal _ h hl)
          (fun h hl M hM hi => Tt_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_t A E _ hA h hop) hne
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tf (26 + pre.length)) false (fun _ => rfl)
          (fun h hl => Tf_legal _ h hl)
          (fun h hl M hM hi => Tf_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_f A E _ hA h hop) hne
    · exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).1)
    · have hac : a = c := by simpa using hd'
      subst hac
      exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).2)
    · have h3 : (a :: c :: d :: r).length ≤ 2 := hlen
      simp only [List.length_cons] at h3
      omega

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma pairs_lt2 (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    (T T' : Finset (ℕ × ℕ))
    (hT : ∀ p : ℕ × ℕ, p ∈ T ↔ (p.1 < C.gates.length ∧ p.2 < C.gates.length) ∧
      (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)
    (hT' : ∀ p : ℕ × ℕ, p ∈ T' ↔ (p.1 < C'.gates.length ∧ p.2 < C'.gates.length) ∧
      (gateAt C' p.1).op = GateOp.and ∧ (gateAt C' p.2).op = GateOp.and ∧
        InCone n C' p.1 p.2) :
    T'.card < T.card := by
  classical
  have e : T = (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2) := by
    ext p
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  have e' : T' = (Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2) := by
    ext p
    rw [hT', Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  rw [e, e']
  exact pairs_lt n C C' r i j hr hir hlen hops htop hcone hno hi hj hij

lemma reader_or (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hC r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hC) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x hb => V1_fun n C r (n + i) x hC hr hir hout hb (key x)
  have hle := hmin _ (V1_AO2 n C r (n + i) hC hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hC hout i r1 hr1 hmin hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hC hout i r2 hr2 hmin hin2
  have hir1 : i < r1 := by have := (hC r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hC hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x hb => V2_out n C r2 c2 i x hC hr2 hc2lt hir2 hout hb (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x hb =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x hb)
  have hle := hmin _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma step3_core (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hC hout i r hr hmin hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hC hout i k r h hr hmin hkin hrin).elim
    · exact h
    · exact (reader_unique n C hC hout i r k h hk hmin hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hC) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma lift_abs (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hcone : InCone n C i j) :
    ∃ D : Circuit, AO2 n D ∧ D.gates.length = C.gates.length ∧
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) ∧
      PEqualNP.TopForm.andPairs n D < PEqualNP.TopForm.andPairs n C := by
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hC hout i j hmin hcone
  refine ⟨V2 n C r c i, V2_AO2 n C r c i hC hr hclt hir hout, V2_len n C r c i,
    fun x hb => V2_out n C r c i x hC hr hclt hir hout hb (h0 x), ?_⟩
  unfold PEqualNP.TopForm.andPairs
  refine pairs_lt2 n C (V2 n C r c i) r i j hr hir (V2_len n C r c i) ?_ ?_ ?_ ?_ hi hj hcone
    _ _ ?_ ?_
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro a' b' hb' h
    exact V2_cone n C r c i hC hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]

lemma ofFn_of_len (L : List Bool) : ∀ (m : ℕ), L.length = m →
    ∃ x : Fin m → Bool, List.ofFn x = L := by
  intro m hm
  subst hm
  exact ⟨L.get, List.ofFn_get L⟩

lemma AO2_mono {n : ℕ} {C : Circuit} (h : AO2 n C) : Monotone2 C := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have e := gateAt_eq C k hk
  obtain ⟨h1, ⟨a, b, h2⟩, _⟩ := h k hk
  rw [e] at h1 h2
  refine ⟨?_, by rw [h2]; simp⟩
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

lemma to_AO2 (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (h2 : ∀ g ∈ C.gates, ¬ g.inputs.length < 2) : AO2 26 C := by
  intro k hk
  have e := gateAt_eq C k hk
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
  have hl := legal_of C hmono _ hmem
  have h3 := h2 _ hmem
  refine ⟨by rw [e]; exact hl.1, ?_, hrb k hk⟩
  rw [e]
  have h4 : (C.gates[k]).inputs.length = 2 := by
    have := hl.2
    omega
  exact List.length_eq_two.mp h4

theorem main26 (A R : List Bool → Prop) (hA : ∀ L, A L → L.length = 26)
    (hR : ∀ L, R L → L.length = 26) (hAne : ∃ L, A L) (hRne : ∃ L, R L)
    (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hacc : ∀ L, A L → C.eval L = true) (hrej : ∀ L, R L → C.eval L = false)
    (i j : ℕ) (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone 26 C i j)
    (hB : ∀ L, R L → (C.wires L).getD (26 + i) false = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ ((∀ L, A L → D.eval L = true) ∧
      ∀ L, R L → D.eval L = false) ∧
      (D.size < C.size ∨ D.size = C.size ∧
        PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  by_cases hsm : ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
      ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) ∧ D.size < C.size
  · obtain ⟨D, h1, h2, h3, h4⟩ := hsm
    exact ⟨D, h1, h2, h3, Or.inl h4⟩
  · have hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
        C.eval y = false := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨Lr, hr⟩ := hRne
      exact ⟨La, Lr, hA _ ha, hR _ hr, hacc _ ha, hrej _ hr⟩
    have hC : AO2 26 C := by
      apply to_AO2 C hmono hrb
      intro g hg hlt
      obtain ⟨C', m1, m2, heq, hsz⟩ := short_case C hmono hrb hne ⟨g, hg, Or.inl hlt⟩
      apply hsm
      refine ⟨C', m1, m2, ⟨?_, ?_⟩, hsz⟩
      · intro L hL
        rw [heq L (hA L hL)]
        exact hacc L hL
      · intro L hL
        rw [heq L (hR L hL)]
        exact hrej L hL
    have hbelA : ∀ x : Fin 26 → Bool, A (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL _
      exact hacc _ hL
    have hbelR : ∀ x : Fin 26 → Bool, R (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL hv
      have h1 : wv 26 C x (26 + i) = false := hB _ hL
      rw [h1] at hv
      exact absurd hv (by simp)
    have tg : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) →
        ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) := by
      intro D _ hf
      constructor
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hA L hL)
        subst hx
        have h1 := hf x (hbelA x hL)
        have h2 : wv 26 C x C.output = true := hacc _ hL
        show wv 26 D x D.output = true
        rw [h1]
        exact h2
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hR L hL)
        subst hx
        have h1 := hf x (hbelR x hL)
        have h2 : wv 26 C x C.output = false := hrej _ hL
        show wv 26 D x D.output = false
        rw [h1]
        exact h2
    have hmin : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) → C.gates.length ≤ D.gates.length := by
      intro D hD hf
      by_contra hlt
      apply hsm
      refine ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, ?_⟩
      show D.gates.length < C.gates.length
      omega
    have hout : C.output < 26 + C.gates.length := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨x, hx⟩ := ofFn_of_len La 26 (hA La ha)
      subst hx
      exact out_lt 26 C x (hacc _ ha)
    obtain ⟨D, hD, hlen, hf, hp⟩ := lift_abs 26 C hC hout i j hmin hi hj hij
    exact ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, Or.inr ⟨hlen, hp⟩⟩

theorem inc00 : decide ((0 : Fin 13) - 0 = 0 ∨ (0 : Fin 13) - 0 = 1 ∨ (0 : Fin 13) - 0 = 3 ∨
    (0 : Fin 13) - 0 = 9) = true := by decide

theorem quad : ({0, 1, 2, 5} : Finset (Fin 13)).card = 4 ∧ ∀ x3 : Fin 13,
    ({x4 ∈ ({0, 1, 2, 5} : Finset (Fin 13)) | decide (x4 - x3 = 0 ∨ x4 - x3 = 1 ∨ x4 - x3 = 3 ∨
      x4 - x3 = 9) = true}).card ≤ 2 := by decide +kernel

theorem final (x1 : Fin 13 → Bool) (x2 : Finset (Fin 13) → Prop)
    (x3 : Finset (Fin 13) → List Bool)
    (h00 : x1 (0 - 0) = true) (hq : ∃ S, x2 S) (hx3 : ∀ S, (x3 S).length = 26)
    (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack 26 C)
    (hg : (∀ x5 x6 : Fin 13, x1 (x5 - x6) = true →
        C.eval ((List.ofFn fun x8 : Fin 13 => decide (x8 = x5)) ++
          List.ofFn fun x8 : Fin 13 => decide (x8 = x6)) = true) ∧
      ∀ x5, x2 x5 → C.eval (x3 x5) = false)
    (hex : ∃ x9 x10 : ℕ, (gateAt C x9).op = GateOp.and ∧ (gateAt C x10).op = GateOp.and ∧
      InCone 26 C x9 x10 ∧
      ∀ x11, x2 x11 → (C.wires (x3 x11)).getD (26 + x9) false = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
      ((∀ x5 x6 : Fin 13, x1 (x5 - x6) = true →
        D.eval ((List.ofFn fun x8 : Fin 13 => decide (x8 = x5)) ++
          List.ofFn fun x8 : Fin 13 => decide (x8 = x6)) = true) ∧
      ∀ x5, x2 x5 → D.eval (x3 x5) = false) ∧
      (D.size < C.size ∨ D.size = C.size ∧
        PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  obtain ⟨i, j, hi, hj, hij, hB⟩ := hex
  obtain ⟨D, d1, d2, d3, d4⟩ := main26
    (fun L => ∃ a b : Fin 13, x1 (a - b) = true ∧
      L = (List.ofFn fun k : Fin 13 => decide (k = a)) ++
        List.ofFn fun k : Fin 13 => decide (k = b))
    (fun L => ∃ S : Finset (Fin 13), x2 S ∧ L = x3 S)
    (by rintro L ⟨a, b, _, rfl⟩; exact len26 _ _)
    (by rintro L ⟨S, _, rfl⟩; exact hx3 S)
    ⟨_, 0, 0, h00, rfl⟩
    (by obtain ⟨S, hS⟩ := hq; exact ⟨_, S, hS, rfl⟩)
    C hm hr
    (by rintro L ⟨a, b, h, rfl⟩; exact hg.1 a b h)
    (by rintro L ⟨S, hS, rfl⟩; exact hg.2 S hS)
    i j hi hj hij
    (by rintro L ⟨S, hS, rfl⟩; exact hB S hS)
  exact ⟨D, d1, d2, ⟨fun a b h => d3.1 _ ⟨a, b, h, rfl⟩, fun S hS => d3.2 _ ⟨S, hS, rfl⟩⟩, d4⟩

end PEqualNP.Outside.L_meta_2061

theorem PEqualNP.Outside.L_meta_2061 : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x9 x10 ∧ ∀ (x11 : Finset (Fin (13 : ℕ))), x2 x11 → (x5.wires (x3 x11)).getD ((26 : ℕ) + x9) Bool.false = Bool.false) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x4 x10 ∧ (x10.size < x5.size ∨ x10.size = x5.size ∧ PEqualNP.TopForm.andPairs (26 : ℕ) x10 < PEqualNP.TopForm.andPairs (26 : ℕ) x5) := by
  intro x1 x2 x3 x4 C hm hr hg hex
  exact PEqualNP.Outside.L_meta_2061.final x1 x2 x3 PEqualNP.Outside.L_meta_2061.inc00
    ⟨_, PEqualNP.Outside.L_meta_2061.quad⟩ (fun S => PEqualNP.Outside.L_meta_2061.len26 _ _)
    C hm hr hg hex

/- Source work/quad1961/SafeBranch.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership



def goodQuad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2

def quadRow (Q : Finset (Fin 13)) : List Bool :=
  List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
    List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))

def positive (L : List Bool) : Prop :=
  ∃ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ L = incidenceRow p l

def negative (L : List Bool) : Prop :=
  ∃ Q : Finset (Fin 13), goodQuad Q ∧ L = quadRow Q

lemma separates_iff_rows (C : Circuit) : separates C ↔
    (∀ L, positive L → C.eval L = true) ∧ (∀ L, negative L → C.eval L = false) := by
  constructor
  · intro h
    constructor
    · rintro L ⟨p, l, inc, rfl⟩
      exact h.1 p l inc
    · rintro L ⟨Q, ⟨size, limits⟩, rfl⟩
      exact h.2 Q size limits
  · rintro ⟨pos, neg⟩
    exact ⟨fun p l inc => pos _ ⟨p, l, inc, rfl⟩,
      fun Q size limits => neg _ ⟨Q, ⟨size, limits⟩, rfl⟩⟩

lemma gateAt_and_bound (C : Circuit) (j : ℕ) (h : (gateAt C j).op = .and) :
    j < C.gates.length := by
  by_contra! range
  have eq : gateAt C j = ⟨.or, []⟩ := List.getD_eq_default _ _ range
  rw [eq] at h
  cases h

noncomputable def andPairSet (n : ℕ) (C : Circuit) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun p =>
    (gateAt C p.1).op = .and ∧ (gateAt C p.2).op = .and ∧ InCone n C p.1 p.2

lemma andPairSet_card (n : ℕ) (C : Circuit) :
    (andPairSet n C).card = PEqualNP.TopForm.andPairs n C := by
  classical
  unfold PEqualNP.TopForm.andPairs
  congr 1
  ext p
  simp [andPairSet]

lemma andPairSet_mem (n : ℕ) (C : Circuit) (i j : ℕ) :
    (i, j) ∈ andPairSet n C ↔
      (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone n C i j := by
  simp only [andPairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨⟨gateAt_and_bound C i h.1, gateAt_and_bound C j h.2.1⟩, h⟩⟩

theorem unique_and_pair (n : ℕ) (C : Circuit) (i j : ℕ)
    (hi : (gateAt C i).op = .and) (hj : (gateAt C j).op = .and) (hij : InCone n C i j)
    (one : PEqualNP.TopForm.andPairs n C ≤ 1) :
    andPairSet n C = {(i, j)} := by
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · exact Finset.singleton_subset_iff.mpr ((andPairSet_mem n C i j).mpr ⟨hi, hj, hij⟩)
  · simpa only [Finset.card_singleton, andPairSet_card] using one

lemma no_pair_of_zero (n : ℕ) (C : Circuit) (zero : PEqualNP.TopForm.andPairs n C = 0) :
    ¬ ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone n C i j := by
  rintro ⟨i, j, hi, hj, hij⟩
  have empty : andPairSet n C = ∅ := Finset.card_eq_zero.mp ((andPairSet_card n C).trans zero)
  have member := (andPairSet_mem n C i j).mpr ⟨hi, hj, hij⟩
  rw [empty] at member
  exact Finset.notMem_empty _ member

lemma plane_no_nested_bound (C : Circuit) (h : acceptable C)
    (noPair : ¬ ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) :
    64 ≤ C.size :=
  PEqualNP.Outside.L_meta_1751 C h.1 h.2.1 h.2.2 noPair

theorem safe_nested_shrinks (C : Circuit) (ok : acceptable C) (small : C.size < 64)
    (i j : ℕ) (hi : (gateAt C i).op = .and) (hj : (gateAt C j).op = .and)
    (hij : InCone 26 C i j) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (safe : ∀ L, negative L → (C.wires L).getD (26 + i) false = false) :
    ∃ D : Circuit, acceptable D ∧ D.size < C.size := by
  have rows := (separates_iff_rows C).mp ok.2.2
  have hpos : ∃ L, positive L := ⟨_, 0, 0, by decide, rfl⟩
  have hneg : ∃ L, negative L := ⟨_, {0, 1, 2, 5}, by unfold goodQuad; decide +kernel, rfl⟩
  obtain ⟨D, mon, back, drows, measure⟩ := PEqualNP.Outside.L_meta_2061.main26
    positive negative
    (by rintro L ⟨p, l, _, rfl⟩; exact row_length p l)
    (by rintro L ⟨Q, _, rfl⟩; simp [quadRow])
    hpos hneg C ok.1 ok.2.1 rows.1 rows.2 i j hi hj hij safe
  have dOk : acceptable D := ⟨mon, back, (separates_iff_rows D).mpr drows⟩
  rcases measure with shorter | ⟨same, pairs⟩
  · exact ⟨D, dOk, shorter⟩
  · have zero : PEqualNP.TopForm.andPairs 26 D = 0 := by omega
    have bound := plane_no_nested_bound D dOk (no_pair_of_zero 26 D zero)
    omega

theorem lower_has_negative_witness (C : Circuit) (ok : acceptable C) (small : C.size < 64)
    (i j : ℕ) (hi : (gateAt C i).op = .and) (hj : (gateAt C j).op = .and)
    (hij : InCone 26 C i j) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (minimal : ∀ D : Circuit, acceptable D → C.size ≤ D.size) :
    ∃ L, negative L ∧ (C.wires L).getD (26 + i) false = true := by
  by_contra! impossible
  have safe (L : List Bool) (h : negative L) : (C.wires L).getD (26 + i) false = false :=
    Bool.eq_false_iff.mpr (impossible L h)
  obtain ⟨D, dOk, dSize⟩ := safe_nested_shrinks C ok small i j hi hj hij one safe
  exact (Nat.not_lt_of_ge (minimal D dOk)) dSize

end OneNestedAnd

/- Source work/quad1961/OrConeCount.lean -/
namespace OrConeCount

open scoped BigOperators

theorem leaf_count {Wire : Type} [DecidableEq Wire] (leaves joins : Finset Wire)
    (root : Wire) (read : Wire → Finset Wire) (disjoint : Disjoint leaves joins)
    (root_mem : root ∈ leaves ∪ joins)
    (fanin : ∀ gate ∈ joins, (read gate).card ≤ 2)
    (live : ∀ wire ∈ (leaves ∪ joins).erase root, ∃ gate ∈ joins, wire ∈ read gate) :
    leaves.card ≤ joins.card + 1 := by
  let uses : Finset (Wire × Wire) :=
    joins.biUnion fun gate => (read gate).image (fun wire => (gate, wire))
  have covered : (leaves ∪ joins).erase root ⊆ uses.image Prod.snd := by
    intro wire hw
    obtain ⟨gate, hGate, hRead⟩ := live wire hw
    apply Finset.mem_image.mpr
    refine ⟨(gate, wire), Finset.mem_biUnion.mpr ⟨gate, hGate, ?_⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨wire, hRead, rfl⟩
  have lower : ((leaves ∪ joins).erase root).card ≤ uses.card :=
    (Finset.card_le_card covered).trans Finset.card_image_le
  have upper : uses.card ≤ 2 * joins.card := by
    calc
      uses.card ≤ ∑ gate ∈ joins, ((read gate).image (fun wire => (gate, wire))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _gate ∈ joins, 2 :=
        Finset.sum_le_sum fun gate hg => Finset.card_image_le.trans (fanin gate hg)
      _ = 2 * joins.card := by simp [Nat.mul_comm]
  rw [Finset.card_erase_of_mem root_mem, Finset.card_union_of_disjoint disjoint] at lower
  omega

end OrConeCount

/- Source work/quad1961/OrSupportDag.lean -/
namespace OrConeCount

structure SupportDag where
  support : ℕ → Finset ℕ
  inputs : ℕ → Finset ℕ
  leaf : ∀ {wire point}, point ∈ support wire → support point = {point} ∧ point ≤ wire
  split : ∀ wire, 2 ≤ (support wire).card →
    (inputs wire).card ≤ 2 ∧
      (∀ pred ∈ inputs wire, pred < wire) ∧
      support wire = (inputs wire).biUnion support

namespace SupportDag

def representative (D : SupportDag) (wire : ℕ) : ℕ :=
  if h : (D.support wire).card = 1 then
    (D.support wire).min' (Finset.card_pos.mp (by omega))
  else wire

lemma representative_multi (D : SupportDag) (wire : ℕ)
    (multi : 2 ≤ (D.support wire).card) : D.representative wire = wire := by
  simp [representative, show (D.support wire).card ≠ 1 by omega]

lemma representative_singleton (D : SupportDag) (wire point : ℕ)
    (single : D.support wire = {point}) : D.representative wire = point := by
  have one : (D.support wire).card = 1 := by simp [single]
  unfold representative
  rw [dite_eq_left one]
  have hm := Finset.min'_mem (D.support wire) (Finset.card_pos.mp (by omega : 0 < (D.support wire).card))
  simpa only [single, Finset.mem_singleton] using hm

lemma representative_support (D : SupportDag) (wire : ℕ) :
    D.support (D.representative wire) = D.support wire := by
  by_cases h : (D.support wire).card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
    rw [D.representative_singleton _ _ hp, hp]
    exact (D.leaf (by simp [hp] : p ∈ D.support wire)).1
  · simp [representative, h]

lemma representative_le (D : SupportDag) (wire : ℕ) : D.representative wire ≤ wire := by
  by_cases h : (D.support wire).card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
    rw [D.representative_singleton _ _ hp]
    exact (D.leaf (by simp [hp] : p ∈ D.support wire)).2
  · simp [representative, h]

def compressedInputs (D : SupportDag) (wire : ℕ) : Finset ℕ :=
  if 2 ≤ (D.support wire).card then
    ((D.inputs wire).filter fun pred => (D.support pred).Nonempty).image D.representative
  else ∅

lemma compressed_mem (D : SupportDag) {wire pred : ℕ} :
    pred ∈ D.compressedInputs wire ↔ 2 ≤ (D.support wire).card ∧
      ∃ child ∈ D.inputs wire, (D.support child).Nonempty ∧ D.representative child = pred := by
  by_cases h : 2 ≤ (D.support wire).card
  · simp only [compressedInputs, ite_eq_left h, Finset.mem_image, Finset.mem_filter, h, true_and]
    aesop
  · simp [compressedInputs, h]

lemma compressed_fanin (D : SupportDag) (wire : ℕ) : (D.compressedInputs wire).card ≤ 2 := by
  by_cases h : 2 ≤ (D.support wire).card
  · rw [compressedInputs, ite_eq_left h]
    exact Finset.card_image_le.trans (Finset.card_filter_le _ _ |>.trans (D.split wire h).1)
  · simp [compressedInputs, h]

lemma compressed_decreasing (D : SupportDag) {wire pred : ℕ}
    (h : pred ∈ D.compressedInputs wire) : pred < wire := by
  obtain ⟨hm, child, hc, _, rfl⟩ := (D.compressed_mem).mp h
  exact (D.representative_le child).trans_lt ((D.split wire hm).2.1 child hc)

def Reaches (D : SupportDag) (root wire : ℕ) : Prop :=
  Relation.ReflTransGen (fun w p => p ∈ D.compressedInputs w) root wire

lemma reached_le (D : SupportDag) {root wire : ℕ} (h : D.Reaches root wire) : wire ≤ root := by
  induction h with
  | refl => exact le_rfl
  | tail _ step ih => exact (D.compressed_decreasing step).le.trans ih

lemma point_reaches (D : SupportDag) (root : ℕ) {point : ℕ}
    (hb : point ∈ D.support root) : D.Reaches (D.representative root) point := by
  induction root using Nat.strong_induction_on with
  | ind root ih =>
    by_cases multi : 2 ≤ (D.support root).card
    · rw [D.representative_multi root multi]
      have hunion := (D.split root multi).2.2
      rw [hunion] at hb
      obtain ⟨child, ht, hp⟩ := Finset.mem_biUnion.mp hb
      have next : D.representative child ∈ D.compressedInputs root :=
        (D.compressed_mem).mpr ⟨multi, child, ht, ⟨point, hp⟩, rfl⟩
      exact (Relation.ReflTransGen.single next).trans
        (ih child ((D.split root multi).2.1 child ht) hp)
    · have hpos := Finset.card_pos.mpr ⟨point, hb⟩
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (show (D.support root).card = 1 by omega)
      have heq : point = p := by simpa [hp] using hb
      rw [D.representative_singleton root p hp, heq]
      exact Relation.ReflTransGen.refl

noncomputable def joins (D : SupportDag) (root : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (root + 1)).filter fun wire =>
    2 ≤ (D.support wire).card ∧ D.Reaches root wire

lemma joins_mem (D : SupportDag) {root wire : ℕ} :
    wire ∈ D.joins root ↔ 2 ≤ (D.support wire).card ∧ D.Reaches root wire := by
  classical
  simp only [joins, Finset.mem_filter, Finset.mem_range]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact Nat.lt_succ_of_le (D.reached_le h.2)

theorem support_card_le (D : SupportDag) (root : ℕ) :
    (D.support root).card ≤ (D.joins root).card + 1 := by
  by_cases multi : 2 ≤ (D.support root).card
  · apply leaf_count (D.support root) (D.joins root) root D.compressedInputs
    · apply Finset.disjoint_left.mpr
      intro p hp join
      have bad := ((D.joins_mem).mp join).1
      rw [(D.leaf hp).1, Finset.card_singleton] at bad
      omega
    · exact Finset.mem_union_right _ ((D.joins_mem).mpr ⟨multi, Relation.ReflTransGen.refl⟩)
    · exact fun gate _ => D.compressed_fanin gate
    · intro wire h
      obtain ⟨notRoot, belong⟩ := Finset.mem_erase.mp h
      have path : D.Reaches root wire := by
        rcases Finset.mem_union.mp belong with leaf | join
        · have reach := D.point_reaches root leaf
          rwa [D.representative_multi root multi] at reach
        · exact ((D.joins_mem).mp join).2
      rcases Relation.ReflTransGen.cases_tail path with equal | ⟨pred, earlierPath, step⟩
      · contradiction
      · exact ⟨pred, (D.joins_mem).mpr ⟨((D.compressed_mem).mp step).1, earlierPath⟩, step⟩
  · omega

end SupportDag
end OrConeCount

/- Source work/quad1961/RawSupport.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def earlierInputs (n : ℕ) (C : Circuit) (wire : ℕ) : Finset ℕ :=
  (gateAt C (wire - n)).inputs.toFinset.filter fun pred => pred < wire

def rawSupport (n : ℕ) (C : Circuit) (wire : ℕ) : Finset ℕ :=
  if wire < n then {wire}
  else match (gateAt C (wire - n)).op with
    | .or => (earlierInputs n C wire).attach.biUnion fun pred => rawSupport n C pred.val
    | _ => ∅
termination_by wire
decreasing_by exact (Finset.mem_filter.mp pred.property).2

theorem rawSupport_primary (n : ℕ) (C : Circuit) {wire : ℕ} (hw : wire < n) :
    rawSupport n C wire = {wire} := by
  rw [rawSupport, ite_eq_left hw]

theorem rawSupport_and (n : ℕ) (C : Circuit) {wire : ℕ} (hw : n ≤ wire)
    (ng : (gateAt C (wire - n)).op ≠ .or) : rawSupport n C wire = ∅ := by
  rw [rawSupport, ite_eq_right (not_lt_of_ge hw)]
  cases e : (gateAt C (wire - n)).op <;> simp_all

theorem rawSupport_or (n : ℕ) (C : Circuit) {wire : ℕ} (hw : n ≤ wire)
    (op : (gateAt C (wire - n)).op = .or) :
    rawSupport n C wire = (earlierInputs n C wire).biUnion (rawSupport n C) := by
  rw [rawSupport, ite_eq_right (not_lt_of_ge hw), op]
  ext point
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨pred, _, member⟩
    exact ⟨pred.val, pred.property, member⟩
  · rintro ⟨pred, earlier, member⟩
    exact ⟨⟨pred, earlier⟩, Finset.mem_attach _ _, member⟩

lemma rawSupport_bounds (n : ℕ) (C : Circuit) : ∀ wire point,
    point ∈ rawSupport n C wire → point < n ∧ point ≤ wire := by
  intro wire
  induction wire using Nat.strong_induction_on with
  | ind wire ih =>
    intro point member
    by_cases h : wire < n
    · rw [rawSupport_primary n C h, Finset.mem_singleton] at member
      subst point
      exact ⟨h, le_rfl⟩
    · by_cases op : (gateAt C (wire - n)).op = .or
      · rw [rawSupport_or n C (not_lt.mp h) op] at member
        obtain ⟨pred, older, hp⟩ := Finset.mem_biUnion.mp member
        have before := (Finset.mem_filter.mp older).2
        obtain ⟨pointRaw, pointLe⟩ := ih pred before point hp
        exact ⟨pointRaw, pointLe.trans before.le⟩
      · rw [rawSupport_and n C (not_lt.mp h) op] at member
        exact False.elim (Finset.notMem_empty _ member)

lemma gateAt_fanin (C : Circuit) (mono : Monotone2 C) (j : ℕ) :
    (gateAt C j).inputs.length ≤ 2 := by
  by_cases h : j < C.gates.length
  · exact (mono _ (List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j h⟩)).2
  · have eq : gateAt C j = ⟨.or, []⟩ := List.getD_eq_default _ _ (not_lt.mp h)
    rw [eq]
    simp

def selectedSupport (n : ℕ) (C : Circuit) (labels : Finset ℕ) (wire : ℕ) : Finset ℕ :=
  rawSupport n C wire ∩ labels

def selectedDag (n : ℕ) (C : Circuit) (mono : Monotone2 C) (labels : Finset ℕ) :
    OrConeCount.SupportDag where
  support := selectedSupport n C labels
  inputs := earlierInputs n C
  leaf := by
    intro wire point hp
    obtain ⟨path, chosen⟩ := Finset.mem_inter.mp hp
    obtain ⟨raw, order⟩ := rawSupport_bounds n C wire point path
    exact ⟨by simp [selectedSupport, rawSupport_primary n C raw, chosen], order⟩
  split := by
    intro wire bound
    have notPrimary : n ≤ wire := by
      by_contra! h
      simp [selectedSupport, rawSupport_primary n C h, Finset.singleton_inter] at bound
      split at bound <;> simp at bound
    have orGate : (gateAt C (wire - n)).op = .or := by
      by_contra! h
      simp [selectedSupport, rawSupport_and n C notPrimary h] at bound
    refine ⟨(Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans (gateAt_fanin C mono _)),
      fun _ hp => (Finset.mem_filter.mp hp).2, ?_⟩
    ext point
    simp only [selectedSupport, rawSupport_or n C notPrimary orGate, Finset.mem_inter, Finset.mem_biUnion]
    aesop

end OneNestedAnd

/- Source work/quad1961/frontier-lean/ClearLower.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

 
def clearLower (C : Circuit) (h : ℕ) : Circuit :=
  { C with gates := C.gates.set h ⟨.or, []⟩ }

@[simp] theorem clearLower_len (C : Circuit) (h : ℕ) :
    (clearLower C h).gates.length = C.gates.length := by
  simp [clearLower]

@[simp] theorem clearLower_size (C : Circuit) (h : ℕ) :
    (clearLower C h).size = C.size := clearLower_len C h

@[simp] theorem clearLower_output (C : Circuit) (h : ℕ) :
    (clearLower C h).output = C.output := rfl

theorem clearLower_at_self {C : Circuit} {h : ℕ} (hh : h < C.gates.length) :
    gateAt (clearLower C h) h = ⟨.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, clearLower, hh]

theorem clearLower_at_other {C : Circuit} {h j : ℕ} (hne : j ≠ h) :
    gateAt (clearLower C h) j = gateAt C j := by
  simp [gateAt, List.getD_eq_getElem?_getD, clearLower, Ne.symm hne]

theorem clearLower_mono {C : Circuit} (mono : Monotone2 C) (h : ℕ) :
    Monotone2 (clearLower C h) := by
  intro g hg
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
  have jD := (List.getElem?_eq_some_iff.mp hj).1
  have jC : j < C.gates.length := by simpa using jD
  have gj : gateAt (clearLower C h) j = g := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [← gj]
  by_cases e : j = h
  · subst j
    rw [clearLower_at_self jC]
    simp
  · rw [clearLower_at_other e]
    exact mono _ (List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j jC⟩)

theorem clearLower_back {n : ℕ} {C : Circuit} (back : ReadsBack n C) (h : ℕ) :
    ReadsBack n (clearLower C h) := by
  intro j hj i hi
  have jC : j < C.gates.length := by simpa using hj
  by_cases e : j = h
  · subst j
    simp [clearLower_at_self jC] at hi
  · rw [clearLower_at_other e] at hi
    exact back j jC i hi

theorem clearLower_cone {n : ℕ} {C : Circuit} (h i : ℕ) :
    ∀ j, InCone n (clearLower C h) i j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro anc
    obtain ⟨bound, k, before, reads, prior⟩ := (inCone_iff n (clearLower C h) i j).mp anc
    have boundC : j < C.gates.length := by simpa using bound
    by_cases e : j = h
    · subst j
      simp [clearLower_at_self boundC] at reads
    · rw [clearLower_at_other e] at reads
      exact (inCone_iff n C i j).mpr ⟨boundC, k, before, reads, prior.imp_right (ih k before)⟩

theorem cone_lt {n : ℕ} {C : Circuit} {i j : ℕ} (anc : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨_, k, before, _, prior⟩ := (inCone_iff n C i j).mp anc
    rcases prior with rfl | prior
    · exact before
    · exact (ih k before prior).trans before

 
theorem andPair_unique {n : ℕ} {C : Circuit} {h H : ℕ}
    (small : PEqualNP.TopForm.andPairs n C ≤ 1) (low : (gateAt C h).op = .and)
    (high : (gateAt C H).op = .and) (nest : InCone n C h H) :
    ∀ {i j}, (gateAt C i).op = .and → (gateAt C j).op = .and →
      InCone n C i j → i = h ∧ j = H := by
  classical
  let pairs : Finset (ℕ × ℕ) := (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
    (fun p => (gateAt C p.1).op = .and ∧ (gateAt C p.2).op = .and ∧ InCone n C p.1 p.2)
  have card : pairs.card ≤ 1 := by
    have e : pairs.card = PEqualNP.TopForm.andPairs n C := by
      unfold PEqualNP.TopForm.andPairs
      congr 1
      ext p
      simp [pairs]
    rwa [e]
  have member {a b : ℕ} (oa : (gateAt C a).op = .and) (ob : (gateAt C b).op = .and)
      (ab : InCone n C a b) : (a,b) ∈ pairs := by
    have be := ((inCone_iff n C a b).mp ab).1
    have ae := (cone_lt ab).trans be
    simp [pairs, ae, be, oa, ob, ab]
  intro i j oi oj ij
  have e := Finset.card_le_one.mp card _ (member oi oj ij) _ (member low high nest)
  exact Prod.mk.inj e

 
theorem clearLower_flat {n : ℕ} {C : Circuit} {h H : ℕ}
    (small : PEqualNP.TopForm.andPairs n C ≤ 1) (low : (gateAt C h).op = .and)
    (high : (gateAt C H).op = .and) (nest : InCone n C h H) :
    ∀ i j, (gateAt (clearLower C h) i).op = .and →
      (gateAt (clearLower C h) j).op = .and → ¬ InCone n (clearLower C h) i j := by
  intro i j oi oj ij
  have jC := ((inCone_iff n C i j).mp (clearLower_cone h i j ij)).1
  have iC := (cone_lt ij).trans jC
  have ne {k : ℕ} (bound : k < C.gates.length) (op : (gateAt (clearLower C h) k).op = .and) :
      k ≠ h := by
    rintro rfl
    rw [clearLower_at_self bound] at op
    contradiction
  have ni := ne iC oi
  have nj := ne jC oj
  rw [clearLower_at_other ni] at oi
  rw [clearLower_at_other nj] at oj
  exact ni (andPair_unique small low high nest oi oj (clearLower_cone h i j ij)).1

private theorem gateValue {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (back : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false = (gateAt C j).op.eval
      ((gateAt C j).inputs.map ((C.wires x).getD · false)) := by
  have h := W_spec C.gates x j _ (gateAt_some C j hj)
  rw [hx] at h
  change (W C.gates x).getD (n + j) false = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [ite_eq_left (back j hj a ha)]
  rfl

private theorem gate_mono {g : Gate} (hop : g.op = .and ∨ g.op = .or)
    {a b : ℕ → Bool} (under : ∀ i ∈ g.inputs, a i = true → b i = true) :
    g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
  rcases hop with op | op
  · simp only [op, GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro all t ⟨i, hi, rfl⟩
    exact under i hi (all (a i) ⟨i, hi, rfl⟩)
  · simp only [op, GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨_, ⟨i, hi, rfl⟩, hp⟩
    exact ⟨b i, ⟨i, hi, rfl⟩, under i hi hp⟩

 
theorem clearLower_le {n : ℕ} {C : Circuit} (mono : Monotone2 C) (back : ReadsBack n C)
    {x : List Bool} (hx : x.length = n) (h : ℕ) :
    ∀ w, ((clearLower C h).wires x).getD w false = true → (C.wires x).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro positive
    by_cases primary : w < n
    · change (W (clearLower C h).gates x).getD w false = true at positive
      change (W C.gates x).getD w false = true
      rw [W_inp (clearLower C h).gates x w (by omega)] at positive
      rw [W_inp C.gates x w (by omega)]
      exact positive
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases bound : j < C.gates.length
      · have boundD : j < (clearLower C h).gates.length := by simpa using bound
        rw [gateValue hx (clearLower_back back h) boundD] at positive
        by_cases e : j = h
        · subst j
          simp [clearLower_at_self bound, GateOp.eval] at positive
        · rw [clearLower_at_other e] at positive
          rw [gateValue hx back bound]
          have hm := mono _ (List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j bound⟩)
          exact gate_mono hm.1 (fun i hi => ih i (back j bound i hi)) positive
      · have oob : x.length + (clearLower C h).gates.length ≤ n + j := by
          simp only [hx, clearLower_len]
          omega
        change (W (clearLower C h).gates x).getD (n + j) false = true at positive
        rw [W_oob (clearLower C h).gates x _ oob] at positive
        contradiction

theorem clearLower_eval_le {n : ℕ} {C : Circuit} (mono : Monotone2 C) (back : ReadsBack n C)
    {x : List Bool} (hx : x.length = n) (h : ℕ) :
    (clearLower C h).eval x = true → C.eval x = true := by
  simpa [Circuit.eval] using clearLower_le mono back hx h C.output

 
theorem clearLower_agree {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    {x : List Bool} (hx : x.length = n) {h : ℕ}
    (already : (C.wires x).getD (n + h) false = false) :
    ∀ w, ((clearLower C h).wires x).getD w false = (C.wires x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases primary : w < n
    · change (W (clearLower C h).gates x).getD w false = (W C.gates x).getD w false
      rw [W_inp _ x w (by omega), W_inp _ x w (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases bound : j < C.gates.length
      · have boundD : j < (clearLower C h).gates.length := by simpa using bound
        rw [gateValue hx (clearLower_back back h) boundD]
        by_cases e : j = h
        · subst j
          rw [clearLower_at_self bound, already]
          rfl
        · rw [clearLower_at_other e, gateValue hx back bound]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact ih i (back j bound i hi)
      · have oob : x.length + C.gates.length ≤ n + j := by omega
        change (W (clearLower C h).gates x).getD (n + j) false = (W C.gates x).getD (n + j) false
        rw [W_oob _ x _ (by simpa using oob), W_oob _ x _ oob]

theorem clearLower_eval_agree {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    {x : List Bool} (hx : x.length = n) {h : ℕ}
    (already : (C.wires x).getD (n + h) false = false) :
    (clearLower C h).eval x = C.eval x := by
  simpa [Circuit.eval] using clearLower_agree back hx already C.output

theorem clearLower_lost_requires_true {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    {x : List Bool} (hx : x.length = n) {h : ℕ}
    (lost : (clearLower C h).eval x = false) (orig : C.eval x = true) :
    (C.wires x).getD (n + h) false = true := by
  by_contra neg
  have e := clearLower_eval_agree back hx (Bool.eq_false_iff.mpr neg)
  rw [lost, orig] at e
  contradiction

private theorem clearLower_drop_input {n : ℕ} {C : Circuit} (mono : Monotone2 C)
    (back : ReadsBack n C) {x : List Bool} (hx : x.length = n) {h j : ℕ}
    (bound : j < C.gates.length) (ne : j ≠ h)
    (orig : (C.wires x).getD (n + j) false = true)
    (lost : ((clearLower C h).wires x).getD (n + j) false = false) :
    ∃ w ∈ (gateAt C j).inputs, (C.wires x).getD w false = true ∧
      ((clearLower C h).wires x).getD w false = false := by
  classical
  have boundD : j < (clearLower C h).gates.length := by simpa using bound
  rw [gateValue hx back bound] at orig
  rw [gateValue hx (clearLower_back back h) boundD, clearLower_at_other ne] at lost
  have hm := mono _ (List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j bound⟩)
  by_contra missing
  have above : ∀ i ∈ (gateAt C j).inputs, (C.wires x).getD i false = true →
      ((clearLower C h).wires x).getD i false = true := by
    intro i hi positive
    cases e : ((clearLower C h).wires x).getD i false
    · exact (missing ⟨i, hi, positive, e⟩).elim
    · rfl
  have h := gate_mono hm.1 above orig
  rw [lost] at h
  contradiction

private theorem dropped_wire_is_gate {n : ℕ} {C : Circuit} {h w : ℕ}
    {x : List Bool} (hx : x.length = n) (orig : (C.wires x).getD w false = true)
    (lost : ((clearLower C h).wires x).getD w false = false) :
    ∃ j < C.gates.length, w = n + j := by
  have lower : n ≤ w := by
    by_contra smaller
    change (W C.gates x).getD w false = true at orig
    change (W (clearLower C h).gates x).getD w false = false at lost
    rw [W_inp _ x w (by omega)] at orig lost
    rw [orig] at lost
    contradiction
  have upper : w < n + C.gates.length := by
    by_contra larger
    change (W C.gates x).getD w false = true at orig
    rw [W_oob _ x w (by omega)] at orig
    contradiction
  exact ⟨w - n, by omega, by omega⟩

private theorem clearLower_lost_has_path {n : ℕ} {C : Circuit} (mono : Monotone2 C)
    (back : ReadsBack n C) {x : List Bool} (hx : x.length = n) (h : ℕ) :
    ∀ j < C.gates.length, (C.wires x).getD (n + j) false = true →
      ((clearLower C h).wires x).getD (n + j) false = false → h = j ∨ InCone n C h j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro bound orig lost
    by_cases e : j = h
    · exact Or.inl e.symm
    · obtain ⟨w, reads, pos, neg⟩ := clearLower_drop_input mono back hx bound e orig lost
      obtain ⟨i, iC, rfl⟩ := dropped_wire_is_gate hx pos neg
      have before : i < j := by have := back j bound (n+i) reads; omega
      exact Or.inr ((inCone_iff n C h j).mpr ⟨bound, i, before, reads, ih i before iC pos neg⟩)

private theorem or_input_negative {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    {x : List Bool} (hx : x.length = n) {j w : ℕ} (bound : j < C.gates.length)
    (op : (gateAt C j).op = .or) (reads : w ∈ (gateAt C j).inputs)
    (neg : (C.wires x).getD (n + j) false = false) :
    (C.wires x).getD w false = false := by
  apply Bool.eq_false_iff.mpr
  intro pos
  have any : (gateAt C j).op.eval ((gateAt C j).inputs.map ((C.wires x).getD · false)) = true := by
    simp only [op, GateOp.eval, List.any_eq_true, List.mem_map, id]
    exact ⟨true, ⟨w, reads, pos⟩, rfl⟩
  rw [gateValue hx back bound, any] at neg
  contradiction

 
theorem clearLower_lost_at_upper {n : ℕ} {C : Circuit} (mono : Monotone2 C)
    (back : ReadsBack n C) {h H : ℕ} (small : PEqualNP.TopForm.andPairs n C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone n C h H)
    {x z : List Bool} (hx : x.length = n) (hz : z.length = n)
    (lowerOnNegative : (C.wires z).getD (n + h) false = true)
    (neg : C.eval z = false) (positive : C.eval x = true)
    (lost : (clearLower C h).eval x = false) :
    (C.wires x).getD (n + H) false = true ∧
      ((clearLower C h).wires x).getD (n + H) false = false := by
  have through : ∀ j < C.gates.length, (C.wires x).getD (n+j) false = true →
      ((clearLower C h).wires x).getD (n+j) false = false →
      (C.wires z).getD (n+j) false = false →
      (C.wires x).getD (n+H) false = true ∧
        ((clearLower C h).wires x).getD (n+H) false = false := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro bound orig drop noZ
      have ne : j ≠ h := by
        rintro rfl
        rw [lowerOnNegative] at noZ
        contradiction
      have hm := mono _ (List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j bound⟩)
      rcases hm.1 with op | op
      · rcases clearLower_lost_has_path mono back hx h j bound orig drop with equal | anc
        · exact (ne equal.symm).elim
        · have equal := (andPair_unique small low high nest low op anc).2
          subst j
          exact ⟨orig, drop⟩
      · obtain ⟨w, reads, pos, zero⟩ := clearLower_drop_input mono back hx bound ne orig drop
        have noZ' := or_input_negative back hz bound op reads noZ
        obtain ⟨i, iC, rfl⟩ := dropped_wire_is_gate hx pos zero
        have before : i < j := by have := back j bound (n+i) reads; omega
        exact ih i before iC pos zero noZ'
  change (C.wires z).getD C.output false = false at neg
  change (C.wires x).getD C.output false = true at positive
  change ((clearLower C h).wires x).getD C.output false = false at lost
  obtain ⟨j, bound, out⟩ := dropped_wire_is_gate hx positive lost
  rw [out] at positive lost neg
  exact through j bound positive lost neg


end OneNestedAnd

/- Source work/quad1961/SupportEval.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def Feeds (n : ℕ) (C : Circuit) (gate wire : ℕ) : Prop :=
  wire = n + gate ∨ (n ≤ wire ∧ InCone n C gate (wire - n))

lemma feeds_of_reader (n : ℕ) (C : Circuit) (back : ReadsBack n C) {src dst wire : ℕ}
    (hdst : dst < C.gates.length) (read : wire ∈ (gateAt C dst).inputs)
    (source : Feeds n C src wire) : Feeds n C src (n + dst) := by
  have early := back dst hdst wire read
  right
  refine ⟨by omega, ?_⟩
  simp only [Nat.add_sub_cancel_left]
  apply (inCone_iff n C src dst).mpr
  rcases source with equal | ⟨raw, path⟩
  · subst wire
    exact ⟨hdst, src, by omega, read, Or.inl rfl⟩
  · refine ⟨hdst, wire - n, by omega, ?_, Or.inr path⟩
    rwa [Nat.add_sub_of_le raw]

lemma feeds_iff_reader (n : ℕ) (C : Circuit) (back : ReadsBack n C) {src dst : ℕ}
    (hdst : dst < C.gates.length) (different : src ≠ dst) :
    Feeds n C src (n + dst) ↔ ∃ w ∈ (gateAt C dst).inputs, Feeds n C src w := by
  constructor
  · rintro (equal | ⟨_, anc⟩)
    · exact False.elim (different (by omega))
    · simp only [Nat.add_sub_cancel_left] at anc
      obtain ⟨_, pred, _, member, equal | hp⟩ := (inCone_iff n C src dst).mp anc
      · exact ⟨n + pred, member, Or.inl (by rw [equal])⟩
      · exact ⟨n + pred, member, Or.inr ⟨by omega, by simpa using hp⟩⟩
  · rintro ⟨w, hw, source⟩
    exact feeds_of_reader n C back hdst hw source

def wireOn (C : Circuit) (x : List Bool) (wire : ℕ) : Prop :=
  (C.wires x).getD wire false = true

lemma wireOn_or (n : ℕ) (C : Circuit) (back : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    {j : ℕ} (bound : j < C.gates.length) (op : (gateAt C j).op = .or) :
    wireOn C x (n + j) ↔ ∃ w ∈ (gateAt C j).inputs, wireOn C x w := by
  have evaluation := W_spec C.gates x j (gateAt C j) (gateAt_some C j bound)
  simp only [hx] at evaluation
  have readEq : ((gateAt C j).inputs.map fun i =>
      if i < n + j then (W C.gates x).getD i false else false) =
      (gateAt C j).inputs.map (fun i => (W C.gates x).getD i false) := by
    apply List.map_congr_left
    intro i hi
    simp [back j bound i hi]
  change (W C.gates x).getD (n + j) false = true ↔
    ∃ w ∈ (gateAt C j).inputs, (W C.gates x).getD w false = true
  rw [evaluation, readEq, op, GateOp.eval, List.any_eq_true]
  simp only [List.mem_map, id_eq]
  aesop

theorem selected_or_value (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (h : ℕ) (hAnd : (gateAt C h).op = .and) :
    ∀ w < n + C.gates.length,
      (∀ j, (gateAt C j).op = .and → Feeds n C j w → j = h) →
      (wireOn C x w ↔ (∃ p ∈ rawSupport n C w, x.getD p false = true) ∨
        (Feeds n C h w ∧ wireOn C x (n + h))) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro valid allowed
    by_cases primary : w < n
    · have noFeed : ¬ Feeds n C h w := by
        rintro (eq | ⟨ge, _⟩) <;> omega
      change (W C.gates x).getD w false = true ↔ _
      rw [W_inp _ _ _ (by simpa [hx] using primary), rawSupport_primary n C primary]
      simp [noFeed]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have gmem : gateAt C j ∈ C.gates := List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j hj⟩
      have options : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by simpa using (mono _ gmem).1
      rcases options with andGate | orGate
      · have jeq := allowed j andGate (Or.inl rfl)
        subst j
        have empty : rawSupport n C (n + h) = ∅ := by
          apply rawSupport_and n C (by omega)
          simp [andGate]
        simp [empty, Feeds]
      · have different : h ≠ j := by
          intro equal
          subst h
          rw [orGate] at hAnd
          cases hAnd
        have eq : rawSupport n C (n + j) = (earlierInputs n C (n + j)).biUnion (rawSupport n C) := by
          apply rawSupport_or n C (by omega)
          simpa using orGate
        rw [wireOn_or n C back x hx hj orGate, eq, feeds_iff_reader n C back hj different]
        have child_value (w : ℕ) (used : w ∈ (gateAt C j).inputs) :=
          ih w (back j hj w used) (by have := back j hj w used; omega)
            (fun k kAnd feed => allowed k kAnd (feeds_of_reader n C back hj used feed))
        constructor
        · rintro ⟨w, used, on⟩
          rcases (child_value w used).mp on with ⟨p, raw, bit⟩ | ⟨feed, visible⟩
          · left
            refine ⟨p, Finset.mem_biUnion.mpr ⟨w, ?_, raw⟩, bit⟩
            exact Finset.mem_filter.mpr ⟨by simpa using used, back j hj w used⟩
          · exact Or.inr ⟨⟨w, used, feed⟩, visible⟩
        · rintro (⟨p, inSupport, bit⟩ | ⟨⟨w, used, feed⟩, hOn⟩)
          · obtain ⟨w, child, pchild⟩ := Finset.mem_biUnion.mp inSupport
            have used : w ∈ (gateAt C j).inputs := by
              simpa [earlierInputs] using (Finset.mem_filter.mp child).1
            exact ⟨w, used, (child_value w used).mpr (Or.inl ⟨p, pchild, bit⟩)⟩
          · exact ⟨w, used, (child_value w used).mpr (Or.inr ⟨feed, hOn⟩)⟩

end OneNestedAnd

/- Source work/nested1962/DeadSlot.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

private def lower (removed wire : ℕ) : ℕ :=
  if removed < wire then wire - 1 else wire

private def lowerGate (removed : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (lower removed)⟩

private def eraseSlot (n : ℕ) (C : Circuit) (p : ℕ) : Circuit :=
  ⟨(C.gates.eraseIdx p).map (lowerGate (n + p)), lower (n + p) C.output⟩

private lemma lower_add (n p i : ℕ) : lower (n + p) (n + i) = n + lower p i := by
  unfold lower
  by_cases h : p < i
  · rw [if_pos (by omega), if_pos h]; omega
  · rw [if_neg (by omega), if_neg h]

private lemma lower_lt {p u v : ℕ} (h : u < v) (ne : u ≠ p) : lower p u < lower p v := by
  unfold lower
  split <;> split <;> omega

private lemma erased_get (n : ℕ) (C : Circuit) {p j : ℕ} (hne : j ≠ p) :
    (eraseSlot n C p).gates[lower p j]? = (C.gates[j]?).map (lowerGate (n + p)) := by
  simp only [eraseSlot, List.getElem?_map]
  congr 1
  by_cases h : j < p
  · simp only [lower, if_neg (by omega : ¬ p < j)]
    exact List.getElem?_eraseIdx_of_lt h
  · simp only [lower, if_pos (by omega : p < j)]
    rw [List.getElem?_eraseIdx_of_ge (by omega : p ≤ j - 1)]
    simp only [show j - 1 + 1 = j by omega]

private lemma gateAt_of_some {C : Circuit} {j : ℕ} {g : Gate} (hj : C.gates[j]? = some g) :
    gateAt C j = g := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

private lemma lowered_back {n : ℕ} {C : Circuit} {p : ℕ} (hp : p < C.size)
    (back : ReadsBack n C) (unread : ∀ j < C.size, n + p ∉ (gateAt C j).inputs) :
    ReadsBack n (eraseSlot n C p) := by
  intro j hj w hw
  have hlen : (eraseSlot n C p).gates.length + 1 = C.gates.length := by
    simpa [eraseSlot] using List.length_eraseIdx_add_one (l := C.gates) hp
  let k := if j < p then j else j + 1
  have hk : k < C.gates.length := by dsimp [k]; split <;> omega
  have hne : k ≠ p := by dsimp [k]; split <;> omega
  have lowered : lower p k = j := by
    dsimp [k]
    split <;> simp only [lower] <;> split <;> omega
  let g : Gate := C.gates[k]
  have hg : C.gates[k]? = some g := List.getElem?_eq_getElem hk
  have hr : (eraseSlot n C p).gates[j]? = some (lowerGate (n + p) g) := by
    simpa [lowered, hg] using erased_get n C hne
  rw [gateAt_of_some hr] at hw
  obtain ⟨old, holds, rfl⟩ := List.mem_map.mp hw
  have ih : old ∈ (gateAt C k).inputs := by simpa [gateAt_of_some hg] using holds
  have absent : old ≠ n + p := by
    intro equal
    exact unread k hk (by simpa only [equal] using ih)
  have rel := lower_lt (back k hk old ih) absent
  simpa [lower_add, lowered] using rel

private lemma gate_value {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (back : ReadsBack n C) {j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) :
    (C.wires x).getD (n + j) false = g.op.eval (g.inputs.map ((C.wires x).getD · false)) := by
  have h := W_spec C.gates x j g hg
  rw [hx] at h
  change (W C.gates x).getD (n + j) false = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro a ha
  have ha' : a ∈ (gateAt C j).inputs := by simpa [gateAt_of_some hg] using ha
  rw [if_pos (back j (List.getElem?_eq_some_iff.mp hg).1 a ha')]
  rfl

 
theorem erase_unread (n : ℕ) (C : Circuit) (p : ℕ) (hp : p < C.size)
    (mono : Monotone2 C) (back : ReadsBack n C) (hout : C.output ≠ n + p)
    (unread : ∀ j < C.size, n + p ∉ (gateAt C j).inputs) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size + 1 = C.size ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  let D := eraseSlot n C p
  have len : D.size + 1 = C.size := by
    simpa [D, eraseSlot, Circuit.size] using List.length_eraseIdx_add_one (l := C.gates) hp
  have monoD : Monotone2 D := by
    intro g hg
    obtain ⟨old, hm, rfl⟩ := List.mem_map.mp hg
    have original : old ∈ C.gates := (List.eraseIdx_sublist (l := C.gates) p).subset hm
    simpa [lowerGate] using mono old original
  have backD : ReadsBack n D := lowered_back hp back unread
  refine ⟨D, monoD, backD, len, ?_⟩
  intro x hx
  have values : ∀ w, w ≠ n + p →
      (D.wires x).getD (lower (n + p) w) false = (C.wires x).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hne
      by_cases hw : w < n
      · simp only [lower, if_neg (by omega : ¬ n + p < w)]
        exact (W_inp D.gates x w (by omega)).trans (W_inp C.gates x w (by omega)).symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hne' : j ≠ p := by omega
        rw [lower_add]
        by_cases hj : j < C.size
        · let g : Gate := C.gates[j]
          have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
          have hr : D.gates[lower p j]? = some (lowerGate (n + p) g) := by
            simp [D, erased_get n C hne', hg]
          rw [gate_value hx backD hr, gate_value hx back hg]
          simp only [lowerGate, List.map_map, Function.comp_def]
          congr 1
          apply List.map_congr_left
          intro a ha
          have ha' : a ∈ (gateAt C j).inputs := by simpa [gateAt_of_some hg] using ha
          exact ih a (back j hj a ha') (fun e => unread j hj (e ▸ ha'))
        · have hD : x.length + D.gates.length ≤ n + lower p j := by
            unfold Circuit.size at hp len hj
            simp only [lower, if_pos (by omega : p < j)]
            omega
          have hC : x.length + C.gates.length ≤ n + j := by
            unfold Circuit.size at hj
            omega
          exact (W_oob D.gates x _ hD).trans (W_oob C.gates x _ hC).symm
  exact values C.output hout

 
theorem minimal_inCone (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (minimal : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      (∀ x : List Bool, x.length = n → D.eval x = C.eval x) → C.size ≤ D.size)
    (out : ℕ) (hout : C.output = n + out) :
    ∀ i < C.size, i ≠ out → InCone n C i out := by
  intro i hi hne
  by_contra missing
  obtain ⟨p, hp, notOut, unread⟩ := unread_dead_slot n C back out ⟨i, hi, hne, missing⟩
  obtain ⟨D, hm, hb, smaller, value⟩ := erase_unread n C p hp mono back (by omega) unread
  have := minimal D hm hb value
  omega

end OneNestedAnd

/- Source work/quad1961/UniqueNest.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

abbrev StrictBinary (C : Circuit) : Prop := ∀ g ∈ C.gates,
  g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0

abbrev AllowsOnly (n : ℕ) (C : Circuit) (h wire : ℕ) : Prop :=
  ∀ k, (gateAt C k).op = .and → Feeds n C k wire → k = h

lemma input_pair (C : Circuit) (strict : StrictBinary C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a ≠ b := by
  have member := List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j hj⟩
  obtain ⟨two, distinct⟩ := strict _ member
  obtain ⟨a, b, equal⟩ := List.length_eq_two.mp two
  exact ⟨a, b, equal, by simpa [equal] using distinct⟩

lemma feeds_order (n : ℕ) (C : Circuit) {j wire : ℕ} (h : Feeds n C j wire) : n + j ≤ wire := by
  rcases h with rfl | ⟨_, path⟩
  · exact le_rfl
  · have order := cone_lt path
    omega

lemma feeds_and_input_unique (n : ℕ) (C : Circuit) (back : ReadsBack n C) {h H : ℕ}
    (one : PEqualNP.TopForm.andPairs n C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone n C h H)
    {j w t : ℕ} (jAnd : (gateAt C j).op = .and) (read : w ∈ (gateAt C j).inputs)
    (tAnd : (gateAt C t).op = .and) (source : Feeds n C t w) : t = h ∧ j = H := by
  have bound := gateAt_and_bound C j jAnd
  have order := (feeds_order n C source).trans_lt (back j bound w read)
  have enters := feeds_of_reader n C back bound read source
  rcases enters with equal | ⟨_, path⟩
  · omega
  · simp only [Nat.add_sub_cancel_left] at path
    exact andPair_unique one low high nest tAnd jAnd path

theorem empty_raw_is_lower (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (strict : StrictBinary C) (h : ℕ) : ∀ w < n + C.gates.length,
      AllowsOnly n C h w → rawSupport n C w = ∅ → w = n + h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro valid allowed empty
    by_cases primary : w < n
    · rw [rawSupport_primary n C primary] at empty
      simp at empty
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have gmem : gateAt C j ∈ C.gates := List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j hj⟩
      have options : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by simpa using (mono _ gmem).1
      rcases options with andGate | orGate
      · rw [allowed j andGate (Or.inl rfl)]
      · obtain ⟨a, b, two, distinct⟩ := input_pair C strict j hj
        have root := rawSupport_or n C (wire := n + j) (by omega) (by simpa using orGate)
        have childEqual (v : ℕ) (read : v ∈ (gateAt C j).inputs) : v = n + h := by
          have earlier := back j hj v read
          apply ih v earlier (by omega) (fun k kAnd feed => allowed k kAnd (feeds_of_reader n C back hj read feed))
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro label inChild
          have mem : label ∈ (earlierInputs n C (n + j)).biUnion (rawSupport n C) := by
            apply Finset.mem_biUnion.mpr
            refine ⟨v, Finset.mem_filter.mpr ⟨?_, earlier⟩, inChild⟩
            simpa using read
          rw [← root, empty] at mem
          exact Finset.notMem_empty _ mem
        exact False.elim (distinct ((childEqual a (by simp [two])).trans (childEqual b (by simp [two])).symm))

theorem first_mixing_reader (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (strict : StrictBinary C) (h : ℕ) : ∀ w < n + C.gates.length,
      AllowsOnly n C h w → Feeds n C h w → w ≠ n + h →
      ∃ j r, j < C.gates.length ∧ h < j ∧ n + j ≤ w ∧ (gateAt C j).op = .or ∧
        ((gateAt C j).inputs = [n + h, r] ∨ (gateAt C j).inputs = [r, n + h]) ∧
        (rawSupport n C r).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro bound allowed feed notLower
    have before := feeds_order n C feed
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have nhj : h ≠ j := by omega
    have gmem := List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j hj⟩
    have options : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by simpa using (mono _ gmem).1
    have orGate := options.resolve_left (fun isAnd => nhj (allowed j isAnd (Or.inl rfl)).symm)
    obtain ⟨p, hp, hasFeed⟩ := (feeds_iff_reader n C back hj nhj).mp feed
    have early := back j hj p hp
    by_cases primary : p = n + h
    · obtain ⟨a, b, words, different⟩ := input_pair C strict j hj
      have liveRaw (r : ℕ) (used : r ∈ (gateAt C j).inputs) (notH : r ≠ n + h) :
          (rawSupport n C r).Nonempty := by
        by_contra! noRaw
        have er := back j hj r used
        apply notH
        exact empty_raw_is_lower n C mono back strict h r (by omega)
          (fun k kAnd atR => allowed k kAnd (feeds_of_reader n C back hj used atR)) noRaw
      have ways : p = a ∨ p = b := by simpa [words] using hp
      rcases ways with equal | equal
      · have ah := equal.symm.trans primary
        have bh : b ≠ n + h := fun eq => different (ah.trans eq.symm)
        exact ⟨j, b, hj, by omega, le_rfl, orGate, Or.inl (by simpa [ah] using words),
          liveRaw b (by simp [words]) bh⟩
      · have bh := equal.symm.trans primary
        have ah : a ≠ n + h := fun eq => different (eq.trans bh.symm)
        exact ⟨j, a, hj, by omega, le_rfl, orGate, Or.inr (by simpa [bh] using words),
          liveRaw a (by simp [words]) ah⟩
    · obtain ⟨k, r, hk, earlier, order, op, reads, rn⟩ := ih p early (by omega)
        (fun i iAnd atP => allowed i iAnd (feeds_of_reader n C back hj hp atP)) hasFeed primary
      exact ⟨k, r, hk, earlier, order.trans early.le, op, reads, rn⟩

theorem upper_safe (C : Circuit) (ok : acceptable C)
    (minimal : ∀ D : Circuit, acceptable D → C.size ≤ D.size)
    {h H : ℕ} (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H) :
    ∀ L, negative L → ¬ wireOn C L (26 + H) := by
  have rows := (separates_iff_rows C).mp ok.2.2
  obtain ⟨out, _, outEq⟩ := output_gate C (rows.1 _ ⟨0, 0, by decide, rfl⟩)
    (rows.1 _ ⟨1, 1, by decide, rfl⟩)
  have minEval (D : Circuit) (mon : Monotone2 D) (back : ReadsBack 26 D)
      (same : ∀ x : List Bool, x.length = 26 → D.eval x = C.eval x) : C.size ≤ D.size := by
    apply minimal D ⟨mon, back, (separates_iff_rows D).mpr ?_⟩
    constructor
    · rintro L ⟨p, l, inc, rfl⟩
      exact (same _ (row_length p l)).trans (rows.1 _ ⟨p, l, inc, rfl⟩)
    · rintro L ⟨Q, good, rfl⟩
      exact (same _ (by simp [quadRow])).trans (rows.2 _ ⟨Q, good, rfl⟩)
  intro L negativeRow hit
  have Llen : L.length = 26 := by
    obtain ⟨Q, _, rfl⟩ := negativeRow
    simp [quadRow]
  have falseOut : (C.wires L).getD (26 + out) false = false := by
    simpa [Circuit.eval, outEq] using rows.2 L negativeRow
  have different : H ≠ out := by
    intro eq
    change (C.wires L).getD (26 + H) false = true at hit
    rw [eq, falseOut] at hit
    contradiction
  have live := minimal_inCone 26 C ok.1 ok.2.1 minEval out outEq H (gateAt_and_bound C H high) different
  obtain ⟨j, _, jAnd, path⟩ := and_between 26 C ok.1 H L Llen hit out live falseOut
  have both := andPair_unique one low high nest high jAnd path
  have ordered := cone_lt nest
  omega

end OneNestedAnd

/- Source work/quad1961/frontier-lean/Retain.lean -/
namespace OneNestedAnd.Retain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

 
def move (n : ℕ) (ks : List ℕ) (w : ℕ) : ℕ :=
  if w < n then w else n + ks.idxOf (w - n)

private def newGate (n : ℕ) (C : Circuit) (ks : List ℕ) (j : ℕ) : Gate :=
  ⟨(gateAt C j).op, (gateAt C j).inputs.map (move n ks)⟩

def circuit (n : ℕ) (C : Circuit) (ks : List ℕ) : Circuit :=
  ⟨ks.map (newGate n C ks), move n ks C.output⟩

def Closed (n : ℕ) (C : Circuit) (ks : List ℕ) : Prop :=
  ∀ j ∈ ks, ∀ i, n + i ∈ (gateAt C j).inputs → i ∈ ks

@[simp] theorem circuit_len (n : ℕ) (C : Circuit) (ks : List ℕ) :
    (circuit n C ks).gates.length = ks.length := List.length_map _

@[simp] theorem circuit_size (n : ℕ) (C : Circuit) (ks : List ℕ) :
    (circuit n C ks).size = ks.length := circuit_len n C ks

@[simp] theorem move_gate (n : ℕ) (ks : List ℕ) (j : ℕ) :
    move n ks (n + j) = n + ks.idxOf j := by
  simp [move]

theorem circuit_at {n : ℕ} {C : Circuit} {ks : List ℕ} {k : ℕ}
    (hk : k < ks.length) : gateAt (circuit n C ks) k = newGate n C ks ks[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, circuit, List.getElem?_eq_getElem hk]

theorem circuit_at_idxOf (n : ℕ) (C : Circuit) {ks : List ℕ} {j : ℕ} (hj : j ∈ ks) :
    gateAt (circuit n C ks) (ks.idxOf j) = newGate n C ks j := by
  rw [circuit_at (List.idxOf_lt_length_of_mem hj), List.getElem_idxOf]

private theorem idxOf_strict {ks : List ℕ} (sorted : ks.Pairwise (· < ·))
    {i j : ℕ} (im : i ∈ ks) (jm : j ∈ ks) (before : i < j) : ks.idxOf i < ks.idxOf j := by
  rcases lt_trichotomy (ks.idxOf i) (ks.idxOf j) with lt | eq | lt
  · exact lt
  · have ei := List.getElem?_idxOf im
    rw [eq, List.getElem?_idxOf jm] at ei
    have := Option.some.inj ei
    omega
  · have below := List.pairwise_iff_getElem.mp sorted _ _
      (List.idxOf_lt_length_of_mem jm) (List.idxOf_lt_length_of_mem im) lt
    rw [List.getElem_idxOf, List.getElem_idxOf] at below
    omega

theorem circuit_mono {n : ℕ} {C : Circuit} {ks : List ℕ} (mono : Monotone2 C)
    (legal : ∀ j ∈ ks, j < C.gates.length) : Monotone2 (circuit n C ks) := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  have hm := mono _ (List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j (legal j hj)⟩)
  simpa [newGate] using hm

theorem circuit_back {n : ℕ} {C : Circuit} {ks : List ℕ} (back : ReadsBack n C)
    (sorted : ks.Pairwise (· < ·)) (legal : ∀ j ∈ ks, j < C.gates.length)
    (closed : Closed n C ks) : ReadsBack n (circuit n C ks) := by
  intro k hk w reads
  have hk' : k < ks.length := by simpa using hk
  have jm : ks[k] ∈ ks := List.getElem_mem hk'
  rw [circuit_at hk'] at reads
  obtain ⟨u, read, rfl⟩ := List.mem_map.mp reads
  have before := back _ (legal _ jm) u read
  by_cases primary : u < n
  · rw [move, ite_eq_left primary]
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, u = n + i := ⟨u-n, by omega⟩
    have smaller : i < ks[k] := by omega
    have im := closed _ jm _ read
    have below := idxOf_strict sorted im jm smaller
    have nd : ks.Nodup := sorted.imp (fun h => Nat.ne_of_lt h)
    rw [nd.idxOf_getElem k hk'] at below
    rw [move_gate]
    omega

private theorem gateValue {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (back : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false = (gateAt C j).op.eval
      ((gateAt C j).inputs.map ((C.wires x).getD · false)) := by
  have h := W_spec C.gates x j _ (gateAt_some C j hj)
  rw [hx] at h
  change (W C.gates x).getD (n + j) false = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [ite_eq_left (back j hj a ha)]
  rfl

private theorem primary_value {n : ℕ} {C : Circuit} {ks : List ℕ} {x : List Bool}
    (hx : x.length = n) {w : ℕ} (hw : w < n) :
    ((circuit n C ks).wires x).getD (move n ks w) false = (C.wires x).getD w false := by
  rw [move, ite_eq_left hw]
  change (W (circuit n C ks).gates x).getD w false = (W C.gates x).getD w false
  rw [W_inp _ x w (by omega), W_inp _ x w (by omega)]

theorem circuit_value {n : ℕ} {C : Circuit} {ks : List ℕ} (back : ReadsBack n C)
    (sorted : ks.Pairwise (· < ·)) (legal : ∀ j ∈ ks, j < C.gates.length)
    (closed : Closed n C ks) {x : List Bool} (hx : x.length = n) :
    ∀ j ∈ ks, ((circuit n C ks).wires x).getD (move n ks (n+j)) false =
      (C.wires x).getD (n+j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro jm
    have jn : ks.idxOf j < (circuit n C ks).gates.length := by
      simpa using List.idxOf_lt_length_of_mem jm
    rw [move_gate, gateValue hx (circuit_back back sorted legal closed) jn,
      circuit_at_idxOf n C jm, gateValue hx back (legal j jm)]
    simp only [newGate, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro w reads
    by_cases primary : w < n
    · exact primary_value hx primary
    · obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w-n, by omega⟩
      have before : i < j := by have := back j (legal j jm) (n+i) reads; omega
      exact ih i before (closed j jm i reads)

theorem circuit_eval {n : ℕ} {C : Circuit} {ks : List ℕ} (back : ReadsBack n C)
    (sorted : ks.Pairwise (· < ·)) (legal : ∀ j ∈ ks, j < C.gates.length) (closed : Closed n C ks)
    (output : C.output < n ∨ C.output - n ∈ ks) {x : List Bool} (hx : x.length = n) :
    (circuit n C ks).eval x = C.eval x := by
  change ((circuit n C ks).wires x).getD (move n ks C.output) false =
    (C.wires x).getD C.output false
  by_cases ho : C.output < n
  · exact primary_value hx ho
  · obtain ⟨j, h⟩ : ∃ j, C.output = n + j := ⟨C.output-n, by omega⟩
    rw [h]
    apply circuit_value back sorted legal closed hx
    rcases output with p | p
    · exact (ho p).elim
    · simpa [h] using p

theorem circuit_cone {n : ℕ} {C : Circuit} {ks : List ℕ} (sorted : ks.Pairwise (· < ·))
    (legal : ∀ j ∈ ks, j < C.gates.length) (closed : Closed n C ks)
    {i j : ℕ} (ib : i < ks.length) (jb : j < ks.length) :
    InCone n (circuit n C ks) i j → InCone n C ks[i] ks[j] := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro anc
    obtain ⟨_, k, kj, reads, prior⟩ := (inCone_iff n (circuit n C ks) i j).mp anc
    have kb := kj.trans jb
    rw [circuit_at jb] at reads
    obtain ⟨w, wm, e⟩ := List.mem_map.mp reads
    have nonprimary : ¬ w < n := by
      intro primary
      rw [move, ite_eq_left primary] at e
      omega
    obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w-n, by omega⟩
    have rm := closed _ (List.getElem_mem jb) _ wm
    rw [move_gate] at e
    have idx : ks.idxOf r = k := Nat.add_left_cancel e
    have elem := List.getElem?_idxOf rm
    rw [idx, List.getElem?_eq_getElem kb] at elem
    have rq : ks[k] = r := Option.some.inj elem
    rw [← rq] at wm
    have before := List.pairwise_iff_getElem.mp sorted k j kb jb kj
    refine (inCone_iff n C _ _).mpr ⟨legal _ (List.getElem_mem jb), ks[k], before, wm, ?_⟩
    rcases prior with rfl | prev
    · exact Or.inl rfl
    · exact Or.inr (ih k kj kb prev)

theorem circuit_flat {n : ℕ} {C : Circuit} {ks : List ℕ} (sorted : ks.Pairwise (· < ·))
    (legal : ∀ j ∈ ks, j < C.gates.length) (closed : Closed n C ks)
    (flat : ∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → ¬ InCone n C i j) :
    ∀ i j, (gateAt (circuit n C ks) i).op = .and → (gateAt (circuit n C ks) j).op = .and →
      ¬ InCone n (circuit n C ks) i j := by
  intro i j oi oj anc
  have jb : j < ks.length := by
    simpa using ((inCone_iff n (circuit n C ks) i j).mp anc).1
  have less : ∀ j, InCone n (circuit n C ks) i j → i < j := by
    intro j'
    induction j' using Nat.strong_induction_on with
    | _ j' ih =>
      intro c
      obtain ⟨_, k, before, _, prior⟩ := (inCone_iff n (circuit n C ks) i j').mp c
      rcases prior with rfl | c
      · exact before
      · exact (ih k before c).trans before
  have ib := (less j anc).trans jb
  rw [circuit_at ib] at oi
  rw [circuit_at jb] at oj
  exact flat _ _ oi oj (circuit_cone sorted legal closed ib jb anc)


end OneNestedAnd.Retain

/- Source work/quad1961/frontier-lean/ProjectAliases.lean -/
namespace OneNestedAnd.ProjectAliases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def read (v : ℕ → Bool) : Option ℕ → Bool
  | none => false
  | some i => v i

def onOperands (R : ℕ → Option ℕ) (v : ℕ → Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => read v (R i)))

 
structure Rules (n : ℕ) (C : Circuit) (R : ℕ → Option ℕ) : Prop where
  inputs : ∀ w < n, R w = some w
  earlier : ∀ {w u}, R w = some u → u ≤ w
  root : ∀ {w u}, R w = some u → R u = some u
  path : ∀ {j k}, j < C.gates.length → R (n+j) = some (n+k) →
    k = j ∨ InCone n C k j
  sound : ∀ j < C.gates.length, R (n+j) ≠ some (n+j) →
    ∀ v, onOperands R v (gateAt C j) = read v (R (n+j))

 
noncomputable def substituted (R : ℕ → Option ℕ) (g : Gate) : Gate := by
  classical
  exact if g.op = .and ∧ g.inputs.any (fun i => decide (R i = none)) = true then ⟨.or, []⟩
    else ⟨g.op, g.inputs.filterMap R⟩

private theorem any_filterMap (R : ℕ → Option ℕ) (v : ℕ → Bool) (L : List ℕ) :
    ((L.filterMap R).map v).any id = (L.map (fun z => read v (R z))).any id := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    cases h : R a <;> simp [h, read, ih]

private theorem all_filterMap (R : ℕ → Option ℕ) (v : ℕ → Bool) :
    ∀ (L : List ℕ), (∀ i ∈ L, R i ≠ none) →
      ((L.filterMap R).map v).all id = (L.map (fun z => read v (R z))).all id := by
  intro L
  induction L with
  | nil =>
    intro _
    rfl
  | cons a as ih =>
    intro noneAbsent
    have rest : ∀ i ∈ as, R i ≠ none := fun i hm => noneAbsent i (List.mem_cons_of_mem a hm)
    cases h : R a with
    | none => exact (noneAbsent a (by simp) h).elim
    | some b => simp [h, read, ih rest]

theorem and_false {R : ℕ → Option ℕ} {g : Gate} (op : g.op = .and)
    {i : ℕ} (mem : i ∈ g.inputs) (absent : R i = none) (v : ℕ → Bool) :
    onOperands R v g = false := by
  apply Bool.eq_false_iff.mpr
  simp only [onOperands, op, GateOp.eval]
  intro all
  exact Bool.false_ne_true ((List.all_eq_true.mp all) false
    (List.mem_map.mpr ⟨i, mem, by simp [absent, read]⟩))

theorem or_alias {R : ℕ → Option ℕ} {g : Gate} (op : g.op = .or)
    {u : ℕ} (list : g.inputs.filterMap R = [u]) (v : ℕ → Bool) :
    onOperands R v g = v u := by
  rw [onOperands, op, GateOp.eval, ← any_filterMap R v, list]
  simp

theorem or_false {R : ℕ → Option ℕ} {g : Gate} (op : g.op = .or)
    (list : g.inputs.filterMap R = []) (v : ℕ → Bool) : onOperands R v g = false := by
  rw [onOperands, op, GateOp.eval, ← any_filterMap R v, list]
  rfl

private theorem substituted_sound {R : ℕ → Option ℕ} {g : Gate}
    (op : g.op = .and ∨ g.op = .or) (v : ℕ → Bool) :
    (substituted R g).op.eval ((substituted R g).inputs.map v) = onOperands R v g := by
  unfold substituted
  split
  · rename_i h
    obtain ⟨hand, someFalse⟩ := h
    obtain ⟨i, mem, absent⟩ := List.any_eq_true.mp someFalse
    exact (and_false hand mem (of_decide_eq_true absent) v).symm
  · rename_i h
    rcases op with hand | hor
    · simp only [hand, GateOp.eval, onOperands]
      apply all_filterMap
      intro i hi absent
      exact h ⟨hand, List.any_eq_true.mpr ⟨i, hi, decide_eq_true absent⟩⟩
    · simp only [hor, GateOp.eval, onOperands]
      exact any_filterMap R v g.inputs

private theorem substituted_read {R : ℕ → Option ℕ} {g : Gate} {u : ℕ}
    (mem : u ∈ (substituted R g).inputs) : ∃ w ∈ g.inputs, R w = some u := by
  unfold substituted at mem
  split at mem
  · simp at mem
  · exact List.mem_filterMap.mp mem

private theorem substituted_le {R : ℕ → Option ℕ} {g : Gate} :
    (substituted R g).inputs.length ≤ g.inputs.length := by
  unfold substituted
  split
  · simp
  · exact List.length_filterMap_le _ _

private theorem substituted_op {R : ℕ → Option ℕ} {g : Gate} :
    (substituted R g).op = .or ∨ (substituted R g).op = g.op := by
  unfold substituted
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private noncomputable def gate (n : ℕ) (R : ℕ → Option ℕ) (j : ℕ) (g : Gate) : Gate :=
  if R (n+j) = some (n+j) then substituted R g else ⟨.or, []⟩

noncomputable def circuit (n : ℕ) (C : Circuit) (R : ℕ → Option ℕ) : Circuit :=
  ⟨C.gates.mapIdx (gate n R), (R C.output).getD (n + C.gates.length)⟩

@[simp] theorem circuit_len (n : ℕ) (C : Circuit) (R : ℕ → Option ℕ) :
    (circuit n C R).gates.length = C.gates.length := by simp [circuit]

private theorem circuit_at {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} {j : ℕ}
    (hj : j < C.gates.length) :
    gateAt (circuit n C R) j = gate n R j (gateAt C j) := by
  simp [gateAt, circuit, List.getD_eq_getElem?_getD, hj]

theorem circuit_at_fixed {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} {j : ℕ}
    (hj : j < C.gates.length) (fixed : R (n+j) = some (n+j)) :
    gateAt (circuit n C R) j = substituted R (gateAt C j) := by
  rw [circuit_at hj, gate, ite_eq_left fixed]

theorem circuit_at_changed {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} {j : ℕ}
    (hj : j < C.gates.length) (changed : R (n+j) ≠ some (n+j)) :
    gateAt (circuit n C R) j = ⟨.or, []⟩ := by
  rw [circuit_at hj, gate, ite_eq_right changed]

theorem circuit_read {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} {j u : ℕ}
    (hj : j < C.gates.length) (read : u ∈ (gateAt (circuit n C R) j).inputs) :
    ∃ w ∈ (gateAt C j).inputs, R w = some u := by
  rw [circuit_at hj, gate] at read
  split at read
  · exact substituted_read read
  · simp at read

theorem circuit_back {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} (rules : Rules n C R)
    (back : ReadsBack n C) : ReadsBack n (circuit n C R) := by
  intro j hj u read
  have jC : j < C.gates.length := by simpa using hj
  obtain ⟨w, mem, rw⟩ := circuit_read jC read
  exact (rules.earlier rw).trans_lt (back j jC w mem)

theorem circuit_mono {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} (mono : Monotone2 C) :
    Monotone2 (circuit n C R) := by
  intro g hg
  obtain ⟨j, eq⟩ := List.mem_iff_getElem?.mp hg
  have jD := (List.getElem?_eq_some_iff.mp eq).1
  have jC : j < C.gates.length := by simpa using jD
  have atGate : gateAt (circuit n C R) j = g := by simp [gateAt, List.getD_eq_getElem?_getD, eq]
  rw [← atGate, circuit_at jC, gate]
  split
  · have m := mono _ (List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j jC⟩)
    refine ⟨?_, substituted_le.trans m.2⟩
    rcases substituted_op (R := R) (g := gateAt C j) with op | op
    · simp [op]
    · rw [op]
      exact m.1
  · simp

private theorem gateValue {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (back : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires x).getD (n+j) false = (gateAt C j).op.eval
      ((gateAt C j).inputs.map ((C.wires x).getD · false)) := by
  have h := W_spec C.gates x j _ (gateAt_some C j hj)
  rw [hx] at h
  change (W C.gates x).getD (n+j) false = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [ite_eq_left (back j hj a ha)]
  rfl

theorem circuit_value {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} (rules : Rules n C R)
    (mono : Monotone2 C) (back : ReadsBack n C) {x : List Bool} (hx : x.length = n) :
    ∀ w < n+C.gates.length,
      (C.wires x).getD w false = read (((circuit n C R).wires x).getD · false) (R w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro bound
    by_cases primary : w < n
    · rw [rules.inputs w primary]
      change (W C.gates x).getD w false = (W (circuit n C R).gates x).getD w false
      rw [W_inp _ x w (by omega), W_inp _ x w (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have jC : j < C.gates.length := by omega
      have jD : j < (circuit n C R).gates.length := by simpa using jC
      let v : ℕ → Bool := fun i => ((circuit n C R).wires x).getD i false
      have val : (C.wires x).getD (n+j) false = onOperands R v (gateAt C j) := by
        rw [gateValue hx back jC]
        unfold onOperands
        congr 1
        apply List.map_congr_left
        intro i hi
        have before := back j jC i hi
        exact ih i before (before.trans bound)
      rw [val]
      by_cases fixed : R (n+j) = some (n+j)
      · rw [fixed]
        change onOperands R v (gateAt C j) = ((circuit n C R).wires x).getD (n+j) false
        rw [gateValue hx (circuit_back rules back) jD, circuit_at jC, gate, ite_eq_left fixed]
        have hm := mono _ (List.mem_iff_getElem?.mpr ⟨j, gateAt_some C j jC⟩)
        exact (substituted_sound hm.1 v).symm
      · exact rules.sound j jC fixed v

theorem circuit_eval {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} (rules : Rules n C R)
    (mono : Monotone2 C) (back : ReadsBack n C) (out : C.output < n + C.gates.length)
    {x : List Bool} (hx : x.length = n) : (circuit n C R).eval x = C.eval x := by
  have val := circuit_value rules mono back hx C.output out
  unfold Circuit.eval
  change ((circuit n C R).wires x).getD ((R C.output).getD (n+C.gates.length)) false = _
  rw [val]
  cases hr : R C.output with
  | some w => rfl
  | none =>
    change (W (circuit n C R).gates x).getD (n+C.gates.length) false = false
    apply W_oob
    rw [hx, circuit_len]

theorem circuit_cone {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} (rules : Rules n C R)
    (back : ReadsBack n C) (i : ℕ) :
    ∀ j, InCone n (circuit n C R) i j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro anc
    obtain ⟨jD, k, before, reads, prior⟩ := (inCone_iff n (circuit n C R) i j).mp anc
    have jC : j < C.gates.length := by simpa using jD
    obtain ⟨w, mem, eq⟩ := circuit_read jC reads
    have wj := back j jC w mem
    have kw := rules.earlier eq
    obtain ⟨l, rfl⟩ : ∃ l, w = n+l := ⟨w-n, by omega⟩
    have lb : l < j := by omega
    have step : InCone n C k j := by
      exact (inCone_iff n C k j).mpr ⟨jC, l, lb, mem, rules.path (lb.trans jC) eq⟩
    rcases prior with rfl | prev
    · exact step
    · exact cone_trans n C i k (ih k before prev) j step

theorem circuit_flat {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} (rules : Rules n C R)
    (back : ReadsBack n C)
    (flat : ∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → ¬ InCone n C i j) :
    ∀ i j, (gateAt (circuit n C R) i).op = .and → (gateAt (circuit n C R) j).op = .and →
      ¬ InCone n (circuit n C R) i j := by
  intro i j oi oj link
  have anc := circuit_cone rules back i j link
  have jb := ((inCone_iff n C i j).mp anc).1
  have ib := (cone_lt anc).trans jb
  have old {k : ℕ} (bound : k < C.gates.length)
      (op : (gateAt (circuit n C R) k).op = .and) : (gateAt C k).op = .and := by
    rw [circuit_at bound, gate] at op
    split at op
    · rcases substituted_op (R := R) (g := gateAt C k) with eq | eq
      · rw [eq] at op
        contradiction
      · exact eq.symm.trans op
    · contradiction
  exact flat i j (old ib oi) (old jb oj) anc

 
theorem circuit_cone_root {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} (rules : Rules n C R)
    (i : ℕ) : ∀ j, InCone n (circuit n C R) i j → R (n+i) = some (n+i) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro anc
    obtain ⟨jD, k, before, reads, prior⟩ := (inCone_iff n (circuit n C R) i j).mp anc
    rcases prior with rfl | anc
    · have jC : j < C.gates.length := by simpa using jD
      obtain ⟨_, _, eq⟩ := circuit_read jC reads
      exact rules.root eq
    · exact ih k before anc

theorem circuit_output_root {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ}
    (rules : Rules n C R) {u : ℕ} (out : R C.output = some u) :
    (circuit n C R).output = u ∧ R u = some u := by
  exact ⟨by simp [circuit, out], rules.root out⟩

theorem erase_aliases {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ} (rules : Rules n C R)
    (mono : Monotone2 C) (back : ReadsBack n C) (out : C.output < n + C.gates.length)
    (keptOutput : ∃ u, R C.output = some u)
    (flat : ∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → ¬ InCone n C i j) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
      (∀ i j, (gateAt D i).op = .and → (gateAt D j).op = .and → ¬ InCone n D i j) ∧
      D.size = ((List.range C.gates.length).filter (fun j => R (n+j) == some (n+j))).length ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  let S := circuit n C R
  let ks := (List.range C.gates.length).filter (fun j => R (n+j) == some (n+j))
  have sorted : ks.Pairwise (· < ·) := List.pairwise_lt_range.sublist (List.filter_sublist ..)
  have legal : ∀ j ∈ ks, j < S.gates.length := by
    intro j mem
    have hm := (List.mem_filter.mp mem).1
    simpa [S] using List.mem_range.mp hm
  have Sback := circuit_back rules back
  have closed : Retain.Closed n S ks := by
    intro j jm i reads
    have jS := legal j jm
    have jC : j < C.gates.length := by simpa [S] using jS
    obtain ⟨w, wm, eq⟩ := circuit_read jC reads
    have smaller := Sback j jS (n+i) reads
    have root := rules.root eq
    simp only [ks, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨by omega, root⟩
  have output : S.output < n ∨ S.output - n ∈ ks := by
    obtain ⟨u, hu⟩ := keptOutput
    have use : S.output = u := by simp [S, circuit, hu]
    rw [use]
    by_cases primary : u < n
    · exact Or.inl primary
    · apply Or.inr
      have bound := rules.earlier hu
      have root := rules.root hu
      have e : n + (u-n) = u := by omega
      simp only [ks, List.mem_filter, List.mem_range, beq_iff_eq, e]
      exact ⟨by omega, root⟩
  let D := Retain.circuit n S ks
  refine ⟨D, Retain.circuit_mono (circuit_mono mono) legal, Retain.circuit_back Sback sorted legal closed,
    Retain.circuit_flat sorted legal closed (circuit_flat rules back flat), by simp [D, ks], ?_⟩
  intro x hx
  exact (Retain.circuit_eval Sback sorted legal closed output hx).trans
    (circuit_eval rules mono back out hx)


end OneNestedAnd.ProjectAliases

/- Source work/quad1961/SupportRewrite.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma rawSupport_clearLower (n : ℕ) (C : Circuit) (h : ℕ) (bound : h < C.gates.length)
    (isAnd : (gateAt C h).op = .and) : ∀ wire,
    rawSupport n (clearLower C h) wire = rawSupport n C wire := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases primary : w < n
    · rw [rawSupport_primary n _ primary, rawSupport_primary n _ primary]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases same : j = h
      · subst j
        have hOr : (gateAt (clearLower C h) ((n + h) - n)).op = .or := by
          simpa [clearLower_at_self bound]
        rw [rawSupport_or n _ (by omega) hOr, rawSupport_and n C (by omega) (by simp [isAnd])]
        simp [earlierInputs, clearLower_at_self bound]
      · have gateEq : gateAt (clearLower C h) ((n + j) - n) = gateAt C ((n + j) - n) := by
          simpa only [Nat.add_sub_cancel_left] using clearLower_at_other (C := C) same
        by_cases op : (gateAt C ((n + j) - n)).op = .or
        · rw [rawSupport_or n _ (by omega) (by simpa only [gateEq] using op),
            rawSupport_or n C (by omega) op]
          apply Finset.biUnion_congr
          · simp only [earlierInputs, gateEq]
          · intro p hp
            exact ih p ((Finset.mem_filter.mp hp).2)
        · rw [rawSupport_and n _ (by omega) (by simpa only [gateEq] using op),
            rawSupport_and n C (by omega) op]

theorem rawSupport_project_aliases (n : ℕ) (C : Circuit) (R : ℕ → Option ℕ)
    (rules : ProjectAliases.Rules n C R) (back : ReadsBack n C)
    (localSupport : ∀ j < C.gates.length, R (n+j) ≠ some (n+j) →
      ((R (n+j)).map (rawSupport n C)).getD ∅ = rawSupport n C (n+j)) :
    ∀ w < n + C.gates.length,
      ((R w).map (rawSupport n (ProjectAliases.circuit n C R))).getD ∅ = rawSupport n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro bound
    by_cases primary : w < n
    · simp [rules.inputs w primary, rawSupport_primary n _ primary]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases fixed : R (n+j) = some (n+j)
      · simp only [fixed, Option.map_some, Option.getD_some]
        let D := ProjectAliases.circuit n C R
        have gateEq : gateAt D j = ProjectAliases.substituted R (gateAt C j) :=
          ProjectAliases.circuit_at_fixed hj fixed
        by_cases oldOp : (gateAt C j).op = .or
        · have newGate : gateAt D j = ⟨.or, (gateAt C j).inputs.filterMap R⟩ := by
            rw [gateEq]
            simp [ProjectAliases.substituted, oldOp]
          rw [rawSupport_or n C (by omega) (by simpa using oldOp),
            rawSupport_or n D (by omega) (by simpa [newGate])]
          ext label
          simp only [Finset.mem_biUnion, earlierInputs, Nat.add_sub_cancel_left,
            Finset.mem_filter, List.mem_toFinset, newGate, List.mem_filterMap]
          constructor
          · rintro ⟨u, ⟨⟨v, read, rep⟩, _⟩, accepted⟩
            have vlt := back j hj v read
            have e := ih v vlt (by omega)
            simp only [rep, Option.map_some, Option.getD_some] at e
            exact ⟨v, ⟨read, vlt⟩, e ▸ accepted⟩
          · rintro ⟨v, ⟨read, vlt⟩, accepted⟩
            have e := ih v vlt (by omega)
            cases rep : R v with
            | none => simp [rep, ← e] at accepted
            | some u =>
              simp only [rep, Option.map_some, Option.getD_some] at e
              exact ⟨u, ⟨⟨v, read, rep⟩, (rules.earlier rep).trans_lt vlt⟩, e.symm ▸ accepted⟩
        · have empty := rawSupport_and n C (wire := n+j) (by omega) (by simpa using oldOp)
          rw [empty]
          unfold ProjectAliases.substituted at gateEq
          split at gateEq
          · rw [rawSupport_or n D (by omega) (by simpa [gateEq])]
            simp [earlierInputs, gateEq]
          · exact rawSupport_and n D (by omega) (by simpa [gateEq] using oldOp)
      · have localRule := localSupport j hj fixed
        cases represented : R (n+j) with
        | none => simpa [represented] using localRule
        | some v =>
          have earlier := rules.earlier represented
          have strictly : v < n+j := by
            apply lt_of_le_of_ne earlier
            intro equal
            exact fixed (equal ▸ represented)
          have eq := ih v strictly (by omega)
          simp only [rules.root represented, Option.map_some, Option.getD_some] at eq
          simpa only [represented, Option.map_some, Option.getD_some] using eq.trans
            (by simpa only [represented, Option.map_some, Option.getD_some] using localRule)

end OneNestedAnd

/- Source work/quad1961/NestedView.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def rawOn (n : ℕ) (C : Circuit) (x : List Bool) (w : ℕ) : Prop :=
  ∃ p ∈ rawSupport n C w, x.getD p false = true

lemma wireOn_and_two (n : ℕ) (C : Circuit) (back : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    {j a b : ℕ} (bound : j < C.gates.length) (op : (gateAt C j).op = .and)
    (gateInputs : (gateAt C j).inputs = [a, b]) :
    wireOn C x (n + j) ↔ wireOn C x a ∧ wireOn C x b := by
  have aEarly := back j bound a (by simp [gateInputs])
  have bEarly := back j bound b (by simp [gateInputs])
  have evaluation := W_spec C.gates x j (gateAt C j) (gateAt_some C j bound)
  simp only [hx, op, gateInputs, List.map_cons, List.map_nil, aEarly, bEarly, ite_true, GateOp.eval,
    List.all_cons, List.all_nil, id_eq, Bool.and_true] at evaluation
  change (W C.gates x).getD (n+j) false = true ↔
    (W C.gates x).getD a false = true ∧ (W C.gates x).getD b false = true
  rw [evaluation, Bool.and_eq_true]

lemma wireOn_and_two_either (n : ℕ) (C : Circuit) (back : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    {j a b : ℕ} (bound : j < C.gates.length) (op : (gateAt C j).op = .and)
    (inputs : (gateAt C j).inputs = [a, b] ∨ (gateAt C j).inputs = [b, a]) :
    wireOn C x (n + j) ↔ wireOn C x a ∧ wireOn C x b := by
  rcases inputs with ab | ba
  · exact wireOn_and_two n C back x hx bound op ab
  · simpa only [and_comm] using wireOn_and_two n C back x hx bound op ba

structure NestInputs (C : Circuit) (h H : ℕ) where
  lowLeft : ℕ
  lowRight : ℕ
  upperFeed : ℕ
  upperOther : ℕ
  lower_eq : (gateAt C h).inputs = [lowLeft, lowRight]
  upper_eq : (gateAt C H).inputs = [upperFeed, upperOther] ∨
    (gateAt C H).inputs = [upperOther, upperFeed]
  connects : Feeds 26 C h upperFeed
  separate : ¬ Feeds 26 C h upperOther

theorem exists_nest_inputs (C : Circuit) (ok : acceptable C) (strict : StrictBinary C)
    (minimal : ∀ D : Circuit, acceptable D → C.size ≤ D.size)
    (h H : ℕ) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (bad : ∃ L, negative L ∧ wireOn C L (26 + h)) : Nonempty (NestInputs C h H) := by
  have hb := gateAt_and_bound C h low
  have Hb := gateAt_and_bound C H high
  obtain ⟨u, v, lowerWords, _⟩ := input_pair C strict h hb
  obtain ⟨a, b, upperWords, _⟩ := input_pair C strict H Hb
  have either : Feeds 26 C h a ∨ Feeds 26 C h b := by
    have feeds : Feeds 26 C h (26 + H) := Or.inr ⟨by omega, by simpa using nest⟩
    obtain ⟨w, wasRead, inCone⟩ := (feeds_iff_reader 26 C ok.2.1 Hb (cone_lt nest).ne).mp feeds
    have choose : w = a ∨ w = b := by simpa [upperWords] using wasRead
    rcases choose with rfl | rfl
    · exact Or.inl inCone
    · exact Or.inr inCone
  have notBoth : ¬ (Feeds 26 C h a ∧ Feeds 26 C h b) := by
    rintro ⟨fa, fb⟩
    obtain ⟨row, rn, hv⟩ := bad
    have len : row.length = 26 := by obtain ⟨Q, _, rfl⟩ := rn; simp [quadRow]
    have on (w : ℕ) (read : w ∈ (gateAt C H).inputs) (feed : Feeds 26 C h w) : wireOn C row w := by
      have order := ok.2.1 H Hb w read
      apply (selected_or_value 26 C ok.1 ok.2.1 row len h low w (by omega) ?_).mpr
      · exact Or.inr ⟨feed, hv⟩
      · intro k kAnd inWire
        exact (feeds_and_input_unique 26 C ok.2.1 one low high nest high read kAnd inWire).1
    exact upper_safe C ok minimal one low high nest row rn
      ((wireOn_and_two 26 C ok.2.1 row len Hb high upperWords).mpr
        ⟨on a (by simp [upperWords]) fa, on b (by simp [upperWords]) fb⟩)
  rcases either with fa | fb
  · exact ⟨⟨u, v, a, b, lowerWords, Or.inl upperWords, fa, fun fb => notBoth ⟨fa, fb⟩⟩⟩
  · exact ⟨⟨u, v, b, a, lowerWords, Or.inr upperWords, fb, fun fa => notBoth ⟨fa, fb⟩⟩⟩

namespace NestInputs

variable {C : Circuit} {h H : ℕ} (ports : NestInputs C h H)

lemma reads_lowerLeft : ports.lowLeft ∈ (gateAt C h).inputs := by simp [ports.lower_eq]
lemma reads_lowerRight : ports.lowRight ∈ (gateAt C h).inputs := by simp [ports.lower_eq]
lemma reads_upperFeed : ports.upperFeed ∈ (gateAt C H).inputs := by
  rcases ports.upper_eq with ab | ab <;> simp [ab]
lemma reads_upperOther : ports.upperOther ∈ (gateAt C H).inputs := by
  rcases ports.upper_eq with ab | ab <;> simp [ab]

theorem lower_value (ok : acceptable C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (x : List Bool) (hx : x.length = 26) :
    wireOn C x (26 + h) ↔ rawOn 26 C x ports.lowLeft ∧ rawOn 26 C x ports.lowRight := by
  have bound := gateAt_and_bound C h low
  have simple (w : ℕ) (used : w ∈ (gateAt C h).inputs) : wireOn C x w ↔ rawOn 26 C x w := by
    have order := ok.2.1 h bound w used
    have allowed : AllowsOnly 26 C h w := fun j jAnd dep =>
      (feeds_and_input_unique 26 C ok.2.1 one low high nest low used jAnd dep).1
    have absent : ¬ Feeds 26 C h w := fun feed => Nat.not_le_of_gt order (feeds_order 26 C feed)
    simpa [rawOn, absent] using selected_or_value 26 C ok.1 ok.2.1 x hx h low w (by omega) allowed
  rw [wireOn_and_two 26 C ok.2.1 x hx bound low ports.lower_eq,
    simple _ ports.reads_lowerLeft, simple _ ports.reads_lowerRight]

theorem upper_value (ok : acceptable C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (x : List Bool) (hx : x.length = 26) :
    wireOn C x (26 + H) ↔ (rawOn 26 C x ports.upperFeed ∨ wireOn C x (26 + h)) ∧
      rawOn 26 C x ports.upperOther := by
  have bound := gateAt_and_bound C H high
  have simple (w : ℕ) (used : w ∈ (gateAt C H).inputs) := by
    have order := ok.2.1 H bound w used
    have allowed : AllowsOnly 26 C h w := fun j jAnd dep =>
      (feeds_and_input_unique 26 C ok.2.1 one low high nest high used jAnd dep).1
    exact selected_or_value 26 C ok.1 ok.2.1 x hx h low w (by omega) allowed
  rw [wireOn_and_two_either 26 C ok.2.1 x hx bound high ports.upper_eq,
    simple _ ports.reads_upperFeed, simple _ ports.reads_upperOther]
  simp [rawOn, ports.connects, ports.separate]

theorem clear_upper_value (ok : acceptable C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (x : List Bool) (hx : x.length = 26) :
    wireOn (clearLower C h) x (26 + H) ↔
      rawOn 26 C x ports.upperFeed ∧ rawOn 26 C x ports.upperOther := by
  let D := clearLower C h
  have mh : Monotone2 D := clearLower_mono ok.1 h
  have bh : ReadsBack 26 D := clearLower_back ok.2.1 h
  have full := clearLower_flat one low high nest
  have oldLen := gateAt_and_bound C h low
  have hEq : gateAt D H = gateAt C H := clearLower_at_other (cone_lt nest).ne.symm
  have dh : (gateAt D H).op = .and := hEq ▸ high
  have db := gateAt_and_bound D H dh
  have simple (w : ℕ) (used : w ∈ (gateAt C H).inputs) : wireOn D x w ↔ rawOn 26 C x w := by
    have usedD : w ∈ (gateAt D H).inputs := by rwa [hEq]
    have earlier := bh H db w usedD
    have noH : ¬ Feeds 26 D H w := fun reach => Nat.not_le_of_gt earlier (feeds_order 26 D reach)
    have allow : AllowsOnly 26 D H w := by
      intro j op reaches
      have enters := feeds_of_reader 26 D bh db usedD reaches
      have le := (feeds_order 26 D reaches).trans_lt earlier
      rcases enters with eq | ⟨_, tail⟩
      · omega
      · simp only [Nat.add_sub_cancel_left] at tail
        exact False.elim (full j H op dh tail)
    have bits := selected_or_value 26 D mh bh x hx H dh w (by omega) allow
    simpa [rawOn, noH, D, rawSupport_clearLower 26 C h oldLen low] using bits
  rw [wireOn_and_two_either 26 D bh x hx db dh (by simpa only [hEq] using ports.upper_eq),
    simple _ ports.reads_upperFeed, simple _ ports.reads_upperOther]

end NestInputs
end OneNestedAnd

/- Source work/quad1961/frontier-lean/LiveRetain.lean -/
namespace OneNestedAnd.Retain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def liveSlots (n : ℕ) (C : Circuit) : List ℕ :=
  (List.range C.gates.length).filter fun i =>
    decide (n ≤ C.output ∧ (i = C.output-n ∨ InCone n C i (C.output-n)))

theorem mem_liveSlots {n : ℕ} {C : Circuit} {j : ℕ} :
    j ∈ liveSlots n C ↔ j < C.gates.length ∧ n ≤ C.output ∧
      (j = C.output-n ∨ InCone n C j (C.output-n)) := by
  simp [liveSlots]

 
theorem strip_dead {n : ℕ} {C : Circuit} (mono : Monotone2 C) (back : ReadsBack n C)
    (out : C.output < n+C.gates.length)
    (flat : ∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → ¬ InCone n C i j)
    (dead : Finset ℕ) (valid : ∀ j ∈ dead, j < C.gates.length)
    (outside : ∀ j ∈ dead, j ∉ liveSlots n C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
      (∀ i j, (gateAt D i).op = .and → (gateAt D j).op = .and → ¬ InCone n D i j) ∧
      D.size + dead.card ≤ C.size ∧ ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  let ks := liveSlots n C
  have sorted : ks.Pairwise (· < ·) := List.pairwise_lt_range.sublist (List.filter_sublist ..)
  have legal : ∀ j ∈ ks, j < C.gates.length := fun _ hm => (mem_liveSlots.mp hm).1
  have closed : Closed n C ks := by
    intro j jm i reads
    obtain ⟨jb, hOut, hc⟩ := mem_liveSlots.mp jm
    have ib : i < j := by have := back j jb (n+i) reads; omega
    have ij : InCone n C i j := (inCone_iff n C i j).mpr ⟨jb, i, ib, reads, Or.inl rfl⟩
    have reach : InCone n C i (C.output-n) := by
      rcases hc with eq | anc
      · rwa [eq] at ij
      · exact cone_trans n C i j ij _ anc
    exact mem_liveSlots.mpr ⟨ib.trans jb, hOut, Or.inr reach⟩
  have output : C.output < n ∨ C.output-n ∈ ks := by
    rcases Nat.lt_or_ge C.output n with low | high
    · exact Or.inl low
    · exact Or.inr (mem_liveSlots.mpr ⟨by omega, high, Or.inl rfl⟩)
  have allBound : dead ⊆ Finset.range C.gates.length := fun j h => Finset.mem_range.mpr (valid j h)
  have left : ks.toFinset ⊆ Finset.range C.gates.length \ dead := by
    intro j hm
    have jm : j ∈ ks := List.mem_toFinset.mp hm
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (legal j jm), fun hd => outside j hd jm⟩
  have count := Finset.card_le_card left
  have nodup : ks.Nodup := sorted.imp (fun h => Nat.ne_of_lt h)
  rw [List.toFinset_card_of_nodup nodup, Finset.card_sdiff_of_subset allBound, Finset.card_range] at count
  have small := Finset.card_le_card allBound
  rw [Finset.card_range] at small
  refine ⟨circuit n C ks, circuit_mono mono legal, circuit_back back sorted legal closed,
    circuit_flat sorted legal closed flat, ?_, ?_⟩
  · rw [circuit_size]
    unfold Circuit.size
    omega
  · intro x hx
    exact circuit_eval back sorted legal closed output hx


end OneNestedAnd.Retain

/- Source work/quad1961/frontier-lean/TwoSlots.lean -/
namespace OneNestedAnd.ProjectAliases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

 
def mapTwo (n h k : ℕ) (second : Option ℕ) (w : ℕ) : Option ℕ :=
  if w = n+h then none else if w = n+k then second else some w

@[simp] theorem mapTwo_first (n h k : ℕ) (second : Option ℕ) :
    mapTwo n h k second (n+h) = none := by simp [mapTwo]

@[simp] theorem mapTwo_second (n : ℕ) {h k : ℕ} (lt : h < k) (second : Option ℕ) :
    mapTwo n h k second (n+k) = second := by
  simp [mapTwo, Nat.ne_of_gt lt]

theorem mapTwo_other {n h k : ℕ} {second : Option ℕ} {w : ℕ}
    (first : w ≠ n+h) (next : w ≠ n+k) :
    mapTwo n h k second w = some w := by simp [mapTwo, first, next]

private theorem mapTwo_rules {n : ℕ} {C : Circuit} {h k : ℕ}
    {second : Option ℕ} (lt : h < k) (kb : k < C.gates.length) (back : ReadsBack n C)
    (hEmpty : gateAt C h = ⟨.or, []⟩)
    (direct : ∀ {u}, second = some u → u ∈ (gateAt C k).inputs ∧ u ≠ n+h)
    (secondSound : ∀ v, onOperands (mapTwo n h k second) v (gateAt C k) = read v second) :
    Rules n C (mapTwo n h k second) := by
  constructor
  · intro w primary
    exact mapTwo_other (by omega) (by omega)
  · intro w u mapped
    by_cases first : w = n+h
    · simp [first] at mapped
    · by_cases next : w = n+k
      · subst w
        rw [mapTwo_second n lt] at mapped
        exact (back k kb u (direct mapped).1).le
      · rw [mapTwo_other first next] at mapped
        exact (Option.some.inj mapped).ge
  · intro w u mapped
    by_cases first : w = n+h
    · simp [first] at mapped
    · by_cases next : w = n+k
      · subst w
        rw [mapTwo_second n lt] at mapped
        have ⟨mem, ne⟩ := direct mapped
        exact mapTwo_other ne (Nat.ne_of_lt (back k kb u mem))
      · rw [mapTwo_other first next] at mapped
        cases mapped
        exact mapTwo_other first next
  · intro j i jb eq
    by_cases first : j = h
    · simp [first] at eq
    · by_cases next : j = k
      · subst j
        rw [mapTwo_second n lt] at eq
        have mem := (direct eq).1
        have before : i < k := by have := back k kb (n+i) mem; omega
        exact Or.inr ((inCone_iff n C i k).mpr ⟨kb, i, before, mem, Or.inl rfl⟩)
      · rw [mapTwo_other (by omega) (by omega)] at eq
        have := Option.some.inj eq
        exact Or.inl (by omega)
  · intro j _ altered v
    by_cases first : j = h
    · subst j
      simp [hEmpty, onOperands, read, GateOp.eval]
    · by_cases next : j = k
      · subst j
        rw [mapTwo_second n lt]
        exact secondSound v
      · exact (altered (mapTwo_other (by omega) (by omega))).elim

 
theorem mapTwo_or {n : ℕ} {C : Circuit} {h k u : ℕ}
    (lt : h < k) (kb : k < C.gates.length) (back : ReadsBack n C)
    (hEmpty : gateAt C h = ⟨.or, []⟩) (op : (gateAt C k).op = .or)
    (shape : (gateAt C k).inputs = [n+h,u] ∨ (gateAt C k).inputs = [u,n+h])
    (distinct : u ≠ n+h) :
    Rules n C (mapTwo n h k (some u)) := by
  have mem : u ∈ (gateAt C k).inputs := by rcases shape with s | s <;> simp [s]
  have uFixed : mapTwo n h k (some u) u = some u :=
    mapTwo_other distinct (Nat.ne_of_lt (back k kb u mem))
  apply mapTwo_rules lt kb back hEmpty
  · intro w eq
    cases eq
    exact ⟨mem, distinct⟩
  · intro v
    exact or_alias op (by rcases shape with e | e <;> simp [e, uFixed]) v

 
theorem mapTwo_and {n : ℕ} {C : Circuit} {h k : ℕ}
    (lt : h < k) (kb : k < C.gates.length) (back : ReadsBack n C)
    (hEmpty : gateAt C h = ⟨.or, []⟩) (op : (gateAt C k).op = .and)
    (mem : n+h ∈ (gateAt C k).inputs) :
    Rules n C (mapTwo n h k none) := by
  apply mapTwo_rules lt kb back hEmpty
  · intro u eq
    cases eq
  · intro v
    exact and_false op mem (mapTwo_first n h k none) v

theorem altered_not_live {n : ℕ} {C : Circuit} {R : ℕ → Option ℕ}
    (rules : Rules n C R) {u : ℕ} (out : R C.output = some u) {j : ℕ}
    (altered : R (n+j) ≠ some (n+j)) :
    j ∉ Retain.liveSlots n (circuit n C R) := by
  intro mem
  obtain ⟨_, low, output⟩ := Retain.mem_liveSlots.mp mem
  rcases output with eq | cone
  · have ⟨outEq, outRoot⟩ := circuit_output_root rules out
    exact altered (by convert outRoot <;> omega)
  · exact altered (circuit_cone_root rules j _ cone)


end OneNestedAnd.ProjectAliases

/- Source work/quad1961/frontier-lean/AddStar.lean -/
namespace OneNestedAnd.AddStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def Flat (n : ℕ) (C : Circuit) : Prop :=
  ∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → ¬ InCone n C i j

def Pure (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ i, (gateAt C i).op = .and → n ≤ w → i ≠ w-n ∧ ¬ InCone n C i (w-n)

private def put (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op,[a,b]⟩], n+C.gates.length⟩

@[simp] private theorem put_len (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (put n C op a b).gates.length = C.gates.length+1 := by simp [put]

@[simp] private theorem put_output (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (put n C op a b).output = n+C.gates.length := rfl

private theorem put_at_old {n : ℕ} {C : Circuit} {op : GateOp} {a b j : ℕ}
    (old : j < C.gates.length) : gateAt (put n C op a b) j = gateAt C j := by
  simp only [gateAt, put, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left old]

private theorem put_at_last {n : ℕ} {C : Circuit} {op : GateOp} {a b : ℕ} :
    gateAt (put n C op a b) C.gates.length = ⟨op,[a,b]⟩ := by
  simp [gateAt, put, List.getD_eq_getElem?_getD]

private theorem put_mono {n : ℕ} {C : Circuit} {op : GateOp} {a b : ℕ}
    (mono : Monotone2 C) (hop : op = .and ∨ op = .or) :
    Monotone2 (put n C op a b) := by
  intro g mem
  rcases List.mem_append.mp mem with old | last
  · exact mono g old
  · have e : g = ⟨op,[a,b]⟩ := List.mem_singleton.mp last
    subst g
    exact ⟨hop, by simp⟩

private theorem put_back {n : ℕ} {C : Circuit} {op : GateOp} {a b : ℕ}
    (back : ReadsBack n C) (ha : a < n+C.gates.length) (hb : b < n+C.gates.length) :
    ReadsBack n (put n C op a b) := by
  intro j hj w mem
  by_cases old : j < C.gates.length
  · rw [put_at_old old] at mem
    exact back j old w mem
  · have e : j = C.gates.length := by simp only [put_len] at hj; omega
    subst j
    rw [put_at_last] at mem
    rcases (by simpa using mem : w = a ∨ w = b) with rfl | rfl
    · exact ha
    · exact hb

private theorem put_cone_old {n : ℕ} {C : Circuit} {op : GateOp} {a b i : ℕ} :
    ∀ j < C.gates.length, InCone n (put n C op a b) i j ↔ InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro old
    rw [inCone_iff n (put n C op a b), inCone_iff n C, put_at_old old, put_len]
    have valid : j < C.gates.length + 1 := by omega
    simp only [old, valid, true_and]
    constructor <;> rintro ⟨k, before, mem, prev⟩
    · exact ⟨k, before, mem, prev.imp_right ((ih k before (before.trans old)).mp)⟩
    · exact ⟨k, before, mem, prev.imp_right ((ih k before (before.trans old)).mpr)⟩

private theorem put_last_pure_cone {n : ℕ} {C : Circuit} {op : GateOp} {a b i : ℕ}
    (pa : Pure n C a) (pb : Pure n C b) (andI : (gateAt C i).op = .and) :
    ¬ InCone n (put n C op a b) i C.gates.length := by
  intro anc
  obtain ⟨_, k, before, reads, prior⟩ :=
    (inCone_iff n (put n C op a b) i C.gates.length).mp anc
  rw [put_at_last] at reads
  have e : n+k = a ∨ n+k = b := by simpa using reads
  have forbidden : i ≠ k ∧ ¬ InCone n C i k := by
    rcases e with rfl | rfl
    · simpa using pa i andI (by omega)
    · simpa using pb i andI (by omega)
  rcases prior with eq | tail
  · exact forbidden.1 eq
  · exact forbidden.2 ((put_cone_old k before).mp tail)

private theorem put_flat {n : ℕ} {C : Circuit} {op : GateOp} {a b : ℕ}
    (flat : Flat n C) (prep : op = .and → Pure n C a ∧ Pure n C b) :
    Flat n (put n C op a b) := by
  intro i j oi oj cone
  have jb := ((inCone_iff n (put n C op a b) i j).mp cone).1
  simp only [put_len] at jb
  have before := cone_lt cone
  have ib : i < C.gates.length := by omega
  rw [put_at_old ib] at oi
  by_cases old : j < C.gates.length
  · rw [put_at_old old] at oj
    exact flat i j oi oj ((put_cone_old j old).mp cone)
  · have last : j = C.gates.length := by omega
    subst j
    rw [put_at_last] at oj
    exact put_last_pure_cone (prep oj).1 (prep oj).2 oi cone

private theorem put_or_pure {n : ℕ} {C : Circuit} {a b : ℕ} (pa : Pure n C a) (pb : Pure n C b) :
    Pure n (put n C .or a b) (put n C .or a b).output := by
  intro i oi _
  rw [put_output, Nat.add_sub_cancel_left]
  have old : i < C.gates.length := by
    have bnd : i < (put n C .or a b).gates.length := by
      by_contra h
      have none := List.getElem?_eq_none (Nat.le_of_not_gt h)
      simp [gateAt, List.getD_eq_getElem?_getD, none] at oi
    simp only [put_len] at bnd
    by_contra h
    have e : i = C.gates.length := by omega
    subst i
    rw [put_at_last] at oi
    contradiction
  rw [put_at_old old] at oi
  exact ⟨Nat.ne_of_lt old, put_last_pure_cone pa pb oi⟩

private theorem put_oldValue {n : ℕ} {C : Circuit} {op : GateOp} {a b w : ℕ}
    {x : List Bool} (hx : x.length = n) (old : w < n+C.gates.length) :
    ((put n C op a b).wires x).getD w false = (C.wires x).getD w false := by
  change (W (C.gates ++ [⟨op,[a,b]⟩]) x).getD w false = (W C.gates x).getD w false
  rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len,hx]; exact old)]

private theorem put_eval {n : ℕ} {C : Circuit} {op : GateOp} {a b : ℕ}
    {x : List Bool} (hx : x.length = n) :
    (put n C op a b).eval x = op.eval [(C.wires x).getD a false, (C.wires x).getD b false] := by
  change (W (C.gates ++ [⟨op,[a,b]⟩]) x).getD (n+C.gates.length) false = _
  rw [W_snoc, List.getD_append_right _ _ _ _ (by rw [W_len,hx]), W_len, hx]
  simp [Circuit.wires, W]

private def putOrs (n : ℕ) (C : Circuit) : List ℕ → Circuit
  | [] => C
  | w :: ws => putOrs n (put n C .or C.output w) ws

@[simp] private theorem putOrs_len (n : ℕ) (C : Circuit) (ws : List ℕ) :
    (putOrs n C ws).gates.length = C.gates.length + ws.length := by
  induction ws generalizing C with
  | nil => simp [putOrs]
  | cons w ws ih => simp [putOrs, ih]; omega

private theorem putOrs_oldValue {n : ℕ} {C : Circuit} (ws : List ℕ) {w : ℕ}
    {x : List Bool} (hx : x.length = n) (old : w < n+C.gates.length) :
    ((putOrs n C ws).wires x).getD w false = (C.wires x).getD w false := by
  induction ws generalizing C with
  | nil => rfl
  | cons a as ih =>
    rw [putOrs, ih (by simp; omega), put_oldValue hx old]

private theorem putOrs_props {n : ℕ} {C : Circuit} {ws : List ℕ}
    (mono : Monotone2 C) (back : ReadsBack n C) (flat : Flat n C)
    (out : C.output < n+C.gates.length) (pureOut : Pure n C C.output)
    (inputs : ∀ w ∈ ws, w < n) :
    Monotone2 (putOrs n C ws) ∧ ReadsBack n (putOrs n C ws) ∧ Flat n (putOrs n C ws) ∧
    (putOrs n C ws).output < n+(putOrs n C ws).gates.length ∧
      Pure n (putOrs n C ws) (putOrs n C ws).output := by
  induction ws generalizing C with
  | nil => exact ⟨mono,back,flat,out,pureOut⟩
  | cons w ws ih =>
    rw [putOrs]
    have primary := inputs w (by simp)
    exact ih (put_mono mono (Or.inr rfl)) (put_back back out (by omega))
      (put_flat flat (fun contra => by cases contra))
      (by simp) (put_or_pure pureOut (by intro _ _ low; omega))
      (fun i im => inputs i (List.mem_cons_of_mem w im))

private theorem putOrs_eval {n : ℕ} {C : Circuit} {ws : List ℕ}
    (inputs : ∀ w ∈ ws, w < n) {x : List Bool} (hx : x.length = n) :
    (putOrs n C ws).eval x = (C.eval x || ws.any fun w => x.getD w false) := by
  induction ws generalizing C with
  | nil => simp [putOrs]
  | cons w ws ih =>
    have primary := inputs w (by simp)
    rw [putOrs, ih (fun i im => inputs i (List.mem_cons_of_mem w im)), put_eval hx]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
    change (((C.wires x).getD C.output false || (C.wires x).getD w false) ||
      ws.any (fun w => x.getD w false)) = _
    change (((W C.gates x).getD C.output false || (W C.gates x).getD w false) ||
      ws.any (fun w => x.getD w false)) = _
    rw [W_inp _ x w (by omega)]
    simp [Circuit.eval, W, Circuit.wires, Bool.or_assoc]

 
def circuit (n : ℕ) (C : Circuit) (center : ℕ) (leaves : List ℕ) : Circuit :=
  match leaves with
  | [] => C
  | first :: rest =>
    let lower := putOrs n { C with output := first } rest
    let term := put n lower .and center lower.output
    put n term .or C.output term.output

theorem circuit_size {n : ℕ} {C : Circuit} {center : ℕ} {leaves : List ℕ} :
    (circuit n C center leaves).size = C.size + leaves.length + (if leaves = [] then 0 else 1) := by
  cases leaves with
  | nil => simp [circuit]
  | cons first rest =>
    simp [circuit, Circuit.size]
    omega

theorem circuit_props {n : ℕ} {C : Circuit} {center : ℕ} {leaves : List ℕ}
    (mono : Monotone2 C) (back : ReadsBack n C) (flat : Flat n C)
    (out : C.output < n+C.gates.length) (hc : center < n) (hl : ∀ w ∈ leaves, w < n) :
    Monotone2 (circuit n C center leaves) ∧ ReadsBack n (circuit n C center leaves) ∧
      Flat n (circuit n C center leaves) ∧
        (circuit n C center leaves).output < n+(circuit n C center leaves).gates.length := by
  cases leaves with
  | nil => exact ⟨mono,back,flat,out⟩
  | cons first rest =>
    have prim := hl first (by simp)
    have restPrim : ∀ w ∈ rest, w < n := fun w hm => hl w (List.mem_cons_of_mem first hm)
    let lower := putOrs n { C with output := first } rest
    have ⟨lm,lb,lf,lo,lp⟩ : Monotone2 lower ∧ ReadsBack n lower ∧
        Flat n lower ∧ lower.output < n+lower.gates.length ∧ Pure n lower lower.output :=
      putOrs_props (C := { C with output := first }) mono back flat (by simp; omega)
        (by intro _ _ low; exact (Nat.not_le_of_gt prim low).elim) restPrim
    let term := put n lower .and center lower.output
    have tm : Monotone2 term := put_mono lm (Or.inl rfl)
    have tb : ReadsBack n term := put_back lb (by omega) lo
    have tf : Flat n term := put_flat lf (fun _ => ⟨by intro _ _ h; omega,lp⟩)
    have ti : term.output < n+term.gates.length := by simp [term]
    have oi : C.output < n+term.gates.length := by simp [term,lower]; omega
    exact ⟨put_mono tm (Or.inr rfl),put_back tb oi ti,put_flat tf (fun contra => by cases contra),
      by simp [circuit]⟩

theorem circuit_eval {n : ℕ} {C : Circuit} {center : ℕ} {leaves : List ℕ}
    (out : C.output < n+C.gates.length) (hc : center < n) (hl : ∀ w ∈ leaves, w < n)
    {x : List Bool} (hx : x.length = n) :
    (circuit n C center leaves).eval x = (C.eval x ||
      (x.getD center false && leaves.any (fun w => x.getD w false))) := by
  cases leaves with
  | nil => simp [circuit]
  | cons first rest =>
    have prim := hl first (by simp)
    have restPrim : ∀ w ∈ rest, w < n := fun w hm => hl w (List.mem_cons_of_mem first hm)
    let base := { C with output := first }
    let lower := putOrs n base rest
    let term := put n lower .and center lower.output
    have oi : C.output < n+lower.gates.length := by simp [lower,base]; omega
    change (put n term .or C.output term.output).eval x = _
    rw [put_eval hx]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
    change (((put n lower .and center lower.output).wires x).getD C.output false ||
      term.eval x) = _
    rw [put_oldValue hx oi, putOrs_oldValue rest hx (C := base) (by exact out)]
    dsimp only [term]
    rw [put_eval hx]
    simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
    change (C.eval x || (((lower.wires x).getD center false) && lower.eval x)) = _
    have cp : (lower.wires x).getD center false = x.getD center false := W_inp _ x _ (by omega)
    rw [cp, show lower.eval x = (base.eval x || rest.any (fun w => x.getD w false))
      from putOrs_eval restPrim hx]
    have bp : base.eval x = x.getD first false := W_inp _ x first (by omega)
    rw [bp]

theorem output_bound_of_acceptance {n : ℕ} {C : Circuit} {x : List Bool}
    (hx : x.length = n) (positive : C.eval x = true) : C.output < n+C.gates.length := by
  by_contra notBound
  change (W C.gates x).getD C.output false = true at positive
  rw [W_oob _ _ _ (by omega)] at positive
  contradiction

theorem circuit_accepts {n : ℕ} {C : Circuit} {center : ℕ} {leaves : List ℕ}
    (out : C.output < n+C.gates.length) (hc : center < n) (hl : ∀ w ∈ leaves, w < n)
    {x : List Bool} (hx : x.length = n) :
    (circuit n C center leaves).eval x = true ↔ C.eval x = true ∨
      (x.getD center false = true ∧ ∃ w ∈ leaves, x.getD w false = true) := by
  rw [circuit_eval out hc hl hx]
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]


end OneNestedAnd.AddStar

/- Source work/quad1961/frontier-lean/StarReplacement.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership



 
def planeAdjacent (u v : ℕ) : Prop :=
  ∃ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
    ((u = p.val ∧ v = 13+l.val) ∨ (v = p.val ∧ u = 13+l.val))

theorem planeAdjacent_point_line {p l : Fin 13} (edge : p-l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) :
    planeAdjacent p.val (13+l.val) := ⟨p,l,edge,Or.inl ⟨rfl,rfl⟩⟩

theorem planeAdjacent_line_point {p l : Fin 13} (edge : p-l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) :
    planeAdjacent (13+l.val) p.val := ⟨p,l,edge,Or.inr ⟨rfl,rfl⟩⟩

private theorem planeAdjacent_leaf {u v : ℕ} (edge : planeAdjacent u v) : v < 26 := by
  obtain ⟨p, l, _, matchEnds⟩ := edge
  have hp := p.isLt
  have hl := l.isLt
  rcases matchEnds with ⟨_, eq⟩ | ⟨eq, _⟩ <;> omega

private theorem quad_point_bit (Q : Finset (Fin 13)) (p : Fin 13) :
    (quadRow Q).getD p.val false = decide (p ∈ Q) := by
  rw [quadRow, List.getD_append _ _ _ _ (by simp)]
  exact PEqualNP.Outside.L_meta_1751.getD_ofFn 13 _ false p.val p.isLt

private theorem quad_line_bit (Q : Finset (Fin 13)) (l : Fin 13) :
    (quadRow Q).getD (13+l.val) false = decide (∀ p ∈ Q, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))) := by
  rw [quadRow, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  exact PEqualNP.Outside.L_meta_1751.getD_ofFn 13 _ false l.val l.isLt

theorem incidence_point_true (p l : Fin 13) :
    (incidenceRow p l).getD p.val false = true := by
  rw [incidenceRow, List.getD_append _ _ _ _ (by simp),
    PEqualNP.Outside.L_meta_1751.getD_ofFn 13 _ false p.val p.isLt]
  simp

theorem incidence_line_true (p l : Fin 13) :
    (incidenceRow p l).getD (13+l.val) false = true := by
  rw [incidenceRow, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [PEqualNP.Outside.L_meta_1751.getD_ofFn 13 _ false l.val l.isLt]
  simp

theorem negative_no_incidence_pair {L : List Bool} (neg : negative L) {u v : ℕ}
    (edge : planeAdjacent u v) (leftTrue : L.getD u false = true) (rightTrue : L.getD v false = true) :
    False := by
  obtain ⟨Q, _, rfl⟩ := neg
  obtain ⟨p, l, incident, endpoints⟩ := edge
  have impossible (hp : (quadRow Q).getD p.val false = true)
      (hl : (quadRow Q).getD (13+l.val) false = true) : False := by
    rw [quad_point_bit] at hp
    rw [quad_line_bit] at hl
    exact (of_decide_eq_true hl p (of_decide_eq_true hp)) incident
  rcases endpoints with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact impossible leftTrue rightTrue
  · exact impossible rightTrue leftTrue

structure PlaneStar where
  center : ℕ
  leaves : List ℕ

namespace PlaneStar

def Legal (s : PlaneStar) : Prop :=
  s.center < 26 ∧ ∀ leaf ∈ s.leaves, planeAdjacent s.center leaf

def Hits (s : PlaneStar) (L : List Bool) : Prop :=
  L.getD s.center false = true ∧ ∃ leaf ∈ s.leaves, L.getD leaf false = true

def cost (s : PlaneStar) : ℕ :=
  s.leaves.length + if s.leaves = [] then 0 else 1

def empty : PlaneStar := ⟨0, []⟩

theorem empty_legal : empty.Legal := by simp [empty, Legal]
theorem empty_never_hits (L : List Bool) : ¬ empty.Hits L := by simp [empty, Hits]
theorem empty_cost : empty.cost = 0 := rfl

theorem negative_not_hit {s : PlaneStar} (legal : s.Legal) {L : List Bool} (neg : negative L) :
    ¬ s.Hits L := by
  rintro ⟨center, l, mem, leaf⟩
  exact negative_no_incidence_pair neg (legal.2 l mem) center leaf

end PlaneStar

 
theorem plane_star_replacement (D : Circuit) (first second : PlaneStar) (cap : ℕ)
    (mono : Monotone2 D) (back : ReadsBack 26 D) (flat : AddStar.Flat 26 D)
    (output : D.output < 26+D.gates.length)
    (neg : ∀ L, negative L → D.eval L = false)
    (firstLegal : first.Legal) (secondLegal : second.Legal)
    (covers : ∀ L, positive L → D.eval L = false → first.Hits L ∨ second.Hits L)
    (budget : D.size + first.cost + second.cost ≤ cap) :
    ∃ E : Circuit, acceptable E ∧ AddStar.Flat 26 E ∧ E.size ≤ cap := by
  have firstLeaves : ∀ w ∈ first.leaves, w < 26 := fun w hm => planeAdjacent_leaf (firstLegal.2 w hm)
  have secondLeaves : ∀ w ∈ second.leaves, w < 26 := fun w hm => planeAdjacent_leaf (secondLegal.2 w hm)
  let D₁ := AddStar.circuit 26 D first.center first.leaves
  let E := AddStar.circuit 26 D₁ second.center second.leaves
  obtain ⟨m1,b1,f1,o1⟩ := AddStar.circuit_props mono back flat output firstLegal.1 firstLeaves
  obtain ⟨m2,b2,f2,_⟩ := AddStar.circuit_props m1 b1 f1 o1 secondLegal.1 secondLeaves
  have ev (L : List Bool) (hl : L.length = 26) :
      E.eval L = true ↔ (D.eval L = true ∨ first.Hits L) ∨ second.Hits L := by
    unfold E D₁
    rw [AddStar.circuit_accepts o1 secondLegal.1 secondLeaves hl,
      AddStar.circuit_accepts output firstLegal.1 firstLeaves hl]
    rfl
  have epos (L : List Bool) (hp : positive L) : E.eval L = true := by
    have hl : L.length = 26 := by
      obtain ⟨p,l,_,rfl⟩ := hp
      exact row_length p l
    apply (ev L hl).mpr
    cases h : D.eval L with
    | true => exact Or.inl (Or.inl rfl)
    | false =>
      rcases covers L hp h with safe | safe
      · exact Or.inl (Or.inr safe)
      · exact Or.inr safe
  have eneg (L : List Bool) (hn : negative L) : E.eval L = false := by
    have hl : L.length = 26 := by
      obtain ⟨Q,_,rfl⟩ := hn
      simp [quadRow]
    apply Bool.eq_false_iff.mpr
    intro ht
    rcases (ev L hl).mp ht with (hd | hf) | hs
    · rw [neg L hn] at hd
      contradiction
    · exact first.negative_not_hit firstLegal hn hf
    · exact second.negative_not_hit secondLegal hn hs
  refine ⟨E, ⟨m2,b2,(separates_iff_rows E).mpr ⟨epos,eneg⟩⟩, f2, ?_⟩
  unfold E D₁
  rw [AddStar.circuit_size, AddStar.circuit_size]
  unfold PlaneStar.cost at budget
  omega

theorem plane_star_budget (D : Circuit) (first second : PlaneStar) (cap : ℕ)
    (mono : Monotone2 D) (back : ReadsBack 26 D) (flat : AddStar.Flat 26 D)
    (output : D.output < 26+D.gates.length)
    (neg : ∀ L, negative L → D.eval L = false)
    (firstLegal : first.Legal) (secondLegal : second.Legal)
    (covers : ∀ L, positive L → D.eval L = false → first.Hits L ∨ second.Hits L)
    (budget : D.size + first.cost + second.cost ≤ cap) : 64 ≤ cap := by
  obtain ⟨E, ok, nst, size⟩ := plane_star_replacement D first second cap mono back flat output
    neg firstLegal secondLegal covers budget
  have bound := plane_no_nested_bound E ok (by
    rintro ⟨i,j,oi,oj,anc⟩
    exact nst i j oi oj anc)
  exact bound.trans size


end OneNestedAnd

/- Source work/quad1961/frontier-lean/OrderThreeQuadranglePairs.lean -/
namespace Quadrangle1692

open PEqualNP.CircuitLowerBounds

abbrev V := Fin 13

def offsets : Finset V := {0, 1, 3, 9}

def incident (p l : V) : Prop := p - l ∈ offsets

instance (p l : V) : Decidable (incident p l) := inferInstanceAs (Decidable (p - l ∈ offsets))

def Good (Q : Finset V) : Prop :=
  Q.card = 4 ∧ ∀ l : V, (Q.filter (fun p => incident p l)).card ≤ 2

instance (Q : Finset V) : Decidable (Good Q) :=
  inferInstanceAs (Decidable (Q.card = 4 ∧ ∀ l : V, (Q.filter (fun p => incident p l)).card ≤ 2))

def exterior (Q : Finset V) : Finset V := Finset.univ.filter (fun l => ∀ p ∈ Q, ¬ incident p l)

@[simp] theorem mem_exterior {Q : Finset V} {l : V} :
    l ∈ exterior Q ↔ ∀ p ∈ Q, ¬ incident p l := by simp [exterior]

def input (S T : Finset V) : List Bool :=
  List.ofFn (fun p : V => decide (p ∈ S)) ++ List.ofFn (fun l : V => decide (l ∈ T))

def testInput (Q : Finset V) : List Bool := input Q (exterior Q)

theorem testInput_eq (Q : Finset V) : testInput Q =
    List.ofFn (fun p : V => decide (p ∈ Q)) ++
      List.ofFn (fun l : V => decide (∀ p ∈ Q, ¬ incident p l)) := by
  simp [testInput, input]

private def pointTable (d : V) : Finset V :=
  match d.val with
  | 3 => {0, 2, 3, 4}
  | 4 => {0, 1, 4, 6}
  | 6 => {0, 1, 2, 6}
  | 7 => {0, 1, 2, 7}
  | 8 => {0, 1, 4, 8}
  | 9 => {0, 2, 4, 9}
  | 10 => {0, 1, 5, 10}
  | 11 => {0, 1, 2, 11}
  | 12 => {0, 1, 4, 12}
  | _ => {0, 1, 2, 5}

private def lineTable (d : V) : Finset V :=
  match d.val with
  | 1 => {5, 6, 7, 11}
  | 2 => {4, 6, 7, 8}
  | 3 => {2, 5, 7, 8}
  | 4 => {2, 6, 8, 10}
  | 5 => {2, 4, 7, 11}
  | 6 => {4, 5, 8, 10}
  | 8 => {2, 5, 6, 10}
  | 9 => {2, 4, 6, 8}
  | 10 => {2, 4, 5, 8}
  | 12 => {4, 5, 6, 10}
  | _ => {2, 4, 5, 6}

private def mixedTable (d : V) : Finset V :=
  match d.val with
  | 7 => {2, 4, 7, 8}
  | 8 => {2, 4, 5, 8}
  | 10 => {2, 5, 6, 10}
  | 11 => {2, 4, 6, 11}
  | 12 => {2, 4, 5, 12}
  | _ => {2, 4, 5, 6}

private def shift (d : V) (Q : Finset V) : Finset V := Q.image (fun p => p + d)

private def pointQuad (p q : V) : Finset V := shift p (pointTable (q - p))
private def lineQuad (l k : V) : Finset V := shift l (lineTable (k - l))
private def mixedQuad (p l : V) : Finset V := shift l (mixedTable (p - l))

private theorem pointTable_ok : ∀ d : V, Good (pointTable d) ∧ 0 ∈ pointTable d ∧ d ∈ pointTable d := by
  decide +kernel

private theorem lineTable_ok : ∀ d : V, Good (lineTable d) ∧ 0 ∈ exterior (lineTable d) ∧
    d ∈ exterior (lineTable d) := by
  decide +kernel

private theorem mixedTable_ok : ∀ d : V, ¬ incident d 0 →
    Good (mixedTable d) ∧ d ∈ mixedTable d ∧ 0 ∈ exterior (mixedTable d) := by
  decide +kernel

private theorem shift_good {Q : Finset V} (hQ : Good Q) (d : V) : Good (shift d Q) := by
  have inj : Function.Injective (fun p : V => p + d) := fun _ _ h => add_right_cancel h
  refine ⟨?_, ?_⟩
  · rw [shift, Finset.card_image_of_injective _ inj]
    exact hQ.1
  · intro l
    have he : (fun p : V => incident (p + d) l) = fun p : V => incident p (l - d) := by
      funext p
      unfold incident
      congr 1
      abel
    have hf : Q.filter (fun p : V => incident (p + d) l) = Q.filter (fun p : V => incident p (l - d)) := by
      ext p
      simp only [Finset.mem_filter]
      rw [congrFun he p]
    rw [shift, Finset.filter_image, hf, Finset.card_image_of_injective _ inj]
    exact hQ.2 (l - d)

private theorem shift_mem {Q : Finset V} {p : V} (hp : p ∈ Q) (d : V) : p + d ∈ shift d Q :=
  Finset.mem_image_of_mem _ hp

private theorem shift_exterior {Q : Finset V} {l : V} (hl : l ∈ exterior Q) (d : V) :
    l + d ∈ exterior (shift d Q) := by
  rw [mem_exterior]
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  simpa [incident, add_sub_add_right_eq_sub] using (mem_exterior.mp hl) p hp

private theorem pointQuad_ok (p q : V) :
    Good (pointQuad p q) ∧ p ∈ pointQuad p q ∧ q ∈ pointQuad p q := by
  obtain ⟨hQ, hp, hq⟩ := pointTable_ok (q - p)
  exact ⟨shift_good hQ p, by simpa [pointQuad] using shift_mem hp p,
    by simpa [pointQuad] using shift_mem hq p⟩

private theorem lineQuad_ok (l k : V) :
    Good (lineQuad l k) ∧ l ∈ exterior (lineQuad l k) ∧ k ∈ exterior (lineQuad l k) := by
  obtain ⟨hQ, hl, hk⟩ := lineTable_ok (k - l)
  exact ⟨shift_good hQ l, by simpa [lineQuad] using shift_exterior hl l,
    by simpa [lineQuad] using shift_exterior hk l⟩

private theorem mixedQuad_ok (p l : V) (hn : ¬ incident p l) :
    Good (mixedQuad p l) ∧ p ∈ mixedQuad p l ∧ l ∈ exterior (mixedQuad p l) := by
  have hd : ¬ incident (p - l) 0 := by simpa [incident] using hn
  obtain ⟨hQ, hp, hl⟩ := mixedTable_ok (p - l) hd
  exact ⟨shift_good hQ l, by simpa [mixedQuad] using shift_mem hp l,
    by simpa [mixedQuad] using shift_exterior hl l⟩

private theorem pair_cover {S : Finset V} (h : S.card ≤ 2) :
    ∃ p q : V, S ⊆ {p, q} := by
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp⟩ := hS
    have hc : (S.erase p).card ≤ 1 := by
      have he := Finset.card_erase_of_mem hp
      omega
    obtain ⟨q, hq⟩ := Finset.card_le_one_iff_subset_singleton.mp hc
    refine ⟨p, q, ?_⟩
    intro x hx
    by_cases hx' : x = p
    · simp [hx']
    · have : x ∈ ({q} : Finset V) := hq (Finset.mem_erase.mpr ⟨hx', hx⟩)
      exact Finset.mem_insert_of_mem this
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    exact ⟨0, 0, by simp [he]⟩

 
theorem exists_test_cover {S T : Finset V} (hsmall : S.card + T.card ≤ 2)
    (hindependent : ∀ p ∈ S, ∀ l ∈ T, ¬ incident p l) :
    ∃ Q : Finset V, Good Q ∧ S ⊆ Q ∧ T ⊆ exterior Q := by
  by_cases hS : S.Nonempty
  · by_cases hT : T.Nonempty
    · have hSp := Finset.card_pos.mpr hS
      have hTp := Finset.card_pos.mpr hT
      obtain ⟨p, hp⟩ := hS
      obtain ⟨l, hl⟩ := hT
      have hSc : S.card ≤ 1 := by omega
      have hTc : T.card ≤ 1 := by omega
      obtain ⟨hquad, hpq, hlq⟩ := mixedQuad_ok p l (hindependent p hp l hl)
      refine ⟨mixedQuad p l, hquad, ?_, ?_⟩
      · intro x hx
        simpa [Finset.card_le_one.mp hSc x hx p hp] using hpq
      · intro x hx
        simpa [Finset.card_le_one.mp hTc x hx l hl] using hlq
    · have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      obtain ⟨p, q, hpq⟩ := pair_cover (S := S) (by omega)
      obtain ⟨hquad, hp, hq⟩ := pointQuad_ok p q
      refine ⟨pointQuad p q, hquad, ?_, by simp [hTe]⟩
      intro x hx
      rcases Finset.mem_insert.mp (hpq hx) with rfl | hxq
      · exact hp
      · simpa [Finset.mem_singleton.mp hxq] using hq
  · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    obtain ⟨l, k, hlk⟩ := pair_cover (S := T) (by omega)
    obtain ⟨hquad, hl, hk⟩ := lineQuad_ok l k
    refine ⟨lineQuad l k, hquad, by simp [hSe], ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp (hlk hx) with rfl | hxk
    · exact hl
    · simpa [Finset.mem_singleton.mp hxk] using hk

private theorem gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ → Bool) (hab : ∀ i, a i = true → b i = true) :
    g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
  rcases hop with h | h
  · simp only [h, GateOp.eval, List.all_map, List.all_eq_true]
    intro ha i hi
    exact hab i (ha i hi)
  · simp only [h, GateOp.eval, List.any_map, List.any_eq_true]
    rintro ⟨i, hi, hia⟩
    exact ⟨i, hi, hab i hia⟩

private theorem wires_mono (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ w, ((Circuit.mk gs 0).wires a).getD w false = true →
        ((Circuit.mk gs 0).wires b).getD w false = true := by
  induction gs with
  | nil =>
    intro a b _ hab w hw
    exact hab w hw
  | cons g gs ih =>
    intro a b hlen hab w hw
    let ga := g.op.eval (g.inputs.map (fun i => a.getD i false))
    let gb := g.op.eval (g.inputs.map (fun i => b.getD i false))
    change ((Circuit.mk gs 0).wires (a ++ [ga])).getD w false = true at hw
    change ((Circuit.mk gs 0).wires (b ++ [gb])).getD w false = true
    apply ih (fun j hj => hop j (List.mem_cons_of_mem g hj)) _ _ (by simp [hlen]) _ w hw
    intro i hi
    by_cases hlt : i < a.length
    · rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hab i hi
    · by_cases heq : i = a.length
      · subst i
        have hg : ga = true := by simpa using hi
        have hg' := gate_mono g (hop g (by simp)) _ _ hab hg
        simpa [hlen, gb] using hg'
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        contradiction

private theorem input_getD_mono {S T Q R : Finset V} (hS : S ⊆ Q) (hT : T ⊆ R) (i : ℕ) :
    (input S T).getD i false = true → (input Q R).getD i false = true := by
  intro hi
  unfold input at hi ⊢
  by_cases hp : i < 13
  · rw [List.getD_append _ _ _ _ (by simpa using hp)] at hi
    rw [List.getD_append _ _ _ _ (by simpa using hp)]
    rw [List.getD_eq_getElem _ _ (by simpa using hp)] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hp)]
    simp only [List.getElem_ofFn, decide_eq_true_eq] at hi ⊢
    exact hS hi
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hp)] at hi
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hp)]
    simp only [List.length_ofFn] at hi ⊢
    by_cases hl : i - 13 < 13
    · rw [List.getD_eq_getElem _ _ (by simpa using hl)] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hl)]
      simp only [List.getElem_ofFn, decide_eq_true_eq] at hi ⊢
      exact hT hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hl)] at hi
      contradiction

 
theorem reject_small_independent_wire (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hneg : ∀ Q : Finset V, Good Q → ((Circuit.mk gs 0).wires (testInput Q)).getD w false = false)
    (S T : Finset V) (hsmall : S.card + T.card ≤ 2)
    (hindependent : ∀ p ∈ S, ∀ l ∈ T, ¬ incident p l) :
    ((Circuit.mk gs 0).wires (input S T)).getD w false = false := by
  obtain ⟨Q, hQ, hS, hT⟩ := exists_test_cover hsmall hindependent
  by_contra h
  have htrue : ((Circuit.mk gs 0).wires (input S T)).getD w false = true := by simpa using h
  have hv := wires_mono gs hop (input S T) (testInput Q) (by simp [testInput, input])
    (input_getD_mono hS hT) w htrue
  rw [hneg Q hQ] at hv
  contradiction

 
theorem reject_small_independent (C : Circuit)
    (hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hneg : ∀ Q : Finset V, Good Q → C.eval (testInput Q) = false)
    (S T : Finset V) (hsmall : S.card + T.card ≤ 2)
    (hindependent : ∀ p ∈ S, ∀ l ∈ T, ¬ incident p l) : C.eval (input S T) = false := by
  exact reject_small_independent_wire C.gates hop C.output hneg S T hsmall hindependent

 
theorem reject_small_independent_from_tests (gates : List Gate) (out : ℕ)
    (hop : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hneg : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun p => p - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      (Circuit.mk gates out).eval (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false)
    (S T : Finset (Fin 13)) (hsmall : S.card + T.card ≤ 2)
    (hindependent : ∀ p ∈ S, ∀ l ∈ T, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))) :
    (Circuit.mk gates out).eval (List.ofFn (fun p : Fin 13 => decide (p ∈ S)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ T))) = false := by
  refine reject_small_independent ⟨gates, out⟩ (fun g hg => (hop g hg).1) ?_ S T hsmall hindependent
  intro Q hQ
  rw [testInput_eq]
  exact hneg Q hQ.1 hQ.2


end Quadrangle1692

/- Source work/quad1961/frontier-lean/PlanePairs.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open Quadrangle1692 (incident)

abbrev PlaneVertex := Fin 13



theorem quadRow_testInput (Q : Finset PlaneVertex) :
    quadRow Q = Quadrangle1692.testInput Q := by
  rw [Quadrangle1692.testInput_eq]
  rfl

theorem negative_testInput {Q : Finset PlaneVertex} (good : Quadrangle1692.Good Q) :
    negative (Quadrangle1692.testInput Q) :=
  ⟨Q, good, (quadRow_testInput Q).symm⟩

def OrStep (C : Circuit) (u v : ℕ) : Prop :=
  ∃ j < C.gates.length, v = 26+j ∧ (gateAt C j).op = .or ∧
    u ∈ (gateAt C j).inputs ∧ u < v

abbrev OrReaches (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep C)

theorem or_step_of_reads {C : Circuit} (back : ReadsBack 26 C) {j u : ℕ}
    (jC : j < C.gates.length) (op : (gateAt C j).op = .or) (mem : u ∈ (gateAt C j).inputs) :
    OrStep C u (26+j) := ⟨j,jC,rfl,op,mem,back j jC u mem⟩

private theorem or_step_true {C : Circuit} {u v : ℕ} (step : OrStep C u v)
    {L : List Bool} (len : L.length = 26) (positive : (C.wires L).getD u false = true) :
    (C.wires L).getD v false = true := by
  obtain ⟨j,bound,rfl,op,mem,before⟩ := step
  have h := W_spec C.gates L j _ (gateAt_some C j bound)
  rw [len, op] at h
  change (W C.gates L).getD (26+j) false = true
  rw [h]
  apply List.any_eq_true.mpr
  refine ⟨true,List.mem_map.mpr ⟨u,mem,?_⟩,rfl⟩
  rw [ite_eq_left before]
  exact positive

theorem or_reaches_true {C : Circuit} {u v : ℕ} (reach : OrReaches C u v)
    {L : List Bool} (len : L.length = 26) (positive : (C.wires L).getD u false = true) :
    (C.wires L).getD v false = true := by
  induction reach with
  | refl => exact positive
  | tail _ step ih => exact or_step_true step len ih

theorem negative_or_reaching_wire {C : Circuit}
    (reject : ∀ L, negative L → C.eval L = false) {w : ℕ} (reach : OrReaches C w C.output)
    {L : List Bool} (neg : negative L) : (C.wires L).getD w false = false := by
  have len : L.length = 26 := by obtain ⟨Q,_,rfl⟩ := neg; simp [quadRow]
  apply Bool.eq_false_iff.mpr
  intro pos
  have h : C.eval L = true := or_reaches_true reach len pos
  rw [reject L neg] at h
  contradiction

 
theorem reject_plane_pair_at {C : Circuit} (mono : Monotone2 C)
    (reject : ∀ L, negative L → C.eval L = false) {w : ℕ} (reach : OrReaches C w C.output)
    {S T : Finset PlaneVertex} (small : S.card + T.card ≤ 2)
    (independent : ∀ p ∈ S, ∀ l ∈ T, ¬ incident p l) :
    (C.wires (Quadrangle1692.input S T)).getD w false = false := by
  exact Quadrangle1692.reject_small_independent_wire C.gates (fun g mem => (mono g mem).1) w
    (fun Q good => negative_or_reaching_wire reject reach (negative_testInput good)) _ _ small independent

theorem reject_plane_pair {C : Circuit} (mono : Monotone2 C)
    (reject : ∀ L, negative L → C.eval L = false) {S T : Finset PlaneVertex}
    (small : S.card + T.card ≤ 2) (independent : ∀ p ∈ S, ∀ l ∈ T, ¬ incident p l) :
    C.eval (Quadrangle1692.input S T) = false :=
  reject_plane_pair_at mono reject Relation.ReflTransGen.refl small independent

def pointIndices (S : Finset ℕ) : Finset PlaneVertex :=
  Finset.univ.filter (fun p : PlaneVertex => p.val ∈ S)

def lineIndices (S : Finset ℕ) : Finset PlaneVertex :=
  Finset.univ.filter (fun l : PlaneVertex => 13+l.val ∈ S)

@[simp] theorem mem_pointIndices {p : PlaneVertex} {S : Finset ℕ} :
    p ∈ pointIndices S ↔ p.val ∈ S := by simp [pointIndices]

@[simp] theorem mem_lineIndices {l : PlaneVertex} {S : Finset ℕ} :
    l ∈ lineIndices S ↔ 13+l.val ∈ S := by simp [lineIndices]

def rawInput (S : Finset ℕ) : List Bool := Quadrangle1692.input (pointIndices S) (lineIndices S)

theorem rawInput_point (S : Finset ℕ) (p : PlaneVertex) :
    (rawInput S).getD p.val false = decide (p.val ∈ S) := by
  unfold rawInput Quadrangle1692.input
  rw [List.getD_append _ _ _ _ (by simp), PEqualNP.Outside.L_meta_1751.getD_ofFn 13 _ false p.val p.isLt]
  simp only [mem_pointIndices]

theorem rawInput_line (S : Finset ℕ) (l : PlaneVertex) :
    (rawInput S).getD (13+l.val) false = decide (13+l.val ∈ S) := by
  unfold rawInput Quadrangle1692.input
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [PEqualNP.Outside.L_meta_1751.getD_ofFn 13 _ false l.val l.isLt]
  simp only [mem_lineIndices]

theorem rawInput_bit (S : Finset ℕ) {i : ℕ} (valid : i < 26) :
    (rawInput S).getD i false = decide (i ∈ S) := by
  rcases Nat.lt_or_ge i 13 with hp | hl
  · exact rawInput_point S ⟨i,hp⟩
  · let l : PlaneVertex := ⟨i-13,by omega⟩
    have eq : 13+l.val = i := by dsimp [l]; omega
    simpa only [eq] using rawInput_line S l

@[simp] theorem rawInput_length (S : Finset ℕ) : (rawInput S).length = 26 := by
  simp [rawInput, Quadrangle1692.input]

theorem rawInput_incidence (p l : PlaneVertex) :
    rawInput {p.val,13+l.val} = incidenceRow p l := by
  have ps : pointIndices {p.val,13+l.val} = {p} := by
    ext q
    simp only [mem_pointIndices, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (eq | impossible)
      · exact Fin.ext eq
      · have := q.isLt
        omega
    · rintro rfl
      exact Or.inl rfl
  have ls : lineIndices {p.val,13+l.val} = {l} := by
    ext k
    simp only [mem_lineIndices, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (impossible | eq)
      · have := p.isLt
        omega
      · exact Fin.ext (Nat.add_left_cancel eq)
    · rintro rfl
      exact Or.inr rfl
  rw [rawInput, ps, ls]
  simp [Quadrangle1692.input, incidenceRow]

theorem indices_card (S : Finset ℕ) :
    (pointIndices S).card + (lineIndices S).card ≤ S.card := by
  let P := (pointIndices S).image Fin.val
  let L := (lineIndices S).image (fun l => 13+l.val)
  have cover : P ∪ L ⊆ S := by
    intro i mem
    rcases Finset.mem_union.mp mem with pm | lm
    · obtain ⟨p,hm,rfl⟩ := Finset.mem_image.mp pm
      exact mem_pointIndices.mp hm
    · obtain ⟨l,hm,rfl⟩ := Finset.mem_image.mp lm
      exact mem_lineIndices.mp hm
  have disjoint : Disjoint P L := by
    apply Finset.disjoint_left.mpr
    intro i pm lm
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp pm
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp lm
    have := p.isLt
    omega
  have pc : P.card = (pointIndices S).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have lc : L.card = (lineIndices S).card :=
    Finset.card_image_of_injective _ (fun p l e => Fin.ext (Nat.add_left_cancel e))
  have count := Finset.card_le_card cover
  rw [Finset.card_union_of_disjoint disjoint, pc, lc] at count
  exact count

theorem reject_small_raw_at {C : Circuit} (mono : Monotone2 C)
    (reject : ∀ L, negative L → C.eval L = false) {w : ℕ} (reach : OrReaches C w C.output)
    {S : Finset ℕ} (small : S.card ≤ 2)
    (independent : ∀ a ∈ S, ∀ b ∈ S, ¬ planeAdjacent a b) :
    (C.wires (rawInput S)).getD w false = false := by
  apply reject_plane_pair_at mono reject reach ((indices_card S).trans small)
  intro p pm l lm edge
  exact independent p.val (mem_pointIndices.mp pm) (13+l.val) (mem_lineIndices.mp lm)
    (planeAdjacent_point_line edge)

theorem reject_small_raw {C : Circuit} (mono : Monotone2 C)
    (reject : ∀ L, negative L → C.eval L = false) {S : Finset ℕ} (small : S.card ≤ 2)
    (independent : ∀ a ∈ S, ∀ b ∈ S, ¬ planeAdjacent a b) :
    C.eval (rawInput S) = false :=
  reject_small_raw_at mono reject Relation.ReflTransGen.refl small independent

theorem planeAdjacent_reverse {a b : ℕ} (edge : planeAdjacent a b) : planeAdjacent b a := by
  obtain ⟨p,l,inc,ends⟩ := edge
  exact ⟨p,l,inc,ends.symm⟩

theorem planeAdjacent_sides {a b : ℕ} (edge : planeAdjacent a b) :
    (a < 13 ∧ 13 ≤ b ∧ b < 26) ∨ (b < 13 ∧ 13 ≤ a ∧ a < 26) := by
  obtain ⟨p,l,_,pair⟩ := edge
  have hp := p.isLt
  have hl := l.isLt
  rcases pair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨hp,by omega,by omega⟩
  · exact Or.inr ⟨hp,by omega,by omega⟩

theorem planeAdjacent_ne {a b : ℕ} (edge : planeAdjacent a b) : a ≠ b := by
  rcases planeAdjacent_sides edge with h | h <;> omega

theorem planeAdjacent_point_line_iff {p l : PlaneVertex} :
    planeAdjacent p.val (13+l.val) ↔ incident p l := by
  refine ⟨?_, planeAdjacent_point_line⟩
  rintro ⟨q,k,adj,⟨ep,el⟩ | ⟨falseOrientation,_⟩⟩
  · have point : p = q := Fin.ext ep
    have line : l = k := Fin.ext (Nat.add_left_cancel el)
    rwa [point,line]
  · have := p.isLt
    omega

theorem reject_raw_nonedge_at {C : Circuit} (mono : Monotone2 C)
    (reject : ∀ L, negative L → C.eval L = false) {w : ℕ} (reach : OrReaches C w C.output)
    {a b : ℕ} (noEdge : ¬ planeAdjacent a b) :
    (C.wires (rawInput {a,b})).getD w false = false := by
  apply reject_small_raw_at mono reject reach Finset.card_le_two
  intro u um v vm
  simp only [Finset.mem_insert, Finset.mem_singleton] at um vm
  rcases um with rfl | rfl <;> rcases vm with rfl | rfl
  · exact fun edge => planeAdjacent_ne edge rfl
  · exact noEdge
  · exact fun edge => noEdge (planeAdjacent_reverse edge)
  · exact fun edge => planeAdjacent_ne edge rfl

theorem incident_common_line {p q l k : PlaneVertex} (different : p ≠ q)
    (pl : incident p l) (ql : incident q l) (pk : incident p k) (qk : incident q k) :
    l = k := by
  apply Finset.card_le_one.mp (PEqualNP.Outside.L_meta_1751.geo_lines p q different) l ?_ k ?_
  · simpa [PEqualNP.Outside.L_meta_1751.Lp, incident, Quadrangle1692.offsets] using And.intro pl ql
  · simpa [PEqualNP.Outside.L_meta_1751.Lp, incident, Quadrangle1692.offsets] using And.intro pk qk

theorem incident_common_point {l k p q : PlaneVertex} (different : l ≠ k)
    (pl : incident p l) (pk : incident p k) (ql : incident q l) (qk : incident q k) :
    p = q := by
  apply Finset.card_le_one.mp (PEqualNP.Outside.L_meta_1751.geo_points l k different) p ?_ q ?_
  · simpa [PEqualNP.Outside.L_meta_1751.Pl, incident, Quadrangle1692.offsets] using And.intro pl pk
  · simpa [PEqualNP.Outside.L_meta_1751.Pl, incident, Quadrangle1692.offsets] using And.intro ql qk

theorem planeAdjacent_common_neighbor {a b x y : ℕ} (ab : a ≠ b)
    (ax : planeAdjacent a x) (bx : planeAdjacent b x)
    (ay : planeAdjacent a y) (by' : planeAdjacent b y) : x = y := by
  have sx := planeAdjacent_sides bx
  have sy := planeAdjacent_sides ay
  rcases planeAdjacent_sides ax with ⟨aP,xL,xU⟩ | ⟨xP,aL,aU⟩
  · have bP : b < 13 := by rcases sx with h | h <;> omega
    have yL : 13 ≤ y := by rcases sy with h | h <;> omega
    have yU : y < 26 := by rcases sy with h | h <;> omega
    let p : PlaneVertex := ⟨a,aP⟩
    let q : PlaneVertex := ⟨b,bP⟩
    let l : PlaneVertex := ⟨x-13,by omega⟩
    let k : PlaneVertex := ⟨y-13,by omega⟩
    have pl : 13+l.val = x := by dsimp [l]; omega
    have pk : 13+k.val = y := by dsimp [k]; omega
    have pq : p ≠ q := fun eq => ab (congrArg Fin.val eq)
    have pin : incident p l := planeAdjacent_point_line_iff.mp (by simpa only [pl] using ax)
    have qin : incident q l := planeAdjacent_point_line_iff.mp (by simpa only [pl] using bx)
    have poke : incident p k := planeAdjacent_point_line_iff.mp (by simpa only [pk] using ay)
    have qoke : incident q k := planeAdjacent_point_line_iff.mp (by simpa only [pk] using by')
    have eq := incident_common_line pq pin qin poke qoke
    rw [← pl, ← pk, eq]
  · have bL : 13 ≤ b := by rcases sx with h | h <;> omega
    have bU : b < 26 := by rcases sx with h | h <;> omega
    have yP : y < 13 := by rcases sy with h | h <;> omega
    let l : PlaneVertex := ⟨a-13,by omega⟩
    let k : PlaneVertex := ⟨b-13,by omega⟩
    let p : PlaneVertex := ⟨x,xP⟩
    let q : PlaneVertex := ⟨y,yP⟩
    have pl : 13+l.val = a := by dsimp [l]; omega
    have pk : 13+k.val = b := by dsimp [k]; omega
    have lk : l ≠ k := by
      intro eq
      apply ab
      rw [← pl, ← pk, eq]
    have pin : incident p l := planeAdjacent_point_line_iff.mp (by simpa only [pl] using planeAdjacent_reverse ax)
    have poke : incident p k := planeAdjacent_point_line_iff.mp (by simpa only [pk] using planeAdjacent_reverse bx)
    have qin : incident q l := planeAdjacent_point_line_iff.mp (by simpa only [pl] using planeAdjacent_reverse ay)
    have qoke : incident q k := planeAdjacent_point_line_iff.mp (by simpa only [pk] using planeAdjacent_reverse by')
    exact congrArg Fin.val (incident_common_point lk pin poke qin qoke)


end OneNestedAnd

/- Source work/quad1961/frontier-lean/DeadLabels.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

lemma rawSupport_or_reaches (C : Circuit) (back : ReadsBack 26 C) :
    ∀ w < 26+C.gates.length, ∀ p ∈ rawSupport 26 C w, OrReaches C p w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro bound p mem
    by_cases raw : w < 26
    · rw [rawSupport_primary 26 C raw, Finset.mem_singleton] at mem
      subst p
      exact Relation.ReflTransGen.refl
    · obtain ⟨j,rfl⟩ : ∃ j, w = 26+j := ⟨w-26,by omega⟩
      have jb : j < C.gates.length := by omega
      by_cases op : (gateAt C j).op = .or
      · have eq := rawSupport_or 26 C (show 26 ≤ 26+j by omega) (by simpa using op)
        rw [eq] at mem
        obtain ⟨v,older,label⟩ := Finset.mem_biUnion.mp mem
        have hv := (Finset.mem_filter.mp older).2
        have read : v ∈ (gateAt C j).inputs := by
          simpa [earlierInputs] using (Finset.mem_filter.mp older).1
        exact (ih v hv (hv.trans bound) p label).tail (or_step_of_reads back jb op read)
      · rw [rawSupport_and 26 C (show 26 ≤ 26+j by omega) (by simpa using op)] at mem
        exact (Finset.notMem_empty _ mem).elim

theorem rawSupport_mono_or_reaches {C : Circuit} {u v : ℕ} (path : OrReaches C u v) :
    rawSupport 26 C u ⊆ rawSupport 26 C v := by
  intro p label
  induction path with
  | refl => exact label
  | tail _ step ih =>
    obtain ⟨j,_,rfl,op,mem,earlier⟩ := step
    rw [rawSupport_or 26 C (show 26 ≤ 26+j by omega) (by simpa using op)]
    exact Finset.mem_biUnion.mpr ⟨_,
      Finset.mem_filter.mpr ⟨by simpa [earlierInputs] using mem, earlier⟩, ih⟩

theorem or_reaches_feeds {C : Circuit} (back : ReadsBack 26 C) (i : ℕ) :
    ∀ {w}, OrReaches C (26+i) w → Feeds 26 C i w := by
  intro w reach
  induction reach with
  | refl => exact Or.inl rfl
  | tail _ step ih =>
    obtain ⟨j,bound,rfl,_,mem,_⟩ := step
    exact feeds_of_reader 26 C back bound mem ih

private theorem reader_of_feed_contains {C : Circuit} (back : ReadsBack 26 C)
    {i j w : ℕ} (jb : j < C.gates.length) (mem : w ∈ (gateAt C j).inputs)
    (feed : Feeds 26 C i w) : InCone 26 C i j := by
  have before := back j jb w mem
  rcases feed with eq | ⟨lower,cone⟩
  · exact (inCone_iff 26 C i j).mpr ⟨jb,i,by omega,by simpa [eq] using mem,Or.inl rfl⟩
  · have src : 26+(w-26) = w := by omega
    exact (inCone_iff 26 C i j).mpr ⟨jb,w-26,by omega,by simpa [src] using mem,Or.inr cone⟩

 
theorem feed_or_single_and {C : Circuit} (mono : Monotone2 C) (back : ReadsBack 26 C)
    (flat : AddStar.Flat 26 C) (i : ℕ) :
    ∀ w < 26+C.gates.length, Feeds 26 C i w →
      OrReaches C (26+i) w ∨
      ∃ j < C.gates.length, (gateAt C j).op = .and ∧
        ∃ u ∈ (gateAt C j).inputs, OrReaches C (26+i) u ∧ OrReaches C (26+j) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro bound feed
    have lower : 26 ≤ w := by rcases feed with eq | ⟨raw,_⟩ <;> omega
    obtain ⟨slot,rfl⟩ : ∃ slot, w = 26+slot := ⟨w-26,by omega⟩
    have sb : slot < C.gates.length := by omega
    by_cases same : i = slot
    · subst slot
      exact Or.inl Relation.ReflTransGen.refl
    obtain ⟨u,mem,upstream⟩ := (feeds_iff_reader 26 C back sb same).mp feed
    have before := back slot sb u mem
    have prior := ih u before (before.trans bound) upstream
    have hm := mono _ (List.mem_iff_getElem?.mpr ⟨slot,gateAt_some C slot sb⟩)
    rcases hm.1 with hand | hor
    · rcases prior with route | ⟨j,_,op,_,_,_,down⟩
      · exact Or.inr ⟨slot,sb,hand,u,mem,route,Relation.ReflTransGen.refl⟩
      · exact (flat j slot op hand (reader_of_feed_contains back sb mem (or_reaches_feeds back j down))).elim
    · have step := or_step_of_reads back sb hor mem
      rcases prior with route | ⟨j,jb,op,src,reads,up,down⟩
      · exact Or.inl (route.tail step)
      · exact Or.inr ⟨j,jb,op,src,reads,up,down.tail step⟩

theorem live_slot_feeds_output {C : Circuit} {i : ℕ} (live : i ∈ Retain.liveSlots 26 C) :
    Feeds 26 C i C.output := by
  obtain ⟨_,outRaw,shape⟩ := Retain.mem_liveSlots.mp live
  rcases shape with eq | cone
  · exact Or.inl (by omega)
  · exact Or.inr ⟨outRaw,cone⟩

theorem live_and_or_reaches_output {C : Circuit} (mono : Monotone2 C) (back : ReadsBack 26 C)
    (flat : AddStar.Flat 26 C) (output : C.output < 26+C.gates.length)
    {i : ℕ} (live : i ∈ Retain.liveSlots 26 C) (op : (gateAt C i).op = .and) :
    OrReaches C (26+i) C.output := by
  rcases feed_or_single_and mono back flat i C.output output (live_slot_feeds_output live) with
      allOr | ⟨j,jC,andOp,_,mem,entry,_⟩
  · exact allOr
  · exact (flat i j op andOp (reader_of_feed_contains back jC mem (or_reaches_feeds back i entry))).elim

private theorem wireOn_and (C : Circuit) (back : ReadsBack 26 C) (x : List Bool)
    (len : x.length = 26) {j : ℕ} (bound : j < C.gates.length) (op : (gateAt C j).op = .and) :
    wireOn C x (26+j) ↔ ∀ w ∈ (gateAt C j).inputs, wireOn C x w := by
  have eval := W_spec C.gates x j _ (gateAt_some C j bound)
  rw [len, op] at eval
  have map : ((gateAt C j).inputs.map fun i =>
      if i < 26+j then (W C.gates x).getD i false else false) =
      ((gateAt C j).inputs.map fun i => (W C.gates x).getD i false) := by
    apply List.map_congr_left
    intro i hi
    simp [back j bound i hi]
  change (W C.gates x).getD (26+j) false = true ↔
    ∀ w ∈ (gateAt C j).inputs, (W C.gates x).getD w false = true
  rw [eval,map]
  simp [GateOp.eval, List.all_eq_true]

private theorem two_operand_cover {w : ℕ} {xs : List ℕ} (arity : xs.length ≤ 2) (mem : w ∈ xs) :
    ∃ u ∈ xs, ∀ v ∈ xs, v = w ∨ v = u := by
  cases xs with
  | nil => simp at mem
  | cons a tail =>
    cases tail with
    | nil =>
      have e : w = a := by simpa using mem
      subst w
      exact ⟨a,by simp,by simp⟩
    | cons b tail =>
      cases tail with
      | nil =>
        have e : w = a ∨ w = b := by simpa using mem
        rcases e with rfl | rfl
        · exact ⟨b,by simp,by simp⟩
        · exact ⟨a,by simp,by simp [or_comm]⟩
      | cons c tail => simp at arity

private theorem raw_bit_sets_wire {C : Circuit} {S : Finset ℕ} {w : ℕ} (valid : w < 26)
    (mem : w ∈ S) : wireOn C (rawInput S) w := by
  change (W C.gates (rawInput S)).getD w false = true
  rw [W_inp _ _ _ (by simpa using valid), rawInput_bit S valid]
  exact decide_eq_true mem

 
def LiveAndRawMates (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = .and → OrReaches C (26+j) C.output →
    ∀ u ∈ (gateAt C j).inputs, (rawSupport 26 C u).Nonempty

 
theorem live_label_edges {C : Circuit} (mono : Monotone2 C) (back : ReadsBack 26 C)
    (flat : AddStar.Flat 26 C) (output : C.output < 26+C.gates.length)
    (neg : ∀ L, negative L → C.eval L = false) (hasMate : LiveAndRawMates C)
    {i : ℕ} (live : i ∈ Retain.liveSlots 26 C) (support : (rawSupport 26 C (26+i)).Nonempty) :
    ∃ b < 26, ∀ p ∈ rawSupport 26 C (26+i),
      planeAdjacent p b ∧ C.eval (rawInput {p,b}) = true := by
  have iC := (Retain.mem_liveSlots.mp live).1
  rcases feed_or_single_and mono back flat i C.output output (live_slot_feeds_output live) with
      finalOr | ⟨j,jC,andOp,src,read,entry,finish⟩
  · obtain ⟨p,hp⟩ := support
    have pRaw := (rawSupport_bounds 26 C (26+i) p hp).1
    have pToI := rawSupport_or_reaches C back (26+i) (by omega) p hp
    have singletonOn : wireOn C (rawInput {p}) p := raw_bit_sets_wire pRaw (by simp)
    have accepted : C.eval (rawInput {p}) = true :=
      or_reaches_true (pToI.trans finalOr) (rawInput_length {p}) singletonOn
    have rejected := reject_small_raw mono neg (S := {p}) (by simp) (by
      intro a ha b hb edge
      simp only [Finset.mem_singleton] at ha hb
      subst a
      subst b
      exact planeAdjacent_ne edge rfl)
    rw [accepted] at rejected
    contradiction
  · have arity := (mono _ (List.mem_iff_getElem?.mpr ⟨j,gateAt_some C j jC⟩)).2
    obtain ⟨mate,hm,cover⟩ := two_operand_cover arity read
    obtain ⟨b,hb⟩ := hasMate j jC andOp finish mate hm
    have bRaw := (rawSupport_bounds 26 C mate b hb).1
    have mateValid : mate < 26+C.gates.length := by
      have := back j jC mate hm
      omega
    have bPath := rawSupport_or_reaches C back mate mateValid b hb
    refine ⟨b,bRaw,?_⟩
    intro p hp
    have pRaw := (rawSupport_bounds 26 C (26+i) p hp).1
    have pPath := (rawSupport_or_reaches C back (26+i) (by omega) p hp).trans entry
    have srcOn : wireOn C (rawInput {p,b}) src :=
      or_reaches_true pPath (rawInput_length _) (raw_bit_sets_wire pRaw (by simp))
    have mateOn : wireOn C (rawInput {p,b}) mate :=
      or_reaches_true bPath (rawInput_length _) (raw_bit_sets_wire bRaw (by simp))
    have andOn := (wireOn_and C back (rawInput {p,b}) (rawInput_length _) jC andOp).mpr
      (by intro w hw; rcases cover w hw with rfl | rfl; exact srcOn; exact mateOn)
    have positive : C.eval (rawInput {p,b}) = true :=
      or_reaches_true finish (rawInput_length _) andOn
    refine ⟨?_,positive⟩
    by_contra absent
    have h := reject_raw_nonedge_at mono neg Relation.ReflTransGen.refl absent
    change C.eval (rawInput {p,b}) = false at h
    rw [positive] at h
    contradiction

theorem no_live_mixed_labels {C : Circuit} (mono : Monotone2 C) (back : ReadsBack 26 C)
    (flat : AddStar.Flat 26 C) (output : C.output < 26+C.gates.length)
    (neg : ∀ L, negative L → C.eval L = false) (hasMate : LiveAndRawMates C)
    {i p q : ℕ} (hp : p ∈ rawSupport 26 C (26+i)) (hq : q ∈ rawSupport 26 C (26+i))
    (point : p < 13) (line : 13 ≤ q) : i ∉ Retain.liveSlots 26 C := by
  intro live
  obtain ⟨b,_,touch⟩ := live_label_edges mono back flat output neg hasMate live ⟨p,hp⟩
  rcases planeAdjacent_sides (touch p hp).1 with pb | pb <;>
    rcases planeAdjacent_sides (touch q hq).1 with qb | qb <;> omega

theorem no_live_lost_join {C : Circuit} (mono : Monotone2 C) (back : ReadsBack 26 C)
    (flat : AddStar.Flat 26 C) (output : C.output < 26+C.gates.length)
    (neg : ∀ L, negative L → C.eval L = false) (hasMate : LiveAndRawMates C)
    {i p q b : ℕ} (hp : p ∈ rawSupport 26 C (26+i)) (hq : q ∈ rawSupport 26 C (26+i))
    (distinct : p ≠ q) (pb : planeAdjacent p b) (qb : planeAdjacent q b)
    (lost : C.eval (rawInput {p,b}) = false ∨ C.eval (rawInput {q,b}) = false) :
    i ∉ Retain.liveSlots 26 C := by
  intro live
  obtain ⟨m,_,touch⟩ := live_label_edges mono back flat output neg hasMate live ⟨p,hp⟩
  have eq := planeAdjacent_common_neighbor distinct (touch p hp).1 (touch q hq).1 pb qb
  subst m
  rcases lost with lost | lost
  · rw [(touch p hp).2] at lost
    contradiction
  · rw [(touch q hq).2] at lost
    contradiction


end OneNestedAnd

/- Source work/quad1961/ProjectPlan.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

structure ProjectionPlan (C : Circuit) (h : ℕ) where
  slot : ℕ
  target : Option ℕ
  slot_bound : slot < C.gates.length
  order : h < slot
  replacement :
    (target = none ∧ (gateAt C slot).op = .and ∧ 26 + h ∈ (gateAt C slot).inputs) ∨
    ∃ r, target = some r ∧ (gateAt C slot).op = .or ∧
      ((gateAt C slot).inputs = [26 + h, r] ∨ (gateAt C slot).inputs = [r, 26 + h]) ∧ r ≠ 26 + h

namespace ProjectionPlan

variable {C : Circuit} {h H : ℕ} (P : ProjectionPlan C h)

def rep (w : ℕ) : Option ℕ := ProjectAliases.mapTwo 26 h P.slot P.target w

noncomputable def projected : Circuit := ProjectAliases.circuit 26 (clearLower C h) P.rep

lemma rules (back : ReadsBack 26 C) (low : (gateAt C h).op = .and) :
    ProjectAliases.Rules 26 (clearLower C h) P.rep := by
  have slotIn : P.slot < (clearLower C h).gates.length := by simpa using P.slot_bound
  have options := P.replacement
  have empty := clearLower_at_self (gateAt_and_bound C h low)
  have other := clearLower_at_other (C := C) P.order.ne.symm
  unfold rep
  rcases options with ⟨none, op, used⟩ | ⟨r, someR, op, inputs, ne⟩
  · rw [none]
    exact ProjectAliases.mapTwo_and P.order slotIn (clearLower_back back h) empty
      (by simpa only [other] using op) (by simpa only [other] using used)
  · rw [someR]
    exact ProjectAliases.mapTwo_or P.order slotIn (clearLower_back back h) empty
      (by simpa only [other] using op) (by simpa only [other] using inputs) ne

lemma rawSupport_or_pair (C : Circuit) (back : ReadsBack 26 C) {j a b : ℕ}
    (bound : j < C.gates.length) (op : (gateAt C j).op = .or)
    (read : (gateAt C j).inputs = [a,b]) :
    rawSupport 26 C (26 + j) = rawSupport 26 C a ∪ rawSupport 26 C b := by
  have ha := back j bound a (by simp [read])
  have hb := back j bound b (by simp [read])
  rw [rawSupport_or 26 C (by omega) (by simpa using op)]
  ext label
  simp only [earlierInputs, Nat.add_sub_cancel_left, read, Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false, Finset.mem_union]
  constructor
  · rintro ⟨r, ⟨rfl | rfl, _⟩, hp⟩
    · exact Or.inl hp
    · exact Or.inr hp
  · rintro (hp | hp)
    · exact ⟨a, ⟨Or.inl rfl, ha⟩, hp⟩
    · exact ⟨b, ⟨Or.inr rfl, hb⟩, hp⟩

lemma raw_maps (back : ReadsBack 26 C) (low : (gateAt C h).op = .and) :
    ∀ w < 26 + C.gates.length,
      ((P.rep w).map (rawSupport 26 P.projected)).getD ∅ = rawSupport 26 C w := by
  have hb := gateAt_and_bound C h low
  have lowEmpty : rawSupport 26 C (26 + h) = ∅ :=
    rawSupport_and 26 C (by omega) (by simp [low])
  have rule : ∀ j < C.gates.length, P.rep (26+j) ≠ some (26+j) →
      ((P.rep (26+j)).map (rawSupport 26 C)).getD ∅ = rawSupport 26 C (26+j) := by
    intro j bound changed
    by_cases same : j = h
    · subst j
      simp [rep, lowEmpty]
    · by_cases next : j = P.slot
      · subst j
        rw [rep, ProjectAliases.mapTwo_second 26 P.order]
        rcases P.replacement with ⟨zero, op, _⟩ | ⟨r, mapped, op, shape, _⟩
        · rw [zero]
          simp only [Option.map_none, Option.getD_none]
          exact (rawSupport_and 26 C (by omega) (by simp [op])).symm
        · rw [mapped]
          rcases shape with read | read
          · simp [rawSupport_or_pair C back P.slot_bound op read, lowEmpty]
          · simp [rawSupport_or_pair C back P.slot_bound op read, lowEmpty]
      · exact False.elim (changed (ProjectAliases.mapTwo_other (by omega) (by omega)))
  intro w hw
  have rawFun : rawSupport 26 (clearLower C h) = rawSupport 26 C :=
    funext (rawSupport_clearLower 26 C h hb low)
  have equality := rawSupport_project_aliases 26 (clearLower C h) P.rep (P.rules back low)
    (clearLower_back back h) (by
      intro j hj neq
      simpa only [rawFun] using rule j (by simpa using hj) neq)
    w (by simpa using hw)
  simpa only [projected, rawFun] using equality

lemma projected_size : P.projected.size = C.size := by simp [projected, Circuit.size]

lemma projected_gate_count : P.projected.gates.length = C.gates.length := by simp [projected]

theorem projected_eval (ok : acceptable C) (low : (gateAt C h).op = .and)
    (output : C.output < 26 + C.gates.length) {x : List Bool} (hx : x.length = 26) :
    P.projected.eval x = (clearLower C h).eval x :=
  ProjectAliases.circuit_eval (P.rules ok.2.1 low) (clearLower_mono ok.1 h)
    (clearLower_back ok.2.1 h) (by simpa using output) hx

lemma no_live_lower_slot (back : ReadsBack 26 C) (low : (gateAt C h).op = .and)
    (valid : P.projected.output < 26 + P.projected.gates.length) :
    h ∉ Retain.liveSlots 26 P.projected ∧ P.slot ∉ Retain.liveSlots 26 P.projected := by
  have outRep : ∃ u, P.rep C.output = some u := by
    cases eq : P.rep C.output with
    | none => simp [projected, ProjectAliases.circuit, eq] at valid
    | some u => exact ⟨u, rfl⟩
  obtain ⟨u, hu⟩ := outRep
  have realOut : P.rep (clearLower C h).output = some u := hu
  have rule := P.rules back low
  constructor
  · exact ProjectAliases.altered_not_live rule realOut (by simp [rep])
  · apply ProjectAliases.altered_not_live rule realOut
    rw [rep, ProjectAliases.mapTwo_second 26 P.order]
    rcases P.replacement with ⟨zero, _, _⟩ | ⟨r, mapped, _, read, _⟩
    · simp [zero]
    · have member : r ∈ (gateAt C P.slot).inputs := by rcases read with both | both <;> simp [both]
      have earlier := back P.slot P.slot_bound r member
      simp [mapped, earlier.ne]

theorem live_mates (ok : acceptable C) (strict : StrictBinary C)
    (one : PEqualNP.TopForm.andPairs 26 C ≤ 1) (low : (gateAt C h).op = .and)
    (high : (gateAt C H).op = .and) (nest : InCone 26 C h H) : LiveAndRawMates P.projected := by
  let D := clearLower C h
  intro j jBound andGate _ u read
  have jD : j < D.gates.length := by simpa [projected, D] using jBound
  have fixed : P.rep (26 + j) = some (26 + j) := by
    by_contra different
    have zero : gateAt P.projected j = ⟨.or, []⟩ :=
      ProjectAliases.circuit_at_changed jD different
    rw [zero] at andGate
    cases andGate
  have gateEq : gateAt P.projected j = ProjectAliases.substituted P.rep (gateAt D j) :=
    ProjectAliases.circuit_at_fixed jD fixed
  have oldAnd : (gateAt D j).op = .and := by
    rw [gateEq] at andGate
    unfold ProjectAliases.substituted at andGate
    split at andGate
    · cases andGate
    · exact andGate
  have notLower : j ≠ h := by
    intro equal
    subst j
    have zero : gateAt D h = ⟨.or, []⟩ := clearLower_at_self (gateAt_and_bound C h low)
    rw [zero] at oldAnd
    cases oldAnd
  have gateClear : gateAt D j = gateAt C j := clearLower_at_other notLower
  have trueAnd : (gateAt C j).op = .and := by simpa [gateClear] using oldAnd
  obtain ⟨w, usedD, mapped⟩ := ProjectAliases.circuit_read jD read
  have used : w ∈ (gateAt C j).inputs := by simpa [gateClear] using usedD
  have bound : w < 26 + C.gates.length := by
    have jC := gateAt_and_bound C j trueAnd
    have step := ok.2.1 j jC w used
    omega
  have rawNonempty : (rawSupport 26 C w).Nonempty := by
    by_contra! noRaw
    have e := empty_raw_is_lower 26 C ok.1 ok.2.1 strict h w bound
      (fun i op fd => (feeds_and_input_unique 26 C ok.2.1 one low high nest trueAnd used op fd).1) noRaw
    rw [e] at mapped
    simp [rep] at mapped
  have rawEq := P.raw_maps ok.2.1 low w bound
  simp only [mapped, Option.map_some, Option.getD_some] at rawEq
  rw [rawEq]
  exact rawNonempty

end ProjectionPlan

theorem plan_for_inputs {C : Circuit} {h H : ℕ} (ports : NestInputs C h H) (ok : acceptable C)
    (strict : StrictBinary C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H) :
    ∃ P : ProjectionPlan C h, (rawSupport 26 C ports.upperFeed = ∅ ∧ P.slot = H) ∨
      ((rawSupport 26 C ports.upperFeed).Nonempty ∧ P.slot < H) := by
  have hb := gateAt_and_bound C H high
  have used := ports.reads_upperFeed
  have wlt := ok.2.1 H hb _ used
  have allow : AllowsOnly 26 C h ports.upperFeed := fun j op fd =>
    (feeds_and_input_unique 26 C ok.2.1 one low high nest high used op fd).1
  by_cases empty : rawSupport 26 C ports.upperFeed = ∅
  · have p := empty_raw_is_lower 26 C ok.1 ok.2.1 strict h ports.upperFeed (by omega) allow empty
    have mem : 26 + h ∈ (gateAt C H).inputs := p ▸ used
    exact ⟨⟨H, none, hb, cone_lt nest, Or.inl ⟨rfl, high, mem⟩⟩, Or.inl ⟨empty, rfl⟩⟩
  · have lowEmpty := rawSupport_and 26 C (wire := 26+h) (by omega) (by simp [low])
    have proper : ports.upperFeed ≠ 26 + h := by
      intro equal
      exact empty (equal ▸ lowEmpty)
    obtain ⟨j, r, jC, jh, jw, jOr, read, raw⟩ := first_mixing_reader 26 C ok.1 ok.2.1
      strict h ports.upperFeed (by omega) allow ports.connects proper
    have rDifferent : r ≠ 26 + h := by
      intro equal
      simp [equal, lowEmpty] at raw
    exact ⟨⟨j, some r, jC, jh, Or.inr ⟨r, rfl, jOr, read, rDifferent⟩⟩,
      Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr empty, by change j < H; omega⟩⟩

end OneNestedAnd

/- Source work/quad1961/ClauseShape.lean -/
namespace ClauseShape

abbrev Vertex := Fin 13
abbrev Index := Fin 3

structure Clauses where
  points : Index → Finset Vertex
  lines : Index → Finset Vertex

namespace Clauses

def Hit (D : Clauses) (p l : Vertex) : Prop :=
  ∀ i, p ∈ D.points i ∨ l ∈ D.lines i

def mask (S : Index → Finset Vertex) (v : Vertex) : Finset Index :=
  Finset.univ.filter fun i => v ∉ S i

@[simp] lemma mem_mask (S : Index → Finset Vertex) (v : Vertex) (i : Index) :
    i ∈ mask S v ↔ v ∉ S i := by simp [mask]

lemma mask_positive (S : Index → Finset Vertex)
    (reject : ∀ p q, ¬ ∀ i, p ∈ S i ∨ q ∈ S i) (p : Vertex) : 0 < (mask S p).card := by
  apply Finset.card_pos.mpr
  by_contra! h
  apply reject p p
  intro i
  left
  by_contra no
  have member := (mem_mask S p i).mpr no
  rw [h] at member
  exact Finset.notMem_empty _ member

lemma of_single_mask (S : Index → Finset Vertex)
    (reject : ∀ p q, ¬ ∀ i, p ∈ S i ∨ q ∈ S i) {p : Vertex} {i : Index}
    (single : mask S p = {i}) : S i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q qmem
  apply reject p q
  intro j
  by_cases same : j = i
  · exact Or.inr (same ▸ qmem)
  · left
    by_contra no
    have h := (mem_mask S p j).mpr no
    rw [single, Finset.mem_singleton] at h
    exact same h

lemma mask_hit (D : Clauses) (p l : Vertex) : D.Hit p l ↔
    Disjoint (mask D.points p) (mask D.lines l) := by
  rw [Finset.disjoint_left]
  constructor
  · intro h i hm hl
    exact (h i).elim ((mem_mask _ _ _).mp hm) ((mem_mask _ _ _).mp hl)
  · intro h i
    by_contra! absent
    exact h ((mem_mask _ _ _).mpr absent.1) ((mem_mask _ _ _).mpr absent.2)

def RectangleFree (D : Clauses) : Prop :=
  ∀ p q l k, D.Hit p l → D.Hit p k → D.Hit q l → D.Hit q k → p = q ∨ l = k

def swap (D : Clauses) : Clauses := ⟨D.lines, D.points⟩

lemma swap_hit (D : Clauses) (p l : Vertex) : D.swap.Hit l p ↔ D.Hit p l := by
  simp only [Hit, swap, or_comm]

def Star (D : Clauses) : Prop :=
  (∃ p, ∀ q l, D.Hit q l → q = p) ∨ (∃ l, ∀ p k, D.Hit p k → k = l)

lemma singleton_line_of_hit (D : Clauses)
    (rejectP : ∀ p q, ¬ ∀ i, p ∈ D.points i ∨ q ∈ D.points i)
    (rejectL : ∀ l k, ¬ ∀ i, l ∈ D.lines i ∨ k ∈ D.lines i)
    (noSingle : ¬ ∃ p i, mask D.points p = {i}) {p l : Vertex} (hit : D.Hit p l) :
    ∃ i, mask D.lines l = {i} := by
  have hP := mask_positive D.points rejectP p
  have hL := mask_positive D.lines rejectL l
  have hNotOne : (mask D.points p).card ≠ 1 :=
    fun h => noSingle ⟨p, Finset.card_eq_one.mp h⟩
  have disj := (D.mask_hit p l).mp hit
  have cap : (mask D.points p ∪ mask D.lines l).card ≤ 3 := Finset.card_le_univ _
  rw [Finset.card_union_of_disjoint disj] at cap
  exact Finset.card_eq_one.mp (by omega)

theorem star_of_no_point_single (D : Clauses) (rect : D.RectangleFree)
    (rejectP : ∀ p q, ¬ ∀ i, p ∈ D.points i ∨ q ∈ D.points i)
    (rejectL : ∀ l k, ¬ ∀ i, l ∈ D.lines i ∨ k ∈ D.lines i)
    (noSingle : ¬ ∃ p i, mask D.points p = {i}) : D.Star := by
  classical
  by_cases any : ∃ p l, D.Hit p l
  · obtain ⟨p, l, initial⟩ := any
    obtain ⟨i, first⟩ := D.singleton_line_of_hit rejectP rejectL noSingle initial
    have pure := of_single_mask D.lines rejectL first
    have allSame (q k : Vertex) (h : D.Hit q k) : mask D.lines k = {i} := by
      obtain ⟨j, eq⟩ := D.singleton_line_of_hit rejectP rejectL noSingle h
      have hi : i ∈ mask D.lines k := by simp [pure]
      rw [eq, Finset.mem_singleton] at hi
      simpa only [← hi] using eq
    have replace (q k k' : Vertex) (h : D.Hit q k) (same : mask D.lines k' = {i}) : D.Hit q k' := by
      apply (D.mask_hit q k').mpr
      rw [same, ← allSame q k h]
      exact (D.mask_hit q k).mp h
    by_cases other : ∃ q k, q ≠ p ∧ D.Hit q k
    · obtain ⟨q, k, different, second⟩ := other
      right
      refine ⟨l, fun w t ht => ?_⟩
      have h := rect p q t l (replace p l t initial (allSame w t ht)) initial
        (replace q k t second (allSame w t ht)) (replace q k l second first)
      exact h.resolve_left (Ne.symm different)
    · left
      refine ⟨p, fun q k hit => ?_⟩
      by_contra different
      exact other ⟨q, k, different, hit⟩
  · left
    exact ⟨0, fun p l h => False.elim (any ⟨p, l, h⟩)⟩

lemma third_index (i j : Index) : i ≠ j →
    ∃ k : Index, k ≠ i ∧ k ≠ j ∧ ∀ t : Index, t = i ∨ t = j ∨ t = k := by
  have all : ∀ i j : Index, i ≠ j →
      ∃ k : Index, k ≠ i ∧ k ≠ j ∧ ∀ t : Index, t = i ∨ t = j ∨ t = k := by decide
  exact all i j

lemma hit_three (D : Clauses) (i j k : Index)
    (covers : ∀ t : Index, t = i ∨ t = j ∨ t = k)
    (purePoints : D.lines i = ∅) (pureLines : D.points j = ∅) (p l : Vertex) :
    D.Hit p l ↔ p ∈ D.points i ∧ l ∈ D.lines j ∧ (p ∈ D.points k ∨ l ∈ D.lines k) := by
  constructor
  · intro h
    exact ⟨by simpa [purePoints] using h i, by simpa [pureLines] using h j, h k⟩
  · rintro ⟨hp, hl, hmix⟩ t
    rcases covers t with rfl | rfl | rfl
    · exact Or.inl hp
    · exact Or.inr hl
    · exact hmix

def DoubleStar (D : Clauses) : Prop :=
  ∃ (p l : Vertex) (i j k : Index),
    i ≠ j ∧ k ≠ i ∧ k ≠ j ∧ D.lines i = ∅ ∧ D.points j = ∅ ∧
    p ∈ D.points k ∧ l ∈ D.lines k ∧ D.Hit p l ∧
    ∀ q r, D.Hit q r → q ∈ D.points i ∧ r ∈ D.lines j ∧ (q = p ∨ r = l)

theorem star_or_double_of_pure (D : Clauses) (rect : D.RectangleFree) (i j : Index)
    (purePoints : D.lines i = ∅) (pureLines : D.points j = ∅) : D.Star ∨ D.DoubleStar := by
  classical
  by_cases any : ∃ p l, D.Hit p l
  · obtain ⟨p, l, hit⟩ := any
    have distinct : i ≠ j := by
      intro same
      subst j
      simpa [purePoints, pureLines] using hit i
    obtain ⟨k, ki, kj, covers⟩ := third_index i j distinct
    let hit' := D.hit_three i j k covers purePoints pureLines
    by_cases twoP : ∃ a b, a ≠ b ∧ a ∈ D.points i ∧ b ∈ D.points i
    · obtain ⟨p₀, p₁, nep, hp₀, hp₁⟩ := twoP
      by_cases twoL : ∃ a b, a ≠ b ∧ a ∈ D.lines j ∧ b ∈ D.lines j
      · obtain ⟨l₀, l₁, nel, hl₀, hl₁⟩ := twoL
        have uniqueP {a b} (ha : a ∈ D.points i) (ha' : a ∈ D.points k)
            (hb : b ∈ D.points i) (hb' : b ∈ D.points k) : a = b :=
          (rect a b l₀ l₁ ((hit' a l₀).mpr ⟨ha, hl₀, Or.inl ha'⟩)
            ((hit' a l₁).mpr ⟨ha, hl₁, Or.inl ha'⟩)
            ((hit' b l₀).mpr ⟨hb, hl₀, Or.inl hb'⟩)
            ((hit' b l₁).mpr ⟨hb, hl₁, Or.inl hb'⟩)).resolve_right nel
        have uniqueL {a b} (ha : a ∈ D.lines j) (ha' : a ∈ D.lines k)
            (hb : b ∈ D.lines j) (hb' : b ∈ D.lines k) : a = b :=
          (rect p₀ p₁ a b ((hit' p₀ a).mpr ⟨hp₀, ha, Or.inr ha'⟩)
            ((hit' p₀ b).mpr ⟨hp₀, hb, Or.inr hb'⟩)
            ((hit' p₁ a).mpr ⟨hp₁, ha, Or.inr ha'⟩)
            ((hit' p₁ b).mpr ⟨hp₁, hb, Or.inr hb'⟩)).resolve_left nep
        by_cases hasP : ∃ a, a ∈ D.points i ∧ a ∈ D.points k
        · obtain ⟨a, ai, ak⟩ := hasP
          by_cases hasL : ∃ b, b ∈ D.lines j ∧ b ∈ D.lines k
          · obtain ⟨b, bj, bk⟩ := hasL
            right
            refine ⟨a, b, i, j, k, distinct, ki, kj, purePoints, pureLines, ak, bk,
              (hit' a b).mpr ⟨ai, bj, Or.inl ak⟩, fun u v h => ?_⟩
            obtain ⟨ui, vj, uk | vk⟩ := (hit' u v).mp h
            · exact ⟨ui, vj, Or.inl (uniqueP ui uk ai ak)⟩
            · exact ⟨ui, vj, Or.inr (uniqueL vj vk bj bk)⟩
          · left; left
            refine ⟨a, fun q r h => ?_⟩
            obtain ⟨qi, rj, qk | rk⟩ := (hit' q r).mp h
            · exact uniqueP qi qk ai ak
            · exact False.elim (hasL ⟨r, rj, rk⟩)
        · obtain ⟨pi, lj, pk | lk⟩ := (hit' p l).mp hit
          · exact False.elim (hasP ⟨p, pi, pk⟩)
          · left; right
            refine ⟨l, fun q r h => ?_⟩
            obtain ⟨qi, rj, qk | rk⟩ := (hit' q r).mp h
            · exact False.elim (hasP ⟨q, qi, qk⟩)
            · exact uniqueL rj rk lj lk
      · left; right
        refine ⟨l, fun q r h => ?_⟩
        by_contra different
        exact twoL ⟨r, l, different, ((hit' q r).mp h).2.1, ((hit' p l).mp hit).2.1⟩
    · left; left
      refine ⟨p, fun q r h => ?_⟩
      by_contra different
      exact twoP ⟨q, p, different, ((hit' q r).mp h).1, ((hit' p l).mp hit).1⟩
  · left; left
    exact ⟨0, fun p l h => False.elim (any ⟨p, l, h⟩)⟩

theorem star_or_double (D : Clauses) (rect : D.RectangleFree)
    (rejectP : ∀ p q, ¬ ∀ i, p ∈ D.points i ∨ q ∈ D.points i)
    (rejectL : ∀ l k, ¬ ∀ i, l ∈ D.lines i ∨ k ∈ D.lines i) : D.Star ∨ D.DoubleStar := by
  classical
  by_cases hasP : ∃ p i, mask D.points p = {i}
  · by_cases hasL : ∃ l i, mask D.lines l = {i}
    · obtain ⟨p, i, hp⟩ := hasP
      obtain ⟨l, j, hl⟩ := hasL
      exact D.star_or_double_of_pure rect j i (of_single_mask D.lines rejectL hl)
        (of_single_mask D.points rejectP hp)
    · have swappedRect : D.swap.RectangleFree := by
        intro a b c d ac ad bc bd
        have h := rect c d a b ((D.swap_hit c a).mp ac) ((D.swap_hit c b).mp bc)
          ((D.swap_hit d a).mp ad) ((D.swap_hit d b).mp bd)
        exact h.symm
      left
      rcases D.swap.star_of_no_point_single swappedRect rejectL rejectP hasL with ⟨p, hp⟩ | ⟨l, hl⟩
      · exact Or.inr ⟨p, fun q r hit => hp r q ((D.swap_hit q r).mpr hit)⟩
      · exact Or.inl ⟨l, fun q r hit => hl r q ((D.swap_hit q r).mpr hit)⟩
  · exact Or.inl (D.star_of_no_point_single rect rejectP rejectL hasP)

end Clauses
end ClauseShape

/- Source work/quad1961/GuardedShape.lean -/
namespace ClauseShape

structure Sides where
  points : Finset Vertex
  lines : Finset Vertex

namespace Sides

def meets (S : Sides) (p l : Vertex) : Prop := p ∈ S.points ∨ l ∈ S.lines

def guarded (U V : Sides) (B : Finset Vertex) (p l : Vertex) : Prop :=
  l ∈ B ∧ U.meets p l ∧ V.meets p l

def lost (A B : Finset Vertex) (U V : Sides) (p l : Vertex) : Prop :=
  guarded U V B p l ∧ p ∉ A

def NoRect (R : Vertex → Vertex → Prop) : Prop :=
  ∀ p q l k, R p l → R p k → R q l → R q k → p = q ∨ l = k

lemma lost_swap (A B : Finset Vertex) (U V : Sides) (p l : Vertex) :
    lost A B U V p l ↔ lost A B V U p l := by
  unfold lost guarded
  tauto

lemma lost_uses_guard (R : Vertex → Vertex → Prop) (noRect : NoRect R)
    (A B : Finset Vertex) (U V : Sides)
    (a b₀ b₁ : Vertex) (ha : a ∈ A) (hb₀ : b₀ ∈ B) (hb₁ : b₁ ∈ B) (different : b₀ ≠ b₁)
    (base : ∀ p ∈ A, ∀ l ∈ B, R p l)
    (sound : ∀ p l, guarded U V B p l → R p l)
    {p l : Vertex} (lostEdge : lost A B U V p l) : l ∈ U.lines ∨ l ∈ V.lines := by
  obtain ⟨⟨_, hU, hV⟩, outside⟩ := lostEdge
  rcases hU with pointU | lineU
  · rcases hV with pointV | lineV
    · have other := noRect p a b₀ b₁
          (sound p b₀ ⟨hb₀, Or.inl pointU, Or.inl pointV⟩)
          (sound p b₁ ⟨hb₁, Or.inl pointU, Or.inl pointV⟩)
          (base a ha b₀ hb₀) (base a ha b₁ hb₁)
      have eq := other.resolve_right different
      exact False.elim (outside (eq.symm ▸ ha))
    · exact Or.inr lineV
  · exact Or.inl lineU

lemma force_center (R : Vertex → Vertex → Prop) (noRect : NoRect R)
    (A B : Finset Vertex) (U V : Sides)
    (a b₀ b₁ : Vertex) (ha : a ∈ A) (hb₀ : b₀ ∈ B) (hb₁ : b₁ ∈ B) (different : b₀ ≠ b₁)
    (base : ∀ p ∈ A, ∀ l ∈ B, R p l)
    (sound : ∀ p l, guarded U V B p l → R p l)
    (rejectLines : ∀ b ∈ B, b ∈ U.lines → V.lines = ∅)
    {p₀ l₀ : Vertex} (first : lost A B U V p₀ l₀) (guard : l₀ ∈ U.lines) :
    ∀ p l, lost A B U V p l → l = l₀ := by
  classical
  have vl := rejectLines l₀ first.1.1 guard
  have pv₀ : p₀ ∈ V.points := by simpa [meets, vl] using first.1.2.2
  intro p l missing
  have gu : l ∈ U.lines := by
    have use := lost_uses_guard R noRect A B U V a b₀ b₁ ha hb₀ hb₁ different base sound missing
    simpa [vl] using use
  have reach₀ (p : Vertex) (pv : p ∈ V.points) : R p l₀ :=
    sound p l₀ ⟨first.1.1, Or.inr guard, Or.inl pv⟩
  have reach (p : Vertex) (pv : p ∈ V.points) : R p l :=
    sound p l ⟨missing.1.1, Or.inr gu, Or.inl pv⟩
  by_cases two : ∃ q ∈ V.points, q ≠ p₀
  · obtain ⟨q, qv, neq⟩ := two
    exact (noRect q p₀ l l₀ (reach q qv) (reach₀ q qv) (reach p₀ pv₀) (reach₀ p₀ pv₀)).resolve_left neq
  · have pv : p ∈ V.points := by simpa [meets, vl] using missing.1.2.2
    have eq : p = p₀ := by
      by_contra differentP
      exact two ⟨p, pv, differentP⟩
    subst p
    have notA : p₀ ≠ a := fun same => first.2 (same.symm ▸ ha)
    exact (noRect p₀ a l l₀ (reach p₀ pv₀) (reach₀ p₀ pv₀)
      (base a ha l missing.1.1) (base a ha l₀ first.1.1)).resolve_left notA

theorem guarded_star (R : Vertex → Vertex → Prop) (noRect : NoRect R)
    (A B : Finset Vertex) (U V : Sides) (chosen : A.Nonempty)
    (base : ∀ p ∈ A, ∀ l ∈ B, R p l)
    (sound : ∀ p l, guarded U V B p l → R p l)
    (rejectUV : ∀ b ∈ B, b ∈ U.lines → V.lines = ∅)
    (rejectVU : ∀ b ∈ B, b ∈ V.lines → U.lines = ∅) :
    ∃ center, ∀ p l, lost A B U V p l → l = center := by
  classical
  by_cases any : ∃ p l, lost A B U V p l
  · obtain ⟨p, l, first⟩ := any
    refine ⟨l, ?_⟩
    by_cases two : ∃ b₀ b₁, b₀ ∈ B ∧ b₁ ∈ B ∧ b₀ ≠ b₁
    · obtain ⟨a, ha⟩ := chosen
      obtain ⟨b₀, b₁, hb₀, hb₁, different⟩ := two
      rcases lost_uses_guard R noRect A B U V a b₀ b₁ ha hb₀ hb₁ different base sound first with hu | hv
      · exact force_center R noRect A B U V a b₀ b₁ ha hb₀ hb₁ different base sound rejectUV first hu
      · have swappedSound (p l : Vertex) (h : guarded V U B p l) : R p l :=
          sound p l ⟨h.1, h.2.2, h.2.1⟩
        have swappedFirst := (lost_swap A B U V p l).mp first
        have result := force_center R noRect A B V U a b₀ b₁ ha hb₀ hb₁ different base
          swappedSound rejectVU swappedFirst hv
        exact fun q k h => result q k ((lost_swap A B U V q k).mp h)
    · intro q k hk
      by_contra different
      exact two ⟨k, l, hk.1.1, first.1.1, different⟩
  · exact ⟨0, fun p l hl => False.elim (any ⟨p, l, hl⟩)⟩

end Sides
end ClauseShape

/- Source work/quad1961/PairTerms.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def supportHits (S : Finset ℕ) (a b : ℕ) : Prop := a ∈ S ∨ b ∈ S

lemma rawOn_pair (C : Circuit) (a b w : ℕ) :
    rawOn 26 C (rawInput {a,b}) w ↔ supportHits (rawSupport 26 C w) a b := by
  constructor
  · rintro ⟨p, support, enabled⟩
    have limit := (rawSupport_bounds 26 C w p support).1
    rw [rawInput_bit {a,b} limit, decide_eq_true_eq] at enabled
    simp only [Finset.mem_insert, Finset.mem_singleton] at enabled
    rcases enabled with rfl | rfl
    · exact Or.inl support
    · exact Or.inr support
  · rintro (left | right)
    · refine ⟨a, left, ?_⟩
      rw [rawInput_bit {a,b} (rawSupport_bounds 26 C w a left).1]
      simp
    · refine ⟨b, right, ?_⟩
      rw [rawInput_bit {a,b} (rawSupport_bounds 26 C w b right).1]
      simp

structure PairTerms where
  lowLeft : Finset ℕ
  lowRight : Finset ℕ
  upperFeed : Finset ℕ
  upperOther : Finset ℕ

namespace PairTerms

def lower (T : PairTerms) (a b : ℕ) : Prop := supportHits T.lowLeft a b ∧ supportHits T.lowRight a b

def base (T : PairTerms) (a b : ℕ) : Prop := supportHits T.upperFeed a b ∧ supportHits T.upperOther a b

def upper (T : PairTerms) (a b : ℕ) : Prop :=
  (supportHits T.upperFeed a b ∨ T.lower a b) ∧ supportHits T.upperOther a b

end PairTerms

namespace NestInputs
variable {C : Circuit} {h H : ℕ} (ports : NestInputs C h H)

def terms : PairTerms := ⟨rawSupport 26 C ports.lowLeft, rawSupport 26 C ports.lowRight,
  rawSupport 26 C ports.upperFeed, rawSupport 26 C ports.upperOther⟩

lemma upper_pair_value (ok : acceptable C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (a b : ℕ) : wireOn C (rawInput {a,b}) (26 + H) ↔ ports.terms.upper a b := by
  rw [ports.upper_value ok one low high nest _ (rawInput_length _),
    ports.lower_value ok one low high nest _ (rawInput_length _)]
  simp only [rawOn_pair, terms, PairTerms.upper, PairTerms.lower]

lemma clear_pair_value (ok : acceptable C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (a b : ℕ) : wireOn (clearLower C h) (rawInput {a,b}) (26 + H) ↔ ports.terms.base a b := by
  rw [ports.clear_upper_value ok one low high nest _ (rawInput_length _)]
  simp only [rawOn_pair, terms, PairTerms.base]

lemma pair_sound (ok : acceptable C) (minimal : ∀ D : Circuit, acceptable D → C.size ≤ D.size)
    (one : PEqualNP.TopForm.andPairs 26 C ≤ 1) (low : (gateAt C h).op = .and)
    (high : (gateAt C H).op = .and) (nest : InCone 26 C h H) :
    ∀ a b, ports.terms.upper a b → planeAdjacent a b := by
  let Honly : Circuit := { C with output := 26 + H }
  have rejected (L : List Bool) (rows : negative L) : Honly.eval L = false :=
    Bool.eq_false_iff.mpr (upper_safe C ok minimal one low high nest L rows)
  intro a b term
  by_contra missing
  have no := reject_raw_nonedge_at (C := Honly) ok.1 rejected Relation.ReflTransGen.refl missing
  have yes := (ports.upper_pair_value ok one low high nest a b).mpr term
  change (C.wires (rawInput {a,b})).getD (26 + H) false = false at no
  change (C.wires (rawInput {a,b})).getD (26 + H) false = true at yes
  rw [no] at yes
  contradiction

lemma other_nonempty (ok : acceptable C) (strict : StrictBinary C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H) :
    ports.terms.upperOther.Nonempty := by
  by_contra! no
  have hb := gateAt_and_bound C H high
  have used := ports.reads_upperOther
  have early := ok.2.1 H hb _ used
  have e := empty_raw_is_lower 26 C ok.1 ok.2.1 strict h ports.upperOther (by omega)
    (fun k kAnd fd => (feeds_and_input_unique 26 C ok.2.1 one low high nest high used kAnd fd).1) no
  exact ports.separate (Or.inl e)

lemma lost_pair (ok : acceptable C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (bad : ∃ L, negative L ∧ wireOn C L (26 + h)) (P : ProjectionPlan C h)
    (p l : Fin 13) (incident : Quadrangle1692.incident p l)
    (lost : P.projected.eval (incidenceRow p l) = false) :
    ports.terms.lower p.val (13+l.val) ∧ supportHits ports.terms.upperOther p.val (13+l.val) ∧
      ¬ supportHits ports.terms.upperFeed p.val (13+l.val) := by
  have rows := (separates_iff_rows C).mp ok.2.2
  obtain ⟨k, kC, out⟩ := output_gate C (rows.1 _ ⟨0, 0, by decide, rfl⟩)
    (rows.1 _ ⟨1, 1, by decide, rfl⟩)
  have outBound : C.output < 26 + C.gates.length := by omega
  have positiveRow : C.eval (incidenceRow p l) = true := rows.1 _ ⟨p, l, incident, rfl⟩
  have projectedFalse : (clearLower C h).eval (incidenceRow p l) = false :=
    (P.projected_eval ok low outBound (row_length p l)).symm.trans lost
  obtain ⟨negativeRow, hn, fired⟩ := bad
  have negLen : negativeRow.length = 26 := by obtain ⟨Q, _, rfl⟩ := hn; simp [quadRow]
  have atUpper := clearLower_lost_at_upper ok.1 ok.2.1 one low high nest (row_length p l) negLen
    fired (rows.2 _ hn) positiveRow projectedFalse
  have topOn : wireOn C (rawInput {p.val, 13+l.val}) (26+H) := by
    simpa only [rawInput_incidence, wireOn] using atUpper.1
  have topOff : ¬ wireOn (clearLower C h) (rawInput {p.val, 13+l.val}) (26+H) := by
    intro firedUpper
    change ((clearLower C h).wires (rawInput {p.val, 13+l.val})).getD (26+H) false = true at firedUpper
    rw [rawInput_incidence, atUpper.2] at firedUpper
    contradiction
  obtain ⟨hi, guard⟩ := (ports.upper_pair_value ok one low high nest p.val (13+l.val)).mp topOn
  have notBase := fun hits => topOff ((ports.clear_pair_value ok one low high nest p.val (13+l.val)).mpr hits)
  have noUpperFeed : ¬ supportHits ports.terms.upperFeed p.val (13+l.val) :=
    fun feed => notBase ⟨feed, guard⟩
  exact ⟨hi.resolve_left noUpperFeed, guard, noUpperFeed⟩

lemma lost_raw_pair (ok : acceptable C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (bad : ∃ L, negative L ∧ wireOn C L (26 + h)) (P : ProjectionPlan C h)
    {a b : ℕ} (edge : planeAdjacent a b) (lost : P.projected.eval (rawInput {a,b}) = false) :
    ports.terms.lower a b ∧ supportHits ports.terms.upperOther a b ∧
      ¬ supportHits ports.terms.upperFeed a b := by
  obtain ⟨p, l, incident, orientation | orientation⟩ := edge
  · rcases orientation with ⟨rfl, rfl⟩
    exact ports.lost_pair ok one low high nest bad P p l incident (by simpa [rawInput_incidence] using lost)
  · rcases orientation with ⟨rfl, rfl⟩
    have hit := ports.lost_pair ok one low high nest bad P p l incident (by
      rw [Finset.pair_comm, rawInput_incidence] at lost
      exact lost)
    simpa only [PairTerms.lower, supportHits, or_comm] using hit

end NestInputs
end OneNestedAnd

/- Source work/quad1961/GuardedAdapter.lean -/
namespace OneNestedAnd

namespace PairTerms

abbrev V := Fin 13

def indexOn (line : Bool) (v : V) : ℕ := if line then 13 + v.val else v.val

def sideCondition (line : Bool) (w : ℕ) : Prop := if line then 13 ≤ w else w < 13

def sideSet (line : Bool) (S : Finset ℕ) : Finset V :=
  if line then lineIndices S else pointIndices S

@[simp] lemma mem_sideSet (line : Bool) (S : Finset ℕ) (p : V) :
    p ∈ sideSet line S ↔ indexOn line p ∈ S := by
  cases line <;> simp [sideSet, indexOn]

lemma indexOn_side (b : Bool) (p : V) : sideCondition b (indexOn b p) := by
  cases b <;> simp [indexOn, sideCondition, p.isLt]

lemma indexOn_bound (b : Bool) (p : V) : indexOn b p < 26 := by
  have e := p.isLt
  cases b <;> simp [indexOn] <;> omega

lemma different_shore (b : Bool) {w : ℕ} (belongs : sideCondition b w) :
    ¬ sideCondition (!b) w := by
  cases b <;> simp [sideCondition] at * <;> omega

def incidentOn (b : Bool) (p l : V) : Prop :=
  if b then Quadrangle1692.incident l p else Quadrangle1692.incident p l

lemma incidentOn_iff (b : Bool) (p l : V) :
    planeAdjacent (indexOn b p) (indexOn (!b) l) ↔ incidentOn b p l := by
  cases b
  · exact planeAdjacent_point_line_iff
  · exact ⟨fun edge => planeAdjacent_point_line_iff.mp (planeAdjacent_reverse edge),
      fun edge => planeAdjacent_reverse (planeAdjacent_point_line_iff.mpr edge)⟩

lemma incidentOn_rectFree (b : Bool) : ClauseShape.Sides.NoRect (incidentOn b) := by
  intro p q l k pl pk ql qk
  by_cases equal : p = q
  · exact Or.inl equal
  · right
    cases b
    · exact incident_common_line equal pl ql pk qk
    · exact incident_common_point equal pl ql pk qk

lemma sameSide_noEdge (b : Bool) (x y : V) : ¬ planeAdjacent (indexOn b x) (indexOn b y) := by
  intro edge
  have hx := indexOn_side b x
  have hy := indexOn_side b y
  rcases planeAdjacent_sides edge with pos | pos <;> cases b <;> simp [sideCondition] at * <;> omega

def sidesOn (b : Bool) (S : Finset ℕ) : ClauseShape.Sides := ⟨sideSet b S, sideSet (!b) S⟩

lemma meets_sidesOn (b : Bool) (S : Finset ℕ) (p l : V) :
    (sidesOn b S).meets p l ↔ supportHits S (indexOn b p) (indexOn (!b) l) := by
  simp [sidesOn, ClauseShape.Sides.meets, supportHits]

lemma pure_base (T : PairTerms) (a : T.upperFeed.Nonempty) (b : T.upperOther.Nonempty)
    (safe : ∀ u v, T.upper u v → planeAdjacent u v) :
    ∃ s : Bool, (∀ u ∈ T.upperFeed, sideCondition s u) ∧ (∀ v ∈ T.upperOther, sideCondition (!s) v) := by
  obtain ⟨a₀, ha⟩ := a
  obtain ⟨b₀, hb⟩ := b
  have baseEdges (u v : ℕ) (hu : u ∈ T.upperFeed) (hv : v ∈ T.upperOther) : planeAdjacent u v :=
    safe u v ⟨Or.inl (Or.inl hu), Or.inr hv⟩
  rcases planeAdjacent_sides (baseEdges a₀ b₀ ha hb) with orientation | orientation
  · refine ⟨false, ?_, ?_⟩
    · intro u hu
      rcases planeAdjacent_sides (baseEdges u b₀ hu hb) with bound | bound
      · exact bound.1
      · omega
    · intro v hv
      rcases planeAdjacent_sides (baseEdges a₀ v ha hv) with bound | bound
      · exact bound.2.1
      · omega
  · refine ⟨true, ?_, ?_⟩
    · intro u hu
      rcases planeAdjacent_sides (baseEdges u b₀ hu hb) with bound | bound
      · omega
      · exact bound.2.1
    · intro v hv
      rcases planeAdjacent_sides (baseEdges a₀ v ha hv) with bound | bound
      · omega
      · exact bound.1

lemma sideSet_nonempty (s : Bool) (S : Finset ℕ) (hne : S.Nonempty)
    (valid : ∀ x ∈ S, x < 26) (shore : ∀ x ∈ S, sideCondition s x) : (sideSet s S).Nonempty := by
  obtain ⟨a, ha⟩ := hne
  have ht := valid a ha
  have hs := shore a ha
  cases s
  · exact ⟨⟨a, hs⟩, (mem_sideSet false S ⟨a, hs⟩).mpr ha⟩
  · let p : V := ⟨a-13, by simp [sideCondition] at hs; omega⟩
    exact ⟨p, (mem_sideSet true S p).mpr (by simpa [indexOn, p, Nat.add_sub_of_le hs] using ha)⟩

theorem guarded_on_shores (T : PairTerms) (s : Bool)
    (hasFeed : (sideSet s T.upperFeed).Nonempty)
    (feedSide : ∀ w ∈ T.upperFeed, sideCondition s w)
    (otherSide : ∀ w ∈ T.upperOther, sideCondition (!s) w)
    (safe : ∀ a b, T.upper a b → planeAdjacent a b) :
    ∃ center : V, ∀ p l,
      T.lower (indexOn s p) (indexOn (!s) l) →
      supportHits T.upperOther (indexOn s p) (indexOn (!s) l) →
      ¬ supportHits T.upperFeed (indexOn s p) (indexOn (!s) l) → l = center := by
  let A := sideSet s T.upperFeed
  let B := sideSet (!s) T.upperOther
  let U := sidesOn s T.lowLeft
  let Vc := sidesOn s T.lowRight
  have base (p : V) (hp : p ∈ A) (l : V) (hl : l ∈ B) : incidentOn s p l :=
    (incidentOn_iff s p l).mp (safe _ _ ⟨Or.inl (Or.inl ((mem_sideSet _ _ _).mp hp)),
      Or.inr ((mem_sideSet _ _ _).mp hl)⟩)
  have sound (p l : V) (hit : ClauseShape.Sides.guarded U Vc B p l) : incidentOn s p l :=
    (incidentOn_iff s p l).mp (safe _ _ ⟨Or.inr
      ⟨(meets_sidesOn s T.lowLeft p l).mp hit.2.1, (meets_sidesOn s T.lowRight p l).mp hit.2.2⟩,
      Or.inr ((mem_sideSet _ _ _).mp hit.1)⟩)
  have uv (b : V) (hb : b ∈ B) (hu : b ∈ U.lines) : Vc.lines = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact sameSide_noEdge (!s) b w (safe _ _ ⟨Or.inr
      ⟨Or.inl ((mem_sideSet _ _ _).mp hu), Or.inr ((mem_sideSet _ _ _).mp hw)⟩,
      Or.inl ((mem_sideSet _ _ _).mp hb)⟩)
  have vu (b : V) (hb : b ∈ B) (hv : b ∈ Vc.lines) : U.lines = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact sameSide_noEdge (!s) b w (safe _ _ ⟨Or.inr
      ⟨Or.inr ((mem_sideSet _ _ _).mp hw), Or.inl ((mem_sideSet _ _ _).mp hv)⟩,
      Or.inl ((mem_sideSet _ _ _).mp hb)⟩)
  obtain ⟨center, shape⟩ := ClauseShape.Sides.guarded_star (incidentOn s) (incidentOn_rectFree s)
    A B U Vc hasFeed base sound uv vu
  refine ⟨center, fun p l lower guard noFeed => shape p l ?_⟩
  have bl : indexOn (!s) l ∈ T.upperOther := guard.resolve_left
    (fun x => different_shore s (indexOn_side s p) (otherSide _ x))
  exact ⟨⟨(mem_sideSet _ _ _).mpr bl, (meets_sidesOn s T.lowLeft p l).mpr lower.1,
    (meets_sidesOn s T.lowRight p l).mpr lower.2⟩, fun hp => noFeed (Or.inl ((mem_sideSet _ _ _).mp hp))⟩

end PairTerms
end OneNestedAnd

/- Source work/quad1961/frontier-lean/SelectedPaths.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem selected_multi_is_or (C : Circuit) (labels : Finset ℕ) {w : ℕ}
    (many : 2 ≤ (selectedSupport 26 C labels w).card) :
    26 ≤ w ∧ (gateAt C (w-26)).op = .or := by
  have nonprimary : 26 ≤ w := by
    by_contra! primary
    have sub : selectedSupport 26 C labels w ⊆ rawSupport 26 C w := Finset.inter_subset_left
    have count := Finset.card_le_card sub
    rw [rawSupport_primary 26 C primary, Finset.card_singleton] at count
    omega
  refine ⟨nonprimary,?_⟩
  by_contra notOr
  simp [selectedSupport,rawSupport_and 26 C nonprimary notOr] at many

theorem selected_representative_raw_subset (C : Circuit) (mono : Monotone2 C) (labels : Finset ℕ)
    (w : ℕ) :
    rawSupport 26 C ((selectedDag 26 C mono labels).representative w) ⊆ rawSupport 26 C w := by
  let D := selectedDag 26 C mono labels
  change rawSupport 26 C (D.representative w) ⊆ rawSupport 26 C w
  by_cases single : (D.support w).card = 1
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp single
    have selected : p ∈ D.support w := by rw [hp]; simp
    have raw : p ∈ rawSupport 26 C w := (Finset.mem_inter.mp selected).1
    have primary := (rawSupport_bounds 26 C w p raw).1
    rw [D.representative_singleton _ _ hp, rawSupport_primary 26 C primary]
    exact Finset.singleton_subset_iff.mpr raw
  · have e : D.representative w = w := by
      unfold OrConeCount.SupportDag.representative
      rw [dite_eq_right single]
    rw [e]

theorem selected_compressed_raw_subset (C : Circuit) (mono : Monotone2 C) (labels : Finset ℕ)
    {w pred : ℕ} (step : pred ∈ (selectedDag 26 C mono labels).compressedInputs w) :
    rawSupport 26 C pred ⊆ rawSupport 26 C w := by
  let D := selectedDag 26 C mono labels
  obtain ⟨many,u,reads,_,rep⟩ := D.compressed_mem.mp step
  have ⟨gate,op⟩ := selected_multi_is_or C labels many
  rw [← rep]
  intro p label
  have fromChild := selected_representative_raw_subset C mono labels u label
  rw [rawSupport_or 26 C gate op]
  exact Finset.mem_biUnion.mpr ⟨u,reads,fromChild⟩

theorem raw_support_of_selected_path (C : Circuit) (mono : Monotone2 C) (labels : Finset ℕ)
    {root w : ℕ} (reaches : (selectedDag 26 C mono labels).Reaches root w) :
    rawSupport 26 C w ⊆ rawSupport 26 C root := by
  induction reaches with
  | refl => exact Finset.Subset.rfl
  | tail _ step ih => exact (selected_compressed_raw_subset C mono labels step).trans ih

theorem selected_join_raw_subset (C : Circuit) (mono : Monotone2 C) (labels : Finset ℕ)
    {root w : ℕ} (join : w ∈ (selectedDag 26 C mono labels).joins root) :
    rawSupport 26 C w ⊆ rawSupport 26 C root :=
  raw_support_of_selected_path C mono labels (((selectedDag 26 C mono labels).joins_mem).mp join).2


end OneNestedAnd

/- Source work/quad1961/ChargeJoins.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

noncomputable def chargedJoins (C : Circuit) (mono : Monotone2 C) (S : Finset ℕ) (root : ℕ) : Finset ℕ :=
  ((selectedDag 26 C mono S).joins root).image (fun w => w - 26)

lemma charged_card (C : Circuit) (mono : Monotone2 C) (S : Finset ℕ) (root : ℕ)
    (contained : S ⊆ rawSupport 26 C root) : S.card ≤ (chargedJoins C mono S root).card + 1 := by
  let D := selectedDag 26 C mono S
  have raw {w : ℕ} (h : w ∈ D.joins root) : 26 ≤ w :=
    (selected_multi_is_or C S (D.joins_mem.mp h).1).1
  have exactCard : (chargedJoins C mono S root).card = (D.joins root).card := by
    apply Finset.card_image_of_injOn
    intro w hw v hv equal
    have wRaw := raw hw
    have vRaw := raw hv
    change w - 26 = v - 26 at equal
    omega
  have exactSupport : D.support root = S := Finset.inter_eq_right.mpr contained
  calc
    S.card = (D.support root).card := congrArg Finset.card exactSupport.symm
    _ ≤ (D.joins root).card + 1 := D.support_card_le root
    _ = (chargedJoins C mono S root).card + 1 := by rw [exactCard]

lemma charged_labels (C : Circuit) (mono : Monotone2 C) (S : Finset ℕ) {root j : ℕ}
    (charged : j ∈ chargedJoins C mono S root) :
    26 + j ≤ root ∧ (gateAt C j).op = .or ∧
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∈ rawSupport 26 C (26+j) ∧ b ∈ rawSupport 26 C (26+j) := by
  let D := selectedDag 26 C mono S
  obtain ⟨w, used, rfl⟩ := Finset.mem_image.mp charged
  have ⟨large, reaches⟩ := D.joins_mem.mp used
  have ⟨gateWire, op⟩ := selected_multi_is_or C S large
  rw [Nat.add_sub_of_le gateWire]
  refine ⟨D.reached_le reaches, op, ?_⟩
  obtain ⟨a, ha, b, hb, distinct⟩ := Finset.one_lt_card.mp (by omega : 1 < (D.support w).card)
  exact ⟨a, (Finset.mem_inter.mp ha).2, b, (Finset.mem_inter.mp hb).2, distinct,
    (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp hb).1⟩

lemma charged_raw_subset (C : Circuit) (mono : Monotone2 C) (S : Finset ℕ) {root j : ℕ}
    (charged : j ∈ chargedJoins C mono S root) :
    rawSupport 26 C (26+j) ⊆ rawSupport 26 C root := by
  let D := selectedDag 26 C mono S
  obtain ⟨w, used, rfl⟩ := Finset.mem_image.mp charged
  have ⟨large, reaches⟩ := D.joins_mem.mp used
  have ⟨gateWire, _⟩ := selected_multi_is_or C S large
  rw [Nat.add_sub_of_le gateWire]
  exact raw_support_of_selected_path C mono S reaches

lemma charged_fixed_before {C : Circuit} {h : ℕ} (P : ProjectionPlan C h)
    (mono : Monotone2 C) (S : Finset ℕ) {root j : ℕ} (before : root < 26+h)
    (charged : j ∈ chargedJoins C mono S root) : P.rep (26+j) = some (26+j) := by
  have order := (charged_labels C mono S charged).1
  have two := P.order
  exact ProjectAliases.mapTwo_other (by omega) (by omega)

lemma charged_fixed_of_two_ands {C : Circuit} {h : ℕ} (P : ProjectionPlan C h)
    (mono : Monotone2 C) (S : Finset ℕ) {root j : ℕ}
    (inner : (gateAt C h).op = .and) (outer : (gateAt C P.slot).op = .and)
    (charged : j ∈ chargedJoins C mono S root) : P.rep (26+j) = some (26+j) := by
  have op := (charged_labels C mono S charged).2.1
  have notH : j ≠ h := by intro equal; rw [equal, inner] at op; cases op
  have notK : j ≠ P.slot := by intro equal; rw [equal, outer] at op; cases op
  exact ProjectAliases.mapTwo_other (by omega) (by omega)

theorem charged_dead {C : Circuit} {h : ℕ} (P : ProjectionPlan C h)
    (ok : acceptable C) (low : (gateAt C h).op = .and) (S : Finset ℕ) {root center : ℕ}
    (rootValid : root < 26 + C.gates.length)
    (mono : Monotone2 P.projected) (back : ReadsBack 26 P.projected) (flat : AddStar.Flat 26 P.projected)
    (output : P.projected.output < 26 + P.projected.gates.length)
    (negativeSafe : ∀ L, negative L → P.projected.eval L = false) (mates : LiveAndRawMates P.projected)
    (fixed : ∀ j ∈ chargedJoins C ok.1 S root, P.rep (26+j) = some (26+j))
    (neighbor : ∀ p ∈ S, planeAdjacent p center)
    (hasLost : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      P.projected.eval (rawInput {p,center}) = false ∨ P.projected.eval (rawInput {q,center}) = false) :
    ∀ j ∈ chargedJoins C ok.1 S root, j ∉ Retain.liveSlots 26 P.projected := by
  intro j charged
  obtain ⟨before, _, p, pS, q, qS, different, inP, inQ⟩ := charged_labels C ok.1 S charged
  have eq := P.raw_maps ok.2.1 low (26+j) (by omega)
  simp only [fixed j charged, Option.map_some, Option.getD_some] at eq
  apply no_live_lost_join mono back flat output negativeSafe mates
    (by rwa [eq]) (by rwa [eq]) different (neighbor p pS) (neighbor q qS) (hasLost p pS q qS different)

end OneNestedAnd

/- Source work/quad1961/frontier-lean/LostStars.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds



noncomputable def lostLeaves (D : Circuit) (center : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range 26).filter (fun leaf =>
    planeAdjacent center leaf ∧ D.eval (rawInput {center,leaf}) = false)

theorem mem_lostLeaves {D : Circuit} {center leaf : ℕ} :
    leaf ∈ lostLeaves D center ↔
      planeAdjacent center leaf ∧ D.eval (rawInput {center,leaf}) = false := by
  classical
  unfold lostLeaves
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨And.right, fun h => ⟨?_,h⟩⟩
  rcases planeAdjacent_sides h.1 with a | a <;> omega

noncomputable def lostArms (D : Circuit) (center other : ℕ) : Finset ℕ :=
  (lostLeaves D center).erase other

theorem mem_lostArms {D : Circuit} {center other leaf : ℕ} :
    leaf ∈ lostArms D center other ↔ leaf ≠ other ∧ leaf ∈ lostLeaves D center :=
  Finset.mem_erase

noncomputable def lostStar (D : Circuit) (center : ℕ) : PlaneStar :=
  ⟨center,(lostLeaves D center).toList⟩

noncomputable def lostStarExcept (D : Circuit) (center skip : ℕ) : PlaneStar :=
  ⟨center,(lostArms D center skip).toList⟩

theorem mem_lostStar_leaves {D : Circuit} {center leaf : ℕ} :
    leaf ∈ (lostStar D center).leaves ↔ leaf ∈ lostLeaves D center := Finset.mem_toList

theorem mem_lostStarExcept_leaves {D : Circuit} {center skip leaf : ℕ} :
    leaf ∈ (lostStarExcept D center skip).leaves ↔ leaf ∈ lostArms D center skip := Finset.mem_toList

@[simp] theorem lostStar_length (D : Circuit) (center : ℕ) :
    (lostStar D center).leaves.length = (lostLeaves D center).card := Finset.length_toList _

@[simp] theorem lostStarExcept_length (D : Circuit) (center skip : ℕ) :
    (lostStarExcept D center skip).leaves.length = (lostArms D center skip).card := Finset.length_toList _

theorem lostStar_legal {D : Circuit} {center : ℕ} (bound : center < 26) :
    (lostStar D center).Legal :=
  ⟨bound,fun _ mem => (mem_lostLeaves.mp (mem_lostStar_leaves.mp mem)).1⟩

theorem lostStarExcept_legal {D : Circuit} {center skip : ℕ} (bound : center < 26) :
    (lostStarExcept D center skip).Legal :=
  ⟨bound,fun _ mem => (mem_lostLeaves.mp ((mem_lostArms.mp (mem_lostStarExcept_leaves.mp mem)).2)).1⟩

theorem lostStar_cost (D : Circuit) (center : ℕ) :
    (lostStar D center).cost = (lostLeaves D center).card +
      if lostLeaves D center = ∅ then 0 else 1 := by
  simp only [PlaneStar.cost, lostStar, Finset.length_toList, Finset.toList_eq_nil]

theorem lostStarExcept_cost (D : Circuit) (center skip : ℕ) :
    (lostStarExcept D center skip).cost = (lostArms D center skip).card +
      if lostArms D center skip = ∅ then 0 else 1 := by
  simp only [PlaneStar.cost, lostStarExcept, Finset.length_toList, Finset.toList_eq_nil]

theorem lostStar_cost_le (D : Circuit) (center : ℕ) :
    (lostStar D center).cost ≤ (lostLeaves D center).card + 1 := by
  rw [lostStar_cost]
  split <;> omega

theorem lostStarExcept_cost_le (D : Circuit) (center skip : ℕ) :
    (lostStarExcept D center skip).cost ≤ (lostArms D center skip).card + 1 := by
  rw [lostStarExcept_cost]
  split <;> omega

theorem lostStars_cost_le (D : Circuit) (first second : ℕ) :
    (lostStar D first).cost + (lostStarExcept D second first).cost ≤
      (lostArms D first second).card + (lostArms D second first).card + 3 := by
  have a := lostStar_cost_le D first
  have b := lostStarExcept_cost_le D second first
  by_cases shared : second ∈ lostLeaves D first
  · have h : (lostArms D first second).card = (lostLeaves D first).card - 1 :=
      Finset.card_erase_of_mem shared
    omega
  · have h : lostArms D first second = lostLeaves D first := Finset.erase_eq_of_notMem shared
    rw [h]
    omega

private lemma swap_raw_row (a b : ℕ) : rawInput {a,b} = rawInput {b,a} := by
  rw [Finset.pair_comm]

private lemma incidence_hits_of_either {p l : Fin 13} {s : PlaneStar}
    (shape : (s.center = p.val ∧ 13+l.val ∈ s.leaves) ∨
      (s.center = 13+l.val ∧ p.val ∈ s.leaves)) : s.Hits (incidenceRow p l) := by
  rcases shape with ⟨pt,hasLine⟩ | ⟨ln,hasPoint⟩
  · exact ⟨by rw [pt]; exact incidence_point_true p l, _, hasLine, incidence_line_true p l⟩
  · exact ⟨by rw [ln]; exact incidence_line_true p l, _, hasPoint, incidence_point_true p l⟩

theorem lostStar_hits {D : Circuit} {center : ℕ} {p l : Fin 13}
    (incident : p-l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) (lost : D.eval (incidenceRow p l) = false)
    (covers : center = p.val ∨ center = 13+l.val) :
    (lostStar D center).Hits (incidenceRow p l) := by
  have row := rawInput_incidence p l
  apply incidence_hits_of_either
  rcases covers with rfl | rfl
  · refine Or.inl ⟨rfl,mem_lostStar_leaves.mpr (mem_lostLeaves.mpr ⟨planeAdjacent_point_line incident,?_⟩)⟩
    rwa [row]
  · refine Or.inr ⟨rfl,mem_lostStar_leaves.mpr (mem_lostLeaves.mpr ⟨planeAdjacent_line_point incident,?_⟩)⟩
    rwa [swap_raw_row, row]

theorem lostStarExcept_hits {D : Circuit} {center skip : ℕ} {p l : Fin 13}
    (incident : p-l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) (lost : D.eval (incidenceRow p l) = false)
    (covers : (center = p.val ∧ skip ≠ 13+l.val) ∨ (center = 13+l.val ∧ skip ≠ p.val)) :
    (lostStarExcept D center skip).Hits (incidenceRow p l) := by
  have row := rawInput_incidence p l
  apply incidence_hits_of_either
  rcases covers with ⟨rfl,keep⟩ | ⟨rfl,keep⟩
  · refine Or.inl ⟨rfl,mem_lostStarExcept_leaves.mpr (mem_lostArms.mpr ⟨Ne.symm keep,
      mem_lostLeaves.mpr ⟨planeAdjacent_point_line incident,?_⟩⟩)⟩
    rwa [row]
  · refine Or.inr ⟨rfl,mem_lostStarExcept_leaves.mpr (mem_lostArms.mpr ⟨Ne.symm keep,
      mem_lostLeaves.mpr ⟨planeAdjacent_line_point incident,?_⟩⟩)⟩
    rwa [swap_raw_row, row]

theorem lostStar_covers {D : Circuit} {center : ℕ}
    (shape : ∀ p l : Fin 13, p-l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → D.eval (incidenceRow p l) = false →
      center = p.val ∨ center = 13+l.val) :
    ∀ L, positive L → D.eval L = false →
      (lostStar D center).Hits L ∨ PlaneStar.empty.Hits L := by
  rintro L ⟨p,l,incident,rfl⟩ lost
  exact Or.inl (lostStar_hits incident lost (shape p l incident lost))

theorem lostStars_cover {D : Circuit} {first second : ℕ}
    (shape : ∀ p l : Fin 13, p-l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → D.eval (incidenceRow p l) = false →
      (first = p.val ∨ first = 13+l.val) ∨ (second = p.val ∨ second = 13+l.val)) :
    ∀ L, positive L → D.eval L = false →
      (lostStar D first).Hits L ∨ (lostStarExcept D second first).Hits L := by
  rintro L ⟨p,l,incident,rfl⟩ lost
  by_cases belongsFirst : first = p.val ∨ first = 13+l.val
  · exact Or.inl (lostStar_hits incident lost belongsFirst)
  · have belongsSecond := (shape p l incident lost).resolve_left belongsFirst
    apply Or.inr (lostStarExcept_hits incident lost ?_)
    rcases belongsSecond with eq | eq
    · exact Or.inl ⟨eq,fun h => belongsFirst (Or.inr h)⟩
    · exact Or.inr ⟨eq,fun h => belongsFirst (Or.inl h)⟩

theorem lostPointLineStars_cover {D : Circuit} {point line : Fin 13}
    (shape : ∀ p l : Fin 13, p-l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → D.eval (incidenceRow p l) = false →
      p = point ∨ l = line) :
    ∀ L, positive L → D.eval L = false →
      (lostStar D (13+line.val)).Hits L ∨ (lostStarExcept D point.val (13+line.val)).Hits L := by
  apply lostStars_cover
  intro p l inc bad
  rcases shape p l inc bad with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (Or.inr rfl)


end OneNestedAnd

/- Source work/quad1961/frontier-lean/RepairDead.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

 
theorem plane_star_budget_from_dead (D : Circuit) (first second : PlaneStar) (cap : ℕ)
    (mono : Monotone2 D) (back : ReadsBack 26 D) (flat : AddStar.Flat 26 D)
    (output : D.output < 26+D.gates.length)
    (accept : ∃ L : List Bool, L.length = 26 ∧ D.eval L = true)
    (neg : ∀ L, negative L → D.eval L = false)
    (firstLegal : first.Legal) (secondLegal : second.Legal)
    (covers : ∀ L, positive L → D.eval L = false → first.Hits L ∨ second.Hits L)
    (dead : Finset ℕ) (valid : ∀ j ∈ dead, j < D.gates.length)
    (outside : ∀ j ∈ dead, j ∉ Retain.liveSlots 26 D)
    (pays : first.cost + second.cost ≤ dead.card) (budget : D.size ≤ cap) : 64 ≤ cap := by
  obtain ⟨E, em, eb, ef, savings, same⟩ := Retain.strip_dead mono back output flat dead valid outside
  obtain ⟨L,len,yes⟩ := accept
  have eo : E.output < 26+E.gates.length :=
    AddStar.output_bound_of_acceptance len ((same L len).trans yes)
  refine plane_star_budget E first second cap em eb ef eo ?_ firstLegal secondLegal ?_ ?_
  · intro x no
    have len : x.length = 26 := by
      obtain ⟨Q,_,rfl⟩ := no
      simp [quadRow]
    exact (same x len).trans (neg x no)
  · intro x pos no
    apply covers x pos
    have len : x.length = 26 := by
      obtain ⟨p,l,_,rfl⟩ := pos
      exact row_length p l
    exact (same x len).symm.trans no
  · omega


end OneNestedAnd

/- Source work/quad1961/frontier-lean/RetainedRay.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem choose_diagonal (a b : ℕ) :
    ∃ p : Fin 13, p.val ≠ a ∧ p.val ≠ b := by
  by_cases zero : 0 ≠ a ∧ 0 ≠ b
  · exact ⟨0,zero⟩
  by_cases one : 1 ≠ a ∧ 1 ≠ b
  · exact ⟨1,one⟩
  have hitZero : a = 0 ∨ b = 0 := by
    by_contra neither
    exact zero ⟨fun eq => neither (Or.inl eq.symm), fun eq => neither (Or.inr eq.symm)⟩
  have hitOne : a = 1 ∨ b = 1 := by
    by_contra neither
    exact one ⟨fun eq => neither (Or.inl eq.symm), fun eq => neither (Or.inr eq.symm)⟩
  refine ⟨2,?_⟩
  change 2 ≠ a ∧ 2 ≠ b
  rcases hitZero with h | h <;> rcases hitOne with g | g <;> omega

theorem exists_uncovered_diagonal {first second : PlaneStar}
    (firstLegal : first.Legal) (secondLegal : second.Legal) :
    ∃ p : Fin 13, ¬ first.Hits (incidenceRow p p) ∧ ¬ second.Hits (incidenceRow p p) := by
  obtain ⟨p,hf,hs⟩ := choose_diagonal (first.center % 13) (second.center % 13)
  have rejected (s : PlaneStar) (legal : s.Legal) (avoid : p.val ≠ s.center % 13) :
      ¬ s.Hits (incidenceRow p p) := by
    rintro ⟨center,_⟩
    rw [← rawInput_incidence p p, rawInput_bit _ legal.1, decide_eq_true_eq,
      Finset.mem_insert, Finset.mem_singleton] at center
    apply avoid
    rcases center with e | e
    · rw [e, Nat.mod_eq_of_lt p.isLt]
    · rw [e]
      have value : (13+p.val) % 13 = p.val := by omega
      exact value.symm
  exact ⟨p,rejected first firstLegal hf,rejected second secondLegal hs⟩

theorem projected_accepts_diagonal {D : Circuit} {first second : PlaneStar}
    (firstLegal : first.Legal) (secondLegal : second.Legal)
    (covers : ∀ L, positive L → D.eval L = false → first.Hits L ∨ second.Hits L) :
    ∃ p : Fin 13, D.eval (incidenceRow p p) = true := by
  obtain ⟨p,neFirst,neSecond⟩ := exists_uncovered_diagonal firstLegal secondLegal
  have pos : positive (incidenceRow p p) := ⟨p,p,by simp,rfl⟩
  refine ⟨p,?_⟩
  by_contra no
  exact (covers _ pos (Bool.eq_false_iff.mpr no)).elim neFirst neSecond

theorem projected_valid_from_stars {D : Circuit} {first second : PlaneStar}
    (firstLegal : first.Legal) (secondLegal : second.Legal)
    (covers : ∀ L, positive L → D.eval L = false → first.Hits L ∨ second.Hits L) :
    D.output < 26+D.gates.length := by
  obtain ⟨p,accepted⟩ := projected_accepts_diagonal firstLegal secondLegal covers
  exact AddStar.output_bound_of_acceptance (row_length p p) accepted

theorem plane_star_budget_from_cover (D : Circuit) (first second : PlaneStar) (cap : ℕ)
    (mono : Monotone2 D) (back : ReadsBack 26 D) (flat : AddStar.Flat 26 D)
    (neg : ∀ L, negative L → D.eval L = false)
    (firstLegal : first.Legal) (secondLegal : second.Legal)
    (covers : ∀ L, positive L → D.eval L = false → first.Hits L ∨ second.Hits L)
    (dead : Finset ℕ) (valid : ∀ j ∈ dead, j < D.gates.length)
    (outside : ∀ j ∈ dead, j ∉ Retain.liveSlots 26 D)
    (pays : first.cost + second.cost ≤ dead.card) (budget : D.size ≤ cap) : 64 ≤ cap := by
  have output := projected_valid_from_stars firstLegal secondLegal covers
  obtain ⟨p,accepted⟩ := projected_accepts_diagonal firstLegal secondLegal covers
  exact plane_star_budget_from_dead D first second cap mono back flat output
    ⟨incidenceRow p p,row_length p p,accepted⟩ neg firstLegal secondLegal covers dead valid outside pays budget


end OneNestedAnd

/- Source work/quad1961/JoinRepair.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

namespace ProjectionPlan
variable {C : Circuit} {h H : ℕ} (P : ProjectionPlan C h)

lemma mono (ok : acceptable C) : Monotone2 P.projected :=
  ProjectAliases.circuit_mono (clearLower_mono ok.1 h)

lemma back (ok : acceptable C) (low : (gateAt C h).op = .and) : ReadsBack 26 P.projected :=
  ProjectAliases.circuit_back (P.rules ok.2.1 low) (clearLower_back ok.2.1 h)

lemma flat (ok : acceptable C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and)
    (nest : InCone 26 C h H) : AddStar.Flat 26 P.projected :=
  ProjectAliases.circuit_flat (P.rules ok.2.1 low) (clearLower_back ok.2.1 h)
    (clearLower_flat one low high nest)

lemma negative_safe (ok : acceptable C) (low : (gateAt C h).op = .and) :
    ∀ L, negative L → P.projected.eval L = false := by
  intro L bad
  have rows := (separates_iff_rows C).mp ok.2.2
  have valid : C.output < 26 + C.gates.length :=
    AddStar.output_bound_of_acceptance (row_length 0 0) (rows.1 _ ⟨0, 0, by decide, rfl⟩)
  have len : L.length = 26 := by obtain ⟨Q, _, rfl⟩ := bad; simp [quadRow]
  rw [P.projected_eval ok low valid len]
  have linked := clearLower_eval_le ok.1 ok.2.1 len h
  rw [rows.2 _ bad] at linked
  exact Bool.eq_false_iff.mpr (fun fired => by simpa using linked fired)

lemma second_changed (back : ReadsBack 26 C) : P.rep (26+P.slot) ≠ some (26+P.slot) := by
  rw [rep, ProjectAliases.mapTwo_second 26 P.order]
  rcases P.replacement with ⟨empty, _, _⟩ | ⟨r, same, _, reads, _⟩
  · simp [empty]
  · have mem : r ∈ (gateAt C P.slot).inputs := by rcases reads with both | both <;> simp [both]
    have earlier := back P.slot P.slot_bound r mem
    simp [same, earlier.ne]

end ProjectionPlan

theorem one_star_from_support {C : Circuit} {h H : ℕ} (P : ProjectionPlan C h) (ok : acceptable C)
    (strict : StrictBinary C) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    {center root : ℕ} (centerBound : center < 26)
    (cover : ∀ p l : Fin 13, Quadrangle1692.incident p l → P.projected.eval (incidenceRow p l) = false →
      center = p.val ∨ center = 13+l.val)
    (rootBound : root < 26 + C.gates.length)
    (cont : lostLeaves P.projected center ⊆ rawSupport 26 C root)
    (fixed : ∀ j ∈ chargedJoins C ok.1 (lostLeaves P.projected center) root,
      P.rep (26+j) = some (26+j)) : 64 ≤ C.size := by
  let D := P.projected
  let S := lostLeaves D center
  let J := chargedJoins C ok.1 S root
  let K : Finset ℕ := {h, P.slot}
  let dead := J ∪ K
  have coverAll := lostStar_covers cover
  have firstLegal := lostStar_legal (D := D) centerBound
  have valid := projected_valid_from_stars firstLegal PlaneStar.empty_legal coverAll
  have mono := P.mono ok
  have back := P.back ok low
  have flat := P.flat ok one low high nest
  have neg := P.negative_safe ok low
  have mates := P.live_mates ok strict one low high nest
  have recovered : ∀ j ∈ J, j ∉ Retain.liveSlots 26 D := by
    apply charged_dead P ok low S rootBound mono back flat valid neg mates fixed
    · exact fun leaf mem => planeAdjacent_reverse (mem_lostLeaves.mp mem).1
    · intro p hp q _ _
      exact Or.inl (by rw [Finset.pair_comm]; exact (mem_lostLeaves.mp hp).2)
  obtain ⟨lowerDead, slotDead⟩ := P.no_live_lower_slot ok.2.1 low valid
  have disjoint : Disjoint J K := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have written := fixed j hj
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simp [ProjectionPlan.rep] at written
    · exact P.second_changed ok.2.1 written
  have kc : K.card = 2 := by simp [K, P.order.ne]
  have dc : dead.card = J.card + 2 := by rw [show dead = J ∪ K from rfl, Finset.card_union_of_disjoint disjoint, kc]
  have counted := charged_card C ok.1 S root cont
  have cost := lostStar_cost_le D center
  have cb := gateAt_and_bound C h low
  refine plane_star_budget_from_cover D (lostStar D center) PlaneStar.empty C.size
    mono back flat neg firstLegal PlaneStar.empty_legal coverAll dead ?_ ?_ ?_ (le_of_eq P.projected_size)
  · intro j hj
    rw [P.projected_gate_count]
    rcases Finset.mem_union.mp hj with jJ | jK
    · have e := (charged_labels C ok.1 S jJ).1
      omega
    · simp only [K, Finset.mem_insert, Finset.mem_singleton] at jK
      rcases jK with rfl | rfl
      · exact cb
      · exact P.slot_bound
  · intro j hj
    rcases Finset.mem_union.mp hj with jJ | jK
    · exact recovered j jJ
    · simp only [K, Finset.mem_insert, Finset.mem_singleton] at jK
      rcases jK with rfl | rfl
      · exact lowerDead
      · exact slotDead
  · rw [PlaneStar.empty_cost, Nat.add_zero, dc]
    change (lostStar D center).cost ≤ J.card + 2
    change S.card ≤ J.card + 1 at counted
    change (lostStar D center).cost ≤ S.card + 1 at cost
    omega

end OneNestedAnd

/- Source work/quad1961/GuardedRepair.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PairTerms

lemma adjacent_not_same_side {u v : ℕ} (s : Bool) (edge : planeAdjacent u v)
    (hu : sideCondition s u) : ¬ sideCondition s v := by
  intro hv
  rcases planeAdjacent_sides edge with e | e <;> cases s <;> simp [sideCondition] at * <;> omega

theorem guarded_repair {C : Circuit} {h H : ℕ} (ports : NestInputs C h H) (P : ProjectionPlan C h)
    (ok : acceptable C) (strict : StrictBinary C) (minimal : ∀ D : Circuit, acceptable D → C.size ≤ D.size)
    (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (low : (gateAt C h).op = .and) (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (bad : ∃ L, negative L ∧ wireOn C L (26+h))
    (nonempty : (rawSupport 26 C ports.upperFeed).Nonempty) : 64 ≤ C.size := by
  classical
  let T := ports.terms
  have safe := ports.pair_sound ok minimal one low high nest
  have hasOther := ports.other_nonempty ok strict one low high nest
  obtain ⟨s, feedSide, guardSide⟩ := T.pure_base nonempty hasOther safe
  have feedBound : ∀ w ∈ T.upperFeed, w < 26 := fun w hw => (rawSupport_bounds 26 C _ w hw).1
  have selected := sideSet_nonempty s T.upperFeed nonempty feedBound feedSide
  obtain ⟨b, shape⟩ := T.guarded_on_shores s selected feedSide guardSide safe
  let center := indexOn (!s) b
  have cover (p l : Fin 13) (incident : Quadrangle1692.incident p l)
      (lost : P.projected.eval (incidenceRow p l) = false) : center = p.val ∨ center = 13+l.val := by
    have raw := ports.lost_pair ok one low high nest bad P p l incident lost
    change T.lower p.val (13+l.val) ∧ supportHits T.upperOther p.val (13+l.val) ∧
      ¬ supportHits T.upperFeed p.val (13+l.val) at raw
    cases s
    · have eq := shape p l raw.1 raw.2.1 raw.2.2
      exact Or.inr (by simp [center, indexOn, eq])
    · have rearranged : T.lower (13+l.val) p.val ∧ supportHits T.upperOther (13+l.val) p.val ∧
        ¬ supportHits T.upperFeed (13+l.val) p.val := by
        simpa only [PairTerms.lower, supportHits, or_comm] using raw
      have eq := shape l p rearranged.1 rearranged.2.1 rearranged.2.2
      exact Or.inl (by simp [center, indexOn, eq])
  let S := lostLeaves P.projected center
  have repair (root : ℕ) (read : root ∈ (gateAt C h).inputs) (cont : S ⊆ rawSupport 26 C root) :
      64 ≤ C.size := by
    have hC := gateAt_and_bound C h low
    have earlier := ok.2.1 h hC root read
    exact one_star_from_support P ok strict one low high nest (indexOn_bound (!s) b) cover
      (by omega) cont (fun _ hj => charged_fixed_before P ok.1 S earlier hj)
  by_cases hasLeaves : S.Nonempty
  · obtain ⟨leaf, hleaf⟩ := hasLeaves
    have adj := (mem_lostLeaves.mp hleaf).1
    have initial := ports.lost_raw_pair ok one low high nest bad P adj (mem_lostLeaves.mp hleaf).2
    have guard : center ∈ T.upperOther := initial.2.1.resolve_right
      (fun other => adjacent_not_same_side (!s) adj (indexOn_side (!s) b) (guardSide _ other))
    have notBoth : ¬ (center ∈ T.lowLeft ∧ center ∈ T.lowRight) := by
      rintro ⟨hl, hr⟩
      exact planeAdjacent_ne (safe center center ⟨Or.inr ⟨Or.inl hl, Or.inl hr⟩, Or.inl guard⟩) rfl
    have fromLoss (u : ℕ) (hu : u ∈ S) : T.lower center u :=
      (ports.lost_raw_pair ok one low high nest bad P (mem_lostLeaves.mp hu).1 (mem_lostLeaves.mp hu).2).1
    by_cases inLeft : center ∈ T.lowLeft
    · apply repair ports.lowRight ports.reads_lowerRight
      intro u hu
      exact (fromLoss u hu).2.resolve_left (fun c => notBoth ⟨inLeft, c⟩)
    · apply repair ports.lowLeft ports.reads_lowerLeft
      intro u hu
      exact (fromLoss u hu).1.resolve_left inLeft
  · apply repair ports.lowLeft ports.reads_lowerLeft
    exact fun u hu => False.elim (hasLeaves ⟨u, hu⟩)

end OneNestedAnd

/- Source work/quad1961/frontier-lean/EmptyShape.lean -/
namespace OneNestedAnd.PairTerms

open PEqualNP.CircuitLowerBounds

def rawClause (T : PairTerms) (i : Fin 3) : Finset ℕ :=
  if i = 0 then T.lowLeft else if i = 1 then T.lowRight else T.upperOther

@[simp] theorem rawClause_zero (T : PairTerms) : T.rawClause 0 = T.lowLeft := by simp [rawClause]
@[simp] theorem rawClause_one (T : PairTerms) : T.rawClause 1 = T.lowRight := by simp [rawClause]
@[simp] theorem rawClause_two (T : PairTerms) : T.rawClause 2 = T.upperOther := by simp [rawClause]

def clauses (T : PairTerms) : ClauseShape.Clauses :=
  ⟨fun i => pointIndices (T.rawClause i), fun i => lineIndices (T.rawClause i)⟩

@[simp] theorem clauses_point {T : PairTerms} {p : Fin 13} {i : Fin 3} :
    p ∈ T.clauses.points i ↔ p.val ∈ T.rawClause i := mem_pointIndices

@[simp] theorem clauses_line {T : PairTerms} {l : Fin 13} {i : Fin 3} :
    l ∈ T.clauses.lines i ↔ 13+l.val ∈ T.rawClause i := mem_lineIndices

theorem upper_iff_clauses (T : PairTerms) (empty : T.upperFeed = ∅) (a b : ℕ) :
    T.upper a b ↔ ∀ i, supportHits (T.rawClause i) a b := by
  have noFeed : ¬ supportHits T.upperFeed a b := by simp [supportHits, empty]
  unfold upper lower
  simp only [noFeed, false_or]
  constructor
  · intro both i
    fin_cases i
    · exact both.1.1
    · exact both.1.2
    · exact both.2
  · intro each
    exact ⟨⟨by simpa using each 0,by simpa using each 1⟩,by simpa using each 2⟩

theorem upper_iff_hit (T : PairTerms) (empty : T.upperFeed = ∅) (p l : Fin 13) :
    T.upper p.val (13+l.val) ↔ T.clauses.Hit p l := by
  rw [upper_iff_clauses T empty]
  simp only [supportHits, ClauseShape.Clauses.Hit, clauses_point, clauses_line]

theorem empty_clauses_shape (T : PairTerms) (empty : T.upperFeed = ∅)
    (sound : ∀ a b, T.upper a b → planeAdjacent a b) :
    T.clauses.Star ∨ T.clauses.DoubleStar := by
  apply T.clauses.star_or_double
  · intro p q l k pl pk ql qk
    by_cases same : p = q
    · exact Or.inl same
    · have edge (u v : Fin 13) (h : T.clauses.Hit u v) : Quadrangle1692.incident u v :=
        planeAdjacent_point_line_iff.mp (sound _ _ ((T.upper_iff_hit empty u v).mpr h))
      exact Or.inr (incident_common_line same (edge p l pl) (edge q l ql) (edge p k pk) (edge q k qk))
  · intro p q all
    have hit : T.upper p.val q.val := (T.upper_iff_clauses empty _ _).mpr (by
      intro i
      simpa only [supportHits, clauses_point] using all i)
    have hp := p.isLt
    have hq := q.isLt
    rcases planeAdjacent_sides (sound _ _ hit) with h | h <;> omega
  · intro l k all
    have hit : T.upper (13+l.val) (13+k.val) := (T.upper_iff_clauses empty _ _).mpr (by
      intro i
      simpa only [supportHits, clauses_line] using all i)
    rcases planeAdjacent_sides (sound _ _ hit) with h | h <;> omega

theorem upper_symmetric (T : PairTerms) (a b : ℕ) : T.upper a b ↔ T.upper b a := by
  simp only [upper, lower, supportHits, or_comm]

theorem empty_star_clause (T : PairTerms) (empty : T.upperFeed = ∅)
    (sound : ∀ a b, T.upper a b → planeAdjacent a b) (center : ℕ) :
    ∃ i, center ∉ T.rawClause i ∧
      ∀ leaf, (T.upper center leaf ∨ T.upper leaf center) → leaf ∈ T.rawClause i := by
  have apart : ∃ i, center ∉ T.rawClause i := by
    by_contra none
    have all : ∀ i, center ∈ T.rawClause i := by
      intro i
      by_contra missing
      exact none ⟨i,missing⟩
    have yes := (T.upper_iff_clauses empty center center).mpr (fun i => Or.inl (all i))
    exact planeAdjacent_ne (sound _ _ yes) rfl
  obtain ⟨i,missing⟩ := apart
  refine ⟨i,missing,?_⟩
  intro leaf hit
  have chosen : T.upper center leaf := hit.elim id (T.upper_symmetric leaf center).mp
  exact ((T.upper_iff_clauses empty _ _).mp chosen i).resolve_left missing

theorem lines_empty_raw_points {T : PairTerms} {i : Fin 3}
    (bound : ∀ w ∈ T.rawClause i, w < 26) (pure : T.clauses.lines i = ∅) :
    ∀ w ∈ T.rawClause i, w < 13 := by
  intro w mw
  by_contra! high
  have hw := bound w mw
  let l : Fin 13 := ⟨w-13,by omega⟩
  have e : 13+l.val = w := by dsimp [l]; omega
  have hit : l ∈ T.clauses.lines i := clauses_line.mpr (e.symm ▸ mw)
  rw [pure] at hit
  exact Finset.notMem_empty _ hit

theorem points_empty_raw_lines {T : PairTerms} {i : Fin 3}
    (pure : T.clauses.points i = ∅) : ∀ w ∈ T.rawClause i, 13 ≤ w := by
  intro w mw
  by_contra! small
  let p : Fin 13 := ⟨w,small⟩
  have hit : p ∈ T.clauses.points i := clauses_point.mpr mw
  rw [pure] at hit
  exact Finset.notMem_empty _ hit

theorem empty_double_data (T : PairTerms) (empty : T.upperFeed = ∅)
    (bound : ∀ i w, w ∈ T.rawClause i → w < 26) (double : T.clauses.DoubleStar) :
    ∃ (p l : Fin 13) (i j k : Fin 3), i ≠ j ∧ k ≠ i ∧ k ≠ j ∧
      (∀ w ∈ T.rawClause i, w < 13) ∧ (∀ w ∈ T.rawClause j, 13 ≤ w) ∧
      p.val ∈ T.rawClause k ∧ 13+l.val ∈ T.rawClause k ∧ T.upper p.val (13+l.val) ∧
      ∀ q r : Fin 13, T.upper q.val (13+r.val) →
        q.val ∈ T.rawClause i ∧ 13+r.val ∈ T.rawClause j ∧ (q = p ∨ r = l) := by
  obtain ⟨p,l,i,j,k,ij,ki,kj,pt,ln,mP,mL,center,covers⟩ := double
  refine ⟨p,l,i,j,k,ij,ki,kj,lines_empty_raw_points (bound i) pt,points_empty_raw_lines ln,
    clauses_point.mp mP,clauses_line.mp mL,(T.upper_iff_hit empty p l).mpr center,?_⟩
  intro q r got
  obtain ⟨mQ,mR,star⟩ := covers q r ((T.upper_iff_hit empty q r).mp got)
  exact ⟨clauses_point.mp mQ,clauses_line.mp mR,star⟩

end OneNestedAnd.PairTerms

namespace OneNestedAnd.NestInputs

def clauseWire {C : PEqualNP.CircuitLowerBounds.Circuit} {h H : ℕ}
    (ports : NestInputs C h H) (i : Fin 3) : ℕ :=
  if i = 0 then ports.lowLeft else if i = 1 then ports.lowRight else ports.upperOther

theorem rawClause_eq {C : PEqualNP.CircuitLowerBounds.Circuit} {h H : ℕ}
    (ports : NestInputs C h H) (i : Fin 3) :
    ports.terms.rawClause i = rawSupport 26 C (ports.clauseWire i) := by
  fin_cases i <;> simp [clauseWire, terms]

theorem rawClause_bounds {C : PEqualNP.CircuitLowerBounds.Circuit} {h H : ℕ}
    (ports : NestInputs C h H) : ∀ i w, w ∈ ports.terms.rawClause i → w < 26 := by
  intro i w mem
  rw [ports.rawClause_eq] at mem
  exact (rawSupport_bounds 26 C _ _ mem).1

end OneNestedAnd.NestInputs

/- Source work/quad1961/frontier-lean/EmptyRepair.lean -/
namespace OneNestedAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

theorem NestInputs.clauseWire_valid {C : Circuit} {h H : ℕ} (ports : NestInputs C h H)
    (back : ReadsBack 26 C) (lo : (gateAt C h).op = .and)
    (hi : (gateAt C H).op = .and) (i : Fin 3) : ports.clauseWire i < 26+C.gates.length := by
  have hC := gateAt_and_bound C h lo
  have HC := gateAt_and_bound C H hi
  have l := back h hC ports.lowLeft ports.reads_lowerLeft
  have r := back h hC ports.lowRight ports.reads_lowerRight
  have o := back H HC ports.upperOther ports.reads_upperOther
  fin_cases i <;> simp [NestInputs.clauseWire] <;> omega

theorem empty_double_repair {C : Circuit} {h H : ℕ} (P : ProjectionPlan C h)
    (ports : NestInputs C h H) (ok : acceptable C) (strict : StrictBinary C)
    (minimal : ∀ D : Circuit, acceptable D → C.size ≤ D.size)
    (one : PEqualNP.TopForm.andPairs 26 C ≤ 1) (low : (gateAt C h).op = .and)
    (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (bad : ∃ L, negative L ∧ wireOn C L (26+h))
    (empty : ports.terms.upperFeed = ∅) (slotEq : P.slot = H)
    (double : ports.terms.clauses.DoubleStar) : 64 ≤ C.size := by
  obtain ⟨p,l,i,j,k,_,_,_,pureP,pureL,mixedP,mixedL,center,shape⟩ :=
    ports.terms.empty_double_data empty ports.rawClause_bounds double
  let D := P.projected
  let a := p.val
  let b := 13+l.val
  have aP : a < 13 := p.isLt
  have bL : 13 ≤ b := by dsimp [b]; omega
  have bU : b < 26 := by have := l.isLt; dsimp [b]; omega
  have central : planeAdjacent a b := ports.pair_sound ok minimal one low high nest a b center
  have rowShape : ∀ q r : Fin 13, Quadrangle1692.incident q r →
      D.eval (incidenceRow q r) = false → q = p ∨ r = l := by
    intro q r edge lost
    have data := ports.lost_pair ok one low high nest bad P q r edge lost
    exact (shape q r ⟨Or.inr data.1,data.2.1⟩).2.2
  have cover := lostPointLineStars_cover rowShape
  have bl := lostStar_legal (D := D) bU
  have al := lostStarExcept_legal (D := D) (skip := b) (by omega : a < 26)
  have valid := projected_valid_from_stars bl al cover
  have rules := P.rules ok.2.1 low
  have oldBack := clearLower_back ok.2.1 h
  have dm : Monotone2 D := ProjectAliases.circuit_mono (clearLower_mono ok.1 h)
  have db : ReadsBack 26 D := ProjectAliases.circuit_back rules oldBack
  have df : AddStar.Flat 26 D := ProjectAliases.circuit_flat rules oldBack (clearLower_flat one low high nest)
  have rows := (separates_iff_rows C).mp ok.2.2
  have oc := AddStar.output_bound_of_acceptance (row_length 0 0) (rows.1 _ ⟨0,0,by decide,rfl⟩)
  have negativeSafe : ∀ L, negative L → D.eval L = false := by
    intro L no
    have len : L.length = 26 := by obtain ⟨Q,_,rfl⟩ := no; simp [quadRow]
    rw [show D = P.projected from rfl, P.projected_eval ok low oc len]
    apply Bool.eq_false_iff.mpr
    intro fired
    have original := clearLower_eval_le ok.1 ok.2.1 len h fired
    rw [rows.2 L no] at original
    contradiction
  have mates := P.live_mates ok strict one low high nest
  have twoDead : h ∉ Retain.liveSlots 26 D ∧ H ∉ Retain.liveSlots 26 D := by
    simpa only [slotEq] using P.no_live_lower_slot ok.2.1 low valid
  let S := insert a (lostArms D b a)
  let T := insert b (lostArms D a b)
  let ip := ports.clauseWire i
  let jl := ports.clauseWire j
  let mk := ports.clauseWire k
  have ipB : ip < 26+C.gates.length := ports.clauseWire_valid ok.2.1 low high i
  have jlB : jl < 26+C.gates.length := ports.clauseWire_valid ok.2.1 low high j
  have mkB : mk < 26+C.gates.length := ports.clauseWire_valid ok.2.1 low high k
  have supportP : S ⊆ rawSupport 26 C ip := by
    intro w mem
    change w ∈ rawSupport 26 C (ports.clauseWire i)
    rw [← ports.rawClause_eq]
    rcases Finset.mem_insert.mp mem with rfl | arm
    · exact (shape p l center).1
    · obtain ⟨adj,lost⟩ := mem_lostLeaves.mp (mem_lostArms.mp arm).2
      have wP : w < 13 := by rcases planeAdjacent_sides adj with g | g <;> omega
      let q : Fin 13 := ⟨w,wP⟩
      have info := ports.lost_raw_pair ok one low high nest bad P adj lost
      have top : ports.terms.upper b w := ⟨Or.inr info.1,info.2.1⟩
      exact (shape q l ((ports.terms.upper_symmetric b w).mp top)).1
  have supportL : T ⊆ rawSupport 26 C jl := by
    intro w mem
    change w ∈ rawSupport 26 C (ports.clauseWire j)
    rw [← ports.rawClause_eq]
    rcases Finset.mem_insert.mp mem with rfl | arm
    · exact (shape p l center).2.1
    · obtain ⟨adj,lost⟩ := mem_lostLeaves.mp (mem_lostArms.mp arm).2
      have side : 13 ≤ w ∧ w < 26 := by rcases planeAdjacent_sides adj with g | g <;> omega
      let r : Fin 13 := ⟨w-13,by omega⟩
      have eq : 13+r.val = w := by dsimp [r]; omega
      have info := ports.lost_raw_pair ok one low high nest bad P adj lost
      have top : ports.terms.upper a w := ⟨Or.inr info.1,info.2.1⟩
      have top' : ports.terms.upper p.val (13+r.val) := by rwa [eq]
      simpa only [eq] using (shape p r top').2.1
  let J₁ := chargedJoins C ok.1 S ip
  let J₂ := chargedJoins C ok.1 T jl
  have charge (guard armCenter root : ℕ) (rootB : root < 26+C.gates.length)
      (anchorEdge : planeAdjacent armCenter guard)
      (contains : insert armCenter (lostArms D guard armCenter) ⊆ rawSupport 26 C root) :
      let J := chargedJoins C ok.1 (insert armCenter (lostArms D guard armCenter)) root
      (lostArms D guard armCenter).card ≤ J.card ∧
      (∀ v ∈ J, v < D.gates.length) ∧ (∀ v ∈ J, v ∉ Retain.liveSlots 26 D) := by
    intro J
    let labels := insert armCenter (lostArms D guard armCenter)
    have apart : armCenter ∉ lostArms D guard armCenter := fun m => (mem_lostArms.mp m).1 rfl
    have count := charged_card C ok.1 labels root contains
    dsimp [labels] at count
    rw [Finset.card_insert_of_notMem apart] at count
    change (lostArms D guard armCenter).card + 1 ≤ J.card + 1 at count
    have fixed : ∀ v ∈ J, P.rep (26+v) = some (26+v) := by
      intro v hv
      exact charged_fixed_of_two_ands P ok.1 labels low (by simpa only [slotEq] using high) hv
    have adjacent (w : ℕ) (mem : w ∈ labels) : planeAdjacent w guard := by
      rcases Finset.mem_insert.mp mem with rfl | arm
      · exact anchorEdge
      · exact planeAdjacent_reverse (mem_lostLeaves.mp (mem_lostArms.mp arm).2).1
    have armLost (w : ℕ) (mem : w ∈ lostArms D guard armCenter) :
        D.eval (rawInput {w,guard}) = false := by
      rw [show ({w,guard} : Finset ℕ) = {guard,w} from Finset.pair_comm _ _]
      exact (mem_lostLeaves.mp (mem_lostArms.mp mem).2).2
    have hasLost (u : ℕ) (um : u ∈ labels) (v : ℕ) (vm : v ∈ labels) (different : u ≠ v) :
        D.eval (rawInput {u,guard}) = false ∨ D.eval (rawInput {v,guard}) = false := by
      rcases Finset.mem_insert.mp um with rfl | un
      · exact Or.inr (armLost v ((Finset.mem_insert.mp vm).resolve_left different.symm))
      · exact Or.inl (armLost u un)
    refine ⟨by omega,?_,charged_dead P ok low labels rootB dm db df valid negativeSafe mates fixed adjacent hasLost⟩
    intro v hv
    have earlier := (charged_labels C ok.1 labels hv).1
    change v < P.projected.gates.length
    rw [P.projected_gate_count]
    omega
  obtain ⟨card₁,valid₁,dead₁⟩ := charge b a ip ipB central supportP
  obtain ⟨card₂,valid₂,dead₂⟩ := charge a b jl jlB (planeAdjacent_reverse central) supportL
  change (lostArms D b a).card ≤ J₁.card at card₁
  change (lostArms D a b).card ≤ J₂.card at card₂
  have aAtMix : a ∈ rawSupport 26 C mk := by
    change a ∈ rawSupport 26 C (ports.clauseWire k)
    rwa [← ports.rawClause_eq]
  have bAtMix : b ∈ rawSupport 26 C mk := by
    change b ∈ rawSupport 26 C (ports.clauseWire k)
    rwa [← ports.rawClause_eq]
  have ab : a ≠ b := by omega
  have pairAtMix : ({a,b} : Finset ℕ) ⊆ rawSupport 26 C mk := by
    intro w mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at mem
    rcases mem with rfl | rfl
    · exact aAtMix
    · exact bAtMix
  have mixedMany : 2 ≤ (selectedSupport 26 C {a,b} mk).card := by
    simp [selectedSupport, Finset.inter_eq_right.mpr pairAtMix, Finset.card_pair ab]
  obtain ⟨mkRaw,mkOp⟩ := selected_multi_is_or C {a,b} mixedMany
  let m := mk-26
  have mEq : 26+m = mk := by dsimp [m]; omega
  have mOp : (gateAt C m).op = .or := mkOp
  have mh : m ≠ h := by intro eq; rw [eq,low] at mOp; cases mOp
  have mH : m ≠ H := by intro eq; rw [eq,high] at mOp; cases mOp
  have fixedM : P.rep (26+m) = some (26+m) :=
    ProjectAliases.mapTwo_other (by omega) (by omega)
  have mSame := P.raw_maps ok.2.1 low (26+m) (by omega)
  rw [fixedM, Option.map_some, Option.getD_some, mEq] at mSame
  have mDead : m ∉ Retain.liveSlots 26 D :=
    no_live_mixed_labels dm db df valid negativeSafe mates (by rw [mEq,mSame]; exact aAtMix)
      (by rw [mEq,mSame]; exact bAtMix) aP bL
  have apart : Disjoint J₁ J₂ := by
    apply Finset.disjoint_left.mpr
    intro v left right
    obtain ⟨_,_,w,_,_,_,_,raw,_⟩ := charged_labels C ok.1 S left
    have pMem := charged_raw_subset C ok.1 S left raw
    have lMem := charged_raw_subset C ok.1 T right raw
    change w ∈ rawSupport 26 C (ports.clauseWire i) at pMem
    change w ∈ rawSupport 26 C (ports.clauseWire j) at lMem
    rw [← ports.rawClause_eq] at pMem lMem
    exact (Nat.not_lt_of_ge (pureL w lMem)) (pureP w pMem)
  have mixedAside : m ∉ J₁ ∪ J₂ := by
    intro mem
    rcases Finset.mem_union.mp mem with left | right
    · have atM : b ∈ rawSupport 26 C (26+m) := by rwa [mEq]
      have pMem := charged_raw_subset C ok.1 S left atM
      change b ∈ rawSupport 26 C (ports.clauseWire i) at pMem
      rw [← ports.rawClause_eq] at pMem
      exact (Nat.not_lt_of_ge bL) (pureP b pMem)
    · have atM : a ∈ rawSupport 26 C (26+m) := by rwa [mEq]
      have lMem := charged_raw_subset C ok.1 T right atM
      change a ∈ rawSupport 26 C (ports.clauseWire j) at lMem
      rw [← ports.rawClause_eq] at lMem
      exact (Nat.not_lt_of_ge (pureL a lMem)) aP
  have andAside (v : ℕ) (op : (gateAt C v).op = .and) : v ∉ J₁ ∪ J₂ := by
    intro mem
    have raw := (Finset.mem_union.mp mem).elim
      (fun left => (charged_labels C ok.1 S left).2.1)
      (fun right => (charged_labels C ok.1 T right).2.1)
    rw [op] at raw
    cases raw
  have upperAside : H ∉ insert m (J₁ ∪ J₂) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨mH.symm,andAside H high⟩
  have lowerAside : h ∉ insert H (insert m (J₁ ∪ J₂)) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨(cone_lt nest).ne,mh.symm,andAside h low⟩
  let dead := insert h (insert H (insert m (J₁ ∪ J₂)))
  have deadCard : dead.card = J₁.card+J₂.card+3 := by
    dsimp [dead]
    rw [Finset.card_insert_of_notMem lowerAside, Finset.card_insert_of_notMem upperAside,
      Finset.card_insert_of_notMem mixedAside, Finset.card_union_of_disjoint apart] <;> omega
  have deadValid : ∀ v ∈ dead, v < D.gates.length := by
    intro v mem
    simp only [dead, Finset.mem_insert, Finset.mem_union] at mem
    have len : D.gates.length = C.gates.length := P.projected_gate_count
    rcases mem with rfl | rfl | rfl | left | right
    · simpa only [len] using gateAt_and_bound C _ low
    · simpa only [len] using gateAt_and_bound C _ high
    · omega
    · exact valid₁ _ left
    · exact valid₂ _ right
  have deadOutside : ∀ v ∈ dead, v ∉ Retain.liveSlots 26 D := by
    intro v mem
    simp only [dead, Finset.mem_insert, Finset.mem_union] at mem
    rcases mem with rfl | rfl | rfl | left | right
    · exact twoDead.1
    · exact twoDead.2
    · exact mDead
    · exact dead₁ _ left
    · exact dead₂ _ right
  apply plane_star_budget_from_cover D (lostStar D b) (lostStarExcept D a b) C.size
    dm db df negativeSafe bl al cover dead deadValid deadOutside
  · have costs := lostStars_cost_le D b a
    omega
  · exact P.projected_size.le

theorem empty_star_repair {C : Circuit} {h H : ℕ} (P : ProjectionPlan C h)
    (ports : NestInputs C h H) (ok : acceptable C) (strict : StrictBinary C)
    (minimal : ∀ D : Circuit, acceptable D → C.size ≤ D.size)
    (one : PEqualNP.TopForm.andPairs 26 C ≤ 1) (low : (gateAt C h).op = .and)
    (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (bad : ∃ L, negative L ∧ wireOn C L (26+h))
    (empty : ports.terms.upperFeed = ∅) (slotEq : P.slot = H)
    (star : ports.terms.clauses.Star) : 64 ≤ C.size := by
  have fromLost (p l : Fin 13) (edge : Quadrangle1692.incident p l)
      (lost : P.projected.eval (incidenceRow p l) = false) : ports.terms.clauses.Hit p l := by
    have got := ports.lost_pair ok one low high nest bad P p l edge lost
    exact (ports.terms.upper_iff_hit empty p l).mp ⟨Or.inr got.1,got.2.1⟩
  have starCover : ∃ center < 26, ∀ p l : Fin 13, Quadrangle1692.incident p l →
      P.projected.eval (incidenceRow p l) = false → center = p.val ∨ center = 13+l.val := by
    rcases star with ⟨p,shape⟩ | ⟨l,shape⟩
    · refine ⟨p.val,by have := p.isLt; omega, fun q r edge lost => ?_⟩
      exact Or.inl (congrArg Fin.val (shape q r (fromLost q r edge lost))).symm
    · refine ⟨13+l.val,by have := l.isLt; omega, fun q r edge lost => ?_⟩
      exact Or.inr (congrArg (fun v : Fin 13 => 13+v.val) (shape q r (fromLost q r edge lost))).symm
  obtain ⟨center,bound,cover⟩ := starCover
  obtain ⟨i,_,which⟩ := ports.terms.empty_star_clause empty
    (ports.pair_sound ok minimal one low high nest) center
  apply one_star_from_support P ok strict one low high nest bound cover
    (ports.clauseWire_valid ok.2.1 low high i)
  · intro w wLost
    rw [← ports.rawClause_eq]
    obtain ⟨adj,lost⟩ := mem_lostLeaves.mp wLost
    have got := ports.lost_raw_pair ok one low high nest bad P adj lost
    exact which w (Or.inl ⟨Or.inr got.1,got.2.1⟩)
  · intro j hj
    exact charged_fixed_of_two_ands P ok.1 _ low (by simpa only [slotEq] using high) hj

theorem empty_repair {C : Circuit} {h H : ℕ} (P : ProjectionPlan C h)
    (ports : NestInputs C h H) (ok : acceptable C) (strict : StrictBinary C)
    (minimal : ∀ D : Circuit, acceptable D → C.size ≤ D.size)
    (one : PEqualNP.TopForm.andPairs 26 C ≤ 1) (low : (gateAt C h).op = .and)
    (high : (gateAt C H).op = .and) (nest : InCone 26 C h H)
    (bad : ∃ L, negative L ∧ wireOn C L (26+h))
    (empty : ports.terms.upperFeed = ∅) (slotEq : P.slot = H) : 64 ≤ C.size := by
  rcases ports.terms.empty_clauses_shape empty (ports.pair_sound ok minimal one low high nest) with
    star | double
  · exact empty_star_repair P ports ok strict minimal one low high nest bad empty slotEq star
  · exact empty_double_repair P ports ok strict minimal one low high nest bad empty slotEq double


end OneNestedAnd

/- Source work/quad1961/Final.lean -/

end PEqualNP.Outside.L_meta_1961_aux

open PEqualNP.Outside.L_meta_1961_aux

open OneNestedAnd PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
theorem PEqualNP.Outside.L_meta_1961 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → PEqualNP.TopForm.andPairs (26 : ℕ) x4 ≤ (1 : ℕ) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  classical
  by_contra failed
  have counter : OneNestedAnd.postedClaim := failed
  obtain ⟨C, ok, small, pair, minimal⟩ := counterexample_is_minimal.mp counter
  obtain ⟨⟨h, H, low, high, nest⟩, strict, one⟩ := pair
  have bad : ∃ L, negative L ∧ wireOn C L (26+h) :=
    lower_has_negative_witness C ok small h H low high nest one minimal
  obtain ⟨ports⟩ := exists_nest_inputs C ok strict minimal h H one low high nest bad
  obtain ⟨projection, cases⟩ := plan_for_inputs ports ok strict one low high nest
  have tooLarge : 64 ≤ C.size := by
    rcases cases with ⟨empty, slotEq⟩ | ⟨nonempty, _⟩
    · exact empty_repair projection ports ok strict minimal one low high nest bad empty slotEq
    · exact guarded_repair ports projection ok strict minimal one low high nest bad nonempty
  omega
