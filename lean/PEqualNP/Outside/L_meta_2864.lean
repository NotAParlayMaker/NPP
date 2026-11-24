import Mathlib
import PEqualNP.Defs

-- Circuit evaluation helpers adapted from trimbe, PR #2080 (L-meta-1042).
namespace PEqualNP.Outside.L_meta_2864

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

open PEqualNP.MetaComplexity

def V {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (w : ℕ) : Bool :=
  wireValue C (List.ofFn x ++ List.ofFn y) w

lemma ofFn_mono {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using h ⟨i, hi⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]

lemma V_mono {n : ℕ} (C : Circuit) (hC : Monotone2 C)
    (x x' y y' : Fin n → Bool)
    (hx : ∀ i, x i = true → x' i = true) (hy : ∀ i, y i = true → y' i = true)
    (w : ℕ) : V C x y w = true → V C x' y' w = true := by
  apply wiresFrom_mono C.gates (fun g hg => (hC g hg).1) _ _ (by simp)
  intro i hi
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h)] at hi
    rw [List.getD_append _ _ _ _ (by simpa using h)]
    exact ofFn_mono x x' hx i hi
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simpa using ofFn_mono y y' hy (i-n) (by simpa using hi)

lemma V_right {n : ℕ} (C : Circuit) (hC : Monotone2 C) (w : ℕ)
    (h : ∀ x : Fin n → Bool, V C x (fun _ => false) w = V C x (fun _ => true) w)
    (x y : Fin n → Bool) : V C x y w = V C x (fun _ => false) w := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rw [h x]
    exact V_mono C hC x x y (fun _ => true) (by simp) (by simp) w hv
  · exact V_mono C hC x x (fun _ => false) y (by simp) (by simp) w

lemma V_left {n : ℕ} (C : Circuit) (hC : Monotone2 C) (w : ℕ)
    (h : ∀ y : Fin n → Bool, V C (fun _ => false) y w = V C (fun _ => true) y w)
    (x y : Fin n → Bool) : V C x y w = V C (fun _ => false) y w := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rw [h y]
    exact V_mono C hC x (fun _ => true) y y (by simp) (by simp) w hv
  · exact V_mono C hC (fun _ => false) x y y (by simp) (by simp) w


lemma V_constant {n : ℕ} (C : Circuit) (hC : Monotone2 C) (w : ℕ)
    (hr : ∀ x : Fin n → Bool, V C x (fun _ => false) w = V C x (fun _ => true) w)
    (hl : ∀ y : Fin n → Bool, V C (fun _ => false) y w = V C (fun _ => true) y w)
    (x y : Fin n → Bool) : V C x y w = V C (fun _ : Fin n => false) (fun _ => false) w := by
  rw [V_right C hC w hr, V_left C hC w hl]

lemma separate {n : ℕ} (C : Circuit) (hC : Monotone2 C) (u v : ℕ)
    (hr : (∀ x : Fin n → Bool, V C x (fun _ => false) u = V C x (fun _ => true) u) ∨
      (∀ x : Fin n → Bool, V C x (fun _ => false) v = V C x (fun _ => true) v))
    (hl : (∀ y : Fin n → Bool, V C (fun _ => false) y u = V C (fun _ => true) y u) ∨
      (∀ y : Fin n → Bool, V C (fun _ => false) y v = V C (fun _ => true) y v)) :
    (∃ w ∈ [u,v], ∀ x y : Fin n → Bool, (V C x y u && V C x y v) = V C x y w) ∨
      ∃ f g : (Fin n → Bool) → Bool, ∀ x y, (V C x y u && V C x y v) = (f x && g y) := by
  rcases hr with hru | hrv <;> rcases hl with hlu | hlv
  · have hc := V_constant C hC u hru hlu
    cases hz : V C (fun _ : Fin n => false) (fun _ => false) u with
    | false =>
      left
      refine ⟨u, by simp, ?_⟩
      intro x y
      rw [hc x y, hz]
      simp
    | true =>
      left
      refine ⟨v, by simp, ?_⟩
      intro x y
      rw [hc x y, hz]
      simp
  · right
    refine ⟨fun x => V C x (fun _ => false) u, fun y => V C (fun _ => false) y v, ?_⟩
    intro x y
    rw [V_right C hC u hru x y, V_left C hC v hlv x y]
  · right
    refine ⟨fun x => V C x (fun _ => false) v, fun y => V C (fun _ => false) y u, ?_⟩
    intro x y
    rw [V_left C hC u hlu x y, V_right C hC v hrv x y, Bool.and_comm]
  · have hc := V_constant C hC v hrv hlv
    cases hz : V C (fun _ : Fin n => false) (fun _ => false) v with
    | false =>
      left
      refine ⟨v, by simp, ?_⟩
      intro x y
      rw [hc x y, hz]
      simp
    | true =>
      left
      refine ⟨u, by simp, ?_⟩
      intro x y
      rw [hc x y, hz]
      simp

def one {n : ℕ} (p : Fin n) : Fin n → Bool := fun i => decide (i = p)
def pairInput {n : ℕ} (p l : Fin n) : Fin (n+n) → Bool := Fin.append (one p) (one l)

lemma left_ne_right {n : ℕ} (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma pairInput_eq {n : ℕ} (p l : Fin n) :
    pairInput p l = fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [pairInput, Fin.append_left, one, Fin.castAdd_inj, left_ne_right, or_false]
  · simp only [pairInput, Fin.append_right, one, Fin.natAdd_inj, Ne.symm (left_ne_right p _), false_or]

abbrev Sound (q n : ℕ) (I : Fin n → Fin n → Prop) (C : Circuit) : Prop :=
  ∀ z : Fin (n+n) → Bool,
    Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q →
    (¬ ∃ p l : Fin n, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true) →
    circuitFun (n+n) C z = false

lemma singleton_sound (q n : ℕ) (I : Fin n → Fin n → Prop) (C : Circuit)
    (hq : 0 < q) (hs : Sound q n I C) (p l : Fin n)
    (ha : circuitFun (n+n) C (pairInput p l) = true) : I p l := by
  have hn : Fintype.card {l' : Fin n // pairInput p l (Fin.natAdd n l') = true} = 1 := by
    simp only [pairInput, Fin.append_right, one, decide_eq_true_eq]
    simp
  by_contra h
  have he := hs (pairInput p l) (by rw [hn]; omega) (by
    rintro ⟨p',l',hi,hp,hl⟩
    simp only [pairInput, Fin.append_left, Fin.append_right, one, decide_eq_true_eq] at hp hl
    subst p'
    subst l'
    exact h hi)
  rw [ha] at he
  contradiction

end PEqualNP.Outside.L_meta_2864

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2864 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_2864 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) →       PEqualNP.MetaComplexity.Monotone2 x5 →         (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) →           ∀ (x10 x11 : ℕ),             ¬((∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.false)).getD x12 Bool.false ≠ (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.true)).getD x12 Bool.false) ∨ ∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x14)).getD x12 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x14)).getD x12 Bool.false) →               have x13 : ℕ → (Fin x2 → Bool) → (Fin x2 → Bool) → Bool := fun (x13 : ℕ) (x14 x15 : Fin x2 → Bool) => (x5.wires (List.ofFn x14 ++ List.ofFn x15)).getD x13 Bool.false;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               (∃ x15 ∈ [x10, x11], ∀ (x16 x17 : Fin x2 → Bool), (x13 x10 x16 x17 && x13 x11 x16 x17) = x13 x15 x16 x17) ∨ ∃ (x15 : (Fin x2 → Bool) → Bool) (x16 : (Fin x2 → Bool) → Bool), (∀ (x17 x18 : Fin x2 → Bool), (x13 x10 x17 x18 && x13 x11 x17 x18) = (x15 x17 && x16 x18)) ∧ ((∀ (x17 x18 : Fin x2), (x15 (x14 x17) && x16 (x14 x18)) = Bool.true → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x17 ∨ x20 = Fin.natAdd x2 x18)) = Bool.true) → ∀ (x18 x19 x20 x21 : Fin x2), (x15 (x14 x18) && x16 (x14 x20)) = Bool.true → (x15 (x14 x19) && x16 (x14 x21)) = Bool.true → x18 = x19 ∨ x20 = x21) := by
  classical
  intro q n I inst C hq hUnique hC hSound u v hn
  push Not at hn
  obtain ⟨⟨a,ha,hra⟩,⟨b,hb,hlb⟩⟩ := hn
  have hr : (∀ x : Fin n → Bool, V C x (fun _ => false) u = V C x (fun _ => true) u) ∨
      (∀ x : Fin n → Bool, V C x (fun _ => false) v = V C x (fun _ => true) v) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | ha
    · left
      intro x
      subst a
      simpa [V, wireValue, List.ofFn_const] using hra x
    · right
      intro x
      subst a
      simpa [V, wireValue, List.ofFn_const] using hra x
  have hl : (∀ y : Fin n → Bool, V C (fun _ => false) y u = V C (fun _ => true) y u) ∨
      (∀ y : Fin n → Bool, V C (fun _ => false) y v = V C (fun _ => true) y v) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb
    · left
      intro y
      subst b
      simpa [V, wireValue, List.ofFn_const] using hlb y
    · right
      intro y
      subst b
      simpa [V, wireValue, List.ofFn_const] using hlb y
  rcases separate C hC u v hr hl with hpick | ⟨f,g,hfg⟩
  · exact Or.inl hpick
  · right
    refine ⟨f,g,hfg,?_⟩
    intro hsupport p p' l l' h1 h2
    have accept : ∀ p l : Fin n, (f (one p) && g (one l)) = true → I p l := by
      intro p l h
      apply singleton_sound q n I C hq hSound p l
      rw [pairInput_eq]
      exact hsupport p l h
    by_cases hpp : p = p'
    · exact Or.inl hpp
    · right
      have hf1 := (Bool.and_eq_true_iff.mp h1).1
      have hg1 := (Bool.and_eq_true_iff.mp h1).2
      have hf2 := (Bool.and_eq_true_iff.mp h2).1
      have hg2 := (Bool.and_eq_true_iff.mp h2).2
      obtain ⟨z,hz,hzunique⟩ := hUnique p p' hpp
      exact (hzunique l ⟨accept p l h1, accept p' l (Bool.and_eq_true_iff.mpr ⟨hf2,hg1⟩)⟩).trans
        (hzunique l' ⟨accept p l' (Bool.and_eq_true_iff.mpr ⟨hf1,hg2⟩), accept p' l' h2⟩).symm
