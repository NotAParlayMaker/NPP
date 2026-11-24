import Mathlib.Data.Set.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4651

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def unary (p : ℕ) : Gate := ⟨.and,[p]⟩

def changed (C : Circuit) (j p : ℕ) : Circuit := ⟨C.gates.set j (unary p), C.output⟩

def orSet (C : Circuit) : Set (Fin C.gates.length) := {i | (C.gates.get i).op = .or}

theorem changedMono (C : Circuit) (j : Fin C.gates.length) (p : ℕ)
    (hm : Monotone2 C) : Monotone2 (changed C j p) := by
  intro g hg
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hg
  change i < (C.gates.set j (unary p)).length at hi
  change (C.gates.set j (unary p))[i] = g at he
  by_cases h : j.val = i
  · subst i
    rw [List.getElem_set_self] at he
    subst g
    simp [unary]
  · rw [List.getElem_set_ne h] at he
    apply hm
    rw [← he]
    exact List.getElem_mem _

theorem changedCount (C : Circuit) (j : Fin C.gates.length) (p : ℕ)
    (hop : (C.gates.get j).op = .or) : (orSet (changed C j p)).ncard < (orSet C).ncard := by
  classical
  let D := changed C j p
  have hlen : D.gates.length = C.gates.length := by simp [D,changed]
  let e : Fin D.gates.length ≃ Fin C.gates.length := finCongr hlen
  have hval (i : Fin D.gates.length) : (e i).val = i.val := rfl
  have hiff (i : Fin D.gates.length) : i ∈ orSet D ↔ e i ∈ (orSet C \ {j}) := by
    change (C.gates.set j (unary p))[i.val].op = .or ↔
      (C.gates.get (e i)).op = .or ∧ e i ∉ ({j} : Set _)
    by_cases hij : j.val = i.val
    · have heq : e i = j := Fin.ext ((hval i).trans hij.symm)
      simp [← hij,List.getElem_set_self,unary,heq]
    · have heq : e i ≠ j := fun h => hij ((hval i).symm.trans (congrArg Fin.val h)).symm
      simp only [List.getElem_set_ne hij, Set.mem_singleton_iff, heq, not_false_eq_true, and_true]
      rfl
  have eqn : (orSet D).ncard = (orSet C \ {j}).ncard :=
    Set.ncard_congr' (e.subtypeEquiv hiff)
  exact eqn.trans_lt (Set.ncard_sdiff_singleton_lt_of_mem (s := orSet C) hop)

def semWiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma semGetD_snoc_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp

lemma semGateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact h _ (List.getElem_mem (by omega))
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]
      exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma semWiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (semWiresFrom gs w₁).getD i false = true →
        (semWiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : semWiresFrom (g :: gs) w₁ =
        semWiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : semWiresFrom (g :: gs) w₂ =
        semWiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
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
        rw [semGetD_snoc_eq] at hj
        rw [hlen, semGetD_snoc_eq]
        exact semGateOp_eval_mono g.op (hmono g List.mem_cons_self)
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

lemma semWiresFrom_append (gs hs : List Gate) (w : List Bool) :
    semWiresFrom (gs ++ hs) w = semWiresFrom hs (semWiresFrom gs w) := by
  simp [semWiresFrom, List.foldl_append]

lemma semSplitAt {α : Type} (xs : List α) (j : ℕ) (hj : j < xs.length) :
    xs = xs.take j ++ xs[j] :: xs.drop (j + 1) := by
  induction j generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hj
    | cons a as => simp
  | succ j ih =>
    cases xs with
    | nil => simp at hj
    | cons a as =>
      have hj' : j < as.length := by simp at hj; omega
      simpa using congrArg (fun ys : List α => a :: ys) (ih as hj')

lemma semSetSplitAt {α : Type} (xs : List α) (j : ℕ) (hj : j < xs.length) (a : α) :
    xs.set j a = xs.take j ++ a :: xs.drop (j + 1) := by
  induction j generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hj
    | cons b bs => simp
  | succ j ih =>
    cases xs with
    | nil => simp at hj
    | cons b bs =>
      have hj' : j < bs.length := by simp at hj; omega
      simpa using congrArg (fun ys : List α => b :: ys) (ih bs hj')

lemma semOr_mem {g : Gate} {p : ℕ} {w : List Bool}
    (hop : g.op = GateOp.or) (hp : p ∈ g.inputs) :
    w.getD p false = true → g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
  intro hpw
  rw [hop, GateOp.eval]
  apply List.any_eq_true.mpr
  exact ⟨w.getD p false, List.mem_map.mpr ⟨p, hp, rfl⟩, hpw⟩

lemma semMiddle_le (w : List Bool) (g : Gate) (p : ℕ) (hp : p ∈ g.inputs)
    (hw : w.getD p false = true → g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    ∀ i, (w ++ [GateOp.and.eval [w.getD p false]]).getD i false = true →
      (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).getD i false = true := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi ⊢
    exact hi
  · by_cases heq : i = w.length
    · subst i
      rw [semGetD_snoc_eq] at hi ⊢
      have hbit : w.getD p false = true := by simpa [GateOp.eval] using hi
      exact hw hbit
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact Bool.noConfusion hi

theorem changed_eval_le (n : ℕ) (C : Circuit) (j : Fin C.gates.length) (p : ℕ)
    (hm : Monotone2 C) (hop : (C.gates.get j).op = GateOp.or)
    (hp : p ∈ (C.gates.get j).inputs) (x : Fin n → Bool)
    (hnew : (changed C j p).eval (List.ofFn x) = true) : C.eval (List.ofFn x) = true := by
  let gs := C.gates
  let k := j.val
  let pre := gs.take k
  let post := gs.drop (k + 1)
  let w := semWiresFrom pre (List.ofFn x)
  have hk : k < gs.length := j.isLt
  have hsplit := semSplitAt gs k hk
  have hchanged := semSetSplitAt gs k hk (unary p)
  have hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have hgm := hm g (List.mem_of_mem_take hg)
    simpa using hgm.1
  have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have hgm := hm g (List.mem_of_mem_drop hg)
    simpa using hgm.1
  have hsame : C.gates = pre ++ (gs[k] :: post) := by
    change C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1)
    exact hsplit
  have hnewgs : C.gates.set k (unary p) = pre ++ (unary p :: post) := by
    change C.gates.set k (unary p) = C.gates.take k ++ unary p :: C.gates.drop (k + 1)
    exact hchanged
  change (semWiresFrom (C.gates.set k (unary p)) (List.ofFn x)).getD C.output false = true at hnew
  rw [hnewgs, semWiresFrom_append] at hnew
  change (semWiresFrom post (w ++ [GateOp.and.eval [w.getD p false]])).getD
    C.output false = true at hnew
  change (semWiresFrom C.gates (List.ofFn x)).getD C.output false = true
  rw [hsame, semWiresFrom_append]
  change (semWiresFrom post
    (w ++ [gs[k].op.eval (gs[k].inputs.map fun i => w.getD i false)])).getD
      C.output false = true
  apply semWiresFrom_mono post hpost
    (w ++ [GateOp.and.eval [w.getD p false]])
    (w ++ [gs[k].op.eval (gs[k].inputs.map fun i => w.getD i false)])
    (by simp) ?_ C.output hnew
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi ⊢
    exact hi
  · by_cases heq : i = w.length
    · subst i
      rw [semGetD_snoc_eq] at hi ⊢
      have hbit : w.getD p false = true := by simpa [GateOp.eval] using hi
      have hcurrent : gs[k] = C.gates.get j := by simp [gs, k]
      have hmem : p ∈ gs[k].inputs := by simpa [hcurrent] using hp
      have hhop : gs[k].op = GateOp.or := by simpa [hcurrent] using hop
      exact semOr_mem hhop hmem hbit
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact Bool.noConfusion hi

theorem eval_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hle : ∀ i, x i = true → y i = true)
    (hx : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have hgm := hm g hg
    simpa using hgm.1
  have hstate : ∀ i, (List.ofFn x).getD i false = true →
      (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hlt : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hle ⟨i, hlt⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact Bool.noConfusion hi
  change (semWiresFrom C.gates (List.ofFn x)).getD C.output false = true at hx
  exact semWiresFrom_mono C.gates hops (List.ofFn x) (List.ofFn y) (by simp)
    hstate C.output hx

end PEqualNP.Outside.L_meta_4651

open PEqualNP.Outside.L_meta_4651 in
theorem PEqualNP.Outside.L_meta_4651 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => {x2 : Fin x1.gates.length | (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) => { gates := x2.gates.set x3 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit }; ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x4.gates.length) (x6 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x4 →     (x4.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →       x6 ∈ (x4.gates.get x5).inputs →         have x10 : PEqualNP.CircuitLowerBounds.Circuit := x2 x4 (↑x5) x6;         PEqualNP.MetaComplexity.Monotone2 x10 ∧ x1 x10 < x1 x4 ∧ (∀ (x11 : Fin x3 → Bool), x10.eval (List.ofFn x11) = Bool.true → x4.eval (List.ofFn x11) = Bool.true) ∧ ∀ (x11 x12 : Fin x3 → Bool), (∀ (x13 : Fin x3), x11 x13 = Bool.true → x12 x13 = Bool.true) → x10.eval (List.ofFn x11) = Bool.true → x10.eval (List.ofFn x12) = Bool.true := by
  dsimp only
  intro n C j p hmono hop hp
  have hd := changedMono C j p hmono
  exact ⟨hd, changedCount C j p hop,
    changed_eval_le n C j p hmono hop hp,
    eval_mono n (changed C j p) hd⟩
