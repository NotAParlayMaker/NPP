import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1580.Cut

-- The line partition count follows L-meta-1567 with arbitrary nonempty label sets.
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M c τ i X

def Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X

theorem single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ p ∈ M, ∀ v, τ p v = true → c v = false → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at hwc h1 h2
      have e1 := hc y hy _ h1 hwc
      have e2 := hc y' hy' _ h2 hwc
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    Con gates M c τ (k + 1) X ↔ Con gates M c τ k X ∧ Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : Con gates M c τ k X) :
    Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : Con gates M c τ k X)
    (hY : Con gates M c τ k Y) : Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => Con gates M c τ k X)

open Classical in
theorem symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ P gates M c τ k)
    (hY : Y ⊆ M) (hYc : Con gates M c τ k Y) : symmDiff X Y ∈ P gates M c τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ p ∈ M, ∀ v, τ p v = true → c v = false → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M c τ ((g : ℕ) + 1)).card * (if Mrg gates M c τ g then 2 else 1)
      = (P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : P gates M c τ ((g : ℕ) + 1) = P gates M c τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, ite_eq_right hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := (hin g) a hma
    have hb : b < n + (g : ℕ) := (hin g) b hmb
    have hac : val gates a c = false := by
      cases hv : val gates a c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : val gates b c = false := by
      cases hv : val gates b c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hc legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hc legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [ite_eq_left hmrg]
      have hP : P gates M c τ ((g : ℕ) + 1)
          = (P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [ite_eq_right hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M c τ g X h⟩

open Classical in
theorem count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ p ∈ M, ∀ v, τ p v = true → c v = false → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M c τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M c τ (k + 1)).card * (if Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M c τ k).card := step gates M c τ hc legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
          + (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring

open Classical in
theorem tally {n d : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ p ∈ M, ∀ v, τ p v = true → c v = false → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : M.card = d + 1) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = d := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M c τ hc legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := count gates M c τ hc legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hM, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hpow : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ d := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    simpa only [pow_succ, Nat.mul_comm (2 ^ d) 2] using hcnt
  exact Nat.pow_right_injective (le_refl 2) hpow

end PEqualNP.Outside.L_meta_1580.Cut

namespace PEqualNP.Outside.L_meta_1580

open Classical in
private noncomputable def signature (E : Finset ℕ) (C : ℕ → ℕ → Prop) (a : ℕ) : Finset ℕ :=
  E.filter fun j => C j a

-- A new cut separates two old signatures, increasing the image size.
private lemma cuts_image (U E : Finset ℕ) (C : ℕ → ℕ → Prop) (nonempty : U.Nonempty)
    (cross : ∀ i ∈ E, ∃ a ∈ U, ∃ b ∈ U, C i a ∧ ¬ C i b ∧
      ∀ j ∈ E, i < j → (C j a ↔ C j b)) :
    E.card + 1 ≤ (U.image (signature E C)).card := by
  classical
  induction E using Finset.strongInduction with
  | H E ih =>
    rcases E.eq_empty_or_nonempty with emp | ne
    · subst E
      simpa using (Finset.card_pos.mpr (nonempty.image (signature ∅ C)))
    · let k := E.min' ne
      have hmem : k ∈ E := E.min'_mem ne
      let D := E.erase k
      have hd : D ⊂ E := Finset.erase_ssubset hmem
      have sub : D ⊆ E := Finset.erase_subset _ _
      have nSmall := ih D hd fun i hi => by
        obtain ⟨a,ha,b,hb,yes,no,later⟩ := cross i (sub hi)
        exact ⟨a,ha,b,hb,yes,no,fun j hj lt => later j (sub hj) lt⟩
      obtain ⟨a,ha,b,hb,yes,no,later⟩ := cross k hmem
      let big := U.image (signature E C)
      let project (v : Finset ℕ) := v.erase k
      have proj (z : ℕ) : project (signature E C z) = signature D C z := by
        ext j
        simp only [project,signature,D,Finset.mem_erase,Finset.mem_filter]
        tauto
      have eq : big.image project = U.image (signature D C) := by
        unfold big
        rw [Finset.image_image]
        exact Finset.image_congr fun a _ => proj a
      have diff : signature E C a ≠ signature E C b := by
        intro same
        have ka : k ∈ signature E C a := Finset.mem_filter.mpr ⟨hmem,yes⟩
        exact no (Finset.mem_filter.mp (same ▸ ka : k ∈ signature E C b)).2
      have eqSmall : signature D C a = signature D C b := by
        ext j
        simp only [signature,Finset.mem_filter]
        by_cases jmem : j ∈ D
        · have lt : k < j := lt_of_le_of_ne (E.min'_le j (sub jmem))
              (Ne.symm (Finset.mem_erase.mp jmem).1)
          exact and_congr_right fun _ => later j (sub jmem) lt
        · simp [jmem]
      have strict : (big.image project).card < big.card := by
        apply lt_of_le_of_ne Finset.card_image_le
        intro same
        exact diff ((Finset.card_image_iff.mp same)
          (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
          ((proj a).trans (eqSmall.trans (proj b).symm)))
      rw [eq] at strict
      have step : D.card+1=E.card := Finset.card_erase_add_one hmem
      change E.card + 1 ≤ big.card
      omega

lemma count_sources (U E : Finset ℕ) (parent C : ℕ → ℕ → Prop) (nonempty : U.Nonempty)
    (before : ∀ w v, parent w v → v < w)
    (closed : ∀ w ∈ U, ∀ v, parent w v → v ∈ U)
    (consistent : ∀ i ∈ E, ∀ w, w < i → ∀ v, parent w v → (C i w ↔ C i v))
    (marked : ∀ i ∈ E, i ∈ U ∧ ∃ a b, parent i a ∧ parent i b ∧ C i a ∧ ¬ C i b) :
    ∃ S : Finset ℕ, (∀ w, w ∈ S ↔ w ∈ U ∧ ¬ ∃ v, parent w v) ∧ E.card+1 ≤ S.card := by
  classical
  let S := U.filter fun w => ¬ ∃ v, parent w v
  have root : ∀ w ∈ U, ∃ r ∈ S, ∀ i ∈ E, w < i → (C i r ↔ C i w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hu
      by_cases child : ∃ v, parent w v
      · obtain ⟨v,hv⟩ := child
        have lt := before w v hv
        obtain ⟨r,hr,uses⟩ := ih v lt (closed w hu v hv)
        exact ⟨r,hr,fun i hi wi => (uses i hi (lt_trans lt wi)).trans
          (consistent i hi w wi v hv).symm⟩
      · exact ⟨w,Finset.mem_filter.mpr ⟨hu,child⟩,fun _ _ _ => Iff.rfl⟩
  have sn : S.Nonempty := by
    obtain ⟨w,hw⟩ := nonempty
    obtain ⟨r,hr,_⟩ := root w hw
    exact ⟨r,hr⟩
  have bound := cuts_image S E C sn (by
    intro i hi
    obtain ⟨ui,a,b,pa,pb,a_yes,b_no⟩ := marked i hi
    have al := before i a pa
    have bl := before i b pb
    obtain ⟨s,hs,sa⟩ := root a (closed i ui a pa)
    obtain ⟨t,ht,tb⟩ := root b (closed i ui b pb)
    refine ⟨s,hs,t,ht,(sa i hi al).mpr a_yes,fun h => b_no ((tb i hi bl).mp h),?_⟩
    intro j hj ij
    exact (sa j hj (lt_trans al ij)).trans (((consistent j hj i ij a pa).symm.trans
      (consistent j hj i ij b pb)).trans (tb j hj (lt_trans bl ij)).symm))
  exact ⟨S,fun w => Finset.mem_filter,(bound.trans Finset.card_image_le)⟩

end PEqualNP.Outside.L_meta_1580

namespace PEqualNP.Outside.L_meta_1580.Plane

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1580.Cut

abbrev Pt := Fin 13
def ln (t : Pt) : Finset Pt := {t,t+1,t+3,t+9}
def lefts : Finset Pt := {4,10,12}
def rights : Finset Pt := {1,5,11}
def lbl (t : Pt) : Finset Pt := if t = 0 then {0,1,3} else ln t
def co (t p : Pt) : Bool := decide (p ∉ ln t)
-- The central row uses the two base inputs and the test containing every point off the central line.
def pos (t p v : Pt) : Bool :=
  decide (v = p ∨ (t = 0 ∧ p = 3 ∧ v ∉ ln 0) ∨
    (t ≠ 0 ∧ p ≠ 0 ∧ p ≠ 1 ∧ v = if t ∈ lefts then 1 else 0))
def dom (x : Pt → Bool) : Prop :=
  x 0 = true ∨ x 1 = true ∨ ∀ p, p ∉ ln 0 → x p = true
abbrev Legal (gs : List Gate) := ∀ g ∈ gs,
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
abbrev WF (gs : List Gate) := ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 13+i.val
abbrev OK (gs : List Gate) (o : Pt → ℕ) := ∀ t x, dom x →
  val gs (o t) x = decide (∃ p ∈ ln t, x p = true)
abbrev wire {gs : List Gate} (i : Fin gs.length) := 13+i.val
def hits (gs : List Gate) (t : Pt) (w : ℕ) : Prop := ∃ p ∈ lbl t, val gs w (pos t p) = true
def zero (gs : List Gate) (t : Pt) (w : ℕ) : Prop := val gs w (co t) = false
def active (gs : List Gate) (l m : Pt) (w : ℕ) : Prop :=
  zero gs l w ∧ zero gs m w ∧ hits gs l w ∧ hits gs m w
abbrev merge (gs : List Gate) (t : Pt) (i : Fin gs.length) :=
  Mrg gs (lbl t) (co t) (pos t) i
def source (gs : List Gate) (l m : Pt) (i : Fin gs.length) : Prop :=
  active gs l m (wire i) ∧ ∀ a ∈ (gs.get i).inputs, ¬ active gs l m a

lemma wire_inj {gs : List Gate} : Function.Injective (@wire gs) := by
  intro a b h
  apply Fin.ext
  exact Nat.add_left_cancel h

lemma sep : ∀ (t p : Pt), p ∈ lbl t → ∀ v, pos t p v = true → co t v = false → v = p := by
  decide

lemma hdco : ∀ t, dom (co t) := by unfold dom; decide
lemma hdpos : ∀ t p, p ∈ lbl t → dom (pos t p) := by unfold dom; decide
lemma geomPos : ∀ t p, p ∈ lbl t → ∃ v ∈ ln t, pos t p v = true := by decide
lemma geomMeet : ∀ l ∈ lefts, ∀ m ∈ rights, ∃ c : Pt, ∀ v : Pt, v ∈ ln l → v ∈ ln m → v = c := by decide
lemma geomClass : ∀ l ∈ lefts, ∀ m ∈ rights, l ≠ 0 ∧ m ≠ 0 ∧ l ≠ m := by decide
lemma geomLen : ∀ t : Pt, (lbl t).card = (if t = 0 then 2 else 3) + 1 := by decide

lemma low {gs : List Gate} {o : Pt → ℕ} (h : OK gs o) (t : Pt) : zero gs t (o t) := by
  unfold zero
  rw [h t _ (hdco t)]
  apply decide_eq_false
  rintro ⟨v,ht,hv⟩
  exact (of_decide_eq_true hv) ht

lemma high {gs : List Gate} {o : Pt → ℕ} (h : OK gs o) (t p : Pt) (hm : p ∈ lbl t) :
    val gs (o t) (pos t p) = true := by
  rw [h t _ (hdpos t p hm)]
  exact decide_eq_true (geomPos t p hm)

open Classical in
lemma row_tally (gs : List Gate) (o : Pt → ℕ) (hg : Legal gs) (wf : WF gs) (ok : OK gs o) (t : Pt) :
    (∑ g : Fin gs.length, if merge gs t g then 1 else 0) = (if t = 0 then 2 else 3) := by
  classical
  exact tally gs (lbl t) (co t) (pos t) (sep t) hg wf (geomLen t) (o t) (low ok t) (high ok t)

lemma mono (gs : List Gate) (hg : Legal gs) {x y : Pt → Bool}
    (xy : ∀ v, x v = true → y v = true) (w : ℕ) :
    val gs w x = true → val gs w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < 13
    · simpa only [val_input gs _ w hw] using xy ⟨w,hw⟩
    by_cases valid : w-13 < gs.length
    · let i : Fin gs.length := ⟨w-13,valid⟩
      have eq : w = wire i := by change w = 13+(w-13); omega
      rw [eq]
      rcases (hg _ (List.get_mem gs i)).1 with a | a
      · intro h
        apply (val_and gs y i i.2 a).2
        intro u hu
        obtain ⟨ul,yes⟩ := (val_and gs x i i.2 a).1 h u hu
        exact ⟨ul,ih u (by rw [eq]; exact ul) yes⟩
      · intro h
        obtain ⟨u,hu,ul,yes⟩ := (val_or gs x i i.2 a).1 h
        exact (val_or gs y i i.2 a).2 ⟨u,hu,ul,ih u (by rw [eq]; exact ul) yes⟩
    · rw [val_big gs x w (by omega)]
      simp

def fits (t : Pt) (N : Finset Pt) : Finset Pt :=
  (lbl t).filter fun p => ∀ j ∈ N, ∃ v ∈ ln j, pos t p v = true

lemma fit_of_hit (gs : List Gate) (hg : Legal gs) (w : ℕ) {t p : Pt}
    (hp : p ∈ lbl t) (hit : val gs w (pos t p) = true)
    (N : Finset Pt) (hn : ∀ j ∈ N, zero gs j w) : p ∈ fits t N := by
  refine Finset.mem_filter.mpr ⟨hp,?_⟩
  intro j hj
  by_contra no
  have le (v : Pt) (h : pos t p v = true) : co j v = true :=
    decide_eq_true fun h' => no ⟨v,h',h⟩
  exact Bool.false_ne_true ((hn j hj).symm.trans (mono gs hg le w hit))

lemma geom_left : ∀ l ∈ lefts, ∀ m ∈ rights, ∀ t ∈ lefts, l ≠ t → fits l {m,t} = ∅ := by decide
lemma geom_right : ∀ l ∈ lefts, ∀ m ∈ rights, ∀ t ∈ rights, m ≠ t → fits m {l,t} = ∅ := by decide
lemma geom_others : ∀ l ∈ lefts, ∀ m ∈ rights, ∀ t : Pt, t ∉ lefts → t ∉ rights →
    (fits t {l,m}).card ≤ 1 := by decide
lemma geom_pairs : ∀ t u : Pt, t ≠ 0 → u ≠ 0 → t ≠ u →
    ¬ ((t ∈ lefts ∧ u ∈ rights) ∨ (u ∈ lefts ∧ t ∈ rights)) →
    (fits t {u}).card ≤ 1 ∨ (fits u {t}).card ≤ 1 := by decide
lemma geom_center : ∀ t : Pt, t ≠ 0 → t ∉ lefts → t ∉ rights → (fits 0 {t}).card ≤ 1 := by decide

lemma pair_unique_left (gs : List Gate) (hg : Legal gs) {w : ℕ} {l m t : Pt}
    (hl : l ∈ lefts) (hm : m ∈ rights) (ht : t ∈ lefts)
    (ha : active gs l m w) (hz : zero gs t w) : l = t := by
  by_contra ne
  obtain ⟨p,hp,yes⟩ := ha.2.2.1
  have f := fit_of_hit gs hg w hp yes {m,t} (by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | e
    · exact ha.2.1
    · simp only [Finset.mem_singleton] at e; subst j; exact hz)
  rw [geom_left l hl m hm t ht ne] at f
  exact Finset.notMem_empty p f

lemma pair_unique_right (gs : List Gate) (hg : Legal gs) {w : ℕ} {l m t : Pt}
    (hl : l ∈ lefts) (hm : m ∈ rights) (ht : t ∈ rights)
    (ha : active gs l m w) (hz : zero gs t w) : m = t := by
  by_contra ne
  obtain ⟨p,hp,yes⟩ := ha.2.2.2
  have f := fit_of_hit gs hg w hp yes {l,t} (by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | e
    · exact ha.1
    · simp only [Finset.mem_singleton] at e; subst j; exact hz)
  rw [geom_right l hl m hm t ht ne] at f
  exact Finset.notMem_empty p f

end PEqualNP.Outside.L_meta_1580.Plane

namespace PEqualNP.Outside.L_meta_1580.Plane

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1580.Cut

lemma or_up {gs : List Gate} (wf : WF gs) {i : Fin gs.length} (op : (gs.get i).op = GateOp.or)
    {w : ℕ} (mem : w ∈ (gs.get i).inputs) {x : Pt → Bool} (h : val gs w x = true) :
    val gs (wire i) x = true :=
  (val_or gs x i i.2 op).2 ⟨w,mem,wf i w mem,h⟩

lemma or_down_zero {gs : List Gate} (wf : WF gs) {i : Fin gs.length} (op : (gs.get i).op = GateOp.or)
    {w : ℕ} (mem : w ∈ (gs.get i).inputs) {t : Pt} (z : zero gs t (wire i)) : zero gs t w := by
  cases h : val gs w (co t) with
  | false => exact h
  | true => exact (Bool.false_ne_true (z.symm.trans (or_up wf op mem h))).elim

lemma merge_parent {gs : List Gate} (wf : WF gs) {i : Fin gs.length} {t : Pt} (mg : merge gs t i)
    {v : ℕ} (mem : v ∈ (gs.get i).inputs) : zero gs t v ∧ hits gs t v := by
  obtain ⟨op,z,a,b,e,p,hp,q,hq,va,vb,X,yes,no,hcut⟩ := mg
  refine ⟨or_down_zero wf op mem z,?_⟩
  rw [e] at mem
  rcases List.mem_pair.mp mem with rfl | rfl
  · exact ⟨p,hp,va⟩
  · exact ⟨q,hq,vb⟩

lemma merge_hits {gs : List Gate} (wf : WF gs) {i : Fin gs.length} {t : Pt} (mg : merge gs t i) :
    hits gs t (wire i) := by
  obtain ⟨op,z,a,b,e,p,hp,q,hq,va,vb,_⟩ := mg
  exact ⟨p,hp,or_up wf op (by rw [e]; simp : a ∈ (gs.get i).inputs) va⟩

lemma merge_fits {gs : List Gate} (hg : Legal gs) (wf : WF gs) {i : Fin gs.length} {t : Pt}
    (mg : merge gs t i) (N : Finset Pt) (hn : ∀ j ∈ N, zero gs j (wire i)) :
    2 ≤ (fits t N).card := by
  obtain ⟨op,z,a,b,e,p,hp,q,hq,va,vb,X,yes,no,hcut⟩ := mg
  have p1 := fit_of_hit gs hg (wire i) hp (or_up wf op (by rw [e]; simp : a ∈ (gs.get i).inputs) va) N hn
  have q1 := fit_of_hit gs hg (wire i) hq (or_up wf op (by rw [e]; simp : b ∈ (gs.get i).inputs) vb) N hn
  have ne : p ≠ q := by rintro rfl; exact no yes
  have sub : {p,q} ⊆ fits t N := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact p1
    · rw [Finset.mem_singleton.mp h]
      exact q1
  have le := Finset.card_le_card sub
  simpa only [Finset.card_pair ne] using le

lemma merge_active {gs : List Gate} (wf : WF gs) {i : Fin gs.length} {l m : Pt}
    (hl : merge gs l i) (hm : merge gs m i) : active gs l m (wire i) :=
  ⟨hl.2.1,hm.2.1,merge_hits wf hl,merge_hits wf hm⟩

lemma merge_parent_active {gs : List Gate} (wf : WF gs) {i : Fin gs.length} {l m : Pt}
    (hl : merge gs l i) (hm : merge gs m i) {v : ℕ} (mem : v ∈ (gs.get i).inputs) :
    active gs l m v := by
  obtain ⟨zl,yl⟩ := merge_parent wf hl mem
  obtain ⟨zm,ym⟩ := merge_parent wf hm mem
  exact ⟨zl,zm,yl,ym⟩

lemma class_of_two {gs : List Gate} (hg : Legal gs) (wf : WF gs) {i : Fin gs.length} {t u : Pt}
    (mt : merge gs t i) (mu : merge gs u i) (nt : t ≠ 0) (nu : u ≠ 0) (ne : t ≠ u) :
    (t ∈ lefts ∧ u ∈ rights) ∨ (u ∈ lefts ∧ t ∈ rights) := by
  by_contra no
  have a := merge_fits hg wf mt {u} (fun j hj => (Finset.mem_singleton.mp hj) ▸ mu.2.1)
  have b := merge_fits hg wf mu {t} (fun j hj => (Finset.mem_singleton.mp hj) ▸ mt.2.1)
  rcases geom_pairs t u nt nu ne no with h | h <;> omega

lemma class_of_central {gs : List Gate} (hg : Legal gs) (wf : WF gs) {i : Fin gs.length} {t : Pt}
    (mt : merge gs t i) (mo : merge gs 0 i) (nt : t ≠ 0) : t ∈ lefts ∨ t ∈ rights := by
  by_contra no
  have a := merge_fits hg wf mo {t} (fun j hj => (Finset.mem_singleton.mp hj) ▸ mt.2.1)
  have b := geom_center t nt (fun h => no (Or.inl h)) (fun h => no (Or.inr h))
  omega

lemma active_nomerge_other {gs : List Gate} (hg : Legal gs) (wf : WF gs)
    {i : Fin gs.length} {l m t : Pt} (hl : l ∈ lefts) (hm : m ∈ rights)
    (act : active gs l m (wire i)) (mt : merge gs t i) : t = l ∨ t = m := by
  by_cases tl : t ∈ lefts
  · exact Or.inl (pair_unique_left gs hg hl hm tl act mt.2.1).symm
  by_cases tr : t ∈ rights
  · exact Or.inr (pair_unique_right gs hg hl hm tr act mt.2.1).symm
  have a := merge_fits hg wf mt {l,m} (by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | e
    · exact act.1
    · rw [Finset.mem_singleton.mp e]; exact act.2.1)
  have b := geom_others l hl m hm t tl tr
  omega

-- A source for a pair of lines cannot perform a merge for any line.
lemma source_free {gs : List Gate} (hg : Legal gs) (wf : WF gs) {i : Fin gs.length} {l m : Pt}
    (hl : l ∈ lefts) (hm : m ∈ rights) (s : source gs l m i) : ∀ t, ¬ merge gs t i := by
  intro t mt
  rcases active_nomerge_other hg wf hl hm s.1 mt with rfl | rfl
  · obtain ⟨p,hp,yes⟩ := s.1.2.2.2
    obtain ⟨a,ha,_,fire⟩ := (val_or gs _ i i.2 mt.1).1 yes
    obtain ⟨z,hit⟩ := merge_parent wf mt ha
    exact s.2 a ha ⟨z,or_down_zero wf mt.1 ha s.1.2.1,hit,p,hp,fire⟩
  · obtain ⟨p,hp,yes⟩ := s.1.2.2.1
    obtain ⟨a,ha,_,fire⟩ := (val_or gs _ i i.2 mt.1).1 yes
    obtain ⟨z,hit⟩ := merge_parent wf mt ha
    exact s.2 a ha ⟨or_down_zero wf mt.1 ha s.1.1,z,⟨p,hp,fire⟩,hit⟩

end PEqualNP.Outside.L_meta_1580.Plane

namespace PEqualNP.Outside.L_meta_1580.Norm

open PEqualNP.CircuitLowerBounds

open Classical in
-- An unavailable input reads false. Cleaning preserves that behavior and the gate count.
noncomputable def fixed (n : ℕ) (g : Gate) : Gate :=
  if g.op = GateOp.and ∧ ∃ a ∈ g.inputs, n ≤ a then ⟨GateOp.or,[]⟩
  else ⟨g.op,g.inputs.filter fun a => a < n⟩

noncomputable def clean (n : ℕ) : List Gate → List Gate
  | [] => []
  | g :: tail => fixed n g :: clean (n+1) tail

lemma fixed_bounded (n : ℕ) (g : Gate) : ∀ a ∈ (fixed n g).inputs, a < n := by
  classical
  unfold fixed
  split
  · simp
  · intro a h
    simpa using (List.mem_filter.mp h).2

lemma fixed_legal (n : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((fixed n g).op = GateOp.and ∨ (fixed n g).op = GateOp.or) ∧ (fixed n g).inputs.length ≤ 2 := by
  classical
  unfold fixed
  split
  · simp
  · exact ⟨hg.1,(List.length_filter_le _ _).trans hg.2⟩

lemma clean_length (gs : List Gate) (n : ℕ) : (clean n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g tail ih => simp [clean,ih]

lemma clean_legal (gs : List Gate) (n : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ clean n gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing n with
  | nil => simp [clean]
  | cons g tail ih =>
    intro h hh
    rcases List.mem_cons.mp hh with rfl | ht
    · exact fixed_legal n g (hg g List.mem_cons_self)
    · exact ih (n+1) (fun v hv => hg v (List.mem_cons_of_mem _ hv)) h ht

lemma clean_bounded (gs : List Gate) (n : ℕ) :
    ∀ i : Fin (clean n gs).length, ∀ a ∈ ((clean n gs).get i).inputs, a < n+i.val := by
  induction gs generalizing n with
  | nil => intro i; exact Fin.elim0 i
  | cons g tail ih =>
    intro ⟨i,hi⟩ a ha
    cases i with
    | zero => exact fixed_bounded n g a ha
    | succ j =>
      have hj : j < (clean (n+1) tail).length := Nat.lt_of_succ_lt_succ hi
      have lt := ih (n+1) ⟨j,hj⟩ a ha
      change a < n+1+j at lt
      change a < n+(j+1)
      omega

lemma fixed_eval (g : Gate) (w : List Bool)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (fixed w.length g).op.eval ((fixed w.length g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  classical
  unfold fixed
  split
  · rename_i bad
    obtain ⟨op,a,ha,high⟩ := bad
    rw [op]
    have off : w.getD a false = false := List.getD_eq_default _ _ high
    have zero : (g.inputs.map fun i => w.getD i false).all id = false := by
      apply List.all_eq_false.mpr
      exact ⟨false,List.mem_map.mpr ⟨a,ha,off⟩,by decide⟩
    exact zero.symm
  · rename_i ok
    rcases hg with op | op
    · have allowed (a : ℕ) (ha : a ∈ g.inputs) : a < w.length := by
        by_contra h
        exact ok ⟨op,a,ha,by omega⟩
      have eq : g.inputs.filter (fun a => decide (a < w.length)) = g.inputs :=
        List.filter_eq_self.mpr (fun a ha => decide_eq_true (allowed a ha))
      change g.op.eval ((g.inputs.filter _).map _) = _
      rw [eq]
    · change g.op.eval ((g.inputs.filter _).map _) = _
      rw [op]
      have eqBool (x y : Bool) (same : x = true ↔ y = true) : x = y := by
        cases x <;> cases y <;> simp_all
      apply eqBool
      simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq,List.mem_filter,
        decide_eq_true_eq]
      constructor
      · rintro ⟨a,⟨ha,_⟩,yes⟩
        exact ⟨a,ha,yes⟩
      · rintro ⟨a,ha,yes⟩
        refine ⟨a,⟨ha,?_⟩,yes⟩
        by_contra h
        rw [List.getD_eq_default _ _ (by omega)] at yes
        exact Bool.noConfusion yes

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) w

lemma clean_run (gs : List Gate) (w : List Bool)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    run (clean w.length gs) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g tail ih =>
    let z := g.op.eval (g.inputs.map fun i => w.getD i false)
    change run (clean (w.length+1) tail) (w ++ [(fixed w.length g).op.eval
      ((fixed w.length g).inputs.map fun i => w.getD i false)]) = run tail (w ++ [z])
    rw [fixed_eval g w (h g List.mem_cons_self)]
    have len : (w ++ [z]).length = w.length + 1 := by simp
    rw [← len]
    exact ih (w ++ [z]) (fun g hmem => h g (List.mem_cons_of_mem _ hmem))

end PEqualNP.Outside.L_meta_1580.Norm

namespace PEqualNP.Outside.L_meta_1580.Plane

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1580.Cut

open Classical in
noncomputable def doubles (gs : List Gate) (l m : Pt) : Finset (Fin gs.length) :=
  Finset.univ.filter fun i => merge gs l i ∧ merge gs m i

open Classical in
noncomputable def sources (gs : List Gate) (l m : Pt) : Finset (Fin gs.length) :=
  Finset.univ.filter fun i => source gs l m i

def splitAt (gs : List Gate) (l m : Pt) (w : ℕ) (X : Finset Pt) : Prop :=
  ∃ i : Fin gs.length, wire i = w ∧ Con gs (lbl l) (co l) (pos l) i X ∧
    ∃ a b, (gs.get i).inputs = [a,b] ∧ active gs l m a ∧ active gs l m b ∧
    ∃ p ∈ lbl l, ∃ q ∈ lbl l, val gs a (pos l p) = true ∧ val gs b (pos l q) = true ∧
      p ∈ X ∧ q ∉ X

-- Bound repeated merges of two lines by gates where activity on both lines starts.
lemma pair_bound (gs : List Gate) (hg : Legal gs) (wf : WF gs) (l m : Pt)
    (hl : l ∈ lefts) (hm : m ∈ rights) : (doubles gs l m).card ≤ (sources gs l m).card := by
  classical
  let K := doubles gs l m
  let E := K.image (@wire gs)
  let U := (Finset.range (13+gs.length)).filter (active gs l m)
  let parent (w v : ℕ) := active gs l m w ∧ ∃ i : Fin gs.length, wire i = w ∧ v ∈ (gs.get i).inputs ∧ active gs l m v
  have before : ∀ w v, parent w v → v < w := by
    rintro w v ⟨_,i,rfl,h,_⟩
    exact wf i v h
  have closed : ∀ w ∈ U, ∀ v, parent w v → v ∈ U := by
    intro w hw v edge
    obtain ⟨aw,i,e,hp,act⟩ := edge
    have top := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans (before w v ⟨aw,i,e,hp,act⟩) top),act⟩
  have sp : ∀ w ∈ E, ∃ X, splitAt gs l m w X := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a,b⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨op,zero,a1,a2,ie,r,hr,s,hs,vr,vs,X,rx,sx,hX⟩ := a
    have ha : a1 ∈ (gs.get i).inputs := by rw [ie]; simp
    have hb : a2 ∈ (gs.get i).inputs := by rw [ie]; simp
    have ma : merge gs l i := ⟨op,zero,a1,a2,ie,r,hr,s,hs,vr,vs,X,rx,sx,hX⟩
    exact ⟨X,i,rfl,hX,a1,a2,ie,merge_parent_active wf ma b ha,merge_parent_active wf ma b hb,
      r,hr,s,hs,vr,vs,rx,sx⟩
  let cut (w : ℕ) : Finset Pt := if h : w ∈ E then (sp w h).choose else ∅
  have spec {w : ℕ} (hw : w ∈ E) : splitAt gs l m w (cut w) := by
    simpa only [cut,dite_eq_left hw] using (sp w hw).choose_spec
  let lab (w : ℕ) : Pt := if h : hits gs l w then h.choose else 0
  have lab_ok {w : ℕ} (h : active gs l m w) :
      lab w ∈ lbl l ∧ val gs w (pos l (lab w)) = true := by
    have f := h.2.2.1
    simpa only [lab,dite_eq_left f] using f.choose_spec
  let C (g w : ℕ) : Prop := lab w ∈ cut g
  have same {g w : ℕ} (mg : g ∈ E) (wg : w < g) (z : zero gs l w) {p q : Pt}
      (hp : p ∈ lbl l) (hq : q ∈ lbl l) (vp : val gs w (pos l p) = true)
      (vq : val gs w (pos l q) = true) : p ∈ cut g ↔ q ∈ cut g := by
    obtain ⟨i,eq,con,_⟩ := spec mg
    exact single gs (lbl l) (co l) (pos l) (sep l) hg wf i i.2.le (cut g) con w
      (by change w < wire i; rwa [eq]) z p hp q hq vp vq
  have consistent : ∀ g ∈ E, ∀ w, w < g → ∀ v, parent w v → (C g w ↔ C g v) := by
    intro g mg w wg v edge
    obtain ⟨aw,i,eq,mem,av⟩ := edge
    obtain ⟨lp,lv⟩ := lab_ok aw
    obtain ⟨rp,rv⟩ := lab_ok av
    rcases (hg _ (List.get_mem gs i)).1 with andOp | orOp
    · have vv : val gs v (pos l (lab w)) = true :=
        ((val_and gs _ i i.2 andOp).1 (by simpa only [eq] using lv) v mem).2
      exact same mg (lt_trans (eq ▸ wf i v mem) wg) av.1 lp rp vv rv
    · have vw : val gs w (pos l (lab v)) = true := eq ▸ or_up wf orOp mem rv
      exact same mg wg aw.1 lp rp lv vw
  have marked : ∀ g ∈ E, g ∈ U ∧ ∃ a b, parent g a ∧ parent g b ∧ C g a ∧ ¬ C g b := by
    intro g mg
    obtain ⟨i,eq,hX,a,b,ie,aa,ab,p,hp,q,hq,pa,qb,px,qx⟩ := spec mg
    obtain ⟨j,hj,ej⟩ := Finset.mem_image.mp mg
    obtain ⟨mj1,mj2⟩ := (Finset.mem_filter.mp hj).2
    have ag : active gs l m g := ej ▸ merge_active wf mj1 mj2
    have top : g < 13+gs.length := by rw [← eq]; exact Nat.add_lt_add_left i.2 13
    have ma : a ∈ (gs.get i).inputs := by rw [ie]; simp
    have mb : b ∈ (gs.get i).inputs := by rw [ie]; simp
    have ca := same mg (eq ▸ wf i a ma) aa.1 (lab_ok aa).1 hp (lab_ok aa).2 pa
    have cb := same mg (eq ▸ wf i b mb) ab.1 (lab_ok ab).1 hq (lab_ok ab).2 qb
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr top,ag⟩,a,b,⟨ag,i,eq,ma,aa⟩,
      ⟨ag,i,eq,mb,ab⟩,ca.mpr px,fun h => qx (cb.mp h)⟩
  by_cases ne : E.Nonempty
  · obtain ⟨w,hw⟩ := ne
    obtain ⟨S,hS,rank⟩ := PEqualNP.Outside.L_meta_1580.count_sources U E parent C
      ⟨w,(marked w hw).1⟩ before closed consistent marked
    obtain ⟨c,hc⟩ := geomMeet l hl m hm
    have sub : S ⊆ insert c.val ((sources gs l m).image (@wire gs)) := by
      intro v hv
      obtain ⟨uv,no⟩ := (hS v).1 hv
      obtain ⟨vr,av⟩ := Finset.mem_filter.mp uv
      have top := Finset.mem_range.mp vr
      by_cases lo : v < 13
      · let p : Pt := ⟨v,lo⟩
        have a : p ∈ ln l := by have h := av.1; change val gs v (co l) = false at h; simpa [val_input gs _ v lo,co,p] using h
        have b : p ∈ ln m := by have h := av.2.1; change val gs v (co m) = false at h; simpa [val_input gs _ v lo,co,p] using h
        exact Finset.mem_insert.mpr (Or.inl (congrArg Fin.val (hc p a b)))
      · have ix : v-13 < gs.length := by omega
        let i : Fin gs.length := ⟨v-13,ix⟩
        have eq : wire i = v := by change 13+(v-13) = v; omega
        have si : source gs l m i := ⟨eq.symm ▸ av,fun a ha hp => no ⟨a,av,i,eq,ha,hp⟩⟩
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,si⟩,eq⟩))
    have sz := Finset.card_le_card sub
    have cap := Finset.card_insert_le c.val ((sources gs l m).image (@wire gs))
    have big := Finset.card_image_le (s := sources gs l m) (f := @wire gs)
    have ecard : E.card = K.card := Finset.card_image_of_injective _ wire_inj
    change K.card ≤ _
    omega
  · have empty : K = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      exact fun i hi => ne ⟨wire i,Finset.mem_image_of_mem _ hi⟩
    change K.card ≤ _
    simp [empty]

end PEqualNP.Outside.L_meta_1580.Plane

namespace PEqualNP.Outside.L_meta_1580.Plane

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1580.Cut

lemma rim_pair : ∀ t : Pt, t ≠ 0 → ∀ p ∈ fits 0 {t}, ∀ q ∈ fits 0 {t},
    p ≠ q → p = 3 ∨ q = 3 := by decide

lemma rim_raw : ∀ t ∈ lefts ∪ rights, ∀ v : Pt,
    co 0 v = false → co t v = false → pos 0 3 v = false := by decide

lemma coline_hits_center : ∀ t : Pt, t ≠ 0 → ∃ v ∈ ln 0, co t v = true := by decide
lemma distinct_rays : ∀ p : Pt, ¬ (pos 0 0 p = true ∧ pos 0 1 p = true) := by decide
lemma pencils_nonzero : ∀ t ∈ lefts ∪ rights, t ≠ (0 : Pt) := by decide

def rimWire (gs : List Gate) (w : ℕ) : Prop :=
  zero gs 0 w ∧ (∃ t ∈ lefts ∪ rights, zero gs t w) ∧ val gs w (pos 0 3) = true

lemma shared_rim {gs : List Gate} (hg : Legal gs) (wf : WF gs) {i : Fin gs.length} {t : Pt}
    (nt : t ≠ 0) (mo : merge gs 0 i) (mt : merge gs t i) : rimWire gs (wire i) := by
  have side := class_of_central hg wf mt mo nt
  obtain ⟨op,z,a,b,e,p,hp,q,hq,va,vb,X,yes,no,xc⟩ := mo
  have pa := or_up wf op (by rw [e]; simp : a ∈ (gs.get i).inputs) va
  have qb := or_up wf op (by rw [e]; simp : b ∈ (gs.get i).inputs) vb
  have nz (j : Pt) (hj : j ∈ ({t} : Finset Pt)) : zero gs j (wire i) := by
    rw [Finset.mem_singleton.mp hj]; exact mt.2.1
  have fp := fit_of_hit gs hg (wire i) hp pa {t} nz
  have fq := fit_of_hit gs hg (wire i) hq qb {t} nz
  have ne : p ≠ q := by rintro rfl; exact no yes
  refine ⟨z,⟨t,Finset.mem_union.mpr side,mt.2.1⟩,?_⟩
  rcases rim_pair t nt p fp q fq ne with rfl | rfl
  · exact pa
  · exact qb

lemma and_zero_parent {gs : List Gate} (wf : WF gs) {i : Fin gs.length}
    (op : (gs.get i).op = GateOp.and) {t : Pt} (z : zero gs t (wire i)) :
    ∃ a ∈ (gs.get i).inputs, zero gs t a := by
  by_contra no
  have h : val gs (wire i) (co t) = true := (val_and gs _ i i.2 op).2 (by
    intro a ha
    refine ⟨wf i a ha,?_⟩
    cases o : val gs a (co t) with
    | true => rfl
    | false => exact (no ⟨a,ha,o⟩).elim)
  exact Bool.false_ne_true (z.symm.trans h)

lemma three_inputs (xs : List ℕ) (h : xs.length ≤ 2) (a b c : ℕ)
    (ha : a ∈ xs) (hb : b ∈ xs) (hc : c ∈ xs) : a = b ∨ a = c ∨ b = c := by
  rcases xs with _ | ⟨v,_ | ⟨w,_ | ⟨k,t⟩⟩⟩
  · simp at ha
  · simp at ha hb hc
    omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb hc
    omega
  · simp at h

-- The earliest wire that fires on the third central test while vanishing on two complements is an AND.
lemma spare_and (gs : List Gate) (hg : Legal gs) (wf : WF gs)
    (someRim : ∃ w, rimWire gs w) :
    ∃ i : Fin gs.length, (gs.get i).op = GateOp.and ∧
      (∃ t ∈ lefts ∪ rights, zero gs t (wire i)) ∧
      ∀ l ∈ lefts, ∀ m ∈ rights, ¬ source gs l m i := by
  classical
  let w := Nat.find someRim
  obtain ⟨z0,⟨t,ht,zt⟩,fire⟩ := Nat.find_spec someRim
  have prior (u : ℕ) (lt : u < w) : ¬ rimWire gs u := Nat.find_min someRim lt
  have lo : 13 ≤ w := by
    by_contra! raw
    have e0 := (val_input gs (co 0) w raw).symm.trans z0
    have et := (val_input gs (co t) w raw).symm.trans zt
    have yes := (val_input gs (pos 0 3) w raw).symm.trans fire
    exact Bool.false_ne_true ((rim_raw t ht ⟨w,raw⟩ e0 et).symm.trans yes)
  have top : w < 13+gs.length := by
    by_contra h
    have no := val_big gs (pos 0 3) w (by omega)
    exact Bool.false_ne_true (no.symm.trans fire)
  let i : Fin gs.length := ⟨w-13,by omega⟩
  have ei : wire i = w := by change 13+(w-13) = w; omega
  have z0i : zero gs 0 (wire i) := ei.symm ▸ z0
  have zti : zero gs t (wire i) := ei.symm ▸ zt
  have yesi : val gs (wire i) (pos 0 3) = true := ei.symm ▸ fire
  rcases (hg _ (List.get_mem gs i)).1 with op | op
  · refine ⟨i,op,⟨t,ht,zti⟩,?_⟩
    intro l hl m hm src
    obtain ⟨a,ha,za⟩ := and_zero_parent wf op z0i
    obtain ⟨b,hb,zb⟩ := and_zero_parent wf op src.1.1
    obtain ⟨c,hc,zc⟩ := and_zero_parent wf op src.1.2.1
    have af := ((val_and gs _ i i.2 op).1 yesi a ha).2
    have alt : a < w := ei ▸ wf i a ha
    have nb : a ≠ b := by
      rintro rfl
      exact prior a alt ⟨za,⟨l,Finset.mem_union_left _ hl,zb⟩,af⟩
    have nc : a ≠ c := by
      rintro rfl
      exact prior a alt ⟨za,⟨m,Finset.mem_union_right _ hm,zc⟩,af⟩
    have bc := ((three_inputs _ (hg _ (List.get_mem gs i)).2 a b c ha hb hc).resolve_left nb).resolve_left nc
    subst c
    obtain ⟨p,hp,vp⟩ := src.1.2.2.1
    obtain ⟨q,hq,vq⟩ := src.1.2.2.2
    exact src.2 b hb ⟨zb,zc,⟨p,hp,((val_and gs _ i i.2 op).1 vp b hb).2⟩,
      ⟨q,hq,((val_and gs _ i i.2 op).1 vq b hb).2⟩⟩
  · obtain ⟨a,ha,_,af⟩ := (val_or gs _ i i.2 op).1 yesi
    exact (prior a (ei ▸ wf i a ha) ⟨or_down_zero wf op ha z0i,
      ⟨t,ht,or_down_zero wf op ha zti⟩,af⟩).elim

lemma central_output (gs : List Gate) (o : Pt → ℕ) (right : OK gs o) :
    ∃ i : Fin gs.length, wire i = o 0 ∧ ∀ t : Pt, t ≠ 0 → ¬ zero gs t (wire i) := by
  have y0 := high right 0 0 (by decide)
  have y1 := high right 0 1 (by decide)
  have lo : 13 ≤ o 0 := by
    by_contra! lt
    exact distinct_rays ⟨o 0,lt⟩ ⟨(val_input gs _ _ lt).symm.trans y0,
      (val_input gs _ _ lt).symm.trans y1⟩
  have hi : o 0 < 13+gs.length := by
    by_contra h
    exact Bool.false_ne_true ((val_big gs _ (o 0) (by omega)).symm.trans y0)
  let i : Fin gs.length := ⟨o 0-13,by omega⟩
  have e : wire i = o 0 := by change 13+(o 0-13) = o 0; omega
  refine ⟨i,e,?_⟩
  intro t ne z
  have y : val gs (o 0) (co t) = true := by
    rw [right 0 _ (hdco t)]
    exact decide_eq_true (coline_hits_center t ne)
  exact Bool.false_ne_true (z.symm.trans (e.symm ▸ y))

end PEqualNP.Outside.L_meta_1580.Plane

namespace PEqualNP.Outside.L_meta_1580.Plane

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1580.Cut

open Classical in
noncomputable def rows (gs : List Gate) (i : Fin gs.length) : Finset Pt :=
  Finset.univ.filter fun t => merge gs t i

lemma in_rows {gs : List Gate} {i : Fin gs.length} {t : Pt} : t ∈ rows gs i ↔ merge gs t i := by
  classical
  simp only [rows, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev crossRows (R : Finset Pt) :=
  ∃ l ∈ lefts, ∃ m ∈ rights, l ∈ R ∧ m ∈ R

abbrev centerRows (R : Finset Pt) :=
  (0 : Pt) ∈ R ∧ ∃ t ∈ R, t ≠ 0

def balance (R : Finset Pt) : Prop :=
  R.card + (if R = ∅ then 1 else 0) = 1 + (if crossRows R then 1 else 0) +
    (if centerRows R then 1 else 0)

lemma balance_empty : balance ∅ := by unfold balance; decide
lemma balance_one : ∀ t : Pt, balance {t} := by unfold balance; decide
lemma balance_pair : ∀ l ∈ lefts, ∀ m ∈ rights, balance {l,m} := by unfold balance; decide
lemma balance_center : ∀ t : Pt, t ≠ 0 → balance {0,t} := by unfold balance; decide

lemma balance_rows (gs : List Gate) (hg : Legal gs) (wf : WF gs) (i : Fin gs.length) :
    balance (rows gs i) := by
  classical
  by_cases cross : crossRows (rows gs i)
  · obtain ⟨l,hl,m,hm,ml,mm⟩ := cross
    have act := merge_active wf (in_rows.mp ml) (in_rows.mp mm)
    have eq : rows gs i = {l,m} := by
      ext t
      constructor
      · intro ht
        rcases active_nomerge_other hg wf hl hm act (in_rows.mp ht) with rfl | rfl <;> simp
      · intro ht
        rcases Finset.mem_insert.mp ht with rfl | e
        · exact ml
        · rw [Finset.mem_singleton.mp e]; exact mm
    rw [eq]
    exact balance_pair l hl m hm
  · have unique {t u : Pt} (ht : t ∈ rows gs i) (hu : u ∈ rows gs i) (nt : t ≠ 0) (nu : u ≠ 0) : t = u := by
      by_contra ne
      rcases class_of_two hg wf (in_rows.mp ht) (in_rows.mp hu) nt nu ne with h | h
      · exact cross ⟨t,h.1,u,h.2,ht,hu⟩
      · exact cross ⟨u,h.1,t,h.2,hu,ht⟩
    by_cases has : ∃ t ∈ rows gs i, t ≠ 0
    · obtain ⟨t,ht,nt⟩ := has
      by_cases hz : 0 ∈ rows gs i
      · have eq : rows gs i = {0,t} := by
          ext u
          constructor
          · intro hu
            by_cases e : u = 0
            · simp [e]
            · simp [unique hu ht e nt]
          · intro hu
            rcases Finset.mem_insert.mp hu with rfl | e
            · exact hz
            · rw [Finset.mem_singleton.mp e]; exact ht
        rw [eq]; exact balance_center t nt
      · have eq : rows gs i = {t} := by
          ext u
          constructor
          · intro hu
            exact Finset.mem_singleton.mpr (unique hu ht (fun e => hz (e ▸ hu)) nt)
          · intro hu; rw [Finset.mem_singleton.mp hu]; exact ht
        rw [eq]; exact balance_one t
    · by_cases hz : 0 ∈ rows gs i
      · have eq : rows gs i = {0} := by
          ext u
          constructor
          · intro hu
            apply Finset.mem_singleton.mpr; by_contra e
            exact has ⟨u,hu,e⟩
          · intro hu; rw [Finset.mem_singleton.mp hu]; exact hz
        rw [eq]; exact balance_one 0
      · have eq : rows gs i = ∅ := Finset.eq_empty_of_forall_notMem fun u hu =>
          has ⟨u,hu,fun e => hz (e ▸ hu)⟩
        rw [eq]; exact balance_empty

open Classical in
noncomputable def idle (gs : List Gate) : Finset (Fin gs.length) :=
  Finset.univ.filter fun i => rows gs i = ∅

open Classical in
noncomputable def bothSides (gs : List Gate) : Finset (Fin gs.length) :=
  Finset.univ.filter fun i => crossRows (rows gs i)

open Classical in
noncomputable def withCenter (gs : List Gate) : Finset (Fin gs.length) :=
  Finset.univ.filter fun i => centerRows (rows gs i)

open Classical in
noncomputable def centerVotes (gs : List Gate) : Finset (Fin gs.length) :=
  Finset.univ.filter fun i => merge gs 0 i

lemma sumFilter {α : Type*} [Fintype α] (Q : α → Prop) [DecidablePred Q] :
    (∑ i : α, if Q i then (1 : ℕ) else 0) = (Finset.univ.filter Q).card :=
  Finset.sum_boole Q Finset.univ

-- Count the same incidences by lines and by gates.
lemma total_balance (gs : List Gate) (o : Pt → ℕ) (hg : Legal gs) (wf : WF gs) (ok : OK gs o) :
    38 + (idle gs).card = gs.length + (bothSides gs).card + (withCenter gs).card := by
  classical
  have tally38 : (∑ i : Fin gs.length, (rows gs i).card) = 38 := by
    calc
      _ = ∑ i : Fin gs.length, ∑ t : Pt, if merge gs t i then 1 else 0 :=
        Finset.sum_congr rfl fun i _ => (sumFilter fun t => merge gs t i).symm
      _ = ∑ t : Pt, ∑ i : Fin gs.length, if merge gs t i then 1 else 0 := Finset.sum_comm
      _ = ∑ t : Pt, (if t = 0 then 2 else 3 : ℕ) := Finset.sum_congr rfl fun t _ => row_tally gs o hg wf ok t
      _ = 38 := by decide
  have eq := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin gs.length)) = Finset.univ)
    (fun i _ => (balance_rows gs hg wf i : balance (rows gs i)))
  change (∑ i : Fin gs.length, ((rows gs i).card + (if rows gs i = ∅ then 1 else 0))) =
    ∑ i : Fin gs.length, (1 + (if crossRows (rows gs i) then 1 else 0) + (if centerRows (rows gs i) then 1 else 0)) at eq
  simp only [Finset.sum_add_distrib,tally38,Finset.sum_boole,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at eq
  simpa only [idle,bothSides,withCenter,Nat.cast_id] using eq

lemma count_center (gs : List Gate) (o : Pt → ℕ) (hg : Legal gs) (wf : WF gs) (ok : OK gs o) :
    (centerVotes gs).card = 2 := by
  classical
  have eq := row_tally gs o hg wf ok 0
  rw [sumFilter] at eq
  simpa [centerVotes] using eq

lemma withCenter_sub (gs : List Gate) : withCenter gs ⊆ centerVotes gs := by
  classical
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,in_rows.mp (Finset.mem_filter.mp hi).2.1⟩

end PEqualNP.Outside.L_meta_1580.Plane

namespace PEqualNP.Outside.L_meta_1580.Plane

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1580.Cut

def pencils : Finset (Pt × Pt) := lefts.product rights

open Classical in
noncomputable def allSources (gs : List Gate) : Finset (Fin gs.length) :=
  pencils.biUnion fun t => sources gs t.1 t.2

lemma same_pair (gs : List Gate) (hg : Legal gs) (w : ℕ) {p q : Pt × Pt}
    (hp : p ∈ pencils) (hq : q ∈ pencils) (a : active gs p.1 p.2 w) (b : active gs q.1 q.2 w) :
    p = q := by
  obtain ⟨pl,pr⟩ := Finset.mem_product.mp hp
  obtain ⟨ql,qr⟩ := Finset.mem_product.mp hq
  exact Prod.ext (pair_unique_left gs hg pl pr ql a b.1) (pair_unique_right gs hg pl pr qr a b.2.1)

lemma both_le_sources (gs : List Gate) (hg : Legal gs) (wf : WF gs) :
    (bothSides gs).card ≤ (allSources gs).card := by
  classical
  let K (p : Pt × Pt) := doubles gs p.1 p.2
  let S (p : Pt × Pt) := sources gs p.1 p.2
  have eq : bothSides gs = pencils.biUnion K := by
    ext i
    constructor
    · intro h
      obtain ⟨l,hl,m,hm,ml,mm⟩ := (Finset.mem_filter.mp h).2
      exact Finset.mem_biUnion.mpr ⟨(l,m),Finset.mem_product.mpr ⟨hl,hm⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,in_rows.mp ml,in_rows.mp mm⟩⟩
    · intro h
      obtain ⟨⟨l,m⟩,pr,hi⟩ := Finset.mem_biUnion.mp h
      obtain ⟨hl,hm⟩ := Finset.mem_product.mp pr
      obtain ⟨ml,mm⟩ := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,l,hl,m,hm,in_rows.mpr ml,in_rows.mpr mm⟩
  have dis (p : Pt × Pt) (hp : p ∈ pencils) (q : Pt × Pt) (hq : q ∈ pencils) (ne : p ≠ q) :
      Disjoint (S p) (S q) := by
    apply Finset.disjoint_left.mpr
    intro i ih jh
    exact ne (same_pair gs hg (wire i) hp hq (Finset.mem_filter.mp ih).2.1 (Finset.mem_filter.mp jh).2.1)
  rw [eq]
  calc
    _ ≤ ∑ p ∈ pencils, (K p).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ pencils, (S p).card :=
      Finset.sum_le_sum fun p hp => pair_bound gs hg wf p.1 p.2
        (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
    _ = (pencils.biUnion S).card := (Finset.card_biUnion dis).symm

lemma allSources_idle (gs : List Gate) (hg : Legal gs) (wf : WF gs) : allSources gs ⊆ idle gs := by
  classical
  intro i hi
  obtain ⟨p,hp,s⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨pl,pr⟩ := Finset.mem_product.mp hp
  have all := source_free hg wf pl pr (Finset.mem_filter.mp s).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.eq_empty_of_forall_notMem
    (fun t ht => all t (in_rows.mp ht))⟩

lemma noSources {gs : List Gate} {i : Fin gs.length}
    (h : ∀ l ∈ lefts, ∀ m ∈ rights, ¬ source gs l m i) : i ∉ allSources gs := by
  classical
  intro hi
  obtain ⟨p,hp,s⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨pl,pr⟩ := Finset.mem_product.mp hp
  exact h p.1 pl p.2 pr (Finset.mem_filter.mp s).2

-- Pair sources and the spare central gates account for every merge counted twice.
lemma full (gs : List Gate) (o : Pt → ℕ) (hg : Legal gs) (wf : WF gs) (ok : OK gs o) :
    38 ≤ gs.length := by
  classical
  have budget := total_balance gs o hg wf ok
  have LR := both_le_sources gs hg wf
  have incl := allSources_idle gs hg wf
  have easy := Finset.card_le_card incl
  have votes := count_center gs o hg wf ok
  have sub := withCenter_sub gs
  have lim := Finset.card_le_card sub
  rcases (withCenter gs).eq_empty_or_nonempty with none | some
  · rw [none,Finset.card_empty] at budget
    omega
  · obtain ⟨i,hi⟩ := some
    obtain ⟨z,⟨t,mt,nz⟩⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨a,op,other,unused⟩ := spare_and gs hg wf
      ⟨wire i,shared_rim hg wf nz (in_rows.mp z) (in_rows.mp mt)⟩
    have an : a ∉ allSources gs := noSources unused
    have ai : a ∈ idle gs := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ a, Finset.eq_empty_of_forall_notMem ?_⟩
      intro t ht
      have bad := (in_rows.mp ht).1
      rw [op] at bad
      contradiction
    have incl1 : insert a (allSources gs) ⊆ idle gs := Finset.insert_subset ai incl
    have n1 := Finset.card_le_card incl1
    rw [Finset.card_insert_of_notMem an] at n1
    by_cases both : (withCenter gs).card = 2
    · have all : withCenter gs = centerVotes gs := Finset.eq_of_subset_of_card_le sub (by omega)
      obtain ⟨b,_,zeroOnly⟩ := central_output gs o ok
      have noOther (t : Pt) (nt : t ≠ 0) (ht : t ∈ rows gs b) : False :=
        zeroOnly t nt (in_rows.mp ht).2.1
      have noRow : rows gs b = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro t ht
        by_cases e : t = 0
        · subst t
          have fb : b ∈ centerVotes gs := Finset.mem_filter.mpr ⟨Finset.mem_univ _,in_rows.mp ht⟩
          rw [← all] at fb
          obtain ⟨u,hu,ne⟩ := (Finset.mem_filter.mp fb).2.2
          exact noOther u ne hu
        · exact noOther t e ht
      have bi : b ∈ idle gs := Finset.mem_filter.mpr ⟨Finset.mem_univ b,noRow⟩
      have bn : b ∉ allSources gs := noSources (by
        intro l hl m hm s
        exact zeroOnly l (geomClass l hl m hm).1 s.1.1)
      have ba : b ≠ a := by
        rintro rfl
        obtain ⟨t,ts,zt⟩ := other
        exact zeroOnly t (pencils_nonzero t ts) zt
      have notin : b ∉ insert a (allSources gs) := by simp [ba,bn]
      have incl2 := Finset.insert_subset bi incl1
      have n2 := Finset.card_le_card incl2
      rw [Finset.card_insert_of_notMem notin,Finset.card_insert_of_notMem an] at n2
      omega
    · omega

end PEqualNP.Outside.L_meta_1580.Plane

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1580

theorem PEqualNP.Outside.L_meta_1580 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    38 ≤ gates.length := by
  intro L hl gs o legal correct
  have el : L = Plane.ln := funext hl
  subst L
  let ns := Norm.clean 13 gs
  have nleg : Plane.Legal ns := Norm.clean_legal gs 13 legal
  have wf : Plane.WF ns := Norm.clean_bounded gs 13
  have ok : Plane.OK ns o := by
    intro t x hx
    have same := Norm.clean_run gs (List.ofFn x) (fun g h => (legal g h).1)
    rw [List.length_ofFn] at same
    change (Norm.run ns (List.ofFn x)).getD (o t) false = _
    rw [show Norm.run ns (List.ofFn x) = Norm.run gs (List.ofFn x) from same]
    exact correct t x hx
  simpa only [ns,Norm.clean_length] using Plane.full ns o nleg wf ok
