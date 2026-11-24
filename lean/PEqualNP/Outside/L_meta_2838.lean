import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2838
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
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
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
    · rw [val_input gates _ w hwn] at h1 h2
      have e1 := hτ y hy _ h1
      have e2 := hτ y' hy' _ h2
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
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
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
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
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
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
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
      rw [if_neg hnm, Nat.mul_one]
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
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
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
        = (P gates M c τ k).card := step gates M c τ hτ legal hin ⟨k, hk'⟩
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
theorem mcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = M.card - 1 := by
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
      have hs := single gates M c τ hτ legal hin gates.length le_rfl X hX o holt hoc
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
  have hcnt := count gates M c τ hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

theorem disj {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (L1 L2 A1 A2 : Finset (Fin n)) (hA : A1 ⊆ L1) (hcard : (L1 ∩ L2).card ≤ 1)
    (g : Fin gates.length)
    (h1 : Mrg gates A1 (fun v => decide (v ∉ L1)) (fun y v => decide (v = y)) g)
    (h2 : Mrg gates A2 (fun v => decide (v ∉ L2)) (fun y v => decide (v = y)) g) : False := by
  obtain ⟨ho, _, w1, w2, hab, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := h1
  obtain ⟨_, hc2, _⟩ := h2
  have hne : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have hm1 : w1 ∈ (gates.get g).inputs := by rw [hab]; simp
  have hm2 : w2 ∈ (gates.get g).inputs := by rw [hab]; simp
  have ht1 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r)) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w1, hm1, hin g w1 hm1, hv1⟩
  have ht2 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r')) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w2, hm2, hin g w2 hm2, hv2⟩
  have key : ∀ s : Fin n, val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = s)) = true →
      s ∈ L2 := by
    intro s hs
    by_contra hns
    have hmo := val_mono gates legal (fun v : Fin n => decide (v = s))
      (fun v : Fin n => decide (v ∉ L2)) (by
        intro v hv
        have e : v = s := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hns) _ hs
    rw [hc2] at hmo
    exact Bool.noConfusion hmo
  have hr2 := key r ht1
  have hr2' := key r' ht2
  have hsub : ({r, r'} : Finset (Fin n)) ⊆ L1 ∩ L2 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with e | e
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr, hr2⟩
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr', hr2'⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hc
  omega

def MJ {n m : ℕ} (gates : List Gate) (L A : Fin m → Finset (Fin n)) (j : Fin m)
    (g : Fin gates.length) : Prop :=
  Mrg gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y)) g

open Classical in
theorem main (n m : ℕ) (L A : Fin m → Finset (Fin n)) (gates : List Gate) (o : Fin m → ℕ)
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hA : ∀ j : Fin m, A j ⊆ L j)
    (hot : ∀ (j : Fin m) (p : Fin n), p ∈ A j →
      val gates (o j) (fun i : Fin n => decide (i = p)) = true)
    (hoc : ∀ j : Fin m, val gates (o j) (fun i : Fin n => decide (i ∉ L j)) = false) :
    ∑ j : Fin m, ((A j).card - 1) ≤ gates.length := by
  have h1 : ∀ j : Fin m, (A j).card - 1 ≤
      ∑ g : Fin gates.length, (if MJ gates L A j g then (1 : ℕ) else 0) := by
    intro j
    by_cases hc : 1 ≤ (A j).card
    · exact le_of_eq (mcount gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y))
        (fun p _ v hv => of_decide_eq_true hv) legal hin hc (o j) (hoc j)
        (fun p hp => hot j p hp)).symm
    · have hz : (A j).card - 1 = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  have h2 : ∀ g : Fin gates.length,
      (∑ j : Fin m, (if MJ gates L A j g then (1 : ℕ) else 0)) ≤ 1 := by
    intro g
    by_cases hex : ∃ j0 : Fin m, MJ gates L A j0 g
    · obtain ⟨j0, hj0⟩ := hex
      have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) ≤ (if j = j0 then (1 : ℕ) else 0) := by
        intro j _
        by_cases hj : MJ gates L A j g
        · have e : j = j0 := by
            by_contra hne
            exact disj gates legal hin (L j) (L j0) (A j) (A j0) (hA j) (hL j j0 hne) g hj hj0
          rw [if_pos hj, if_pos e]
        · rw [if_neg hj]
          exact Nat.zero_le _
      refine (Finset.sum_le_sum hle).trans ?_
      simp
    · have hz : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) = 0 :=
        fun j _ => if_neg (fun h => hex ⟨j, h⟩)
      rw [Finset.sum_eq_zero hz]
      exact Nat.zero_le _
  calc ∑ j : Fin m, ((A j).card - 1)
      ≤ ∑ j : Fin m, ∑ g : Fin gates.length, (if MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = ∑ g : Fin gates.length, ∑ j : Fin m, (if MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _g : Fin gates.length, 1 := Finset.sum_le_sum (fun g _ => h2 g)
    _ = gates.length := by simp

theorem bridge (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : Circuit) (o : Fin m → ℕ)
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (hmono : PEqualNP.MetaComplexity.Monotone2 D)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n D)
    (hA : ∀ j : Fin m, A j ⊆ L j)
    (hot : ∀ (j : Fin m) (p : Fin n), p ∈ A j →
      (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true)
    (hoc : ∀ j : Fin m,
      (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) :
    ∑ j : Fin m, ((A j).card - 1) ≤ D.size := by
  have legal : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hin : ∀ i : Fin D.gates.length, ∀ a ∈ (D.gates.get i).inputs, a < n + (i : ℕ) := by
    intro i a ha
    apply hrb i i.2 a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ i.2]
    exact ha
  exact main n m L A D.gates o hL legal hin hA hot hoc


theorem gval (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hin : ∀ i ∈ gs[k].inputs, i < n + k) :
    val gs (n + k) x = gs[k].op.eval (gs[k].inputs.map fun i => val gs i x) := by
  have := gate_val gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [val, wire_take gs (List.ofFn x) k i (by simpa using hin i hi) (Nat.le_of_lt hk)]

theorem val_app (H X : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n + H.length) :
    val (H ++ X) i x = val H i x := by
  unfold val
  exact wf_prefix H X _ i (by simpa using hi)

def rm (n : ℕ) (zf : ℕ → Bool) (i : ℕ) : ℕ := if i < n then (if zf i = true then n else i) else i + 1

def rmG (n : ℕ) (zf : ℕ → Bool) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rm n zf)⟩

def base (n : ℕ) (zf : ℕ → Bool) (gs : List Gate) : List Gate :=
  ⟨GateOp.or, []⟩ :: gs.map (rmG n zf)

def zr {n : ℕ} (zf : ℕ → Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if zf i.val = true then false else x i

theorem base_len (n : ℕ) (zf : ℕ → Bool) (gs : List Gate) :
    (base n zf gs).length = gs.length + 1 := by simp [base]

theorem base_const (n : ℕ) (zf : ℕ → Bool) (gs : List Gate) (x : Fin n → Bool) :
    val (base n zf gs) n x = false := by
  have := gval (base n zf gs) x 0 (by simp [base]) (by simp [base])
  rw [Nat.add_zero] at this
  rw [this]
  simp [base, GateOp.eval]

theorem base_sem (n : ℕ) (zf : ℕ → Bool) (gs : List Gate)
    (hrb : ∀ k (hk : k < gs.length), ∀ i ∈ gs[k].inputs, i < n + k)
    (x : Fin n → Bool) : ∀ i, i < n + gs.length →
      val (base n zf gs) (rm n zf i) x = val gs i (zr zf x) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hin : i < n
    · by_cases hz : zf i = true
      · have e : rm n zf i = n := by simp [rm, hin, hz]
        rw [e, base_const, val_input gs _ i hin]
        simp [zr, hz]
      · have e : rm n zf i = i := by simp [rm, hin, hz]
        rw [e, val_input _ _ i hin, val_input _ _ i hin]
        simp [zr, hz]
    · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      have hk : k < gs.length := by omega
      have e1 : rm n zf (n + k) = n + (k + 1) := by simp [rm]; omega
      rw [e1]
      have hk' : k + 1 < (base n zf gs).length := by simp [base]; omega
      have hg : (base n zf gs)[k + 1] = rmG n zf gs[k] := by simp [base]
      have hin2 : ∀ j ∈ (base n zf gs)[k + 1].inputs, j < n + (k + 1) := by
        rw [hg]
        intro j hj
        simp only [rmG, List.mem_map] at hj
        obtain ⟨i', hi', rfl⟩ := hj
        have := hrb k hk i' hi'
        unfold rm
        split_ifs <;> omega
      rw [gval (base n zf gs) x (k + 1) hk' hin2, gval gs (zr zf x) k hk (hrb k hk), hg]
      simp only [rmG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      have := hrb k hk j hj
      exact ih j (by omega) (by omega)

def chG (b acc : ℕ) : List ℕ → List Gate
  | [] => []
  | w :: ws => ⟨GateOp.or, [acc, w]⟩ :: chG (b + 1) b ws

def chO (b acc : ℕ) : List ℕ → ℕ
  | [] => acc
  | _ :: ws => chO (b + 1) b ws

theorem chG_len (ws : List ℕ) : ∀ b acc : ℕ, (chG b acc ws).length = ws.length := by
  induction ws with
  | nil => intro b acc; rfl
  | cons w ws ih => intro b acc; simp [chG, ih]

theorem chO_lt (ws : List ℕ) : ∀ b acc : ℕ, acc < b → chO b acc ws < b + ws.length := by
  induction ws with
  | nil => intro b acc h; simpa [chO] using h
  | cons w ws ih =>
    intro b acc _
    have := ih (b + 1) b (by omega)
    simp only [chO, List.length_cons]
    omega

theorem any_congr_lt (ws : List ℕ) (f g : ℕ → Bool) (B : ℕ) (hw : ∀ w ∈ ws, w < B)
    (h : ∀ v, v < B → f v = g v) : ws.any f = ws.any g := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨v, hv1, hv2⟩
    exact ⟨v, hv1, by rw [← h v (hw v hv1)]; exact hv2⟩
  · rintro ⟨v, hv1, hv2⟩
    exact ⟨v, hv1, by rw [h v (hw v hv1)]; exact hv2⟩

theorem ch_sem {n : ℕ} (ws : List ℕ) : ∀ (H : List Gate) (acc : ℕ) (x : Fin n → Bool),
    acc < n + H.length → (∀ w ∈ ws, w < n + H.length) →
    val (H ++ chG (n + H.length) acc ws) (chO (n + H.length) acc ws) x
      = (val H acc x || ws.any (fun w => val H w x)) := by
  induction ws with
  | nil => intro H acc x _ _; simp [chG, chO]
  | cons w ws ih =>
    intro H acc x ha hw
    have hw0 : w < n + H.length := hw w (by simp)
    let H' := H ++ [(⟨GateOp.or, [acc, w]⟩ : Gate)]
    have hl : H'.length = H.length + 1 := by simp [H']
    have e1 : H ++ chG (n + H.length) acc (w :: ws)
        = H' ++ chG (n + H'.length) (n + H.length) ws := by
      simp [chG, H', hl, Nat.add_assoc]
    have e2 : chO (n + H.length) acc (w :: ws) = chO (n + H'.length) (n + H.length) ws := by
      simp [chO, hl, Nat.add_assoc]
    have hv : ∀ v, v < n + H.length → val H' v x = val H v x := fun v hv => val_app H _ x v hv
    rw [e1, e2, ih H' (n + H.length) x (by omega)
      (by intro v hv'; have := hw v (by simp [hv']); omega)]
    have hg : val H' (n + H.length) x = (val H acc x || val H w x) := by
      have hlt : H.length < H'.length := by omega
      have hget : H'[H.length] = (⟨GateOp.or, [acc, w]⟩ : Gate) := by simp [H']
      rw [gval H' x H.length hlt (by rw [hget]; intro i hi; simp at hi; omega), hget]
      simp [GateOp.eval, hv acc ha, hv w hw0]
    rw [hg, any_congr_lt ws _ _ (n + H.length) (fun v hv' => hw v (by simp [hv'])) hv]
    simp [List.any_cons, Bool.or_assoc]

def alG (b : ℕ) : List (ℕ × List ℕ) → List Gate
  | [] => []
  | t :: ts => chG b t.1 t.2 ++ alG (b + t.2.length) ts

def alO (b : ℕ) : List (ℕ × List ℕ) → List ℕ
  | [] => []
  | t :: ts => chO b t.1 t.2 :: alO (b + t.2.length) ts

theorem alG_len (ts : List (ℕ × List ℕ)) : ∀ b : ℕ,
    (alG b ts).length = (ts.map (fun t => t.2.length)).sum := by
  induction ts with
  | nil => intro b; rfl
  | cons t ts ih => intro b; simp [alG, ih, chG_len]

theorem al_sem {n : ℕ} (ts : List (ℕ × List ℕ)) : ∀ (H : List Gate) (x : Fin n → Bool),
    (∀ t ∈ ts, t.1 < n + H.length ∧ ∀ w ∈ t.2, w < n + H.length) →
    ∀ k (hk : k < ts.length), val (H ++ alG (n + H.length) ts) ((alO (n + H.length) ts).getD k 0) x
       = (val H ts[k].1 x || ts[k].2.any (fun w => val H w x)) := by
  induction ts with
  | nil => intro H x _ k hk; simp at hk
  | cons t ts ih =>
    intro H x hts k hk
    let H' := H ++ chG (n + H.length) t.1 t.2
    have hl : H'.length = H.length + t.2.length := by simp [H', chG_len]
    have e1 : H ++ alG (n + H.length) (t :: ts) = H' ++ alG (n + H'.length) ts := by
      simp [alG, H', hl, Nat.add_assoc]
    have ht := hts t (by simp)
    have hv : ∀ v, v < n + H.length → val H' v x = val H v x := fun v hv => val_app H _ x v hv
    rw [e1]
    cases k with
    | zero =>
      simp only [alO, List.getD_cons_zero, List.getElem_cons_zero]
      have := chO_lt t.2 (n + H.length) t.1 ht.1
      rw [val_app H' _ x _ (by rw [hl]; omega)]
      exact ch_sem t.2 H t.1 x ht.1 ht.2
    | succ k =>
      have e2 : (alO (n + H.length) (t :: ts)).getD (k + 1) 0
          = (alO (n + H'.length) ts).getD k 0 := by
        simp [alO, hl, Nat.add_assoc]
      have hk' : k < ts.length := by simpa using hk
      rw [e2, ih H' x ?_ k hk']
      · simp only [List.getElem_cons_succ]
        have hts' := hts ts[k] (by simp)
        rw [hv _ hts'.1, any_congr_lt _ _ _ (n + H.length) hts'.2 hv]
      · intro t' ht'
        have := hts t' (by simp [ht'])
        exact ⟨by rw [hl]; omega, fun w hw => by have := this.2 w hw; rw [hl]; omega⟩

def RBf (b : ℕ) (G : List Gate) : Prop := ∀ k (hk : k < G.length), ∀ i ∈ G[k].inputs, i < b + k

theorem rbf_app (b : ℕ) (G1 G2 : List Gate) (h1 : RBf b G1) (h2 : RBf (b + G1.length) G2) :
    RBf b (G1 ++ G2) := by
  intro k hk i hi
  by_cases hk1 : k < G1.length
  · rw [List.getElem_append_left hk1] at hi
    exact h1 k hk1 i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have := h2 (k - G1.length) (by simp at hk; omega) i hi
    omega

theorem rbf_ch (ws : List ℕ) : ∀ b acc : ℕ, acc < b → (∀ w ∈ ws, w < b) → RBf b (chG b acc ws) := by
  induction ws with
  | nil => intro b acc _ _ k hk; simp [chG] at hk
  | cons w ws ih =>
    intro b acc ha hw k hk i hi
    cases k with
    | zero =>
      simp [chG] at hi
      rcases hi with rfl | rfl
      · omega
      · have := hw i (by simp); omega
    | succ k =>
      simp only [chG, List.getElem_cons_succ] at hi
      have := ih (b + 1) b (by omega) (fun v hv => by have := hw v (by simp [hv]); omega) k
        (by simp [chG] at hk; simpa [chG_len] using hk) i hi
      omega

theorem rbf_al (ts : List (ℕ × List ℕ)) : ∀ b : ℕ,
    (∀ t ∈ ts, t.1 < b ∧ ∀ w ∈ t.2, w < b) → RBf b (alG b ts) := by
  induction ts with
  | nil => intro b _ k hk; simp [alG] at hk
  | cons t ts ih =>
    intro b h
    have ht := h t (by simp)
    apply rbf_app
    · exact rbf_ch t.2 b t.1 ht.1 ht.2
    · rw [chG_len]
      apply ih
      intro t' ht'
      have := h t' (by simp [ht'])
      exact ⟨by omega, fun w hw => by have := this.2 w hw; omega⟩

theorem legal_ch (ws : List ℕ) : ∀ b acc : ℕ, ∀ g ∈ chG b acc ws,
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction ws with
  | nil => intro b acc g hg; simp [chG] at hg
  | cons w ws ih =>
    intro b acc g hg
    simp only [chG, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

theorem legal_al (ts : List (ℕ × List ℕ)) : ∀ b : ℕ, ∀ g ∈ alG b ts,
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction ts with
  | nil => intro b g hg; simp [alG] at hg
  | cons t ts ih =>
    intro b g hg
    simp only [alG, List.mem_append] at hg
    rcases hg with hg | hg
    · exact legal_ch _ _ _ g hg
    · exact ih _ g hg

def pre (n : ℕ) (zf : ℕ → Bool) : List ℕ → ℕ × List ℕ
  | [] => (n, [])
  | c :: cs => (rm n zf c, cs.map (rm n zf))

theorem gen (n m : ℕ) (gs : List Gate) (zf : ℕ → Bool)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ k (hk : k < gs.length), ∀ i ∈ gs[k].inputs, i < n + k)
    (R U : Fin m → Finset (Fin n)) (T : Fin m → List ℕ)
    (hR : ∀ i j : Fin m, i ≠ j → (R i ∩ R j).card ≤ 1)
    (hU : ∀ t, U t ⊆ R t)
    (hT : ∀ t, ∀ c ∈ T t, c < n + gs.length)
    (hsg : ∀ t, ∀ i ∈ U t, ∃ c ∈ T t, val gs c (zr zf (fun k : Fin n => decide (k = i))) = true)
    (hrej : ∀ t, ∀ c ∈ T t, val gs c (zr zf (fun k : Fin n => decide (k ∉ R t))) = false) :
    ∑ t, ((U t).card - 1) ≤ gs.length + 1 + ∑ t, ((T t).length - 1) := by
  let B := base n zf gs
  have hBl : B.length = gs.length + 1 := base_len n zf gs
  let ts : List (ℕ × List ℕ) := List.ofFn (fun t => pre n zf (T t))
  let Dg := B ++ alG (n + B.length) ts
  let o : Fin m → ℕ := fun t => (alO (n + B.length) ts).getD t.val 0
  have hrm : ∀ c, c < n + gs.length → rm n zf c < n + B.length := by
    intro c hc; rw [hBl]; unfold rm; split_ifs <;> omega
  have hts : ∀ t ∈ ts, t.1 < n + B.length ∧ ∀ w ∈ t.2, w < n + B.length := by
    intro t ht
    simp only [ts, List.mem_ofFn] at ht
    obtain ⟨u, rfl⟩ := ht
    rcases hTu : T u with _ | ⟨c, cs⟩
    · simp [pre, hBl]
    · simp only [pre]
      refine ⟨hrm c (hT u c (by simp [hTu])), ?_⟩
      intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨c', hc', rfl⟩ := hw
      exact hrm c' (hT u c' (by simp [hTu, hc']))
  have hsem : ∀ (t : Fin m) (x : Fin n → Bool), val Dg (o t) x
      = (val B (pre n zf (T t)).1 x || (pre n zf (T t)).2.any (fun w => val B w x)) := by
    intro t x
    have := al_sem ts B x hts t.val (by simp [ts])
    simp only [ts, List.getElem_ofFn] at this
    exact this
  have hbs : ∀ c, c < n + gs.length → ∀ x : Fin n → Bool,
      val B (rm n zf c) x = val gs c (zr zf x) := fun c hc x => base_sem n zf gs hrb x c hc
  have legalD : ∀ g ∈ Dg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simp only [Dg, List.mem_append] at hg
    rcases hg with hg | hg
    · simp only [B, base, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | ⟨g', hg', rfl⟩
      · simp
      · have := legal g' hg'
        simpa [rmG] using this
    · have := legal_al ts _ g hg
      exact ⟨Or.inr this.1, by omega⟩
  have hrbD : RBf n Dg := by
    apply rbf_app
    · intro k hk i hi
      cases k with
      | zero => simp [B, base] at hi
      | succ k =>
        have hk' : k < gs.length := by simp [B, base] at hk; omega
        simp only [B, base, List.getElem_cons_succ, List.getElem_map, rmG, List.mem_map] at hi
        obtain ⟨i', hi', rfl⟩ := hi
        have := hrb k hk' i' hi'
        unfold rm; split_ifs <;> omega
    · exact rbf_al ts _ hts
  have hin : ∀ i : Fin Dg.length, ∀ a ∈ (Dg.get i).inputs, a < n + (i : ℕ) := by
    intro i a ha
    exact hrbD i i.2 a (by simpa using ha)
  have hmain := main n m R U Dg o hR legalD hin hU ?_ ?_
  · have hDl : Dg.length = gs.length + 1 + ∑ t, ((T t).length - 1) := by
      simp only [Dg, List.length_append, hBl, alG_len, ts, List.map_ofFn]
      rw [List.sum_ofFn]
      have hsum : ∑ t, (pre n zf (T t)).2.length = ∑ t, ((T t).length - 1) := by
        apply Finset.sum_congr rfl
        intro t _
        rcases hTt : T t with _ | ⟨c, cs⟩ <;> simp [pre]
      rw [← hsum]
      rfl
    omega
  · intro t p hp
    rw [hsem]
    obtain ⟨c, hc, hv⟩ := hsg t p hp
    rcases hTt : T t with _ | ⟨c0, cs⟩
    · rw [hTt] at hc; simp at hc
    · rw [hTt] at hc
      simp only [pre]
      rcases List.mem_cons.1 hc with rfl | hc'
      · rw [hbs c (hT t c (by simp [hTt])), hv]; simp
      · have hmem : rm n zf c ∈ cs.map (rm n zf) := List.mem_map.2 ⟨c, hc', rfl⟩
        have hb : (cs.map (rm n zf)).any (fun w => val B w (fun k : Fin n => decide (k = p)))
            = true := List.any_eq_true.2 ⟨_, hmem, by rw [hbs c (hT t c (by simp [hTt, hc'])), hv]⟩
        rw [hb, Bool.or_true]
  · intro t
    rw [hsem]
    rcases hTt : T t with _ | ⟨c0, cs⟩
    · simp [pre, B, base_const]
    · simp only [pre]
      rw [hbs c0 (hT t c0 (by simp [hTt])), hrej t c0 (by simp [hTt])]
      apply Bool.eq_iff_iff.2
      simp only [Bool.false_or, List.any_eq_true, List.mem_map]
      constructor
      · rintro ⟨w, ⟨c, hc, rfl⟩, hw⟩
        rw [hbs c (hT t c (by simp [hTt, hc])), hrej t c (by simp [hTt, hc])] at hw
        exact absurd hw (by simp)
      · intro h; exact absurd h (by simp)

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Classical

theorem legalOf (C : Circuit) (hm : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hm g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem hrbOf (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) :
    ∀ k (hk : k < C.gates.length), ∀ i ∈ C.gates[k].inputs, i < n + k := by
  intro k hk i hi
  apply hrb k hk i
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hk]
  exact hi

def ep (N : ℕ) (p : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)
def el (N : ℕ) (l : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)

def PS (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun p => val C.gates w (ep N p) = true)
def LS (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun l => val C.gates w (el N l) = true)

def xi (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 0 0
def yi (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 1 0

def Ok (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs = [xi C j, yi C j] ∧
  ∀ z : Fin (N + N) → Bool, val C.gates (N + N + j) z = true →
    ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true

theorem ca_ne_na (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem na_ne_ca (N : ℕ) (p l : Fin N) : Fin.natAdd N l ≠ Fin.castAdd N p :=
  fun h => ca_ne_na N p l h.symm

theorem ca_inj (N : ℕ) (a b : Fin N) : Fin.castAdd N a = Fin.castAdd N b ↔ a = b := by
  constructor
  · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro h; rw [h]

theorem na_inj (N : ℕ) (a b : Fin N) : Fin.natAdd N a = Fin.natAdd N b ↔ a = b := by
  constructor
  · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro h; rw [h]

theorem okin (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (j : ℕ) (hj : Ok N I C j) : xi C j < N + N + C.gates.length ∧ yi C j < N + N + C.gates.length := by
  obtain ⟨hlt, _, hin, _⟩ := hj
  have h1 := hrb j hlt (xi C j) (by rw [hin]; simp)
  have h2 := hrb j hlt (yi C j) (by rw [hin]; simp)
  omega

theorem fire (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (j : ℕ) (hj : Ok N I C j) (z : Fin (N + N) → Bool)
    (hx : val C.gates (xi C j) z = true) (hy : val C.gates (yi C j) z = true) :
    ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true := by
  obtain ⟨hlt, hop, hin, hsi⟩ := hj
  apply hsi z
  have hg : gateAt C j = C.gates[j] := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hlt]
  have hop' : C.gates[j].op = GateOp.and := by rw [← hg]; exact hop
  apply (val_and C.gates z j hlt hop').2
  intro i hi
  refine ⟨hrb j hlt i (by rw [hg]; exact hi), ?_⟩
  rw [← hg, hin] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact hx
  · exact hy

theorem mono (C : Circuit) (hm : Monotone2 C) {n : ℕ} (w : ℕ) (z z' : Fin n → Bool)
    (hz : ∀ v, z v = true → z' v = true) (h : val C.gates w z = true) :
    val C.gates w z' = true :=
  val_mono C.gates (legalOf C hm) z z' hz w h

theorem excl (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (hj : Ok N I C j) (p p' : Fin N)
    (hp : p ∈ PS N C (xi C j)) (hp' : p' ∈ PS N C (yi C j)) : False := by
  simp only [PS, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  let z : Fin (N + N) → Bool := fun k => ep N p k || ep N p' k
  obtain ⟨p0, l0, _, _, h2⟩ := fire N I C hrb j hj z
    (mono C hm _ _ _ (fun v hv => by simp [z, hv]) hp)
    (mono C hm _ _ _ (fun v hv => by simp [z, hv]) hp')
  simp only [z, ep, Bool.or_eq_true, decide_eq_true_eq] at h2
  rcases h2 with h2 | h2
  · exact na_ne_ca N p l0 h2
  · exact na_ne_ca N p' l0 h2

theorem rect (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (hj : Ok N I C j) (a c : ℕ)
    (hac : (a = xi C j ∧ c = yi C j) ∨ (a = yi C j ∧ c = xi C j))
    (p l : Fin N) (hp : p ∈ PS N C a) (hl : l ∈ LS N C c) : I p l := by
  simp only [PS, LS, Finset.mem_filter, Finset.mem_univ, true_and] at hp hl
  let z : Fin (N + N) → Bool := fun k => ep N p k || el N l k
  have ha := mono C hm a _ z (fun v hv => by simp [z, hv]) hp
  have hc := mono C hm c _ z (fun v hv => by simp [z, hv]) hl
  obtain ⟨p0, l0, hI, h1, h2⟩ : ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧
      z (Fin.natAdd N l0) = true := by
    rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fire N I C hrb j hj z ha hc
    · exact fire N I C hrb j hj z hc ha
  simp only [z, ep, el, Bool.or_eq_true, decide_eq_true_eq, ca_inj, na_inj, ca_ne_na, na_ne_ca,
    or_false, false_or] at h1 h2
  subst h1
  subst h2
  exact hI

theorem two_lines (N : ℕ) (I : Fin N → Fin N → Prop)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) {p p' l l' : Fin N}
    (h : p ≠ p') (h1 : I p l) (h2 : I p' l) (h3 : I p l') (h4 : I p' l') : l = l' := by
  obtain ⟨l0, _, hu⟩ := huniq p p' h
  rw [hu l ⟨h1, h2⟩, hu l' ⟨h3, h4⟩]

def okA (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (p : Fin N) : Prop :=
  Ok N I C j ∧ (PS N C (xi C j) = {p} ∨ PS N C (yi C j) = {p})
def wA (N : ℕ) (C : Circuit) (j : ℕ) : ℕ := if (PS N C (xi C j)).card = 1 then yi C j else xi C j
def okB (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (l : Fin N) : Prop :=
  Ok N I C j ∧ ((LS N C (yi C j) = {l} ∧ 2 ≤ (PS N C (xi C j)).card) ∨
    (LS N C (xi C j) = {l} ∧ 2 ≤ (PS N C (yi C j)).card))
def wB (N : ℕ) (C : Circuit) (j : ℕ) : ℕ := if 2 ≤ (PS N C (xi C j)).card then xi C j else yi C j

noncomputable def TA (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (p : Fin N) : List ℕ :=
  (((Finset.range C.gates.length).filter (fun j => okA N I C j p)).toList).map (wA N C)
noncomputable def TB (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (l : Fin N) : List ℕ :=
  (((Finset.range C.gates.length).filter (fun j => okB N I C j l)).toList).map (wB N C)

theorem mem_TA {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {p : Fin N} {c : ℕ}
    (h : c ∈ TA N I C p) : ∃ j, okA N I C j p ∧ wA N C j = c := by
  simp only [TA, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_range] at h
  obtain ⟨j, ⟨_, h1⟩, h2⟩ := h
  exact ⟨j, h1, h2⟩

theorem mem_TB {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {l : Fin N} {c : ℕ}
    (h : c ∈ TB N I C l) : ∃ j, okB N I C j l ∧ wB N C j = c := by
  simp only [TB, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_range] at h
  obtain ⟨j, ⟨_, h1⟩, h2⟩ := h
  exact ⟨j, h1, h2⟩

theorem wA_mem {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {p : Fin N} {j : ℕ}
    (h : okA N I C j p) : wA N C j ∈ TA N I C p := by
  simp only [TA, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_range]
  exact ⟨j, ⟨h.1.1, h⟩, rfl⟩

theorem wB_mem {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {l : Fin N} {j : ℕ}
    (h : okB N I C j l) : wB N C j ∈ TB N I C l := by
  simp only [TB, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_range]
  exact ⟨j, ⟨h.1.1, h⟩, rfl⟩

theorem ne_of_two {N : ℕ} {s : Finset (Fin N)} (h : 2 ≤ s.card) : ∃ p, p ∈ s := by
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (by omega : 0 < s.card)
  exact ⟨p, hp⟩

theorem wA_spec (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (p : Fin N) (hA : okA N I C j p) :
    ∃ a, PS N C a = {p} ∧ ((a = xi C j ∧ wA N C j = yi C j) ∨ (a = yi C j ∧ wA N C j = xi C j)) := by
  obtain ⟨hj, h | h⟩ := hA
  · exact ⟨xi C j, h, Or.inl ⟨rfl, by simp [wA, h]⟩⟩
  · have h0 : (PS N C (xi C j)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p' hp'
      exact excl N I C hm hrb j hj p' p hp' (by rw [h]; simp)
    exact ⟨yi C j, h, Or.inr ⟨rfl, by simp [wA, h0]⟩⟩

theorem wB_spec (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) (l : Fin N) (hB : okB N I C j l) :
    ∃ c, LS N C c = {l} ∧ ((wB N C j = xi C j ∧ c = yi C j) ∨ (wB N C j = yi C j ∧ c = xi C j)) := by
  obtain ⟨hj, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hB
  · exact ⟨yi C j, h1, Or.inl ⟨by simp [wB, h2], rfl⟩⟩
  · have h0 : ¬ 2 ≤ (PS N C (xi C j)).card := by
      intro h3
      obtain ⟨p, hp⟩ := ne_of_two h3
      obtain ⟨p', hp'⟩ := ne_of_two h2
      exact excl N I C hm hrb j hj p p' hp hp'
    exact ⟨xi C j, h1, Or.inr ⟨by simp [wB, h0], rfl⟩⟩

def eL (N : ℕ) : Fin N ↪ Fin (N + N) := ⟨Fin.natAdd N, fun a b h => (na_inj N a b).1 h⟩
def eP (N : ℕ) : Fin N ↪ Fin (N + N) := ⟨Fin.castAdd N, fun a b h => (ca_inj N a b).1 h⟩

noncomputable def RA (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) : Finset (Fin (N + N)) :=
  (Finset.univ.filter (fun l => I p l)).map (eL N)
noncomputable def UA (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (p : Fin N) :
    Finset (Fin (N + N)) :=
  (Finset.univ.filter (fun l => ∃ c ∈ TA N I C p, val C.gates c (el N l) = true)).map (eL N)
noncomputable def RB (N : ℕ) (I : Fin N → Fin N → Prop) (l : Fin N) : Finset (Fin (N + N)) :=
  (Finset.univ.filter (fun p => I p l)).map (eP N)
noncomputable def UB (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (l : Fin N) :
    Finset (Fin (N + N)) :=
  (Finset.univ.filter (fun p => ∃ a ∈ TB N I C l, val C.gates a (ep N p) = true)).map (eP N)

theorem mem_RA (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    Fin.natAdd N l ∈ RA N I p ↔ I p l := by
  simp only [RA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, eL]
  constructor
  · rintro ⟨l', h, he⟩
    rw [← (na_inj N l' l).1 he]; exact h
  · intro h; exact ⟨l, h, rfl⟩

theorem mem_RB (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    Fin.castAdd N p ∈ RB N I l ↔ I p l := by
  simp only [RB, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, eP]
  constructor
  · rintro ⟨p', h, he⟩
    rw [← (ca_inj N p' p).1 he]; exact h
  · intro h; exact ⟨p, h, rfl⟩

theorem castlt (N : ℕ) (p : Fin N) : ((Fin.castAdd N p : Fin (N + N)) : ℕ) < N := p.isLt

theorem natnlt (N : ℕ) (l : Fin N) : ¬ ((Fin.natAdd N l : Fin (N + N)) : ℕ) < N := by
  show ¬ (N + (l : ℕ) < N)
  omega

theorem partA (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∑ p : Fin N, ((UA N I C p).card - 1) ≤ C.gates.length + 1 + ∑ p, ((TA N I C p).length - 1) := by
  apply gen (N + N) N C.gates (fun i => decide (i < N)) (legalOf C hm) (hrbOf _ C hrb)
    (RA N I) (UA N I C) (TA N I C)
  · intro p p' hpp
    rw [RA, RA, ← Finset.map_inter, Finset.card_map]
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact two_lines N I huniq hpp ha.1 ha.2 hb.1 hb.2
  · intro p i hi
    simp only [UA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨l, ⟨c, hc, hv⟩, rfl⟩ := hi
    show Fin.natAdd N l ∈ RA N I p
    rw [mem_RA]
    obtain ⟨j, hA, rfl⟩ := mem_TA hc
    obtain ⟨a, ha, hor⟩ := wA_spec N I C hm hrb j p hA
    apply rect N I C hm hrb j hA.1 a (wA N C j) ?_ p l (by rw [ha]; simp) (by simp [LS, hv])
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · intro p c hc
    obtain ⟨j, hA, rfl⟩ := mem_TA hc
    obtain ⟨a, _, hor⟩ := wA_spec N I C hm hrb j p hA
    have := okin N I C hrb j hA.1
    rcases hor with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> omega
  · intro p i hi
    simp only [UA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨l, ⟨c, hc, hv⟩, rfl⟩ := hi
    refine ⟨c, hc, ?_⟩
    have e : zr (fun i => decide (i < N)) (fun k : Fin (N + N) => decide (k = (eL N) l))
        = el N l := by
      funext k
      show (if decide ((k : ℕ) < N) = true then false else decide (k = Fin.natAdd N l))
        = decide (k = Fin.natAdd N l)
      by_cases hk : (k : ℕ) < N
      · have hne : k ≠ Fin.natAdd N l := by
          intro h; rw [h] at hk; exact natnlt N l hk
        rw [if_pos (by simpa using hk)]
        exact (decide_eq_false hne).symm
      · rw [if_neg (by simpa using hk)]
    rw [e]
    exact hv
  · intro p c hc
    obtain ⟨j, hA, rfl⟩ := mem_TA hc
    obtain ⟨a, ha, hor⟩ := wA_spec N I C hm hrb j p hA
    by_contra hne
    have hv : val C.gates (wA N C j)
        (zr (fun i => decide (i < N)) (fun k : Fin (N + N) => decide (k ∉ RA N I p))) = true := by
      simpa using hne
    let z := zr (fun i => decide (i < N)) (fun k : Fin (N + N) => decide (k ∉ RA N I p))
    let z' : Fin (N + N) → Bool := fun k => z k || ep N p k
    have hpa : val C.gates a (ep N p) = true := by
      have : p ∈ PS N C a := by rw [ha]; simp
      simpa [PS] using this
    have h1 := mono C hm a (ep N p) z' (fun v hv => by simp [z', hv]) hpa
    have h2 := mono C hm (wA N C j) z z' (fun v hv => by simp [z', hv]) hv
    obtain ⟨p0, l0, hI, hp0, hl0⟩ : ∃ p0 l0 : Fin N, I p0 l0 ∧ z' (Fin.castAdd N p0) = true ∧
        z' (Fin.natAdd N l0) = true := by
      rcases hor with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1] at h1; rw [e2] at h2; exact fire N I C hrb j hA.1 z' h1 h2
      · rw [e1] at h1; rw [e2] at h2; exact fire N I C hrb j hA.1 z' h2 h1
    have hzc : z (Fin.castAdd N p0) = false := by
      simp [z, zr, castlt N p0]
    have hzl : z (Fin.natAdd N l0) = decide (Fin.natAdd N l0 ∉ RA N I p) := by
      simp only [z, zr, natnlt N l0, decide_false, Bool.false_eq_true, ite_false]
    have hp0' : p0 = p := by
      simp only [z', hzc, Bool.false_or, ep, decide_eq_true_eq, ca_inj] at hp0
      exact hp0
    have hl0' : ¬ I p l0 := by
      simp only [z', hzl, ep, Bool.or_eq_true, decide_eq_true_eq] at hl0
      rcases hl0 with h | h
      · rwa [mem_RA] at h
      · exact absurd h (na_ne_ca N p l0)
    subst hp0'
    exact hl0' hI

theorem partB (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∑ l : Fin N, ((UB N I C l).card - 1) ≤ C.gates.length + 1 + ∑ l, ((TB N I C l).length - 1) := by
  apply gen (N + N) N C.gates (fun i => decide (N ≤ i)) (legalOf C hm) (hrbOf _ C hrb)
    (RB N I) (UB N I C) (TB N I C)
  · intro l l' hll
    rw [RB, RB, ← Finset.map_inter, Finset.card_map]
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    exact hll (two_lines N I huniq hab ha.1 hb.1 ha.2 hb.2)
  · intro l i hi
    simp only [UB, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨p, ⟨a, ha, hv⟩, rfl⟩ := hi
    show Fin.castAdd N p ∈ RB N I l
    rw [mem_RB]
    obtain ⟨j, hB, rfl⟩ := mem_TB ha
    obtain ⟨c, hc, hor⟩ := wB_spec N I C hm hrb j l hB
    apply rect N I C hm hrb j hB.1 (wB N C j) c ?_ p l (by simp [PS, hv]) (by rw [hc]; simp)
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · intro l c hc
    obtain ⟨j, hB, rfl⟩ := mem_TB hc
    obtain ⟨c', _, hor⟩ := wB_spec N I C hm hrb j l hB
    have := okin N I C hrb j hB.1
    rcases hor with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega
  · intro l i hi
    simp only [UB, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨p, ⟨a, ha, hv⟩, rfl⟩ := hi
    refine ⟨a, ha, ?_⟩
    have e : zr (fun i => decide (N ≤ i)) (fun k : Fin (N + N) => decide (k = (eP N) p))
        = ep N p := by
      funext k
      show (if decide (N ≤ (k : ℕ)) = true then false else decide (k = Fin.castAdd N p))
        = decide (k = Fin.castAdd N p)
      by_cases hk : N ≤ (k : ℕ)
      · have hne : k ≠ Fin.castAdd N p := by
          intro h; rw [h] at hk; have := castlt N p; omega
        rw [if_pos (by simpa using hk)]
        exact (decide_eq_false hne).symm
      · rw [if_neg (by simpa using hk)]
    rw [e]
    exact hv
  · intro l a ha
    obtain ⟨j, hB, rfl⟩ := mem_TB ha
    obtain ⟨c, hc, hor⟩ := wB_spec N I C hm hrb j l hB
    by_contra hne
    have hv : val C.gates (wB N C j)
        (zr (fun i => decide (N ≤ i)) (fun k : Fin (N + N) => decide (k ∉ RB N I l))) = true := by
      simpa using hne
    let z := zr (fun i => decide (N ≤ i)) (fun k : Fin (N + N) => decide (k ∉ RB N I l))
    let z' : Fin (N + N) → Bool := fun k => z k || el N l k
    have hlc : val C.gates c (el N l) = true := by
      have : l ∈ LS N C c := by rw [hc]; simp
      simpa [LS] using this
    have h1 := mono C hm c (el N l) z' (fun v hv => by simp [z', hv]) hlc
    have h2 := mono C hm (wB N C j) z z' (fun v hv => by simp [z', hv]) hv
    obtain ⟨p0, l0, hI, hp0, hl0⟩ : ∃ p0 l0 : Fin N, I p0 l0 ∧ z' (Fin.castAdd N p0) = true ∧
        z' (Fin.natAdd N l0) = true := by
      rcases hor with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e2] at h1; rw [e1] at h2; exact fire N I C hrb j hB.1 z' h2 h1
      · rw [e2] at h1; rw [e1] at h2; exact fire N I C hrb j hB.1 z' h1 h2
    have hzl : z (Fin.natAdd N l0) = false := by
      have : N ≤ ((Fin.natAdd N l0 : Fin (N + N)) : ℕ) := by
        show N ≤ N + (l0 : ℕ); omega
      simp [z, zr, this]
    have hzc : z (Fin.castAdd N p0) = decide (Fin.castAdd N p0 ∉ RB N I l) := by
      have : ¬ N ≤ ((Fin.castAdd N p0 : Fin (N + N)) : ℕ) := by
        have := castlt N p0; omega
      simp only [z, zr, this, decide_false, Bool.false_eq_true, ite_false]
    have hl0' : l0 = l := by
      simp only [z', hzl, Bool.false_or, el, decide_eq_true_eq, na_inj] at hl0
      exact hl0
    have hp0' : ¬ I p0 l := by
      simp only [z', hzc, el, Bool.or_eq_true, decide_eq_true_eq] at hp0
      rcases hp0 with h | h
      · rwa [mem_RB] at h
      · exact absurd h (ca_ne_na N p0 l)
    subst hl0'
    exact hp0' hI

theorem uA (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (p : Fin N) :
    (UA N I C p).card + ((TA N I C p).length - 1) ≤ ((UA N I C p).card - 1) + (TA N I C p).length := by
  by_cases h : (UA N I C p).card = 0
  · omega
  · have : (TA N I C p).length ≠ 0 := by
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
      simp only [UA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨l, ⟨c, hc, _⟩, _⟩ := hi
      intro h0
      rw [List.length_eq_zero_iff] at h0
      rw [h0] at hc
      simp at hc
    omega

theorem uB (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (l : Fin N) :
    (UB N I C l).card + ((TB N I C l).length - 1) ≤ ((UB N I C l).card - 1) + (TB N I C l).length := by
  by_cases h : (UB N I C l).card = 0
  · omega
  · have : (TB N I C l).length ≠ 0 := by
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
      simp only [UB, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨p, ⟨c, hc, _⟩, _⟩ := hi
      intro h0
      rw [List.length_eq_zero_iff] at h0
      rw [h0] at hc
      simp at hc
    omega

theorem perj (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) (j : ℕ) :
    (Finset.univ.filter (fun p => okA N I C j p)).card
      + (Finset.univ.filter (fun l => okB N I C j l)).card ≤ 1 := by
  have hA1 : (Finset.univ.filter (fun p => okA N I C j p)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro p hp p' hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    obtain ⟨hj, h1 | h1⟩ := hp <;> obtain ⟨_, h2 | h2⟩ := hp'
    · rw [h1] at h2; exact Finset.singleton_inj.1 h2
    · exact (excl N I C hm hrb j hj p p' (by rw [h1]; simp) (by rw [h2]; simp)).elim
    · exact (excl N I C hm hrb j hj p' p (by rw [h2]; simp) (by rw [h1]; simp)).elim
    · rw [h1] at h2; exact Finset.singleton_inj.1 h2
  have hB1 : (Finset.univ.filter (fun l => okB N I C j l)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro l hl l' hl'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl hl'
    obtain ⟨hj, ⟨h1, h1'⟩ | ⟨h1, h1'⟩⟩ := hl <;> obtain ⟨_, ⟨h2, h2'⟩ | ⟨h2, h2'⟩⟩ := hl'
    · rw [h1] at h2; exact Finset.singleton_inj.1 h2
    · obtain ⟨p, hp⟩ := ne_of_two h1'
      obtain ⟨p', hp'⟩ := ne_of_two h2'
      exact (excl N I C hm hrb j hj p p' hp hp').elim
    · obtain ⟨p, hp⟩ := ne_of_two h2'
      obtain ⟨p', hp'⟩ := ne_of_two h1'
      exact (excl N I C hm hrb j hj p p' hp hp').elim
    · rw [h1] at h2; exact Finset.singleton_inj.1 h2
  have hx : ¬ (0 < (Finset.univ.filter (fun p => okA N I C j p)).card ∧
      0 < (Finset.univ.filter (fun l => okB N I C j l)).card) := by
    rintro ⟨ha, hb⟩
    obtain ⟨p, hp⟩ := Finset.card_pos.1 ha
    obtain ⟨l, hl⟩ := Finset.card_pos.1 hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hl
    obtain ⟨hj, h1 | h1⟩ := hp <;> obtain ⟨_, ⟨_, h2⟩ | ⟨_, h2⟩⟩ := hl
    · rw [h1] at h2; simp at h2
    · obtain ⟨p', hp'⟩ := ne_of_two h2
      exact excl N I C hm hrb j hj p p' (by rw [h1]; simp) hp'
    · obtain ⟨p', hp'⟩ := ne_of_two h2
      exact excl N I C hm hrb j hj p' p hp' (by rw [h1]; simp)
    · rw [h1] at h2; simp at h2
  omega

theorem tcount (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack (N + N) C) :
    ∑ p : Fin N, (TA N I C p).length + ∑ l : Fin N, (TB N I C l).length ≤ C.gates.length := by
  have hcA : ∀ p, (TA N I C p).length
      = ∑ j ∈ Finset.range C.gates.length, if okA N I C j p then 1 else 0 := by
    intro p
    simp only [TA, List.length_map, Finset.length_toList]
    rw [Finset.card_filter]
  have hcB : ∀ l, (TB N I C l).length
      = ∑ j ∈ Finset.range C.gates.length, if okB N I C j l then 1 else 0 := by
    intro l
    simp only [TB, List.length_map, Finset.length_toList]
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun p _ => hcA p), Finset.sum_congr rfl (fun l _ => hcB l),
    Finset.sum_comm, Finset.sum_comm (f := fun l j => if okB N I C j l then 1 else 0),
    ← Finset.sum_add_distrib]
  calc ∑ j ∈ Finset.range C.gates.length, ((∑ p : Fin N, if okA N I C j p then 1 else 0)
        + ∑ l : Fin N, if okB N I C j l then 1 else 0)
      ≤ ∑ j ∈ Finset.range C.gates.length, 1 := by
        apply Finset.sum_le_sum
        intro j _
        have := perj N I C hm hrb j
        rw [Finset.card_filter, Finset.card_filter] at this
        exact this
    _ = C.gates.length := by simp

theorem final (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hN : N = q ^ 2 + q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hm : Monotone2 C) (hrb : ReadsBack (N + N) C) :
    {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ,
      (gateAt C j).op = GateOp.and ∧
      ((gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a]) ∧
      (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true →
        ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a false
        = true ∧
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c false
        = true}.ncard ≤ 3 * C.size + 2 * N := by
  let FA : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun e => ∃ c ∈ TA N I C e.1, val C.gates c (el N e.2) = true)
  let FB : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun e => ∃ a ∈ TB N I C e.2, val C.gates a (ep N e.1) = true)
  have hsub : {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ,
      (gateAt C j).op = GateOp.and ∧
      ((gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a]) ∧
      (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true →
        ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a false
        = true ∧
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c false
        = true} ⊆ ↑(FA ∪ FB) := by
    intro e he
    obtain ⟨hI, j, hj, a, c, hop, hin, hsi, ha, hc⟩ := he
    change val C.gates a (ep N e.1) = true at ha
    change val C.gates c (el N e.2) = true at hc
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, FA, FB, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hgx : (a = xi C j ∧ c = yi C j) ∨ (a = yi C j ∧ c = xi C j) := by
      rcases hin with h | h
      · left; simp [xi, yi, h]
      · right; simp [xi, yi, h]
    have hOk : Ok N I C j := ⟨hj, hop, by rcases hin with h | h <;> simp [xi, yi, h], hsi⟩
    have hpa : e.1 ∈ PS N C a := by simp [PS, ha]
    have hlc : e.2 ∈ LS N C c := by simp [LS, hc]
    by_cases hs : PS N C a = {e.1}
    · left
      have hA : okA N I C j e.1 := ⟨hOk, by
        rcases hgx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl hs
        · exact Or.inr hs⟩
      have hw : wA N C j = c := by
        rcases hgx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [wA, hs]
        · have h0 : (PS N C (xi C j)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro p' hp'
            exact excl N I C hm hrb j hOk p' e.1 hp' hpa
          simp [wA, h0]
      exact ⟨c, by rw [← hw]; exact wA_mem hA, hc⟩
    · right
      obtain ⟨p', hp', hne⟩ : ∃ p' ∈ PS N C a, p' ≠ e.1 := by
        by_contra hcon
        push_neg at hcon
        exact hs (Finset.eq_singleton_iff_unique_mem.2 ⟨hpa, hcon⟩)
      have h2 : 2 ≤ (PS N C a).card := Finset.one_lt_card.2 ⟨e.1, hpa, p', hp', hne.symm⟩
      have hL : LS N C c = {e.2} := by
        apply Finset.eq_singleton_iff_unique_mem.2 ⟨hlc, ?_⟩
        intro l' hl'
        have r1 := rect N I C hm hrb j hOk a c hgx e.1 l' hpa hl'
        have r2 := rect N I C hm hrb j hOk a c hgx p' l' hp' hl'
        have r3 := rect N I C hm hrb j hOk a c hgx p' e.2 hp' hlc
        exact two_lines N I huniq hne.symm r1 r2 hI r3
      have hB : okB N I C j e.2 := ⟨hOk, by
        rcases hgx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨hL, h2⟩
        · exact Or.inr ⟨hL, h2⟩⟩
      have hw : wB N C j = a := by
        rcases hgx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [wB, h2]
        · have h3 : ¬ 2 ≤ (PS N C (xi C j)).card := by
            intro h3
            obtain ⟨p1, hp1⟩ := ne_of_two h3
            exact excl N I C hm hrb j hOk p1 e.1 hp1 hpa
          simp [wB, h3]
      exact ⟨a, by rw [← hw]; exact wB_mem hB, ha⟩
  have hcard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hcard
  have hu := Finset.card_union_le FA FB
  have hFA : FA.card = ∑ p, (UA N I C p).card := by
    simp only [FA, UA, Finset.card_map]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.card_filter]
  have hFB : FB.card = ∑ l, (UB N I C l).card := by
    simp only [FB, UB, Finset.card_map]
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.card_filter]
  have hA := partA N I C hm hrb huniq
  have hB := partB N I C hm hrb huniq
  have sA := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => uA N I C p)
  have sB := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => uB N I C l)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at sA sB
  have hT := tcount N I C hm hrb
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.succ_le_succ (Nat.zero_le _)
  show _ ≤ 3 * C.gates.length + 2 * N
  omega

end PEqualNP.Outside.L_meta_2838

theorem PEqualNP.Outside.L_meta_2838 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧ (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a false = true ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c false = true}.ncard ≤ 3 * C.size + 2 * N := by
  intro q N I _ C _ hN _ huniq hm hrb _ _
  exact PEqualNP.Outside.L_meta_2838.final q N I C hN huniq hm hrb
