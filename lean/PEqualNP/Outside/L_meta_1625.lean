import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1625
open PEqualNP.CircuitLowerBounds

theorem ifp {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ifn {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

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
    rw [hP, ifn hnm, Nat.mul_one]
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
      rw [ifp hmrg]
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
      rw [ifn hnm, Nat.mul_one]
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
          rw [ifp hj, ifp e]
        · rw [ifn hj]
          exact Nat.zero_le _
      refine (Finset.sum_le_sum hle).trans ?_
      simp
    · have hz : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) = 0 :=
        fun j _ => ifn (fun h => hex ⟨j, h⟩)
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


theorem val_snoc_old {n : ℕ} (gs : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length)
    (x : Fin n → Bool) : val (gs ++ [g]) w x = val gs w x := by
  unfold val
  exact wf_prefix gs [g] (List.ofFn x) w (by simpa using hw)

theorem val_snoc_new {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    val (gs ++ [g]) (n + gs.length) x = g.op.eval (g.inputs.map fun i => val gs i x) := by
  unfold val
  rw [wf_snoc]
  have := getD_snoc_eq (wf gs (List.ofFn x))
    (g.op.eval (g.inputs.map fun i => (wf gs (List.ofFn x)).getD i false))
  rw [wf_len, List.length_ofFn] at this
  exact this

abbrev Fn (n : ℕ) := (Fin n → Bool) → Bool

abbrev cF (n : ℕ) : Fn n := fun _ => false

abbrev cT (n : ℕ) : Fn n := fun _ => true

def Avail {n : ℕ} (l : List (Fn n)) (g : Fn n) : Prop :=
  g ∈ l ∨ ∃ p : Fin n, g = fun x => x p

def GForm {n : ℕ} (l : List (Fn n)) (f : Fn n) : Prop :=
  ∃ g h : Fn n, Avail l g ∧ Avail l h ∧ (f = (fun x => g x && h x) ∨ f = (fun x => g x || h x))

def Prog {n : ℕ} : List (Fn n) → Prop
  | [] => True
  | f :: l => Prog l ∧ (f = cF n ∨ f = cT n ∨ GForm l f)

theorem avail_mono {n : ℕ} {l l2 : List (Fn n)} (h : l ⊆ l2) {g : Fn n} (hg : Avail l g) :
    Avail l2 g := by
  rcases hg with hg | hg
  · exact Or.inl (h hg)
  · exact Or.inr hg

theorem gform_mono {n : ℕ} {l l2 : List (Fn n)} (h : l ⊆ l2) {f : Fn n} (hf : GForm l f) :
    GForm l2 f := by
  obtain ⟨g, k, hg, hk, hfk⟩ := hf
  exact ⟨g, k, avail_mono h hg, avail_mono h hk, hfk⟩

theorem prog_circ {n : ℕ} : ∀ l : List (Fn n), Prog l → ∃ gs : List Gate,
    gs.length = l.length ∧
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ i (hi : i < gs.length), ∀ a ∈ (gs[i]).inputs, a < n + i) ∧
    ∀ f, Avail l f → ∃ w, w < n + gs.length ∧ ∀ x, val gs w x = f x := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨[], rfl, by simp, by simp, ?_⟩
    intro f hf
    rcases hf with hf | ⟨p, rfl⟩
    · simp at hf
    · exact ⟨p, by simp, fun x => val_input [] x p p.2⟩
  | cons f l ih =>
    intro hP
    obtain ⟨hPl, hf⟩ := hP
    obtain ⟨gs, hlen, hleg, hin, hval⟩ := ih hPl
    have key : ∀ g : Gate, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ a ∈ g.inputs, a < n + gs.length) →
        (∀ x, g.op.eval (g.inputs.map fun i => val gs i x) = f x) →
        ∃ gs2 : List Gate, gs2.length = (f :: l).length ∧
          (∀ g ∈ gs2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
          (∀ i (hi : i < gs2.length), ∀ a ∈ (gs2[i]).inputs, a < n + i) ∧
          ∀ f2, Avail (f :: l) f2 → ∃ w, w < n + gs2.length ∧ ∀ x, val gs2 w x = f2 x := by
      intro g hg1 hg2 hg3
      refine ⟨gs ++ [g], by simp [hlen], ?_, ?_, ?_⟩
      · intro g2 hg2m
        rcases List.mem_append.mp hg2m with h | h
        · exact hleg g2 h
        · rw [List.mem_singleton] at h; subst h; exact hg1
      · intro i hi a ha
        by_cases hi2 : i < gs.length
        · rw [List.getElem_append_left hi2] at ha
          exact hin i hi2 a ha
        · have hie : i = gs.length := by
            rw [List.length_append, List.length_singleton] at hi; omega
          subst hie
          simp at ha
          exact hg2 a ha
      · intro f2 hf2
        rcases hf2 with hf2 | ⟨p, rfl⟩
        · rcases List.mem_cons.mp hf2 with h | h
          · subst h
            exact ⟨n + gs.length, by simp, fun x => by rw [val_snoc_new]; exact hg3 x⟩
          · obtain ⟨w, hw, hwv⟩ := hval f2 (Or.inl h)
            exact ⟨w, by simp; omega, fun x => by rw [val_snoc_old gs g w hw]; exact hwv x⟩
        · exact ⟨p, by have := p.2; simp; omega, fun x => val_input _ x p p.2⟩
    rcases hf with hf | hf | ⟨g, h, hg, hh, hfk⟩
    · exact key ⟨GateOp.or, []⟩ (by simp) (by simp) (fun x => by rw [hf]; rfl)
    · exact key ⟨GateOp.and, []⟩ (by simp) (by simp) (fun x => by rw [hf]; rfl)
    · obtain ⟨wg, hwg, hvg⟩ := hval g hg
      obtain ⟨wh, hwh, hvh⟩ := hval h hh
      rcases hfk with hfk | hfk
      · exact key ⟨GateOp.and, [wg, wh]⟩ (by simp)
          (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption)
          (fun x => by rw [hfk]; simp [GateOp.eval, hvg, hvh])
      · exact key ⟨GateOp.or, [wg, wh]⟩ (by simp)
          (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption)
          (fun x => by rw [hfk]; simp [GateOp.eval, hvg, hvh])

def mult {n : ℕ} (o : Option (Fn n)) (x : Fin n → Bool) : Bool :=
  match o with
  | none => true
  | some μ => μ x

def ecost {n : ℕ} (e : ℕ × Option (Fn n)) : ℕ :=
  match e.2 with
  | none => 1
  | some _ => 2

def cost {n : ℕ} (U : List (ℕ × Option (Fn n))) : ℕ := (U.map ecost).sum

theorem upd_iff {n : ℕ} (acc : ℕ → Fn n) (u : ℕ) (f : Fn n) (P : (Fin n → Bool) → Prop)
    (hf : ∀ x, f x = true ↔ acc u x = true ∨ P x) (w : ℕ) (x : Fin n → Bool) :
    ((if w = u then f else acc w) x = true) ↔ (acc w x = true ∨ (u = w ∧ P x)) := by
  by_cases hw : w = u
  · rw [ifp hw, hf x, hw]; simp
  · rw [ifn hw]
    have : ¬ u = w := fun h => hw h.symm
    simp [this]

theorem entries {n : ℕ} (G : Fn n) : ∀ (U : List (ℕ × Option (Fn n))) (l : List (Fn n))
    (acc : ℕ → Fn n), Prog l → G ∈ l → (∀ w, acc w ∈ l) →
    (∀ e ∈ U, ∀ μ, e.2 = some μ → Avail l μ) →
    ∃ (l2 : List (Fn n)) (acc2 : ℕ → Fn n), Prog l2 ∧ l ⊆ l2 ∧ l2.length ≤ l.length + cost U ∧
      (∀ w, acc2 w ∈ l2) ∧
      ∀ w x, (acc2 w x = true ↔
        acc w x = true ∨ ∃ e ∈ U, e.1 = w ∧ G x = true ∧ mult e.2 x = true) := by
  intro U
  induction U with
  | nil =>
    intro l acc hP _ hacc _
    exact ⟨l, acc, hP, List.Subset.refl l, by simp [cost], hacc, by simp⟩
  | cons e U ih =>
    intro l acc hP hG hacc hav
    obtain ⟨u, μo⟩ := e
    cases μo with
    | none =>
      obtain ⟨f, hf⟩ : ∃ f : Fn n, f = fun x => acc u x || G x := ⟨_, rfl⟩
      have hfx : ∀ x, f x = true ↔ acc u x = true ∨ G x = true := by
        intro x; rw [hf]; simp
      have hP1 : Prog (f :: l) :=
        ⟨hP, Or.inr (Or.inr ⟨acc u, G, Or.inl (hacc u), Or.inl hG, Or.inr hf⟩)⟩
      have hsub : l ⊆ f :: l := List.subset_cons_self f l
      obtain ⟨l2, acc2, hP2, hsub2, hlen2, hacc2, hiff⟩ := ih (f :: l)
        (fun w => if w = u then f else acc w) hP1 (hsub hG)
        (by
          intro w
          by_cases hw : w = u
          · rw [ifp hw]; simp
          · rw [ifn hw]; exact hsub (hacc w))
        (fun e he μ hμ => avail_mono hsub (hav e (List.mem_cons_of_mem _ he) μ hμ))
      refine ⟨l2, acc2, hP2, fun a ha => hsub2 (hsub ha), ?_, hacc2, ?_⟩
      · simp only [cost, List.map_cons, List.sum_cons, ecost, List.length_cons] at hlen2 ⊢
        omega
      · intro w x
        rw [hiff w x]
        show ((if w = u then f else acc w) x = true ∨ _) ↔ _
        rw [upd_iff acc u f (fun x => G x = true) hfx w x]
        simp only [List.mem_cons, exists_eq_or_imp, mult, and_true]
        tauto
    | some μ =>
      have hμ : Avail l μ := hav (u, some μ) (by simp) μ rfl
      obtain ⟨t, ht⟩ : ∃ t : Fn n, t = fun x => G x && μ x := ⟨_, rfl⟩
      obtain ⟨f, hf⟩ : ∃ f : Fn n, f = fun x => acc u x || t x := ⟨_, rfl⟩
      have hfx : ∀ x, f x = true ↔ acc u x = true ∨ (G x = true ∧ μ x = true) := by
        intro x; rw [hf, ht]; simp
      have hP0 : Prog (t :: l) := ⟨hP, Or.inr (Or.inr ⟨G, μ, Or.inl hG, hμ, Or.inl ht⟩)⟩
      have hP1 : Prog (f :: t :: l) :=
        ⟨hP0, Or.inr (Or.inr ⟨acc u, t, Or.inl (List.mem_cons_of_mem _ (hacc u)),
          Or.inl (by simp), Or.inr hf⟩)⟩
      have hsub : l ⊆ f :: t :: l :=
        fun a ha => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)
      obtain ⟨l2, acc2, hP2, hsub2, hlen2, hacc2, hiff⟩ := ih (f :: t :: l)
        (fun w => if w = u then f else acc w) hP1 (hsub hG)
        (by
          intro w
          by_cases hw : w = u
          · rw [ifp hw]; simp
          · rw [ifn hw]; exact hsub (hacc w))
        (fun e he μ2 hμ2 => avail_mono hsub (hav e (List.mem_cons_of_mem _ he) μ2 hμ2))
      refine ⟨l2, acc2, hP2, fun a ha => hsub2 (hsub ha), ?_, hacc2, ?_⟩
      · simp only [cost, List.map_cons, List.sum_cons, ecost, List.length_cons] at hlen2 ⊢
        omega
      · intro w x
        rw [hiff w x]
        show ((if w = u then f else acc w) x = true ∨ _) ↔ _
        rw [upd_iff acc u f (fun x => G x = true ∧ μ x = true) hfx w x]
        simp only [List.mem_cons, exists_eq_or_imp, mult]
        tauto

def StepOK {n : ℕ} {J : Type} (F : ℕ → Option J → Fn n) (l : List (Fn n)) (g : ℕ)
    (U : List (ℕ × Option (Fn n))) : Prop :=
  (∀ e ∈ U, e.1 < g ∧ (∀ μ, e.2 = some μ → Avail l μ) ∧
    ∀ o x, mult e.2 x = true → F e.1 o x = true → F g o x = true) ∧
  ∀ j x, F g (some j) x = true →
    F g none x = true ∨ ∃ e ∈ U, mult e.2 x = true ∧ F e.1 (some j) x = true

theorem pass {n : ℕ} {J : Type} (F : ℕ → Option J → Fn n) (base : ℕ) (l0 : List (Fn n))
    (U : ℕ → List (ℕ × Option (Fn n))) : ∀ (i : ℕ),
    (∀ i2 < i, StepOK F l0 (base + i2) (U i2)) →
    ∀ (l : List (Fn n)) (acc : ℕ → Fn n), Prog l → l0 ⊆ l → (∀ w, acc w ∈ l) →
    ∃ (l2 : List (Fn n)) (acc2 : ℕ → Fn n), Prog l2 ∧ l ⊆ l2 ∧
      l2.length ≤ l.length + ∑ i2 ∈ Finset.range i, cost (U i2) ∧ (∀ w, acc2 w ∈ l2) ∧
      (∀ w o x, acc2 w x = true → F w o x = true → ∃ w2, acc w2 x = true ∧ F w2 o x = true) ∧
      (∀ w, w < base + i → ∀ j x, acc w x = true → F w (some j) x = true →
        (∃ w2, acc w2 x = true ∧ F w2 none x = true) ∨
          ∃ w2, w2 < base ∧ acc2 w2 x = true ∧ F w2 (some j) x = true) := by
  intro i
  induction i with
  | zero =>
    intro _ l acc hP _ hacc
    refine ⟨l, acc, hP, List.Subset.refl l, by simp, hacc, fun w o x h1 h2 => ⟨w, h1, h2⟩, ?_⟩
    intro w hw j x h1 h2
    exact Or.inr ⟨w, by simpa using hw, h1, h2⟩
  | succ i ih =>
    intro hstep l acc hP hl0 hacc
    obtain ⟨hS1, hS2⟩ := hstep i (Nat.lt_succ_self i)
    obtain ⟨l1, acc1, hP1, hsub1, hlen1, hacc1, hiff⟩ := entries (acc (base + i)) (U i) l acc hP
      (hacc _) hacc (fun e he μ hμ => avail_mono hl0 ((hS1 e he).2.1 μ hμ))
    have hst : ∀ w o x, acc1 w x = true → F w o x = true →
        ∃ w2, acc w2 x = true ∧ F w2 o x = true := by
      intro w o x h1 h2
      rcases (hiff w x).1 h1 with h | ⟨e, he, hew, hG, hm⟩
      · exact ⟨w, h, h2⟩
      · refine ⟨base + i, hG, (hS1 e he).2.2 o x hm ?_⟩
        rw [hew]; exact h2
    obtain ⟨l2, acc2, hP2, hsub2, hlen2, hacc2, hs2, hc2⟩ :=
      ih (fun i2 h => hstep i2 (Nat.lt_succ_of_lt h)) l1 acc1 hP1
        (fun a ha => hsub1 (hl0 ha)) hacc1
    have hA : ∀ w, w < base + i → ∀ j x, acc1 w x = true → F w (some j) x = true →
        (∃ w2, acc w2 x = true ∧ F w2 none x = true) ∨
          ∃ w2, w2 < base ∧ acc2 w2 x = true ∧ F w2 (some j) x = true := by
      intro w hw j x h1 h2
      rcases hc2 w hw j x h1 h2 with ⟨w2, hw1, hw2⟩ | h
      · exact Or.inl (hst w2 none x hw1 hw2)
      · exact Or.inr h
    refine ⟨l2, acc2, hP2, fun a ha => hsub2 (hsub1 ha), ?_, hacc2, ?_, ?_⟩
    · rw [Finset.sum_range_succ]; omega
    · intro w o x h1 h2
      obtain ⟨w2, hw1, hw2⟩ := hs2 w o x h1 h2
      exact hst w2 o x hw1 hw2
    · intro w hw j x h1 h2
      by_cases hwi : w < base + i
      · exact hA w hwi j x ((hiff w x).2 (Or.inl h1)) h2
      · have hwe : w = base + i := by omega
        subst hwe
        rcases hS2 j x h2 with h | ⟨e, he, hm, hF⟩
        · exact Or.inl ⟨base + i, h1, h⟩
        · exact hA e.1 (hS1 e he).1 j x ((hiff e.1 x).2 (Or.inr ⟨e, he, rfl, h1, hm⟩)) hF

theorem target {n : ℕ} {J : Type} (F : ℕ → Option J → Fn n) (base : ℕ) (l : List (Fn n))
    (U : ℕ → List (ℕ × Option (Fn n))) (i : ℕ)
    (hstep : ∀ i2 < i, StepOK F l (base + i2) (U i2))
    (hP : Prog l) (hF : cF n ∈ l) (hT : cT n ∈ l) (t : ℕ) (ht : t < base + i) :
    ∃ (l2 : List (Fn n)) (acc2 : ℕ → Fn n), Prog l2 ∧ l ⊆ l2 ∧
      l2.length ≤ l.length + ∑ i2 ∈ Finset.range i, cost (U i2) ∧ (∀ w, acc2 w ∈ l2) ∧
      (∀ w o x, acc2 w x = true → F w o x = true → F t o x = true) ∧
      (∀ j x, F t (some j) x = true → F t none x = true ∨
          ∃ w2, w2 < base ∧ acc2 w2 x = true ∧ F w2 (some j) x = true) := by
  have hacc : ∀ w, (if w = t then cT n else cF n) ∈ l := by
    intro w
    by_cases hw : w = t
    · rw [ifp hw]; exact hT
    · rw [ifn hw]; exact hF
  have hone : ∀ (w : ℕ) (o : Option J) (x : Fin n → Bool),
      (if w = t then cT n else cF n) x = true → F w o x = true → F t o x = true := by
    intro w o x h1 h2
    by_cases hw : w = t
    · rw [← hw]; exact h2
    · rw [ifn hw] at h1; exact absurd h1 (by simp)
  obtain ⟨l2, acc2, hP2, hsub, hlen, hacc2, hs, hc⟩ := pass F base l U i hstep l
    (fun w => if w = t then cT n else cF n) hP (List.Subset.refl l) hacc
  refine ⟨l2, acc2, hP2, hsub, hlen, hacc2, ?_, ?_⟩
  · intro w o x h1 h2
    obtain ⟨w2, hw1, hw2⟩ := hs w o x h1 h2
    exact hone w2 o x hw1 hw2
  · intro j x h
    rcases hc t ht j x (by simp) h with ⟨w2, hw1, hw2⟩ | h2
    · exact Or.inl (hone w2 none x hw1 hw2)
    · exact Or.inr h2

theorem add_list {n : ℕ} : ∀ (fs : List (Fn n)) (l : List (Fn n)), Prog l →
    (∀ f ∈ fs, GForm l f) →
    ∃ l2 : List (Fn n), Prog l2 ∧ l ⊆ l2 ∧ l2.length ≤ l.length + fs.length ∧
      ∀ f ∈ fs, f ∈ l2 := by
  intro fs
  induction fs with
  | nil => intro l hP _; exact ⟨l, hP, List.Subset.refl l, by simp, by simp⟩
  | cons f fs ih =>
    intro l hP hfs
    have hsub : l ⊆ f :: l := List.subset_cons_self f l
    obtain ⟨l2, hP2, hsub2, hlen2, hmem⟩ := ih (f :: l)
      ⟨hP, Or.inr (Or.inr (hfs f (by simp)))⟩
      (fun g hg => gform_mono hsub (hfs g (by simp [hg])))
    refine ⟨l2, hP2, fun a ha => hsub2 (hsub ha), ?_, ?_⟩
    · simp only [List.length_cons] at hlen2 ⊢; omega
    · intro g hg
      rcases List.mem_cons.mp hg with h | h
      · rw [h]; exact hsub2 (by simp)
      · exact hmem g h

theorem add_fam {n m : ℕ} (l : List (Fn n)) (hP : Prog l) (fj : Fin m → Fn n)
    (h : ∀ j, GForm l (fj j)) :
    ∃ l2 : List (Fn n), Prog l2 ∧ l ⊆ l2 ∧ l2.length ≤ l.length + m ∧ ∀ j, fj j ∈ l2 := by
  obtain ⟨l2, hP2, hsub, hlen, hmem⟩ := add_list ((List.finRange m).map fj) l hP (by
    intro f hf
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
    exact h j)
  refine ⟨l2, hP2, hsub, by simpa using hlen, fun j => hmem _ ?_⟩
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

theorem base_and {n : ℕ} (l : List (Fn n)) (hP : Prog l) (hT : cT n ∈ l)
    (fs : List (Fn n)) (hlen : fs.length ≤ 2) (hav : ∀ f ∈ fs, Avail l f) (f : Fn n)
    (hf : ∀ x, f x = (fs.map (fun g => g x)).all id) :
    ∃ l1 : List (Fn n), Prog l1 ∧ l ⊆ l1 ∧ l1.length ≤ l.length + 1 ∧ Avail l1 f := by
  rcases fs with _ | ⟨g, _ | ⟨h, _ | ⟨z, rest⟩⟩⟩
  · have : f = cT n := funext fun x => by rw [hf x]; rfl
    exact ⟨l, hP, List.Subset.refl l, by omega, Or.inl (by rw [this]; exact hT)⟩
  · have : f = g := funext fun x => by rw [hf x]; simp
    exact ⟨l, hP, List.Subset.refl l, by omega, by rw [this]; exact hav g (by simp)⟩
  · have : f = fun x => g x && h x := funext fun x => by rw [hf x]; simp
    exact ⟨f :: l, ⟨hP, Or.inr (Or.inr ⟨g, h, hav g (by simp), hav h (by simp), Or.inl this⟩)⟩,
      List.subset_cons_self f l, by simp, Or.inl (by simp)⟩
  · simp at hlen

theorem base_or {n : ℕ} (l : List (Fn n)) (hP : Prog l) (hF : cF n ∈ l)
    (fs : List (Fn n)) (hlen : fs.length ≤ 2) (hav : ∀ f ∈ fs, Avail l f) (f : Fn n)
    (hf : ∀ x, f x = (fs.map (fun g => g x)).any id) :
    ∃ l1 : List (Fn n), Prog l1 ∧ l ⊆ l1 ∧ l1.length ≤ l.length + 1 ∧ Avail l1 f := by
  rcases fs with _ | ⟨g, _ | ⟨h, _ | ⟨z, rest⟩⟩⟩
  · have : f = cF n := funext fun x => by rw [hf x]; rfl
    exact ⟨l, hP, List.Subset.refl l, by omega, Or.inl (by rw [this]; exact hF)⟩
  · have : f = g := funext fun x => by rw [hf x]; simp
    exact ⟨l, hP, List.Subset.refl l, by omega, by rw [this]; exact hav g (by simp)⟩
  · have : f = fun x => g x || h x := funext fun x => by rw [hf x]; simp
    exact ⟨f :: l, ⟨hP, Or.inr (Or.inr ⟨g, h, hav g (by simp), hav h (by simp), Or.inr this⟩)⟩,
      List.subset_cons_self f l, by simp, Or.inl (by simp)⟩
  · simp at hlen

def inp (n m : ℕ) (x : Fin n → Bool) (o : Option (Fin m)) : Fin (n + m) → Bool :=
  Fin.append x (fun l => decide (some l = o))

def FF (n m : ℕ) (C : Circuit) (w : ℕ) (o : Option (Fin m)) : Fn n :=
  fun x => val C.gates w (inp n m x o)

theorem FF_pt (n m : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (o : Option (Fin m))
    (x : Fin n → Bool) : FF n m C w o x = x ⟨w, hw⟩ := by
  unfold FF
  rw [val_input C.gates _ w (by omega)]
  have : (⟨w, by omega⟩ : Fin (n + m)) = Fin.castAdd m ⟨w, hw⟩ := rfl
  rw [this]; unfold inp; rw [Fin.append_left]

theorem FF_ln (n m : ℕ) (C : Circuit) (l : Fin m) (o : Option (Fin m)) (x : Fin n → Bool) :
    FF n m C (n + l) o x = decide (some l = o) := by
  unfold FF
  rw [val_input C.gates _ (n + l) (by have := l.2; omega)]
  have : (⟨n + l, by have := l.2; omega⟩ : Fin (n + m)) = Fin.natAdd n l := rfl
  rw [this]; unfold inp; rw [Fin.append_right]

theorem FF_and (n m : ℕ) (C : Circuit) (i : ℕ) (hi : i < C.gates.length)
    (hin : ∀ a ∈ C.gates[i].inputs, a < n + m + i) (hop : C.gates[i].op = GateOp.and)
    (o : Option (Fin m)) (x : Fin n → Bool) :
    FF n m C (n + m + i) o x = true ↔ ∀ a ∈ C.gates[i].inputs, FF n m C a o x = true := by
  unfold FF
  rw [val_and C.gates _ i hi hop]
  exact ⟨fun h a ha => (h a ha).2, fun h a ha => ⟨hin a ha, h a ha⟩⟩

theorem FF_or (n m : ℕ) (C : Circuit) (i : ℕ) (hi : i < C.gates.length)
    (hin : ∀ a ∈ C.gates[i].inputs, a < n + m + i) (hop : C.gates[i].op = GateOp.or)
    (o : Option (Fin m)) (x : Fin n → Bool) :
    FF n m C (n + m + i) o x = true ↔ ∃ a ∈ C.gates[i].inputs, FF n m C a o x = true := by
  unfold FF
  rw [val_or C.gates _ i hi hop]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.2⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, hin a ha, h⟩⟩

theorem FF_big (n m : ℕ) (C : Circuit) (w : ℕ) (hw : n + m + C.gates.length ≤ w)
    (o : Option (Fin m)) (x : Fin n → Bool) : FF n m C w o x = false := by
  unfold FF
  exact val_big C.gates _ w hw

theorem FF_gate (n m : ℕ) (C : Circuit) (i : ℕ) (hi : i < C.gates.length)
    (hin : ∀ a ∈ C.gates[i].inputs, a < n + m + i) (o : Option (Fin m)) (x : Fin n → Bool) :
    FF n m C (n + m + i) o x
      = C.gates[i].op.eval (C.gates[i].inputs.map fun a => FF n m C a o x) := by
  unfold FF val
  have := gate_val C.gates (List.ofFn (inp n m x o)) i hi
  rw [List.length_ofFn] at this
  rw [this]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (wire_take C.gates _ i a (by simpa using hin a ha) (Nat.le_of_lt hi)).symm

theorem FF_mono (n m : ℕ) (C : Circuit)
    (hleg : ∀ i (hi : i < C.gates.length),
      C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or)
    (hin : ∀ i (hi : i < C.gates.length), ∀ a ∈ C.gates[i].inputs, a < n + m + i)
    (j : Fin m) (x : Fin n → Bool) :
    ∀ w, FF n m C w none x = true → FF n m C w (some j) x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases hw : w < n
    · rw [FF_pt n m C w hw] at h ⊢; exact h
    · by_cases hw2 : w < n + m
      · obtain ⟨q, rfl⟩ : ∃ q : Fin m, w = n + q :=
          ⟨⟨w - n, by omega⟩, by show w = n + (w - n); omega⟩
        rw [FF_ln] at h; simp at h
      · by_cases hw3 : w < n + m + C.gates.length
        · obtain ⟨i, rfl⟩ : ∃ i, w = n + m + i := ⟨w - (n + m), by omega⟩
          have hi : i < C.gates.length := by omega
          rcases hleg i hi with hop | hop
          · rw [FF_and n m C i hi (hin i hi) hop] at h ⊢
            exact fun a ha => ih a (hin i hi a ha) (h a ha)
          · rw [FF_or n m C i hi (hin i hi) hop] at h ⊢
            obtain ⟨a, ha, h2⟩ := h
            exact ⟨a, ha, ih a (hin i hi a ha) h2⟩
        · rw [FF_big n m C w (by omega)] at h; exact absurd h (by simp)

def df (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) d

theorem df_snoc (gs : List Gate) (g : Gate) (d : List ℕ) :
    df (gs ++ [g]) d = df gs d ++ [g.lineDegree (df gs d)] := by
  simp [df, List.foldl_append]

theorem df_len (gs : List Gate) : ∀ d : List ℕ, (df gs d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp [df]
  | cons g gs ih =>
    intro d
    have := ih (d ++ [g.lineDegree d])
    simp only [df, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem df_keep (gs : List Gate) : ∀ (d : List ℕ) (i : ℕ), i < d.length →
    (df gs d).getD i 0 = d.getD i 0 := by
  induction gs with
  | nil => intro d i _; rfl
  | cons g gs ih =>
    intro d i hi
    have := ih (d ++ [g.lineDegree d]) i (by simp; omega)
    simp only [df, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem df_prefix (pre post : List Gate) (d : List ℕ) (i : ℕ)
    (hi : i < d.length + pre.length) :
    (df (pre ++ post) d).getD i 0 = (df pre d).getD i 0 := by
  have : df (pre ++ post) d = df post (df pre d) := by simp [df, List.foldl_append]
  rw [this]
  exact df_keep post _ i (by rw [df_len]; exact hi)

theorem df_take (gates : List Gate) (d : List ℕ) (k i : ℕ) (hi : i < d.length + k)
    (hk : k ≤ gates.length) :
    (df gates d).getD i 0 = (df (gates.take k) d).getD i 0 := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact df_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem df_gate (gates : List Gate) (d : List ℕ) (k : ℕ) (hk : k < gates.length) :
    (df gates d).getD (d.length + k) 0 = gates[k].lineDegree (df (gates.take k) d) := by
  rw [df_take gates d (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, df_snoc]
  have h1 : ∀ (L : List ℕ) (a : ℕ), (L ++ [a]).getD L.length 0 = a := by
    intro L a; simp [List.getD_eq_getElem?_getD]
  have h2 := h1 (df (gates.take k) d) (gates[k].lineDegree (df (gates.take k) d))
  rw [df_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at h2
  exact h2

theorem sum_zero : ∀ (l : List ℕ), l.sum = 0 → ∀ a ∈ l, a = 0 := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons b l ih =>
    intro h a ha
    simp only [List.sum_cons] at h
    rcases List.mem_cons.mp ha with h2 | h2
    · omega
    · exact ih (by omega) a h2

theorem fmax_zero : ∀ (l : List ℕ), l.foldr max 0 = 0 → ∀ a ∈ l, a = 0 := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons b l ih =>
    intro h a ha
    simp only [List.foldr_cons] at h
    rcases List.mem_cons.mp ha with h2 | h2
    · omega
    · exact ih (by omega) a h2

theorem deg_zero (g : Gate) (d : List ℕ) (h : g.lineDegree d = 0) :
    ∀ a ∈ g.inputs, d.getD a 0 = 0 := by
  intro a ha
  unfold Gate.lineDegree at h
  split at h
  · exact sum_zero _ h _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · exact fmax_zero _ h _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem FF_deg0 (n m : ℕ) (C : Circuit)
    (hleg : ∀ i (hi : i < C.gates.length),
      C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or)
    (hin : ∀ i (hi : i < C.gates.length), ∀ a ∈ C.gates[i].inputs, a < n + m + i)
    (o : Option (Fin m)) (x : Fin n → Bool) :
    ∀ w, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 = 0 →
      FF n m C w o x = FF n m C w none x := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    by_cases hw : w < n
    · rw [FF_pt n m C w hw, FF_pt n m C w hw]
    · by_cases hw2 : w < n + m
      · exfalso
        have hn : n ≤ w := by omega
        have h1 : (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 = 1 := by
          show (df C.gates ((List.range (n + m)).map
            fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0)).getD w 0 = 1
          rw [df_keep _ _ w (by simpa using hw2)]
          simp [List.getD_eq_getElem?_getD, hw2, hn]
        omega
      · by_cases hw3 : w < n + m + C.gates.length
        · obtain ⟨i, rfl⟩ : ∃ i, w = n + m + i := ⟨w - (n + m), by omega⟩
          have hi : i < C.gates.length := by omega
          have hd2 : C.gates[i].lineDegree (df (C.gates.take i) ((List.range (n + m)).map
              fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0)) = 0 := by
            have := df_gate C.gates ((List.range (n + m)).map
              fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0) i hi
            rw [List.length_map, List.length_range] at this
            rw [← this]; exact hd
          have hall : ∀ a ∈ C.gates[i].inputs, FF n m C a o x = FF n m C a none x := by
            intro a ha
            apply ih a (hin i hi a ha)
            have h0 := deg_zero _ _ hd2 a ha
            rw [← df_take C.gates _ i a (by simpa using hin i hi a ha) (Nat.le_of_lt hi)] at h0
            exact h0
          rw [Bool.eq_iff_iff]
          rcases hleg i hi with hop | hop
          · rw [FF_and n m C i hi (hin i hi) hop, FF_and n m C i hi (hin i hi) hop]
            exact ⟨fun h a ha => by rw [← hall a ha]; exact h a ha,
              fun h a ha => by rw [hall a ha]; exact h a ha⟩
          · rw [FF_or n m C i hi (hin i hi) hop, FF_or n m C i hi (hin i hi) hop]
            exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, by rw [← hall a ha]; exact h⟩,
              fun ⟨a, ha, h⟩ => ⟨a, ha, by rw [hall a ha]; exact h⟩⟩
        · rw [FF_big n m C w (by omega), FF_big n m C w (by omega)]

theorem gateAt_eq (C : Circuit) (i : ℕ) (hi : i < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C i = C.gates[i] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  exact List.getD_eq_getElem _ _ hi

def KK (n m : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0

theorem cost_none {n : ℕ} : ∀ L : List ℕ,
    cost (L.map (fun u => ((u, none) : ℕ × Option (Fn n)))) = L.length := by
  intro L
  induction L with
  | nil => simp [cost]
  | cons a L ih =>
    simp only [cost, List.map_cons, List.sum_cons, List.length_cons, ecost] at ih ⊢
    omega

theorem cost_some {n m : ℕ} (φ : Fin m → Fn n) : ∀ L : List (Fin m),
    cost (L.map (fun j : Fin m => ((n + (j : ℕ), some (φ j)) : ℕ × Option (Fn n)))) = 2 * L.length := by
  intro L
  induction L with
  | nil => simp [cost]
  | cons a L ih =>
    simp only [cost, List.map_cons, List.sum_cons, List.length_cons, ecost] at ih ⊢
    omega

open Classical in
theorem step_ex (n m : ℕ) (C : Circuit)
    (hleg : ∀ i (hi : i < C.gates.length),
      (C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or) ∧ C.gates[i].inputs.length ≤ 2)
    (hin : ∀ i (hi : i < C.gates.length), ∀ a ∈ C.gates[i].inputs, a < n + m + i)
    (l : List (Fn n)) (i : ℕ) (hi : i < C.gates.length)
    (hav : ∀ w < n + m + i, Avail l (FF n m C w none))
    (hK : KK n m C i → ∀ j, FF n m C (n + m + i) (some j) ∈ l) :
    ∃ U : List (ℕ × Option (Fn n)), StepOK (FF n m C) l (n + m + i) U ∧
      cost U ≤ (if KK n m C i then 2 * m else 2) := by
  by_cases hk : KK n m C i
  · refine ⟨(List.finRange m).map
      (fun j : Fin m => ((n + (j : ℕ), some (FF n m C (n + m + i) (some j))) : ℕ × Option (Fn n))),
      ⟨?_, ?_⟩, ?_⟩
    · intro e he
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
      refine ⟨by have := j.2; show n + (j : ℕ) < n + m + i; omega, ?_, ?_⟩
      · intro μ hμ
        have hμ2 : FF n m C (n + m + i) (some j) = μ := Option.some.inj hμ
        rw [← hμ2]
        exact Or.inl (hK hk j)
      · intro o x hm hF
        have hF2 : FF n m C (n + (j : ℕ)) o x = true := hF
        rw [FF_ln] at hF2
        have hjo : some j = o := by simpa using hF2
        rw [← hjo]; exact hm
    · intro j x h
      refine Or.inr ⟨(n + (j : ℕ), some (FF n m C (n + m + i) (some j))),
        List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, h, ?_⟩
      show FF n m C (n + (j : ℕ)) (some j) x = true
      rw [FF_ln]; simp
    · rw [ifp hk, cost_some]; simp
  · rw [ifn hk]
    have hg := hleg i hi
    have hleg1 : ∀ i (hi : i < C.gates.length),
        C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or := fun i hi => (hleg i hi).1
    rcases hg.1 with hop | hop
    · have two : ∀ a b : ℕ, a < n + m + i → b < n + m + i →
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD b 0 = 0 →
          (∀ o x, FF n m C (n + m + i) o x = true ↔
            (FF n m C a o x = true ∧ FF n m C b o x = true)) →
          ∃ U : List (ℕ × Option (Fn n)), StepOK (FF n m C) l (n + m + i) U ∧ cost U ≤ 2 := by
        intro a b ha hb hdb hiff
        refine ⟨[(a, some (FF n m C b none))], ⟨?_, ?_⟩, by simp [cost, ecost]⟩
        · intro e he
          rw [List.mem_singleton] at he
          subst he
          refine ⟨ha, ?_, ?_⟩
          · intro μ hμ
            have hμ2 : FF n m C b none = μ := Option.some.inj hμ
            rw [← hμ2]; exact hav b hb
          · intro o x hm hF
            have hm2 : FF n m C b none x = true := hm
            rw [hiff o x]
            exact ⟨hF, by rw [FF_deg0 n m C hleg1 hin o x b hdb]; exact hm2⟩
        · intro j x h
          rw [hiff (some j) x] at h
          refine Or.inr ⟨(a, some (FF n m C b none)), by simp, ?_, h.1⟩
          show FF n m C b none x = true
          rw [← FF_deg0 n m C hleg1 hin (some j) x b hdb]; exact h.2
      rcases hinp : C.gates[i].inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
      · refine ⟨[], ⟨by simp, ?_⟩, by simp [cost]⟩
        intro j x _
        left
        rw [FF_and n m C i hi (hin i hi) hop, hinp]; simp
      · have hu : u < n + m + i := hin i hi u (by rw [hinp]; simp)
        refine ⟨[(u, none)], ⟨?_, ?_⟩, by simp [cost, ecost]⟩
        · intro e he
          rw [List.mem_singleton] at he
          subst he
          refine ⟨hu, by simp, ?_⟩
          intro o x _ hF
          rw [FF_and n m C i hi (hin i hi) hop, hinp]; simpa using hF
        · intro j x h
          rw [FF_and n m C i hi (hin i hi) hop, hinp] at h
          exact Or.inr ⟨(u, none), by simp, rfl, by simpa using h⟩
      · have hu : u < n + m + i := hin i hi u (by rw [hinp]; simp)
        have hv : v < n + m + i := hin i hi v (by rw [hinp]; simp)
        have h0 : (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD u 0 = 0 ∨
            (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD v 0 = 0 := by
          by_contra hcon
          push Not at hcon
          apply hk
          refine ⟨hi, ?_, ?_, ?_⟩
          · rw [gateAt_eq C i hi]; exact hop
          · rw [gateAt_eq C i hi, hinp]; rfl
          · rw [gateAt_eq C i hi, hinp]
            intro a ha
            simp at ha
            rcases ha with rfl | rfl
            · exact Nat.pos_of_ne_zero hcon.1
            · exact Nat.pos_of_ne_zero hcon.2
        rcases h0 with h0 | h0
        · exact two v u hv hu h0 (fun o x => by
            rw [FF_and n m C i hi (hin i hi) hop, hinp]; simp; tauto)
        · exact two u v hu hv h0 (fun o x => by
            rw [FF_and n m C i hi (hin i hi) hop, hinp]; simp)
      · exfalso
        have := hg.2
        rw [hinp] at this
        simp at this
    · refine ⟨C.gates[i].inputs.map (fun u => ((u, none) : ℕ × Option (Fn n))), ⟨?_, ?_⟩, ?_⟩
      · intro e he
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
        refine ⟨hin i hi u hu, by simp, ?_⟩
        intro o x _ hF
        rw [FF_or n m C i hi (hin i hi) hop]; exact ⟨u, hu, hF⟩
      · intro j x h
        rw [FF_or n m C i hi (hin i hi) hop] at h
        obtain ⟨u, hu, hF⟩ := h
        exact Or.inr ⟨(u, none), List.mem_map.mpr ⟨u, hu, rfl⟩, rfl, hF⟩
      · rw [cost_none]; exact hg.2

open Classical in
noncomputable def kap (n m : ℕ) (C : Circuit) : ℕ → ℕ
  | 0 => 0
  | i + 1 => kap n m C i + (if KK n m C i then 1 else 0)

open Classical in
theorem kap_eq (n m : ℕ) (C : Circuit) : ∀ i,
    kap n m C i = ((Finset.range i).filter (fun j => KK n m C j)).card := by
  intro i
  induction i with
  | zero => simp [kap]
  | succ i ih =>
    rw [kap, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : KK n m C i
    · rw [ifp h, ifp h, Finset.card_insert_of_notMem (by simp)]
    · rw [ifn h, ifn h]; simp

open Classical in
theorem kap_mono (n m : ℕ) (C : Circuit) (i : ℕ) : ∀ d, kap n m C i ≤ kap n m C (i + d) := by
  intro d
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
    have : kap n m C (i + (d + 1)) = kap n m C (i + d) + (if KK n m C (i + d) then 1 else 0) :=
      rfl
    omega

open Classical in
theorem kap_le (n m k : ℕ) (C : Circuit) (hk : Set.ncard {j : ℕ | KK n m C j} ≤ k) :
    kap n m C C.gates.length ≤ k := by
  rw [kap_eq]
  have hset : {j : ℕ | KK n m C j}
      = ↑((Finset.range C.gates.length).filter (fun j => KK n m C j)) := by
    ext j
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  rw [hset, Set.ncard_coe_finset] at hk
  exact hk

open Classical in
theorem pcb (n m : ℕ) (C : Circuit) : ∀ i,
    ∑ i2 ∈ Finset.range i, (if KK n m C i2 then 2 * m else 2) ≤ 2 * i + 2 * m * kap n m C i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hk : kap n m C (i + 1) = kap n m C i + (if KK n m C i then 1 else 0) := rfl
    rw [Finset.sum_range_succ, hk]
    by_cases h : KK n m C i
    · simp only [ifp h]
      have : 2 * m * (kap n m C i + 1) = 2 * m * kap n m C i + 2 * m := by ring
      omega
    · simp only [ifn h, Nat.add_zero]
      omega

open Classical in
theorem wire_all (n m k : ℕ) (C : Circuit)
    (hleg : ∀ i (hi : i < C.gates.length),
      (C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or) ∧ C.gates[i].inputs.length ≤ 2)
    (hin : ∀ i (hi : i < C.gates.length), ∀ a ∈ C.gates[i].inputs, a < n + m + i)
    (hkap : kap n m C C.gates.length ≤ k) (l : List (Fn n)) (i : ℕ) (hi : i ≤ C.gates.length)
    (hP : Prog l) (hF : cF n ∈ l) (hT : cT n ∈ l)
    (hav : ∀ w < n + m + i, Avail l (FF n m C w none))
    (hK : ∀ g < i, KK n m C g → ∀ j, FF n m C (n + m + g) (some j) ∈ l)
    (t : ℕ) (ht : t < n + m + i) :
    ∃ l2 : List (Fn n), Prog l2 ∧ l ⊆ l2 ∧
      l2.length ≤ l.length + (2 * C.gates.length + 2 * m * k) + m ∧
      ∀ j, FF n m C t (some j) ∈ l2 := by
  have hex : ∀ i2, ∃ U : List (ℕ × Option (Fn n)), i2 < i →
      (StepOK (FF n m C) l (n + m + i2) U ∧ cost U ≤ (if KK n m C i2 then 2 * m else 2)) := by
    intro i2
    by_cases h : i2 < i
    · obtain ⟨U, hU⟩ := step_ex n m C hleg hin l i2 (by omega)
        (fun w hw => hav w (by omega)) (hK i2 h)
      exact ⟨U, fun _ => hU⟩
    · exact ⟨[], fun h2 => absurd h2 h⟩
  choose U hU using hex
  obtain ⟨l1, acc, hP1, hsub1, hlen1, hacc, hs, hc⟩ := target (FF n m C) (n + m) l U i
    (fun i2 h => (hU i2 h).1) hP hF hT t ht
  have hcost : ∑ i2 ∈ Finset.range i, cost (U i2) ≤ 2 * C.gates.length + 2 * m * k := by
    have h0 : ∑ i2 ∈ Finset.range i, cost (U i2)
        ≤ ∑ i2 ∈ Finset.range i, (if KK n m C i2 then 2 * m else 2) :=
      Finset.sum_le_sum (fun i2 h => (hU i2 (Finset.mem_range.mp h)).2)
    have h1 := pcb n m C i
    have h2 : kap n m C i ≤ k := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
      have := kap_mono n m C i d
      rw [← hd] at this
      omega
    have h3 := Nat.mul_le_mul_left (2 * m) h2
    omega
  have hfun : ∀ j : Fin m,
      FF n m C t (some j) = fun x => FF n m C t none x || acc (n + (j : ℕ)) x := by
    intro j
    funext x
    rw [Bool.eq_iff_iff, Bool.or_eq_true]
    constructor
    · intro h
      rcases hc j x h with h0 | ⟨w2, hw2, ha, hF2⟩
      · exact Or.inl h0
      · by_cases hwn : w2 < n
        · left
          apply hs w2 none x ha
          rw [FF_pt n m C w2 hwn] at hF2 ⊢; exact hF2
        · obtain ⟨q, rfl⟩ : ∃ q : Fin m, w2 = n + q :=
            ⟨⟨w2 - n, by omega⟩, by show w2 = n + (w2 - n); omega⟩
          rw [FF_ln] at hF2
          have hqj : q = j := by simpa using hF2
          rw [hqj] at ha
          exact Or.inr ha
    · rintro (h | h)
      · exact FF_mono n m C (fun i hi => (hleg i hi).1) hin j x t h
      · apply hs (n + (j : ℕ)) (some j) x h
        rw [FF_ln]; simp
  obtain ⟨l2, hP2, hsub2, hlen2, hmem⟩ := add_fam l1 hP1 (fun j => FF n m C t (some j)) (by
    intro j
    exact ⟨FF n m C t none, acc (n + (j : ℕ)), avail_mono hsub1 (hav t ht), Or.inl (hacc _),
      Or.inr (hfun j)⟩)
  exact ⟨l2, hP2, fun a ha => hsub2 (hsub1 ha), by omega, hmem⟩

open Classical in
theorem inv (n m k : ℕ) (C : Circuit)
    (hleg : ∀ i (hi : i < C.gates.length),
      (C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or) ∧ C.gates[i].inputs.length ≤ 2)
    (hin : ∀ i (hi : i < C.gates.length), ∀ a ∈ C.gates[i].inputs, a < n + m + i)
    (hkap : kap n m C C.gates.length ≤ k) : ∀ i, i ≤ C.gates.length →
    ∃ l : List (Fn n), Prog l ∧ cF n ∈ l ∧ cT n ∈ l ∧
      (∀ w < n + m + i, Avail l (FF n m C w none)) ∧
      (∀ g < i, KK n m C g → ∀ j, FF n m C (n + m + g) (some j) ∈ l) ∧
      l.length ≤ 2 + i + kap n m C i * (2 * (2 * C.gates.length + 2 * m * k) + 3 * m) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨[cT n, cF n], ⟨⟨trivial, Or.inl rfl⟩, Or.inr (Or.inl rfl)⟩, by simp, by simp, ?_,
      ?_, by simp [kap]⟩
    · intro w hw
      by_cases hwn : w < n
      · exact Or.inr ⟨⟨w, hwn⟩, funext fun x => FF_pt n m C w hwn none x⟩
      · obtain ⟨q, rfl⟩ : ∃ q : Fin m, w = n + q :=
          ⟨⟨w - n, by omega⟩, by show w = n + (w - n); omega⟩
        left
        have : FF n m C (n + q) none = cF n := funext fun x => by rw [FF_ln]; simp
        rw [this]; simp
    · intro g hg; omega
  | succ i ih =>
    intro hi
    have hi2 : i < C.gates.length := hi
    obtain ⟨l, hP, hF, hT, hav, hK, hlen⟩ := ih (Nat.le_of_lt hi2)
    have hkk : kap n m C (i + 1) = kap n m C i + (if KK n m C i then 1 else 0) := rfl
    obtain ⟨l1, hP1, hsub1, hlen1, hav1⟩ : ∃ l1 : List (Fn n), Prog l1 ∧ l ⊆ l1 ∧
        l1.length ≤ l.length + 1 ∧ Avail l1 (FF n m C (n + m + i) none) := by
      have hfs : ∀ f ∈ C.gates[i].inputs.map (fun a => FF n m C a none), Avail l f := by
        intro f hf
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
        exact hav a (hin i hi2 a ha)
      have hl2 : (C.gates[i].inputs.map (fun a => FF n m C a none)).length ≤ 2 := by
        rw [List.length_map]; exact (hleg i hi2).2
      rcases (hleg i hi2).1 with hop | hop
      · exact base_and l hP hT _ hl2 hfs _ (fun x => by
          rw [FF_gate n m C i hi2 (hin i hi2) none x, hop, List.map_map]; rfl)
      · exact base_or l hP hF _ hl2 hfs _ (fun x => by
          rw [FF_gate n m C i hi2 (hin i hi2) none x, hop, List.map_map]; rfl)
    have hav2 : ∀ w < n + m + (i + 1), Avail l1 (FF n m C w none) := by
      intro w hw
      by_cases h : w < n + m + i
      · exact avail_mono hsub1 (hav w h)
      · have : w = n + m + i := by omega
        rw [this]; exact hav1
    by_cases hk : KK n m C i
    · have hop : C.gates[i].op = GateOp.and := by
        have := hk.2.1
        rw [gateAt_eq C i hi2] at this
        exact this
      have hl2 : C.gates[i].inputs.length = 2 := by
        have := hk.2.2.1
        rw [gateAt_eq C i hi2] at this
        exact this
      rcases hinp : C.gates[i].inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
      · rw [hinp] at hl2; simp at hl2
      · rw [hinp] at hl2; simp at hl2
      · have hu : u < n + m + i := hin i hi2 u (by rw [hinp]; simp)
        have hv : v < n + m + i := hin i hi2 v (by rw [hinp]; simp)
        obtain ⟨l2, hP2, hsub2, hlen2, hmu⟩ := wire_all n m k C hleg hin hkap l1 i
          (Nat.le_of_lt hi2) hP1 (hsub1 hF) (hsub1 hT)
          (fun w hw => avail_mono hsub1 (hav w hw))
          (fun g hg hKg j => hsub1 (hK g hg hKg j)) u hu
        obtain ⟨l3, hP3, hsub3, hlen3, hmv⟩ := wire_all n m k C hleg hin hkap l2 i
          (Nat.le_of_lt hi2) hP2 (hsub2 (hsub1 hF)) (hsub2 (hsub1 hT))
          (fun w hw => avail_mono (fun a ha => hsub2 (hsub1 ha)) (hav w hw))
          (fun g hg hKg j => hsub2 (hsub1 (hK g hg hKg j))) v hv
        obtain ⟨l4, hP4, hsub4, hlen4, hmg⟩ := add_fam l3 hP3
          (fun j => FF n m C (n + m + i) (some j)) (by
            intro j
            refine ⟨FF n m C u (some j), FF n m C v (some j), Or.inl (hsub3 (hmu j)),
              Or.inl (hmv j), Or.inl ?_⟩
            funext x
            rw [FF_gate n m C i hi2 (hin i hi2) (some j) x, hop, hinp]
            simp [GateOp.eval])
        have hs14 : l1 ⊆ l4 := fun a ha => hsub4 (hsub3 (hsub2 ha))
        refine ⟨l4, hP4, hs14 (hsub1 hF), hs14 (hsub1 hT),
          fun w hw => avail_mono hs14 (hav2 w hw), ?_, ?_⟩
        · intro g hg hKg j
          by_cases hgi : g < i
          · exact hs14 (hsub1 (hK g hgi hKg j))
          · have : g = i := by omega
            rw [this]; exact hmg j
        · rw [hkk, ifp hk, Nat.add_mul, Nat.one_mul]; omega
      · rw [hinp] at hl2; simp at hl2
    · refine ⟨l1, hP1, hsub1 hF, hsub1 hT, hav2, ?_, ?_⟩
      · intro g hg hKg j
        by_cases hgi : g < i
        · exact hsub1 (hK g hgi hKg j)
        · have : g = i := by omega
          rw [this] at hKg
          exact absurd hKg hk
      · simp only [hkk, ifn hk, Nat.add_zero]; omega

theorem arith (k s m len : ℕ) (h1 : 1 ≤ len) (hs : len ≤ s) :
    2 + len + k * (2 * (2 * len + 2 * m * k) + 3 * m) + (2 * len + 2 * m * k) + m + m
      ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  obtain ⟨e, rfl⟩ : ∃ e, len = e + 1 := ⟨len - 1, by omega⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  have : (6 * k + 6) * (e + 1 + d) + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k
      = (2 + (e + 1) + k * (2 * (2 * (e + 1) + 2 * m * k) + 3 * m) + (2 * (e + 1) + 2 * m * k)
          + m + m)
        + (2 * k * (e + 1) + 3 * e + 1 + (6 * k + 6) * d + 8 * k ^ 2 * m + 8 * k * m
          + 6 * k ^ 2 + 5 * k) := by ring
  rw [this]
  exact Nat.le_add_right _ _

theorem final : ∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  intro n m s k L C hL hmono hrb hsize hk hsound
  have hleg : ∀ i (hi : i < C.gates.length),
      (C.gates[i].op = GateOp.and ∨ C.gates[i].op = GateOp.or) ∧
        C.gates[i].inputs.length ≤ 2 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmono _ (List.getElem_mem hi)
    refine ⟨?_, h2⟩
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hin : ∀ i (hi : i < C.gates.length), ∀ a ∈ C.gates[i].inputs, a < n + m + i := by
    intro i hi a ha
    apply hrb i hi a
    rw [gateAt_eq C i hi]; exact ha
  have hcf : ∀ (x : Fin n → Bool) (j : Fin m),
      PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j)))
        = FF n m C C.output (some j) x := by
    intro x j
    have : (fun l : Fin m => decide (l = j)) = (fun l => decide (some l = some j)) := by
      funext l; simp
    rw [this]; rfl
  have hcf0 : ∀ (x : Fin n → Bool),
      PEqualNP.MetaComplexity.circuitFun (n + m) C
        (Fin.append x (fun l => decide (l ∈ (∅ : Finset (Fin m)))))
        = FF n m C C.output none x := by
    intro x
    have : (fun l : Fin m => decide (l ∈ (∅ : Finset (Fin m))))
        = (fun l => decide (some l = none)) := by
      funext l; simp
    rw [this]; rfl
  have hC0 : ∀ x, FF n m C C.output none x = false := by
    intro x
    by_contra hne
    have ht : PEqualNP.MetaComplexity.circuitFun (n + m) C
        (Fin.append x (fun l => decide (l ∈ (∅ : Finset (Fin m))))) = true := by
      rw [hcf0]; simpa using hne
    obtain ⟨j, hj, _⟩ := hsound x ∅ (by simp) ht
    simp at hj
  have hsing : ∀ j : Fin m, (fun l : Fin m => decide (l ∈ ({j} : Finset (Fin m))))
      = (fun l => decide (l = j)) := by
    intro j; funext l; simp
  have hco : ∀ j : Fin m,
      FF n m C C.output (some j) (fun i => decide (i ∉ L j)) = false := by
    intro j
    by_contra hne
    have ht : PEqualNP.MetaComplexity.circuitFun (n + m) C
        (Fin.append (fun i : Fin n => decide (i ∉ L j))
          (fun l => decide (l ∈ ({j} : Finset (Fin m))))) = true := by
      rw [hsing j, hcf]; simpa using hne
    obtain ⟨j2, hj2, p, hp, hx⟩ := hsound _ {j} (by simp) ht
    rw [Finset.mem_singleton] at hj2
    subst hj2
    simp [hp] at hx
  by_cases hlen0 : C.gates.length = 0
  · have hempty : (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1))
          (fun l => decide (l = e.2))) = true)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro ⟨p, j⟩ _ ⟨hp, hacc⟩
      have hacc2 : FF n m C C.output (some j) (fun i => decide (i = p)) = true := by
        rw [← hcf]; exact hacc
      by_cases hw : C.output < n
      · have h0 := hC0 (fun i => decide (i = p))
        rw [FF_pt n m C _ hw] at hacc2 h0
        rw [hacc2] at h0; exact absurd h0 (by simp)
      · by_cases hw2 : C.output < n + m
        · obtain ⟨q, hq⟩ : ∃ q : Fin m, C.output = n + q :=
            ⟨⟨C.output - n, by omega⟩, by show C.output = n + (C.output - n); omega⟩
          have h1 := hco j
          rw [hq, FF_ln] at hacc2 h1
          rw [hacc2] at h1; exact absurd h1 (by simp)
        · rw [FF_big n m C _ (by omega)] at hacc2; exact absurd hacc2 (by simp)
    rw [hempty]; simp
  · have hkap : kap n m C C.gates.length ≤ k := kap_le n m k C hk
    obtain ⟨l, hP, hF, hT, hav, hK, hlen⟩ :=
      inv n m k C hleg hin hkap C.gates.length (le_refl _)
    obtain ⟨l2, hP2, hlen2, hout⟩ : ∃ l2 : List (Fn n), Prog l2 ∧
        l2.length ≤ l.length + (2 * C.gates.length + 2 * m * k) + m ∧
        ∀ j, FF n m C C.output (some j) ∈ l2 := by
      by_cases ho : C.output < n + m + C.gates.length
      · obtain ⟨l2, hP2, _, hlen2, hmem⟩ := wire_all n m k C hleg hin hkap l C.gates.length
          (le_refl _) hP hF hT hav hK C.output ho
        exact ⟨l2, hP2, hlen2, hmem⟩
      · refine ⟨l, hP, by omega, fun j => ?_⟩
        have : FF n m C C.output (some j) = cF n :=
          funext fun x => FF_big n m C _ (by omega) (some j) x
        rw [this]; exact hF
    obtain ⟨gs, hgl, hgleg, hgin, hgval⟩ := prog_circ l2 hP2
    have hw : ∀ j : Fin m, ∃ w, ∀ x, val gs w x = FF n m C C.output (some j) x := by
      intro j
      obtain ⟨w, _, hwv⟩ := hgval _ (Or.inl (hout j))
      exact ⟨w, hwv⟩
    choose o ho using hw
    let A : Fin m → Finset (Fin n) := fun j => (L j).filter (fun p =>
      PEqualNP.MetaComplexity.circuitFun (n + m) C
        (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)
    have hA : ∀ j : Fin m, A j ⊆ L j := fun j => Finset.filter_subset _ _
    have hcount := main n m L A gs o hL hgleg (fun i a ha => hgin i i.2 a ha) hA
      (fun j p hp => by rw [ho, ← hcf]; exact (Finset.mem_filter.mp hp).2)
      (fun j => by rw [ho]; exact hco j)
    have hsub : (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1))
          (fun l => decide (l = e.2))) = true)) ⊆
        (Finset.univ : Finset (Fin m)).biUnion (fun j => (A j).image (fun p => (p, j))) := by
      intro e he
      rw [Finset.mem_filter] at he
      rw [Finset.mem_biUnion]
      refine ⟨e.2, Finset.mem_univ _, ?_⟩
      rw [Finset.mem_image]
      exact ⟨e.1, Finset.mem_filter.mpr ⟨he.2.1, he.2.2⟩, rfl⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 : ((Finset.univ : Finset (Fin m)).biUnion
        (fun j => (A j).image (fun p => (p, j)))).card ≤ ∑ j : Fin m, (A j).card :=
      le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun j _ => Finset.card_image_le))
    have hc3 : ∑ j : Fin m, (A j).card ≤ ∑ j : Fin m, ((A j).card - 1) + m := by
      have : ∑ j : Fin m, (A j).card ≤ ∑ j : Fin m, (((A j).card - 1) + 1) :=
        Finset.sum_le_sum (fun j _ => by omega)
      rw [Finset.sum_add_distrib] at this
      simpa using this
    have hs : C.gates.length ≤ s := hsize
    have ha := arith k s m C.gates.length (by omega) hs
    have hkx := Nat.mul_le_mul_right (2 * (2 * C.gates.length + 2 * m * k) + 3 * m) hkap
    omega

end PEqualNP.Outside.L_meta_1625

theorem PEqualNP.Outside.L_meta_1625 : ∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  exact PEqualNP.Outside.L_meta_1625.final
