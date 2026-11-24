import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1576_aux

-- The counting lemmas below are from the public proof of L-meta-1567.
namespace Counting
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
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at hwc h1 h2
      have hm := hc _ hwc
      have e1 := (hτ y hy _ hm).1 h1
      have e2 := (hτ y' hy' _ hm).1 h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : 1 ≤ gates[w - n].inputs.length ∧ ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp.2 j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp.2 j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp.2 j hj, hv⟩
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
          have hjlt := hinp.2 a (by rw [hinpe]; simp)
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
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
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
    have ha : a < n + (g : ℕ) := (hin g).2 a hma
    have hb : b < n + (g : ℕ) := (hin g).2 b hmb
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
      single gates M c τ hc hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hc hτ legal hin g (le_of_lt g.2) X hX b hb hbc
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
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
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
        = (P gates M c τ k).card := step gates M c τ hc hτ legal hin ⟨k, hk'⟩
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
theorem three {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hc : ∀ v, c v = false → v ∈ M)
    (hτ : ∀ p ∈ M, ∀ v ∈ M, τ p v = true ↔ v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : M.card = 4) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 3 := by
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
      have hs := single gates M c τ hc hτ legal hin gates.length le_rfl X hX o holt hoc
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
  have hcnt := count gates M c τ hc hτ legal hin gates.length le_rfl
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
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ 3 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans (by norm_num))
  exact Nat.pow_right_injective (le_refl 2) h8

end Counting

-- The payers lemmas below are from the public proof of L-meta-1575.
namespace Payers
open PEqualNP.CircuitLowerBounds
abbrev P := Fin 13

def line (t : P) : Finset P := {t, t + 1, t + 3, t + 9}
def LS : Finset P := {4, 10, 12}
def MS : Finset P := {1, 5, 11}

def coline (t : P) : P → Bool := fun v => decide (v ∉ line t)

def testInp (t y : P) : P → Bool :=
  fun v => decide (v = y ∨ (t ∈ LS ∧ y ≠ 0 ∧ v = 1) ∨ (t ∈ MS ∧ y ≠ 1 ∧ v = 0))

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def val (gates : List Gate) (w : ℕ) (x : P → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

lemma val_input (gates : List Gate) (p : P) (x : P → Bool) :
    val gates p.val x = x p := by
  change (run gates (List.ofFn x)).getD p.val false = x p
  have hp : p.val < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp only [List.getElem_ofFn, Fin.eta]

lemma val_gate (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val) :
    val gates (13 + i.val) x =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => val gates a x) := by
  let j := i.val
  have hj : j < gates.length := i.isLt
  let g := gates[j]
  let earlier := run (gates.take j) (List.ofFn x)
  have plen : earlier.length = 13 + j := by
    simp [earlier, run_length, j]
  have split : run gates (List.ofFn x) = run (g :: gates.drop (j + 1)) earlier := by
    rw [run_split gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (a : ℕ) (ha : a < 13 + j) : earlier.getD a false = val gates a x := by
    change earlier.getD a false = (run gates (List.ofFn x)).getD a false
    rw [split]
    exact (run_getD _ earlier a (by simpa only [plen] using ha)).symm
  change (run gates (List.ofFn x)).getD (13 + j) false =
    g.op.eval (g.inputs.map fun a => val gates a x)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact read a (hwf a ha)

lemma val_mono (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (x y : P → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w : ℕ, w < 13 + gates.length → val gates w x = true → val gates w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hx
    by_cases hw : w < 13
    · let p : P := ⟨w, hw⟩
      have hp : p.val = w := rfl
      rw [← hp, val_input] at hx ⊢
      exact hxy p hx
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      rw [← hi, val_gate gates i x (hWF i).2] at hx
      rw [← hi, val_gate gates i y (hWF i).2]
      obtain ⟨hop, _⟩ := hG (gates.get i) (List.get_mem _ _)
      rcases hop with hop | hop
      · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hx ⊢
        intro a ha
        have hlt_a := (hWF i).2 a ha
        exact ih a (by omega) (by omega) (hx a ha)
      · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
        obtain ⟨a, ha, hva⟩ := hx
        have hlt_a := (hWF i).2 a ha
        exact ⟨a, ha, ih a (by omega) (by omega) hva⟩

lemma val_or_iff (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.or) :
    val gates (13 + i.val) x = true ↔ ∃ a ∈ (gates.get i).inputs, val gates a x = true := by
  rw [val_gate gates i x hwf, hop]
  simp [GateOp.eval]

lemma val_or_false (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.or)
    (hf : val gates (13 + i.val) x = false) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    val gates a x = false := by
  cases h : val gates a x with
  | false => rfl
  | true =>
    have ht : val gates (13 + i.val) x = true := (val_or_iff gates i x hwf hop).mpr ⟨a, ha, h⟩
    rw [hf] at ht
    exact Bool.noConfusion ht

lemma val_and_true (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.and)
    (ht : val gates (13 + i.val) x = true) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    val gates a x = true := by
  rw [val_gate gates i x hwf] at ht
  simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at ht
  exact ht a ha

lemma val_and_false_exists (gates : List Gate) (i : Fin gates.length) (x : P → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hop : (gates.get i).op = GateOp.and)
    (hf : val gates (13 + i.val) x = false) :
    ∃ a ∈ (gates.get i).inputs, val gates a x = false := by
  rw [val_gate gates i x hwf, hop] at hf
  simpa only [GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id_eq, Bool.not_eq_true] using hf

def CutRespect (gates : List Gate) (t : P) (g : Fin gates.length) (X : Finset P) : Prop :=
  ∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
    val gates (13 + i.val) (coline t) = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ line t, ∀ y' ∈ line t,
      (val gates a (testInp t y) = true ∨ val gates b (testInp t y) = true) →
      (val gates a (testInp t y') = true ∨ val gates b (testInp t y') = true) →
      (y ∈ X ↔ y' ∈ X)

def Merges (gates : List Gate) (t : P) (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧
  val gates (13 + g.val) (coline t) = false ∧
  ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧
    ∃ r ∈ line t, ∃ r' ∈ line t,
      val gates w1 (testInp t r) = true ∧ val gates w2 (testInp t r') = true ∧
      ∃ X : Finset P, r ∈ X ∧ r' ∉ X ∧ CutRespect gates t g X

def OrReach (gates : List Gate) (start target : ℕ) : Prop :=
  ∀ S : Set ℕ, start ∈ S →
    (∀ i : Fin gates.length, 13 + i.val ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) →
    target ∈ S

lemma orReach_refl (gates : List Gate) (w : ℕ) : OrReach gates w w :=
  fun _ h _ => h

lemma orReach_trans (gates : List Gate) {u v w : ℕ}
    (h1 : OrReach gates u v) (h2 : OrReach gates v w) : OrReach gates u w :=
  fun S hu hstep => h2 S (h1 S hu hstep) hstep

lemma orReach_step (gates : List Gate) (i : Fin gates.length)
    (hop : (gates.get i).op = GateOp.or) {a : ℕ} (ha : a ∈ (gates.get i).inputs) :
    OrReach gates (13 + i.val) a :=
  fun _ hi hstep => hstep i hi hop a ha

lemma orReach_le (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    {u v : ℕ} (h : OrReach gates u v) : v ≤ u :=
  h {w | w ≤ u} (by simp) fun i hi _ a ha => le_trans (le_of_lt ((hWF i).2 a ha)) hi

lemma orReach_false (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    {u v : ℕ} (h : OrReach gates u v) (x : P → Bool)
    (hu : val gates u x = false) : val gates v x = false :=
  h {w | val gates w x = false} hu fun i hi hop _ ha =>
    val_or_false gates i x (hWF i).2 hop hi ha

lemma orReach_find_stop (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (x : P → Bool) :
    ∀ w : ℕ, w < 13 + gates.length → val gates w x = true →
      (∃ v : P, OrReach gates w v.val ∧ x v = true) ∨
      (∃ z : Fin gates.length, (gates.get z).op = GateOp.and ∧
        OrReach gates w (13 + z.val) ∧ val gates (13 + z.val) x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hval
    by_cases hw : w < 13
    · let p : P := ⟨w, hw⟩
      have hp : p.val = w := rfl
      rw [← hp, val_input] at hval
      exact Or.inl ⟨p, orReach_refl gates w, hval⟩
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      obtain ⟨hop | hop, _⟩ := hG (gates.get i) (List.get_mem _ _)
      · exact Or.inr ⟨i, hop, hi ▸ orReach_refl gates w, hi.symm ▸ hval⟩
      · rw [← hi] at hval
        obtain ⟨a, ha, hva⟩ := (val_or_iff gates i x (hWF i).2 hop).mp hval
        have hlt_a := (hWF i).2 a ha
        have hstep : OrReach gates w a := hi ▸ orReach_step gates i hop ha
        rcases ih a (by omega) (by omega) hva with ⟨v, hrv, hxv⟩ | ⟨z, hzop, hrz, hvz⟩
        · exact Or.inl ⟨v, orReach_trans gates hstep hrv, hxv⟩
        · exact Or.inr ⟨z, hzop, orReach_trans gates hstep hrz, hvz⟩

lemma testInp_in_line_eq : ∀ t : P, t ∈ LS ∨ t ∈ MS → ∀ y ∈ line t, ∀ v ∈ line t,
    testInp t y v = true → v = y := by decide

lemma testInp_base_le_coline_LM : ∀ l ∈ LS, ∀ m ∈ MS, ∀ v : P,
    testInp l 0 v = true → coline m v = true := by decide

lemma testInp_base_le_coline_ML : ∀ m ∈ MS, ∀ l ∈ LS, ∀ v : P,
    testInp m 1 v = true → coline l v = true := by decide

lemma testInp_other_le_coline_LL : ∀ l1 ∈ LS, ∀ l2 ∈ LS, l1 ≠ l2 → ∀ y ∈ line l1, y ≠ 0 → ∀ v : P,
    testInp l1 y v = true → coline l2 v = true := by decide

lemma testInp_other_le_coline_MM : ∀ m1 ∈ MS, ∀ m2 ∈ MS, m1 ≠ m2 → ∀ y ∈ line m1, y ≠ 1 → ∀ v : P,
    testInp m1 y v = true → coline m2 v = true := by decide

lemma inter_LM_card : ∀ l ∈ LS, ∀ m ∈ MS, (line l ∩ line m).card = 1 := by decide
lemma inter_ML_card : ∀ m ∈ MS, ∀ l ∈ LS, (line m ∩ line l).card = 1 := by decide
lemma line_sdiff_base_L : ∀ l ∈ LS, (line l \ {0}).card = 3 := by decide
lemma line_sdiff_base_M : ∀ m ∈ MS, (line m \ {1}).card = 3 := by decide

lemma wire_same_comp (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t : P) (ht : t ∈ LS ∨ t ∈ MS) (g : Fin gates.length) (X : Finset P)
    (hcut : CutRespect gates t g X) :
    ∀ w : ℕ, w < 13 + g.val → val gates w (coline t) = false →
      ∀ y ∈ line t, ∀ y' ∈ line t,
        val gates w (testInp t y) = true → val gates w (testInp t y') = true →
        (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hcol y hy y' hy' hvy hvy'
    by_cases hw : w < 13
    · let v : P := ⟨w, hw⟩
      have hv : v.val = w := rfl
      rw [← hv, val_input] at hcol hvy hvy'
      have hvl : v ∈ line t := by simpa [coline] using hcol
      have heq1 := testInp_in_line_eq t ht y hy v hvl hvy
      have heq2 := testInp_in_line_eq t ht y' hy' v hvl hvy'
      rw [← heq1, ← heq2]
    · let i : Fin gates.length := ⟨w - 13, by omega⟩
      have hi : 13 + i.val = w := by change 13 + (w - 13) = w; omega
      have hig : i < g := by change i.val < g.val; omega
      obtain ⟨hop | hop, hlen⟩ := hG (gates.get i) (List.get_mem _ _)
      · rw [← hi] at hcol hvy hvy'
        obtain ⟨a, ha, hfa⟩ := val_and_false_exists gates i (coline t) (hWF i).2 hop hcol
        have hlt_a := (hWF i).2 a ha
        have hya := val_and_true gates i (testInp t y) (hWF i).2 hop hvy ha
        have hya' := val_and_true gates i (testInp t y') (hWF i).2 hop hvy' ha
        exact ih a (by omega) (by omega) hfa y hy y' hy' hya hya'
      · have hpos := (hWF i).1
        match hlist : (gates.get i).inputs with
        | [] => rw [hlist] at hpos; simp at hpos
        | [a] =>
          rw [← hi] at hcol hvy hvy'
          have hmem : a ∈ (gates.get i).inputs := by rw [hlist]; simp
          have hlt_a := (hWF i).2 a hmem
          have hfa := val_or_false gates i (coline t) (hWF i).2 hop hcol hmem
          have hya : val gates a (testInp t y) = true := by
            obtain ⟨c, hc, hvc⟩ := (val_or_iff gates i (testInp t y) (hWF i).2 hop).mp hvy
            rw [hlist] at hc; simp at hc; rwa [← hc]
          have hya' : val gates a (testInp t y') = true := by
            obtain ⟨c, hc, hvc⟩ := (val_or_iff gates i (testInp t y') (hWF i).2 hop).mp hvy'
            rw [hlist] at hc; simp at hc; rwa [← hc]
          exact ih a (by omega) (by omega) hfa y hy y' hy' hya hya'
        | [a, b] =>
          rw [← hi] at hcol hvy hvy'
          have hyab : val gates a (testInp t y) = true ∨ val gates b (testInp t y) = true := by
            obtain ⟨c, hc, hvc⟩ := (val_or_iff gates i (testInp t y) (hWF i).2 hop).mp hvy
            rw [hlist] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact Or.inl hvc
            · exact Or.inr hvc
          have hyab' : val gates a (testInp t y') = true ∨ val gates b (testInp t y') = true := by
            obtain ⟨c, hc, hvc⟩ := (val_or_iff gates i (testInp t y') (hWF i).2 hop).mp hvy'
            rw [hlist] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact Or.inl hvc
            · exact Or.inr hvc
          exact hcut i hig hop hcol a b hlist y hy y' hy' hyab hyab'
        | _ :: _ :: _ :: _ => rw [hlist] at hlen; simp at hlen

lemma mem_of_card_three {α : Type*} [DecidableEq α] {S : Finset α} (hcard : S.card = 3)
    {a b c : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x ∈ S, x = a ∨ x = b ∨ x = c := by
  have hsub : ({a, b, c} : Finset α) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hbc]
    · simp [hab, hac]
  have heq : ({a, b, c} : Finset α) = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x hx
  rw [← heq] at hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

lemma two_ordered_of_one_lt {α : Type*} [LinearOrder α] {S : Finset α} (h : 1 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a < b := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact ⟨x, hx, y, hy, hlt⟩
  · exact ⟨y, hy, x, hx, hlt⟩

lemma three_ordered_of_two_lt {α : Type*} [LinearOrder α] {S : Finset α} (h : 2 < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a < b ∧ b < c := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have h1 : 1 < (S.erase x).card := by
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy, z, hz, hyz⟩ := two_ordered_of_one_lt h1
  have hyS : y ∈ S := (Finset.mem_erase.mp hy).2
  have hzS : z ∈ S := (Finset.mem_erase.mp hz).2
  have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
  have hxz : x ≠ z := (Finset.mem_erase.mp hz).1.symm
  rcases lt_or_gt_of_ne hxy with h1 | h1
  · exact ⟨x, hx, y, hyS, z, hzS, h1, hyz⟩
  · rcases lt_or_gt_of_ne hxz with h2 | h2
    · exact ⟨y, hyS, x, hx, z, hzS, h1, h2⟩
    · exact ⟨y, hyS, z, hzS, x, hx, hyz, h2⟩

lemma ne_base_of_or_true (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t base : P) (g : Fin gates.length) (w1 w2 : ℕ) (r : P)
    (hop : (gates.get g).op = GateOp.or) (hin : (gates.get g).inputs = [w1, w2])
    (hb : val gates (13 + g.val) (testInp t base) = false)
    (hvr : val gates w1 (testInp t r) = true ∨ val gates w2 (testInp t r) = true) :
    r ≠ base := by
  intro hreq
  rw [hreq] at hvr
  have ht : val gates (13 + g.val) (testInp t base) = true := by
    rw [val_or_iff gates g _ (hWF g).2 hop, hin]
    rcases hvr with h | h
    · exact ⟨w1, by simp, h⟩
    · exact ⟨w2, by simp, h⟩
  rw [hb] at ht
  exact Bool.noConfusion ht

lemma card_le_two_of_merges (gates : List Gate)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (t base : P) (hcard3 : (line t \ {base}).card = 3)
    (S : Finset (Fin gates.length))
    (hM : ∀ g ∈ S, Merges gates t g ∧ val gates (13 + g.val) (testInp t base) = false) :
    S.card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨g1, hg1, g2, hg2, g3, hg3, h12, h23⟩ := three_ordered_of_two_lt hgt
  have h13 : g1 < g3 := lt_trans h12 h23
  obtain ⟨⟨hop1, hcol1, w11, w12, hin1, r1, hr1, r1', hr1', hv11, hv12, X1, hr1X, hr1'X, _⟩, hb1⟩ := hM g1 hg1
  obtain ⟨⟨hop2, hcol2, w21, w22, hin2, r2, hr2, r2', hr2', hv21, hv22, X2, hr2X, hr2'X, hcut2⟩, hb2⟩ := hM g2 hg2
  obtain ⟨⟨hop3, _, w31, w32, hin3, r3, hr3, r3', hr3', hv31, hv32, X3, hr3X, hr3'X, hcut3⟩, hb3⟩ := hM g3 hg3
  have hr1_ne : r1 ≠ base := ne_base_of_or_true gates hWF t base g1 w11 w12 r1 hop1 hin1 hb1 (Or.inl hv11)
  have hr1'_ne : r1' ≠ base := ne_base_of_or_true gates hWF t base g1 w11 w12 r1' hop1 hin1 hb1 (Or.inr hv12)
  have hr2_ne : r2 ≠ base := ne_base_of_or_true gates hWF t base g2 w21 w22 r2 hop2 hin2 hb2 (Or.inl hv21)
  have hr2'_ne : r2' ≠ base := ne_base_of_or_true gates hWF t base g2 w21 w22 r2' hop2 hin2 hb2 (Or.inr hv22)
  have hr3_ne : r3 ≠ base := ne_base_of_or_true gates hWF t base g3 w31 w32 r3 hop3 hin3 hb3 (Or.inl hv31)
  have hr3'_ne : r3' ≠ base := ne_base_of_or_true gates hWF t base g3 w31 w32 r3' hop3 hin3 hb3 (Or.inr hv32)
  have h1neq : r1 ≠ r1' := fun h => hr1'X (h ▸ hr1X)
  have h2neq : r2 ≠ r2' := fun h => hr2'X (h ▸ hr2X)
  have h1_X2 : r1 ∈ X2 ↔ r1' ∈ X2 := hcut2 g1 h12 hop1 hcol1 w11 w12 hin1 r1 hr1 r1' hr1' (Or.inl hv11) (Or.inr hv12)
  have h1_X3 : r1 ∈ X3 ↔ r1' ∈ X3 := hcut3 g1 h13 hop1 hcol1 w11 w12 hin1 r1 hr1 r1' hr1' (Or.inl hv11) (Or.inr hv12)
  have h2_X3 : r2 ∈ X3 ↔ r2' ∈ X3 := hcut3 g2 h23 hop2 hcol2 w21 w22 hin2 r2 hr2 r2' hr2' (Or.inl hv21) (Or.inr hv22)
  have hc_ex : ∃ c ∈ line t \ {base}, c ≠ r1 ∧ c ≠ r1' ∧ (c = r2 ∨ c = r2') := by
    by_cases h2 : r2 ≠ r1 ∧ r2 ≠ r1'
    · exact ⟨r2, Finset.mem_sdiff.mpr ⟨hr2, by simp [hr2_ne]⟩, h2.1, h2.2, Or.inl rfl⟩
    · by_cases h2' : r2' ≠ r1 ∧ r2' ≠ r1'
      · exact ⟨r2', Finset.mem_sdiff.mpr ⟨hr2', by simp [hr2'_ne]⟩, h2'.1, h2'.2, Or.inr rfl⟩
      · exfalso
        have ha : r2 = r1 ∨ r2 = r1' := by
          by_cases h : r2 = r1
          · exact Or.inl h
          · by_contra hn; exact h2 ⟨h, fun heq => hn (Or.inr heq)⟩
        have hb : r2' = r1 ∨ r2' = r1' := by
          by_cases h : r2' = r1
          · exact Or.inl h
          · by_contra hn; exact h2' ⟨h, fun heq => hn (Or.inr heq)⟩
        have heq : r2 ∈ X2 ↔ r2' ∈ X2 := by
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · rfl
          · exact h1_X2
          · exact h1_X2.symm
          · rfl
        exact hr2'X (heq.mp hr2X)
  obtain ⟨c, hcS, hcr1, hcr1', hcr2⟩ := hc_ex
  have hall := mem_of_card_three hcard3
    (Finset.mem_sdiff.mpr ⟨hr1, by simp [hr1_ne]⟩)
    (Finset.mem_sdiff.mpr ⟨hr1', by simp [hr1'_ne]⟩)
    hcS h1neq hcr1.symm hcr1'.symm
  have hc_X3 : c ∈ X3 ↔ r1 ∈ X3 := by
    rcases hcr2 with rfl | rfl
    · rcases hall r2' (Finset.mem_sdiff.mpr ⟨hr2', by simp [hr2'_ne]⟩) with h | h | h
      · rw [h2_X3, h]
      · rw [h2_X3, h, ← h1_X3]
      · exact (h2neq h.symm).elim
    · rcases hall r2 (Finset.mem_sdiff.mpr ⟨hr2, by simp [hr2_ne]⟩) with h | h | h
      · rw [← h2_X3, h]
      · rw [← h2_X3, h, ← h1_X3]
      · exact (h2neq h).elim
  have hsame (x : P) (hx : x ∈ line t \ {base}) : x ∈ X3 ↔ r1 ∈ X3 := by
    rcases hall x hx with rfl | rfl | rfl
    · rfl
    · exact h1_X3.symm
    · exact hc_X3
  have h3a := hsame r3 (Finset.mem_sdiff.mpr ⟨hr3, by simp [hr3_ne]⟩)
  have h3b := hsame r3' (Finset.mem_sdiff.mpr ⟨hr3', by simp [hr3'_ne]⟩)
  exact hr3'X (h3b.mpr (h3a.mp hr3X))

lemma side_bound (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (A B : Finset P) (baseA baseB : P)
    (h_sub : ∀ a ∈ A, a ∈ LS ∨ a ∈ MS)
    (h_base_le : ∀ a ∈ A, ∀ b ∈ B, ∀ v : P, testInp a baseA v = true → coline b v = true)
    (h_other_A : ∀ a1 ∈ A, ∀ a2 ∈ A, a1 ≠ a2 → ∀ y ∈ line a1, y ≠ baseA → ∀ v : P,
      testInp a1 y v = true → coline a2 v = true)
    (h_other_B : ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → ∀ y ∈ line b1, y ≠ baseB → ∀ v : P,
      testInp b1 y v = true → coline b2 v = true)
    (h_inter : ∀ a ∈ A, ∀ b ∈ B, (line a ∩ line b).card = 1)
    (h_card3 : ∀ a ∈ A, (line a \ {baseA}).card = 3)
    (K J : Finset (Fin gates.length))
    (hK_side : ∀ g ∈ K, ∃ a ∈ A, ∃ b ∈ B, Merges gates a g ∧ Merges gates b g)
    (hJ_side : ∀ z : Fin gates.length, (gates.get z).op = GateOp.and →
      ∀ g : Fin gates.length, ∀ a ∈ A, ∀ b ∈ B,
        Merges gates a g → Merges gates b g →
        OrReach gates (13 + g.val) (13 + z.val) →
        val gates (13 + z.val) (coline a) = false →
        val gates (13 + z.val) (coline b) = false →
        (∃ p ∈ line a, p ∉ line b ∧ val gates (13 + z.val) (testInp a p) = true) →
        z ∈ J) :
    let JA (a : P) := J.filter (fun z => val gates (13 + z.val) (coline a) = false ∧
      ∃ p ∈ line a, p ≠ baseA ∧ val gates (13 + z.val) (testInp a p) = true)
    let JB (b : P) := J.filter (fun z => val gates (13 + z.val) (coline b) = false ∧
      ∃ s ∈ line b, s ≠ baseB ∧ val gates (13 + z.val) (testInp b s) = true)
    let JA_all := A.biUnion JA
    let JB_all := B.biUnion JB
    K.card ≤ 2 * (JA_all \ JB_all).card + (JA_all ∩ JB_all).card := by
  classical
  intro JA JB JA_all JB_all
  let KA (a : P) := K.filter (fun g => Merges gates a g)
  have hbase_false (g : Fin gates.length) (a : P) (ha : a ∈ A) (b : P) (hb : b ∈ B)
      (hMb : Merges gates b g) : val gates (13 + g.val) (testInp a baseA) = false := by
    cases h : val gates (13 + g.val) (testInp a baseA) with
    | false => rfl
    | true =>
      have ht := val_mono gates hG hWF _ _ (h_base_le a ha b hb) (13 + g.val) (by omega) h
      rw [hMb.2.1] at ht
      exact Bool.noConfusion ht
  have hKA_disj : Set.PairwiseDisjoint (A : Set P) KA := by
    intro a1 ha1 a2 ha2 hne
    show Disjoint (KA a1) (KA a2)
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have hgK : g ∈ K := (Finset.mem_filter.mp hg1).1
    have hM1 : Merges gates a1 g := (Finset.mem_filter.mp hg1).2
    have hM2 : Merges gates a2 g := (Finset.mem_filter.mp hg2).2
    obtain ⟨_, _, b, hb, _, hMb⟩ := hK_side g hgK
    have hb1 := hbase_false g a1 ha1 b hb hMb
    obtain ⟨hop1, _, w1, w2, hin1, r, hr, _, _, hv1, _, _⟩ := hM1
    have hr_ne : r ≠ baseA := ne_base_of_or_true gates hWF a1 baseA g w1 w2 r hop1 hin1 hb1 (Or.inl hv1)
    have hgt : val gates (13 + g.val) (testInp a1 r) = true := by
      rw [val_or_iff gates g _ (hWF g).2 hop1, hin1]
      exact ⟨w1, by simp, hv1⟩
    have hcol2 := val_mono gates hG hWF _ _ (h_other_A a1 ha1 a2 ha2 hne r hr hr_ne) (13 + g.val) (by omega) hgt
    rw [hM2.2.1] at hcol2
    exact Bool.noConfusion hcol2
  have hK_eq : K = A.biUnion KA := by
    ext g
    simp only [Finset.mem_biUnion, KA, Finset.mem_filter]
    constructor
    · intro hg
      obtain ⟨a, ha, _, _, hMa, _⟩ := hK_side g hg
      exact ⟨a, ha, hg, hMa⟩
    · rintro ⟨_, _, hg, _⟩
      exact hg
  have hJA_disj : Set.PairwiseDisjoint (A : Set P) JA := by
    intro a1 ha1 a2 ha2 hne
    show Disjoint (JA a1) (JA a2)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨_, _, p, hp, hpne, hvp⟩ := Finset.mem_filter.mp hz1
    obtain ⟨_, hcol2, _⟩ := Finset.mem_filter.mp hz2
    have ht := val_mono gates hG hWF _ _ (h_other_A a1 ha1 a2 ha2 hne p hp hpne) (13 + z.val) (by omega) hvp
    rw [hcol2] at ht
    exact Bool.noConfusion ht
  -- Helper: from g ∈ K with Merges a g ∧ Merges b g and p ∈ line a \ line b firing on input w of g, find z ∈ JA a
  have find_z (g : Fin gates.length) (a : P) (ha : a ∈ A) (b : P) (hb : b ∈ B)
      (hMa : Merges gates a g) (hMb : Merges gates b g)
      (w : ℕ) (hw : w ∈ (gates.get g).inputs) (p : P) (hpa : p ∈ line a) (hpb : p ∉ line b)
      (hvw : val gates w (testInp a p) = true) :
      ∃ z : Fin gates.length, z ∈ JA a ∧ z < g ∧
        val gates (13 + z.val) (coline b) = false ∧ val gates (13 + z.val) (testInp a p) = true := by
    have hstep : OrReach gates (13 + g.val) w := orReach_step gates g hMa.1 hw
    have hwlt : w < 13 + g.val := (hWF g).2 w hw
    rcases orReach_find_stop gates hG hWF (testInp a p) w (by omega) hvw with ⟨v, hrv, hxv⟩ | ⟨z, hzop, hrz, hvz⟩
    · exfalso
      have hrvg : OrReach gates (13 + g.val) v.val := orReach_trans gates hstep hrv
      have hfa := orReach_false gates hWF hrvg (coline a) hMa.2.1
      have hfb := orReach_false gates hWF hrvg (coline b) hMb.2.1
      rw [val_input] at hfa hfb
      have hva : v ∈ line a := by simpa [coline] using hfa
      have hvb : v ∈ line b := by simpa [coline] using hfb
      have heq := testInp_in_line_eq a (h_sub a ha) p hpa v hva hxv
      exact hpb (heq ▸ hvb)
    · have hrzg : OrReach gates (13 + g.val) (13 + z.val) := orReach_trans gates hstep hrz
      have hfa := orReach_false gates hWF hrzg (coline a) hMa.2.1
      have hfb := orReach_false gates hWF hrzg (coline b) hMb.2.1
      have hzJ : z ∈ J := hJ_side z hzop g a ha b hb hMa hMb hrzg hfa hfb ⟨p, hpa, hpb, hvz⟩
      have hpne : p ≠ baseA := by
        intro hpeq; subst hpeq
        have ht := val_mono gates hG hWF _ _ (h_base_le a ha b hb) (13 + z.val) (by omega) hvz
        rw [hfb] at ht; exact Bool.noConfusion ht
      have hzJA : z ∈ JA a := Finset.mem_filter.mpr ⟨hzJ, hfa, p, hpa, hpne, hvz⟩
      have hle := orReach_le gates hWF hrz
      have hzlt : z < g := by change z.val < g.val; omega
      exact ⟨z, hzJA, hzlt, hfb, hvz⟩
  -- Helper: given two distinct points r, r' ∈ line a and b ∈ B, not both lie in line b
  have not_both_in_b (a : P) (ha : a ∈ A) (b : P) (hb : b ∈ B) (r r' : P)
      (hr : r ∈ line a) (hr' : r' ∈ line a) (hne : r ≠ r') (h1 : r ∈ line b) : r' ∉ line b := by
    intro h2
    have hsub2 : ({r, r'} : Finset P) ⊆ line a ∩ line b := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by assumption, by assumption⟩
    have hc2 : ({r, r'} : Finset P).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have hle := Finset.card_le_card hsub2
    have h1c := h_inter a ha b hb
    omega
  -- Per-line bound for each a ∈ A
  have hper (a : P) (ha : a ∈ A) :
      (KA a).card ≤ 2 * (JA a \ JB_all).card + (JA a ∩ JB_all).card := by
    have hJsplit : (JA a).card = (JA a \ JB_all).card + (JA a ∩ JB_all).card := by
      have := Finset.card_sdiff_add_card_inter (JA a) JB_all
      omega
    have hle2 : (KA a).card ≤ 2 := by
      apply card_le_two_of_merges gates hWF a baseA (h_card3 a ha) (KA a)
      intro g hg
      have hgK : g ∈ K := (Finset.mem_filter.mp hg).1
      have hMa : Merges gates a g := (Finset.mem_filter.mp hg).2
      obtain ⟨_, _, b, hb, _, hMb⟩ := hK_side g hgK
      exact ⟨hMa, hbase_false g a ha b hb hMb⟩
    have get_partner (g : Fin gates.length) (hg : g ∈ KA a) :
        ∃ b ∈ B, Merges gates a g ∧ Merges gates b g := by
      have hgK : g ∈ K := (Finset.mem_filter.mp hg).1
      have hMa : Merges gates a g := (Finset.mem_filter.mp hg).2
      obtain ⟨_, _, b, hb, _, hMb⟩ := hK_side g hgK
      exact ⟨b, hb, hMa, hMb⟩
    by_cases h0 : (KA a).card = 0
    · omega
    by_cases h1 : (KA a).card = 1
    · obtain ⟨g, hg⟩ := Finset.card_pos.mp (by omega : 0 < (KA a).card)
      obtain ⟨b, hb, hMa, hMb⟩ := get_partner g hg
      have ⟨hop, _, w1, w2, hin, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := hMa
      have hneq : r ≠ r' := fun h => hr'X (h ▸ hrX)
      have hz_ex : ∃ z, z ∈ JA a := by
        by_cases hrb : r ∉ line b
        · obtain ⟨z, hz, _⟩ := find_z g a ha b hb hMa hMb w1 (by rw [hin]; simp) r hr hrb hv1
          exact ⟨z, hz⟩
        · push Not at hrb
          have hr'b := not_both_in_b a ha b hb r r' hr hr' hneq hrb
          obtain ⟨z, hz, _⟩ := find_z g a ha b hb hMa hMb w2 (by rw [hin]; simp) r' hr' hr'b hv2
          exact ⟨z, hz⟩
      obtain ⟨z, hz⟩ := hz_ex
      have hpos : 1 ≤ (JA a).card := Finset.card_pos.mpr ⟨z, hz⟩
      omega
    · have h2 : (KA a).card = 2 := by omega
      obtain ⟨g1, hg1, g2, hg2, h12⟩ := two_ordered_of_one_lt (by omega : 1 < (KA a).card)
      obtain ⟨b1, hb1, hMa1, hMb1⟩ := get_partner g1 hg1
      obtain ⟨b2, hb2, hMa2, hMb2⟩ := get_partner g2 hg2
      have ⟨hop1, hcol1, w11, w12, hin1, r1, hr1, r1', hr1', hv11, hv12, X1, hr1X, hr1'X, hcut1⟩ := hMa1
      have ⟨hop2, hcol2, w21, w22, hin2, r2, hr2, r2', hr2', hv21, hv22, X2, hr2X, hr2'X, hcut2⟩ := hMa2
      have h1neq : r1 ≠ r1' := fun h => hr1'X (h ▸ hr1X)
      have h2neq : r2 ≠ r2' := fun h => hr2'X (h ▸ hr2X)
      -- Case 1: neither r1 nor r1' is in line b1
      by_cases hboth1 : r1 ∉ line b1 ∧ r1' ∉ line b1
      · obtain ⟨z1, hz1, hz1lt, _, hvz1⟩ := find_z g1 a ha b1 hb1 hMa1 hMb1 w11 (by rw [hin1]; simp) r1 hr1 hboth1.1 hv11
        obtain ⟨z2, hz2, _, _, hvz2⟩ := find_z g1 a ha b1 hb1 hMa1 hMb1 w12 (by rw [hin1]; simp) r1' hr1' hboth1.2 hv12
        have hzne : z1 ≠ z2 := by
          intro heq; subst heq
          have hcolz := (Finset.mem_filter.mp hz1).2.1
          have hsame := wire_same_comp gates hG hWF a (h_sub a ha) g1 X1 hcut1 (13 + z1.val) (by omega) hcolz r1 hr1 r1' hr1' hvz1 hvz2
          exact hr1'X (hsame.mp hr1X)
        have hcard2 : 2 ≤ (JA a).card := Finset.one_lt_card.mpr ⟨z1, hz1, z2, hz2, hzne⟩
        omega
      · -- At least one of r1, r1' lies in line b1; let q1 be the one in line b1 and p1 be the other
        have hqp1 : ∃ q1 ∈ line a, ∃ p1 ∈ line a, q1 ∈ line b1 ∧ p1 ∉ line b1 ∧
            (q1 = r1 ∧ p1 = r1' ∨ q1 = r1' ∧ p1 = r1) ∧
            ∃ wp1 ∈ (gates.get g1).inputs, val gates wp1 (testInp a p1) = true := by
          by_cases h : r1 ∈ line b1
          · exact ⟨r1, hr1, r1', hr1', h, not_both_in_b a ha b1 hb1 r1 r1' hr1 hr1' h1neq h,
              Or.inl ⟨rfl, rfl⟩, w12, by rw [hin1]; simp, hv12⟩
          · have h' : r1' ∈ line b1 := by
              by_contra hn
              exact hboth1 ⟨h, hn⟩
            exact ⟨r1', hr1', r1, hr1, h', h, Or.inr ⟨rfl, rfl⟩, w11, by rw [hin1]; simp, hv11⟩
        obtain ⟨q1, hq1, p1, hp1, hq1b1, hp1b1, hqp1eq, wp1, hwp1in, hvp1⟩ := hqp1
        obtain ⟨z1, hz1, hz1lt, hfb1, hvz1⟩ := find_z g1 a ha b1 hb1 hMa1 hMb1 wp1 hwp1in p1 hp1 hp1b1 hvp1
        -- At g2 > g1, r1 and r1' are on the same side of X2, while r2 ∈ X2 and r2' ∉ X2
        have h1_X2 : r1 ∈ X2 ↔ r1' ∈ X2 :=
          hcut2 g1 h12 hop1 hcol1 w11 w12 hin1 r1 hr1 r1' hr1' (Or.inl hv11) (Or.inr hv12)
        have hp1_X2 : (r1 ∈ X2 ↔ p1 ∈ X2) := by
          rcases hqp1eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h1_X2
          · rfl
        -- Pick p2 ∈ {r2, r2'} on the opposite side of X2 from p1, and let p2' be the other
        have hp2_ex : ∃ p2 ∈ line a, ∃ p2' ∈ line a, p2 ≠ p2' ∧ ¬ (p1 ∈ X2 ↔ p2 ∈ X2) ∧
            (∃ w ∈ (gates.get g2).inputs, val gates w (testInp a p2) = true) ∧
            (∃ w' ∈ (gates.get g2).inputs, val gates w' (testInp a p2') = true) := by
          by_cases hp : p1 ∈ X2
          · exact ⟨r2', hr2', r2, hr2, h2neq.symm, by simp [hp, hr2'X],
              ⟨w22, by rw [hin2]; simp, hv22⟩, ⟨w21, by rw [hin2]; simp, hv21⟩⟩
          · exact ⟨r2, hr2, r2', hr2', h2neq, by simp [hp, hr2X],
              ⟨w21, by rw [hin2]; simp, hv21⟩, ⟨w22, by rw [hin2]; simp, hv22⟩⟩
        obtain ⟨p2, hp2, p2', hp2', hp2neq, hopp, ⟨wp2, hwp2in, hvp2⟩, ⟨wp2', hwp2'in, hvp2'⟩⟩ := hp2_ex
        by_cases hp2b2 : p2 ∉ line b2
        · obtain ⟨z2, hz2, _, _, hvz2⟩ := find_z g2 a ha b2 hb2 hMa2 hMb2 wp2 hwp2in p2 hp2 hp2b2 hvp2
          have hzne : z1 ≠ z2 := by
            intro heq; subst heq
            have hcolz := (Finset.mem_filter.mp hz1).2.1
            have hlt2 : 13 + z1.val < 13 + g2.val := by
              have : z1.val < g1.val := hz1lt
              have : g1.val < g2.val := h12
              omega
            have hsame := wire_same_comp gates hG hWF a (h_sub a ha) g2 X2 hcut2 (13 + z1.val) hlt2 hcolz p1 hp1 p2 hp2 hvz1 hvz2
            exact hopp hsame
          have hcard2 : 2 ≤ (JA a).card := Finset.one_lt_card.mpr ⟨z1, hz1, z2, hz2, hzne⟩
          omega
        · push Not at hp2b2
          have hp2'b2 := not_both_in_b a ha b2 hb2 p2 p2' hp2 hp2' hp2neq hp2b2
          obtain ⟨z2, hz2, _, hfb2, _⟩ := find_z g2 a ha b2 hb2 hMa2 hMb2 wp2' hwp2'in p2' hp2' hp2'b2 hvp2'
          by_cases hzne : z1 ≠ z2
          · have hcard2 : 2 ≤ (JA a).card := Finset.one_lt_card.mpr ⟨z1, hz1, z2, hz2, hzne⟩
            omega
          · push Not at hzne
            subst hzne
            -- z1 = z2, so val z1 (coline b1) = false AND val z1 (coline b2) = false, and b1 ≠ b2!
            have hq1_X2 : p1 ∈ X2 ↔ q1 ∈ X2 := by
              rcases hqp1eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact h1_X2.symm
              · exact h1_X2
            have hp2_ne_q1 : p2 ≠ q1 := by
              intro h; subst h; exact hopp hq1_X2
            have hb12 : b1 ≠ b2 := by
              intro h; subst h
              exact not_both_in_b a ha b1 hb1 q1 p2 hq1 hp2 hp2_ne_q1.symm hq1b1 hp2b2
            have hz1_not_JB : z1 ∉ JB_all := by
              intro hmem
              obtain ⟨b3, hb3, hzb3⟩ := Finset.mem_biUnion.mp hmem
              obtain ⟨_, _, s, hs, hsne, hvs⟩ := Finset.mem_filter.mp hzb3
              by_cases h31 : b3 ≠ b1
              · have ht := val_mono gates hG hWF _ _ (h_other_B b3 hb3 b1 hb1 h31 s hs hsne) (13 + z1.val) (by omega) hvs
                rw [hfb1] at ht; exact Bool.noConfusion ht
              · push Not at h31
                subst h31
                have ht := val_mono gates hG hWF _ _ (h_other_B b3 hb3 b2 hb2 hb12 s hs hsne) (13 + z1.val) (by omega) hvs
                rw [hfb2] at ht; exact Bool.noConfusion ht
            have hpure : 1 ≤ (JA a \ JB_all).card := Finset.card_pos.mpr ⟨z1, Finset.mem_sdiff.mpr ⟨hz1, hz1_not_JB⟩⟩
            omega
  -- Sum hper over a ∈ A
  have hsumK : K.card = ∑ a ∈ A, (KA a).card := by
    rw [hK_eq, Finset.card_biUnion hKA_disj]
  have hsumPure : (JA_all \ JB_all).card = ∑ a ∈ A, (JA a \ JB_all).card := by
    have hdisj : Set.PairwiseDisjoint (A : Set P) (fun a => JA a \ JB_all) := by
      intro a1 ha1 a2 ha2 hne
      exact Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset (hJA_disj ha1 ha2 hne)
    have heq : JA_all \ JB_all = A.biUnion (fun a => JA a \ JB_all) := by
      ext z
      simp only [JA_all, Finset.mem_sdiff, Finset.mem_biUnion]
      exact ⟨fun ⟨⟨a, ha, hza⟩, hzb⟩ => ⟨a, ha, hza, hzb⟩,
             fun ⟨a, ha, hza, hzb⟩ => ⟨⟨a, ha, hza⟩, hzb⟩⟩
    rw [heq, Finset.card_biUnion hdisj]
  have hsumBoth : (JA_all ∩ JB_all).card = ∑ a ∈ A, (JA a ∩ JB_all).card := by
    have hdisj : Set.PairwiseDisjoint (A : Set P) (fun a => JA a ∩ JB_all) := by
      intro a1 ha1 a2 ha2 hne
      exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left (hJA_disj ha1 ha2 hne)
    have heq : JA_all ∩ JB_all = A.biUnion (fun a => JA a ∩ JB_all) := by
      ext z
      simp only [JA_all, Finset.mem_inter, Finset.mem_biUnion]
      exact ⟨fun ⟨⟨a, ha, hza⟩, hzb⟩ => ⟨a, ha, hza, hzb⟩,
             fun ⟨a, ha, hza, hzb⟩ => ⟨⟨a, ha, hza⟩, hzb⟩⟩
    rw [heq, Finset.card_biUnion hdisj]
  calc
    K.card = ∑ a ∈ A, (KA a).card := hsumK
    _ ≤ ∑ a ∈ A, (2 * (JA a \ JB_all).card + (JA a ∩ JB_all).card) := Finset.sum_le_sum hper
    _ = 2 * (∑ a ∈ A, (JA a \ JB_all).card) + ∑ a ∈ A, (JA a ∩ JB_all).card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (JA_all \ JB_all).card + (JA_all ∩ JB_all).card := by rw [hsumPure, hsumBoth]

lemma main_proof (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (K J : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, g ∈ K ↔ ∃ l ∈ LS, ∃ m ∈ MS, Merges gates l g ∧ Merges gates m g)
    (hJ : ∀ z : Fin gates.length,
      ((gates.get z).op = GateOp.and ∧
        ∃ g : Fin gates.length, ∃ l ∈ LS, ∃ m ∈ MS,
          Merges gates l g ∧ Merges gates m g ∧
          OrReach gates (13 + g.val) (13 + z.val) ∧
          val gates (13 + z.val) (coline l) = false ∧
          val gates (13 + z.val) (coline m) = false ∧
          ((∃ p ∈ line l, p ∉ line m ∧ val gates (13 + z.val) (testInp l p) = true) ∨
           (∃ p ∈ line m, p ∉ line l ∧ val gates (13 + z.val) (testInp m p) = true))) → z ∈ J) :
    K.card ≤ J.card := by
  classical
  let JL (l : P) := J.filter (fun z => val gates (13 + z.val) (coline l) = false ∧
    ∃ p ∈ line l, p ≠ 0 ∧ val gates (13 + z.val) (testInp l p) = true)
  let JM (m : P) := J.filter (fun z => val gates (13 + z.val) (coline m) = false ∧
    ∃ s ∈ line m, s ≠ 1 ∧ val gates (13 + z.val) (testInp m s) = true)
  let JL_all := LS.biUnion JL
  let JM_all := MS.biUnion JM
  have h1 : K.card ≤ 2 * (JL_all \ JM_all).card + (JL_all ∩ JM_all).card :=
    side_bound gates hG hWF LS MS 0 1
      (fun a ha => Or.inl ha)
      testInp_base_le_coline_LM
      testInp_other_le_coline_LL
      testInp_other_le_coline_MM
      inter_LM_card
      line_sdiff_base_L
      K J
      (fun g hg => (hK g).mp hg)
      (fun z hzop g l hl m hm hMl hMm hreach hfl hfm hp =>
        hJ z ⟨hzop, g, l, hl, m, hm, hMl, hMm, hreach, hfl, hfm, Or.inl hp⟩)
  have h2 : K.card ≤ 2 * (JM_all \ JL_all).card + (JM_all ∩ JL_all).card :=
    side_bound gates hG hWF MS LS 1 0
      (fun a ha => Or.inr ha)
      testInp_base_le_coline_ML
      testInp_other_le_coline_MM
      testInp_other_le_coline_LL
      inter_ML_card
      line_sdiff_base_M
      K J
      (fun g hg => by
        obtain ⟨l, hl, m, hm, hMl, hMm⟩ := (hK g).mp hg
        exact ⟨m, hm, l, hl, hMm, hMl⟩)
      (fun z hzop g m hm l hl hMm hMl hreach hfm hfl hp =>
        hJ z ⟨hzop, g, l, hl, m, hm, hMl, hMm, hreach, hfl, hfm, Or.inr hp⟩)
  have hcomm : (JM_all ∩ JL_all).card = (JL_all ∩ JM_all).card := by rw [Finset.inter_comm]
  have hsub : JL_all ∪ JM_all ⊆ J := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨l, _, hzl⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hzl).1
    · obtain ⟨m, _, hzm⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hzm).1
  have hcard_union : (JL_all \ JM_all).card + (JM_all \ JL_all).card + (JL_all ∩ JM_all).card =
      (JL_all ∪ JM_all).card := by
    have ha := Finset.card_sdiff_add_card_inter JL_all JM_all
    have hb := Finset.card_sdiff_add_card_inter JM_all JL_all
    have hu := Finset.card_union_add_card_inter JL_all JM_all
    rw [Finset.inter_comm] at hb
    omega
  have hleJ := Finset.card_le_card hsub
  omega

end Payers

open PEqualNP.CircuitLowerBounds
-- Low-level wire identities are from L-meta-1558.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

abbrev P := Fin 13
abbrev Law (gs : List Gate) := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
abbrev Good (gs : List Gate) := ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
  ∀ a ∈ (gs.get i).inputs, a < 13 + i.val
def V (gs : List Gate) (w : ℕ) (x : P → Bool) := value (⟨gs,0⟩ : Circuit) x w
def arg (gs : List Gate) (k w : ℕ) (x : P → Bool) := if w < 13+k then V gs w x else false

lemma at_gate (gs : List Gate) (i : Fin gs.length) (x : P → Bool) :
    V gs (13+i) x = (gs.get i).op.eval ((gs.get i).inputs.map (fun w => arg gs i w x)) := by
  simpa only [V,arg,List.get_eq_getElem,Nat.add_sub_cancel_left] using gate_value (⟨gs,0⟩ : Circuit) x (13+i.val) (by omega) (show 13+i.val < 13+gs.length from by have := i.isLt; omega)

def dyn (gs : List Gate) (w : ℕ) := V gs w (fun _ => false) != V gs w (fun _ => true)
lemma stable {gs : List Gate} (law : Law gs) (w : ℕ) (fixed : dyn gs w = false) (x : P → Bool) :
    V gs w x = V gs w (fun _ => false) := by
  have h₁ := mono (⟨gs,0⟩ : Circuit) law (fun _ : P => false) x (by simp) w
  have h₂ := mono (⟨gs,0⟩ : Circuit) law x (fun _ : P => true) (by simp) w
  change (V gs w (fun _ => false) = true → V gs w x = true) at h₁
  change (V gs w x = true → V gs w (fun _ => true) = true) at h₂
  have eq : V gs w (fun _ => false) = V gs w (fun _ => true) := by simpa [dyn] using fixed
  exact Bool.eq_iff_iff.mpr ⟨fun h => eq.trans (h₂ h), h₁⟩

def keep (gs : List Gate) (k w : ℕ) : Bool := decide (w < 13+k) && dyn gs w
def args (gs : List Gate) (k : Fin gs.length) := (gs.get k).inputs.filter (keep gs k)
def repl (gs : List Gate) (k : Fin gs.length) : Gate :=
  if (args gs k).isEmpty then ⟨GateOp.or,[0]⟩ else ⟨(gs.get k).op,args gs k⟩
def normalized (gs : List Gate) := List.ofFn (repl gs)
lemma norm_len (gs : List Gate) : (normalized gs).length = gs.length := by simp [normalized]
lemma norm_get (gs : List Gate) (k : Fin (normalized gs).length) :
    (normalized gs).get k = repl gs ⟨k.val,(norm_len gs) ▸ k.isLt⟩ := by apply List.get_ofFn
lemma norm_legal {gs : List Gate} (law : Law gs) : Law (normalized gs) ∧ Good (normalized gs) := by
  constructor
  · intro h hh
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hh
    unfold repl
    split
    · simp
    · have h := law _ (List.get_mem gs k)
      refine ⟨h.1,?_⟩
      exact (List.length_filter_le _ _).trans h.2
  · intro k
    rw [norm_get]
    unfold repl
    split
    · simp
    · rename_i ne
      simp only [Bool.not_eq_true,List.isEmpty_eq_false_iff] at ne
      constructor
      · exact List.length_pos_iff.mpr ne
      · intro a ha
        have h := (List.mem_filter.mp ha).2
        simp only [keep,Bool.and_eq_true,decide_eq_true_eq] at h
        exact h.1

lemma operands_equal {gs : List Gate} (law : Law gs) (k a : ℕ) (hn : keep gs k a = false) (x y : P → Bool) :
    arg gs k a x = arg gs k a y := by
  by_cases hw : a < 13+k
  · have fixed : dyn gs a = false := by simpa [keep,hw] using hn
    simpa [arg,hw] using (stable law a fixed x).trans (stable law a fixed y).symm
  · simp [arg,hw]

lemma neutral {gs : List Gate} (law : Law gs) (k : Fin gs.length) (dynamic : dyn gs (13+k) = true)
    (a : ℕ) (ha : a ∈ (gs.get k).inputs) (fixed : keep gs k a = false) (x : P → Bool) :
    ((gs.get k).op = GateOp.and → arg gs k a x = true) ∧
    ((gs.get k).op = GateOp.or → arg gs k a x = false) := by
  have lo := at_gate gs k (fun _ => false)
  have hi := at_gate gs k (fun _ => true)
  have d1 := operands_equal law k a fixed (fun _ => false) x
  have d2 := operands_equal law k a fixed (fun _ => true) x
  unfold dyn at dynamic
  rw [lo,hi] at dynamic
  constructor
  · intro op
    rw [op] at dynamic
    cases h : arg gs k a x
    · have f (y : P → Bool) (hy : arg gs k a y = false) :
          ((gs.get k).inputs.map (fun b => arg gs k b y)).all id = false := by
        rw [List.all_eq_false]
        exact ⟨false,List.mem_map.mpr ⟨a,ha,hy⟩,by decide⟩
      simp only [GateOp.eval] at dynamic
      rw [f _ (d1.trans h), f _ (d2.trans h)] at dynamic
      contradiction
    · rfl
  · intro op
    rw [op] at dynamic
    cases h : arg gs k a x
    · rfl
    · have f (y : P → Bool) (hy : arg gs k a y = true) :
          ((gs.get k).inputs.map (fun b => arg gs k b y)).any id = true := by
        rw [List.any_eq_true]
        exact ⟨true,List.mem_map.mpr ⟨a,ha,hy⟩,rfl⟩
      simp only [GateOp.eval] at dynamic
      rw [f _ (d1.trans h), f _ (d2.trans h)] at dynamic
      contradiction

lemma filtered_value {gs : List Gate} (law : Law gs) (k : Fin gs.length) (dy : dyn gs (13+k) = true) (x : P → Bool) :
    V gs (13+k) x = (gs.get k).op.eval ((args gs k).map (fun a => arg gs k a x)) := by
  rw [at_gate]
  apply Bool.eq_iff_iff.mpr
  rcases (law _ (List.get_mem gs k)).1 with op | op
  · rw [op]
    simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq,args,List.mem_filter]
    constructor
    · exact fun on a ha => on a ha.1
    · intro on a ha
      cases h : keep gs k a with
      | false => exact (neutral law k dy a ha h x).1 op
      | true => exact on a ⟨ha,h⟩
  · rw [op]
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq,args,List.mem_filter]
    constructor
    · rintro ⟨a,ha,hx⟩
      cases h : keep gs k a with
      | false => exact False.elim (Bool.noConfusion (((neutral law k dy a ha h x).2 op).symm.trans hx))
      | true => exact ⟨a,⟨ha,h⟩,hx⟩
    · rintro ⟨a,ha,hx⟩; exact ⟨a,ha.1,hx⟩

lemma args_nonempty {gs : List Gate} (law : Law gs) (k : Fin gs.length) (dy : dyn gs (13+k) = true) :
    (args gs k).isEmpty = false := by
  cases h : args gs k with
  | cons => rfl
  | nil =>
    unfold dyn at dy
    have eq (x : P → Bool) := filtered_value law k (show dyn gs (13+k) = true from dy) x
    simp only [h,List.map_nil] at eq
    rw [eq,eq] at dy
    simp at dy

lemma preserves {gs : List Gate} (law : Law gs) (w : ℕ) (dy : dyn gs w = true) (x : P → Bool) :
    V (normalized gs) w x = V gs w x := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases low : w < 13
    · let i : P := ⟨w,low⟩
      exact (input_value _ x i).trans (input_value _ x i).symm
    by_cases hi : w < 13+gs.length
    · let k : Fin gs.length := ⟨w-13,by omega⟩
      let k' : Fin (normalized gs).length := ⟨k.val,(norm_len gs).symm ▸ k.isLt⟩
      have e : 13+k.val = w := by change 13+(w-13)=w; omega
      rw [← e] at dy ⊢
      rw [filtered_value law k dy]
      have en := at_gate (normalized gs) k' x
      rw [norm_get] at en
      change V (normalized gs) (13+k.val) x = (repl gs k).op.eval
        ((repl gs k).inputs.map (fun a => arg (normalized gs) k a x)) at en
      simp only [repl,args_nonempty law k dy,Bool.false_eq_true,ite_false] at en
      rw [en]
      congr 1
      apply List.map_congr_left
      intro a ha
      have h := (List.mem_filter.mp ha).2
      simp only [keep,Bool.and_eq_true,decide_eq_true_eq] at h
      simpa only [arg,ite_eq_left h.1] using ih a (h.1.trans_le e.le) h.2
    · have n := missing_value (⟨gs,0⟩ : Circuit) (fun _ : P => true) w
        (show 13+gs.length ≤ w by omega)
      have b := missing_value (⟨gs,0⟩ : Circuit) (fun _ : P => false) w
        (show 13+gs.length ≤ w by omega)
      change V gs w _ = false at n b
      simp only [dyn,b,n] at dy
      contradiction
open PEqualNP.CircuitLowerBounds Finset
open Payers (line coline LS MS testInp)

abbrev Vertex := Fin 13
abbrev Legal (gs : List Gate) := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
abbrev Proper (gs : List Gate) := ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧ ∀ a ∈ (gs.get i).inputs, a < 13 + i.val
def test (t p : Vertex) : Vertex → Bool :=
  if t ∈ LS ∪ MS then testInp t p else fun v => decide (v = p ∨ v = 0)
abbrev onDomain (x : Vertex → Bool) : Prop :=
  x 0 = true ∨ x 1 = true ∨ ∀ v, v ∉ line 0 → x v = true
lemma dark_ok : ∀ t, onDomain (coline t) := by decide +kernel
lemma bright_ok : ∀ t : Vertex, t ≠ 0 → ∀ p ∈ line t, onDomain (test t p) := by decide +kernel
lemma own : ∀ t : Vertex, t ≠ 0 → ∀ p ∈ line t, ∀ v ∈ line t, test t p v = true ↔ v = p := by decide +kernel
lemma size4 : ∀ t : Vertex, (line t).card = 4 := by decide +kernel
abbrev allowed (t u : Vertex) : Prop := (t ∈ LS ∧ u ∈ MS) ∨ (t ∈ MS ∧ u ∈ LS)
def bad (t u : Vertex) : Finset Vertex :=
  (line t).filter fun p => ¬ ∀ v : Vertex, test t p v = true → coline u v = true
set_option maxHeartbeats 2500000 in
lemma geom : ∀ t u : Vertex, t ≠ 0 → u ≠ 0 → t ≠ u → 2 ≤ (bad t u).card →
    2 ≤ (bad u t).card → allowed t u := by decide +kernel

abbrev Correct (gs : List Gate) (o : Vertex → ℕ) := ∀ t x, onDomain x →
  Payers.val gs (o t) x = decide (∃ p ∈ line t, x p = true)
noncomputable def marks (gs : List Gate) (t : Vertex) : Finset (Fin gs.length) := by
  classical
  exact univ.filter (Counting.Mrg gs (line t) (coline t) (test t))
lemma marked {gs : List Gate} {t : Vertex} {k : Fin gs.length} : k ∈ marks gs t ↔
    Counting.Mrg gs (line t) (coline t) (test t) k := by classical simp [marks]
lemma mark_count (gs : List Gate) (o : Vertex → ℕ) (law : Legal gs) (ok : Proper gs) (correct : Correct gs o)
    (t : Vertex) (t0 : t ≠ 0) : (marks gs t).card = 3 := by
  classical
  have dark := correct t _ (dark_ok t)
  have d : Counting.val gs (o t) (coline t) = false := dark.trans (by simp [coline])
  have b (p : Vertex) (hp : p ∈ line t) : Counting.val gs (o t) (test t p) = true :=
    (correct t _ (bright_ok t t0 p hp)).trans (decide_eq_true ⟨p,hp,(own t t0 p hp p hp).mpr rfl⟩)
  have h := Counting.three gs (line t) (coline t) (test t) (fun v => by simp [coline]) (own t t0)
    law ok (size4 t) (o t) d b
  simpa [marks,Finset.sum_boole] using h

lemma side_bad {gs : List Gate} (law : Legal gs) (ok : Proper gs) (t u : Vertex)
    (g : Fin gs.length) (mem : g ∈ marks gs t) (quiet : Payers.val gs (13+g) (coline u) = false) :
    2 ≤ (bad t u).card := by
  obtain ⟨op,_,a,b,ins,p,hp,q,hq,hpa,hqb,X,hx,hn,_⟩ := marked.mp mem
  have has (w : ℕ) (hw : w ∈ (gs.get g).inputs) (r : Vertex) (hr : r ∈ line t)
      (fire : Payers.val gs w (test t r) = true) : r ∈ bad t u := by
    apply mem_filter.mpr
    refine ⟨hr,?_⟩
    intro top
    have active := (Payers.val_or_iff gs g (test t r) (ok g).2 op).mpr ⟨w,hw,fire⟩
    have con := Payers.val_mono gs law ok _ _ top _ (by have := g.isLt; omega) active
    exact Bool.noConfusion (quiet.symm.trans con)
  exact one_lt_card.mpr ⟨p,has a (by rw [ins];simp) p hp hpa,q,has b (by rw [ins];simp) q hq hqb,
    fun e => hn (e ▸ hx)⟩

def leftRows : Finset Vertex := (univ.erase 0) \ MS
lemma sizeLeft : leftRows.card = 9 := by decide +kernel
lemma sizeRight : MS.card = 3 := by decide +kernel
lemma sameSide : (∀ t ∈ leftRows, ∀ u ∈ leftRows, t ≠ 0 ∧ ¬ allowed t u) ∧
    (∀ t ∈ MS, ∀ u ∈ MS, t ≠ 0 ∧ ¬ allowed t u) := by
  have splitSets : Disjoint LS MS := by decide +kernel
  have zeroAway : (0 : Vertex) ∉ MS := by decide
  constructor
  · intro t ht u hu
    obtain ⟨ht0,htm⟩ := mem_sdiff.mp ht
    have hum := (mem_sdiff.mp hu).2
    exact ⟨(mem_erase.mp ht0).1,fun h => h.elim (fun a => hum a.2) (fun a => htm a.1)⟩
  · intro t ht u hu
    exact ⟨fun e => zeroAway (e ▸ ht),fun h => h.elim
      (fun a => disjoint_left.mp splitSets a.1 ht)
      (fun a => disjoint_left.mp splitSets a.2 hu)⟩
lemma across : ∀ t ∈ leftRows, ∀ u ∈ MS, allowed t u → t ∈ LS := by decide +kernel

lemma collision {gs : List Gate} (law : Legal gs) (ok : Proper gs) {t u : Vertex}
    (ht : t ≠ 0) (hu : u ≠ 0) (ne : t ≠ u) {g : Fin gs.length} (a : g ∈ marks gs t) (b : g ∈ marks gs u) :
    allowed t u :=
  geom t u ht hu ne (side_bad law ok t u g a (marked.mp b).2.1)
    (side_bad law ok u t g b (marked.mp a).2.1)

def singletonX (p v : Vertex) := decide (v = p)
lemma singleton0 : onDomain (singletonX 0) := Or.inl (by decide)
lemma singleton1 : onDomain (singletonX 1) := Or.inr (Or.inl (by decide))
lemma separate : ∀ t : Vertex, t ≠ 0 →
    (∀ v, singletonX 0 v = true → coline t v = true) ∨
    (∀ v, singletonX 1 v = true → coline t v = true) := by decide +kernel

lemma extra_or (gs : List Gate) (o : Vertex → ℕ) (law : Legal gs) (ok : Proper gs) (correct : Correct gs o) :
    ∃ k : Fin gs.length, (gs.get k).op = GateOp.or ∧
      ∀ t : Vertex, t ≠ 0 → k ∉ marks gs t := by
  classical
  let Good := fun w => Payers.val gs w (singletonX 0) = true ∧ Payers.val gs w (singletonX 1) = true ∧
    Payers.val gs w (coline 0) = false
  have good : Good (o 0) := ⟨(correct 0 _ singleton0).trans (by decide +kernel),
    (correct 0 _ singleton1).trans (by decide +kernel),(correct 0 _ (dark_ok 0)).trans (by decide +kernel)⟩
  have someGood : ∃ w, Good w := ⟨_,good⟩
  let w := Nat.find someGood
  obtain ⟨h0,h1,hd⟩ := Nat.find_spec someGood
  have low : 13 ≤ w := by
    by_contra! lo
    let v : Vertex := ⟨w,lo⟩
    have a := (Payers.val_input gs v (singletonX 0)).symm.trans h0
    have b := (Payers.val_input gs v (singletonX 1)).symm.trans h1
    have ea : v = 0 := of_decide_eq_true a
    have eb : v = 1 := of_decide_eq_true b
    exact (by decide : (0 : Vertex) ≠ 1) (ea.symm.trans eb)
  have hi : w < 13+gs.length := by
    by_contra! out
    have n := Counting.val_big gs (singletonX 0) w out
    exact Bool.noConfusion (n.symm.trans h0)
  let k : Fin gs.length := ⟨w-13,by omega⟩
  have eq : 13+k.val = w := by change 13+(w-13)=w; omega
  change Payers.val gs w _ = true at h0 h1
  change Payers.val gs w _ = false at hd
  rw [← eq] at h0 h1 hd
  have op : (gs.get k).op = GateOp.or := by
    rcases (law _ (List.get_mem gs k)).1 with op | op
    · obtain ⟨a,ha,d⟩ := Payers.val_and_false_exists gs k _ (ok k).2 op hd
      exact False.elim (Nat.find_min someGood (show a < w from ((ok k).2 _ ha).trans_le eq.le)
        ⟨Payers.val_and_true gs k _ (ok k).2 op h0 ha,
         Payers.val_and_true gs k _ (ok k).2 op h1 ha,d⟩)
    · exact op
  refine ⟨k,op,?_⟩
  intro t t0 hk
  have no := (marked.mp hk).2.1
  have lt : 13+k.val < 13+gs.length := by have := k.isLt; omega
  have yes : Payers.val gs (13+k) (coline t) = true := by
    rcases separate t t0 with h | h
    · exact Payers.val_mono gs law ok _ _ h _ lt h0
    · exact Payers.val_mono gs law ok _ _ h _ lt h1
  exact Bool.noConfusion (no.symm.trans yes)

lemma packed (gs : List Gate) (o : Vertex → ℕ) (law : Legal gs) (ok : Proper gs) (correct : Correct gs o) :
    37 ≤ gs.length := by
  classical
  let A := leftRows.biUnion (marks gs)
  let B := MS.biUnion (marks gs)
  let J := univ.filter fun k : Fin gs.length => (gs.get k).op = GateOp.and
  have disj (S : Finset Vertex) (sep : ∀ t ∈ S, ∀ u ∈ S, t ≠ 0 ∧ ¬ allowed t u) :
      (S : Set Vertex).PairwiseDisjoint (marks gs) := by
    intro i hi j hj ne
    exact disjoint_left.mpr fun _ a b => (sep _ hi _ hj).2
      (collision law ok (sep _ hi _ hi).1 (sep _ hj _ hj).1 ne a b)
  have total (S : Finset Vertex) (sep : ∀ t ∈ S, ∀ u ∈ S, t ≠ 0 ∧ ¬ allowed t u) :
      (S.biUnion (marks gs)).card = S.card * 3 := by
    rw [card_biUnion (disj S sep)]
    exact (sum_congr rfl (fun i hi => mark_count gs o law ok correct i (sep _ hi _ hi).1)).trans (by simp)
  have ca : A.card = 27 := (total leftRows sameSide.1).trans (by rw [sizeLeft])
  have cb : B.card = 9 := (total MS sameSide.2).trans (by rw [sizeRight])
  let mult := univ.filter fun k : Fin gs.length => ∃ l ∈ LS, ∃ m ∈ MS,
    Payers.Merges gs l k ∧ Payers.Merges gs m k
  have both : (A ∩ B) ⊆ mult := by
    intro k hk
    obtain ⟨al,br⟩ := mem_inter.mp hk
    obtain ⟨l,hl,lg⟩ := mem_biUnion.mp al
    obtain ⟨m,hm,mg⟩ := mem_biUnion.mp br
    have lm : l ≠ m := by intro h; exact (mem_sdiff.mp hl).2 (h ▸ hm)
    have hl' := across l hl m hm (collision law ok (sameSide.1 _ hl _ hl).1 (sameSide.2 _ hm _ hm).1 lm lg mg)
    have toMerge (t : Vertex) (ht : t ∈ LS ∪ MS) (a : k ∈ marks gs t) : Payers.Merges gs t k := by
      have h := marked.mp a
      unfold test at h
      simp only [ite_eq_left ht] at h
      exact h
    exact mem_filter.mpr ⟨mem_univ _,l,hl',m,hm,toMerge _ (mem_union_left _ hl') lg,toMerge _ (mem_union_right _ hm) mg⟩
  have pay := Payers.main_proof gs law ok mult J (by intro k; simp [mult])
    (fun z hz => mem_filter.mpr ⟨mem_univ _,hz.1⟩)
  have distinct (C : Finset Vertex) : Disjoint (C.biUnion (marks gs)) J := by
    apply disjoint_left.mpr
    intro k hc hj
    obtain ⟨t,_,h⟩ := mem_biUnion.mp hc
    have a := (marked.mp h).1
    have b := (mem_filter.mp hj).2
    rw [a] at b
    contradiction
  have dis : Disjoint (A ∪ B) J := (distinct leftRows).sup_left (distinct MS)
  obtain ⟨k,op,extra⟩ := extra_or gs o law ok correct
  have absent (S : Finset Vertex) (hS : ∀ t ∈ S, t ≠ 0) : k ∉ S.biUnion (marks gs) := by
    intro h
    obtain ⟨t,ht,hm⟩ := mem_biUnion.mp h
    exact extra t (hS _ ht) hm
  have na : k ∉ A := absent _ (fun t ht => (sameSide.1 _ ht _ ht).1)
  have nb : k ∉ B := absent _ (fun t ht => (sameSide.2 _ ht _ ht).1)
  have nj : k ∉ J := by
    intro h
    have hand : (gs.get k).op = GateOp.and := (mem_filter.mp h).2
    rw [op] at hand
    contradiction
  have lim := card_le_univ (insert k ((A ∪ B) ∪ J))
  rw [card_insert_of_notMem (by simp [na,nb,nj]),card_union_of_disjoint dis,Fintype.card_fin] at lim
  have overlap := (card_le_card both).trans pay
  have cap := card_union_add_card_inter A B
  omega

lemma solve (gs : List Gate) (o : Vertex → ℕ) (law : Legal gs) (correct : Correct gs o) : 37 ≤ gs.length := by
  have dynamic (t : Vertex) : dyn gs (o t) = true := by
    have false_at : V gs (o t) (coline t) = false :=
      (correct t _ (dark_ok t)).trans (by simp [coline])
    have zero : V gs (o t) (fun _ => false) = false := by
      cases eq : V gs (o t) (fun _ => false) with
      | false => rfl
      | true =>
        have con := mono (⟨gs,0⟩ : Circuit) law (fun _ : Vertex => false) (coline t) (by simp) (o t) eq
        exact Bool.noConfusion (false_at.symm.trans con)
    have one : V gs (o t) (fun _ => true) = true :=
      (correct t _ (Or.inl rfl)).trans (decide_eq_true ⟨t,by simp [line],rfl⟩)
    simp [dyn,zero,one]
  have norm := norm_legal law
  have valid : Correct (normalized gs) o := by
    intro t x hx
    exact (preserves law (o t) (dynamic t) x).trans (correct t x hx)
  exact (packed (normalized gs) o norm.1 norm.2 valid).trans (norm_len gs).le

end PEqualNP.Outside.L_meta_1576_aux

open PEqualNP.Outside.L_meta_1576_aux

theorem PEqualNP.Outside.L_meta_1576 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    37 ≤ gates.length := by
  intro L hL gs o hG hout
  obtain rfl : L = Payers.line := funext hL
  exact solve gs o hG hout
