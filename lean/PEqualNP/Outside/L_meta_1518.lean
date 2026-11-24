import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1518_aux

open PEqualNP.CircuitLowerBounds

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wval {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl wstep (List.ofFn x)).getD i false

theorem eval_eq_wval {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = wval gs x o := rfl

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [wstep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem wval_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    wval [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold wval
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem wval_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    wval (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => wval gs x j)
      else wval gs x i := by
  unfold wval
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, wstep]
  have hl : (gs.foldl wstep (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem wval_old {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i ≠ n + gs.length) : wval (gs ++ [g]) x i = wval gs x i := by
  rw [wval_snoc, ite_eq_right hi]

theorem wval_new {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wval (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map fun j => wval gs x j) := by
  rw [wval_snoc, ite_eq_left rfl]

theorem wval_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (h : wval gs x i = true) : i < n + gs.length := by
  by_contra hc
  have hl : (gs.foldl wstep (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  unfold wval at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

theorem eval_and_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  simp [GateOp.eval]

theorem eval_or_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  simp [GateOp.eval]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        (∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) ∧
        (a = b ∨ (g.op = GateOp.or ∧ g.inputs = [a, b]))) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, fun _ => ⟨h, h, ?_, Or.inl rfl⟩⟩
        intro y hy
        simp only [List.map_cons, List.map_nil, eval_and_two, Bool.and_eq_true] at hy
        exact Or.inl hy.1
      · refine ⟨b, b, fun hz => ?_⟩
        simp only [List.map_cons, List.map_nil, eval_and_two] at hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        refine ⟨hb, hb, ?_, Or.inl rfl⟩
        intro y hy
        simp only [List.map_cons, List.map_nil, eval_and_two, Bool.and_eq_true] at hy
        exact Or.inl hy.2
    · right
      refine ⟨a, b, fun hz => ?_⟩
      simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_false_iff] at hz
      refine ⟨hz.1, hz.2, ?_, Or.inr ⟨rfl, rfl⟩⟩
      intro y hy
      simp only [List.map_cons, List.map_nil, eval_or_two, Bool.or_eq_true] at hy
      exact hy
  | _ :: _ :: _ :: _, h => simp at h

def InvL {n : ℕ} (T : Finset (Fin n)) (Z : Fin n → Bool) (Y : Fin n → Fin n → Bool)
    (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, u ∈ T → v ∈ T → wval gs Z i = false → wval gs (Y u) i = true →
    wval gs (Y v) i = true → l u = l v

def Cnt {n : ℕ} (T : Finset (Fin n)) (Z : Fin n → Bool) (Y : Fin n → Fin n → Bool)
    (gs : List Gate) (i : ℕ) : Prop :=
  wval gs Z i = false ∧
  (∃ u v : Fin n, u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ wval gs (Y u) i = true ∧ wval gs (Y v) i = true) ∧
  ∃ g : Gate, gs[i - n]? = some g ∧ g.op = GateOp.or ∧
    ∀ w ∈ g.inputs, w < i ∧ ∃ u : Fin n, u ∈ T ∧ wval gs (Y u) w = true

open Classical in
noncomputable def Dset {n : ℕ} (T : Finset (Fin n)) (Z : Fin n → Bool)
    (Y : Fin n → Fin n → Bool) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt T Z Y gs i

theorem Dset_mono {n : ℕ} (T : Finset (Fin n)) (Z : Fin n → Bool) (Y : Fin n → Fin n → Bool)
    (gs : List Gate) (g : Gate) : Dset T Z Y gs ⊆ Dset T Z Y (gs ++ [g]) := by
  classical
  intro i hi
  simp only [Dset, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, ⟨u, v, huT, hvT, huv, hu, hv⟩, g', hg', hor, hins⟩ := hi.2
  refine ⟨?_, ⟨u, v, huT, hvT, huv, ?_, ?_⟩, g', ?_, hor, ?_⟩
  · rw [wval_old gs g _ i hne]
    exact hz
  · rw [wval_old gs g _ i hne]
    exact hu
  · rw [wval_old gs g _ i hne]
    exact hv
  · rw [List.getElem?_append_left (by omega)]
    exact hg'
  · intro w hw
    obtain ⟨hwi, u', hu'T, hu'⟩ := hins w hw
    refine ⟨hwi, u', hu'T, ?_⟩
    rw [wval_old gs g _ w (by omega)]
    exact hu'

theorem dset_gate {n : ℕ} (T : Finset (Fin n)) (Z : Fin n → Bool) (Y : Fin n → Fin n → Bool)
    (gs : List Gate) (i : ℕ) (hi : i ∈ Dset T Z Y gs) :
    ∃ (k : ℕ) (g : Gate), i = n + k ∧ gs[k]? = some g ∧ g.op = GateOp.or ∧
      ∀ w ∈ g.inputs, ∃ u : Fin n, u ∈ T ∧ wval gs (Y u) w = true := by
  classical
  simp only [Dset, Finset.mem_filter, Finset.mem_Ico] at hi
  obtain ⟨⟨h1, h2⟩, -, -, g, hg, hor, hins⟩ := hi
  exact ⟨i - n, g, by omega, hg, hor, fun w hw => (hins w hw).2⟩

theorem not_shorter {n : ℕ} (gs : List Gate) (g : Gate) (y : Fin n → Bool) (bv : Bool)
    (hnot : ∀ (k : ℕ) (g' : Gate), (gs ++ [g])[k]? = some g' → g'.op = GateOp.not →
      wval (gs ++ [g]) y (n + k) = bv) :
    ∀ (k : ℕ) (g' : Gate), gs[k]? = some g' → g'.op = GateOp.not →
      wval gs y (n + k) = bv := by
  intro k g' hk hg'
  obtain ⟨hklt, -⟩ := List.getElem?_eq_some_iff.mp hk
  have h1 : (gs ++ [g])[k]? = some g' := by
    rw [List.getElem?_append_left hklt]
    exact hk
  have h2 := hnot k g' h1 hg'
  rwa [wval_old gs g y (n + k) (by omega)] at h2

theorem wval_mono_hi {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (hnot : ∀ (k : ℕ) (g : Gate), gs[k]? = some g → g.op = GateOp.not →
      wval gs y (n + k) = true) :
    ∀ i, wval gs x i = true → wval gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [wval_nil] at hi ⊢
    by_cases h : i < n
    · rw [dite_eq_left h] at hi ⊢
      exact hxy _ hi
    · rw [dite_eq_right h] at hi
      exact absurd hi (by simp)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hg g' (by simp [hg'])) (not_shorter gs g y true hnot)
    intro i hi
    by_cases hiN : i = n + gs.length
    · subst hiN
      rcases (hg g (by simp)).1 with h | h | h
      · rw [wval_new] at hi ⊢
        rw [h] at hi ⊢
        simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true] at hi ⊢
        intro w hw
        exact ih' w (hi w hw)
      · rw [wval_new] at hi ⊢
        rw [h] at hi ⊢
        simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true] at hi ⊢
        obtain ⟨w, hw, hv⟩ := hi
        exact ⟨w, hw, ih' w hv⟩
      · exact hnot gs.length g (by simp) h
    · rw [wval_old gs g _ i hiN] at hi ⊢
      exact ih' i hi

theorem wval_mono_lo {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (hnot : ∀ (k : ℕ) (g : Gate), gs[k]? = some g → g.op = GateOp.not →
      wval gs x (n + k) = false) :
    ∀ i, wval gs x i = true → wval gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [wval_nil] at hi ⊢
    by_cases h : i < n
    · rw [dite_eq_left h] at hi ⊢
      exact hxy _ hi
    · rw [dite_eq_right h] at hi
      exact absurd hi (by simp)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hg g' (by simp [hg'])) (not_shorter gs g x false hnot)
    intro i hi
    by_cases hiN : i = n + gs.length
    · subst hiN
      rcases (hg g (by simp)).1 with h | h | h
      · rw [wval_new] at hi ⊢
        rw [h] at hi ⊢
        simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true] at hi ⊢
        intro w hw
        exact ih' w (hi w hw)
      · rw [wval_new] at hi ⊢
        rw [h] at hi ⊢
        simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true] at hi ⊢
        obtain ⟨w, hw, hv⟩ := hi
        exact ⟨w, hw, ih' w hv⟩
      · exact absurd ((hnot gs.length g (by simp) h).symm.trans hi) (by simp)
    · rw [wval_old gs g _ i hiN] at hi ⊢
      exact ih' i hi

theorem wval_not_head {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k hh : ℕ) (g : Gate)
    (r : List ℕ) (hk : gs[k]? = some g) (hop : g.op = GateOp.not)
    (hin : g.inputs = (n + hh) :: r) (hlt : hh < k) :
    wval gs x (n + k) = !(wval gs x (n + hh)) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g0 ih =>
    obtain ⟨hklt, hkg⟩ := List.getElem?_eq_some_iff.mp hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hklt
    by_cases hkl : k = gs.length
    · have hgg : g0 = g := by
        rw [hkl] at hk
        simpa using hk
      rw [hkl, wval_new, wval_old gs g0 x (n + hh) (by omega), hgg, hop, hin]
      simp [GateOp.eval]
    · have hk' : gs[k]? = some g := by
        rw [List.getElem?_append_left (by omega)] at hk
        exact hk
      rw [wval_old gs g0 x (n + k) (by omega), wval_old gs g0 x (n + hh) (by omega)]
      exact ih hk'

theorem nf_of_h {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (hjnot : (gates.get j).op = GateOp.not)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hhj : h < j) (hjin : ∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r)
    (x : Fin n → Bool) (bv : Bool) (hx : wval gates x (n + (h : ℕ)) = !bv) :
    ∀ (k : ℕ) (g : Gate), gates[k]? = some g → g.op = GateOp.not →
      wval gates x (n + k) = bv := by
  intro k g hk hgn
  obtain ⟨hklt, hkg⟩ := List.getElem?_eq_some_iff.mp hk
  have hget : gates.get ⟨k, hklt⟩ = g := hkg
  have hkj : (⟨k, hklt⟩ : Fin gates.length) = j :=
    honly ⟨k, hklt⟩ (by rw [hget]; exact hgn)
  obtain ⟨r, hr⟩ := hjin
  have hjk : (j : ℕ) = k := by rw [← hkj]
  have hlt : (h : ℕ) < (j : ℕ) := hhj
  have hjj : gates[(j : ℕ)]? = some (gates.get j) := by simp
  have key := wval_not_head gates x (j : ℕ) (h : ℕ) (gates.get j) r hjj hjnot hr hlt
  rw [← hjk, key, hx]
  simp

theorem h_above {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hjnot : (gates.get j).op = GateOp.not)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hhj : h < j) (hjin : ∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (hx : wval gates x (n + (h : ℕ)) = true) : wval gates y (n + (h : ℕ)) = true := by
  cases hy : wval gates y (n + (h : ℕ)) with
  | true => rfl
  | false =>
    have hnf := nf_of_h gates j h hjnot honly hhj hjin y true (by rw [hy]; rfl)
    have hmono := wval_mono_hi gates hg x y hxy hnf (n + (h : ℕ)) hx
    rw [hy] at hmono
    exact hmono

theorem main_inv {n : ℕ} (T : Finset (Fin n)) (Z : Fin n → Bool) (Y : Fin n → Fin n → Bool)
    (hin : ∀ (c u v : Fin n), u ∈ T → v ∈ T → Z c = false → Y u c = true → Y v c = true →
      u = v)
    (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ (k : ℕ) (g : Gate), gs[k]? = some g → g.op = GateOp.not →
      ∀ u ∈ T, wval gs (Y u) (n + k) = false) :
    ∃ l : Fin n → Fin n, InvL T Z Y gs l ∧
      T.card ≤ (T.image l).card + (Dset T Z Y gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v huT hvT hz hu1 hv1
    rw [wval_nil] at hz hu1 hv1
    by_cases h : i < n
    · rw [dite_eq_left h] at hz hu1 hv1
      exact hin ⟨i, h⟩ u v huT hvT hz hu1 hv1
    · rw [dite_eq_right h] at hu1
      exact absurd hu1 (by simp)
  | append_singleton gs g ih =>
    have hnot' : ∀ (k : ℕ) (g' : Gate), gs[k]? = some g' → g'.op = GateOp.not →
        ∀ u ∈ T, wval gs (Y u) (n + k) = false := by
      intro k g' hk hg' u hu
      obtain ⟨hklt, -⟩ := List.getElem?_eq_some_iff.mp hk
      have h1 : (gs ++ [g])[k]? = some g' := by
        rw [List.getElem?_append_left hklt]
        exact hk
      have h2 := hnot k g' h1 hg' u hu
      rwa [wval_old gs g (Y u) (n + k) (by omega)] at h2
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg'])) hnot'
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    by_cases hm : wval (gs ++ [g]) Z (n + gs.length) = false ∧
        ∃ u v, u ∈ T ∧ v ∈ T ∧ wval (gs ++ [g]) (Y u) (n + gs.length) = true ∧
          wval (gs ++ [g]) (Y v) (n + gs.length) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0T, hv0T, hu0, hv0, hne⟩ := hm
      have hop2 : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have hf := hnot gs.length g (by simp) h u0 hu0T
          exact absurd (hf.symm.trans hu0) (by simp)
      rcases gate_cases g hop2 hlen (fun (x : Fin n → Bool) (j : ℕ) => wval gs x j) Z
        with hall | ⟨a, b, hab⟩
      · have h1 : g.op.eval (g.inputs.map fun j => wval gs (Y u0) j) = true :=
          (wval_new gs g (Y u0)).symm.trans hu0
        have h2 : g.op.eval (g.inputs.map fun j => wval gs (Y u0) j) = false := hall (Y u0)
        exact absurd (h2.symm.trans h1) (by simp)
      · obtain ⟨ha, hb, hy, hconv⟩ := hab ((wval_new gs g Z).symm.trans hz)
        have hy' : ∀ w, wval (gs ++ [g]) (Y w) (n + gs.length) = true →
            wval gs (Y w) a = true ∨ wval gs (Y w) b = true := by
          intro w hw
          exact hy (Y w) ((wval_new gs g (Y w)).symm.trans hw)
        have hA : ∀ w w', w ∈ T → w' ∈ T → wval gs (Y w) a = true →
            wval gs (Y w') a = true → l w = l w' :=
          fun w w' hw hw' h1 h2 => hinv a w w' hw hw' ha h1 h2
        have hB : ∀ w w', w ∈ T → w' ∈ T → wval gs (Y w) b = true →
            wval gs (Y w') b = true → l w = l w' :=
          fun w w' hw hw' h1 h2 => hinv b w w' hw hw' hb h1 h2
        have hsplit : (wval gs (Y u0) a = true ∧ wval gs (Y v0) b = true) ∨
            (wval gs (Y u0) b = true ∧ wval gs (Y v0) a = true) := by
          rcases hy' u0 hu0 with h1 | h1 <;> rcases hy' v0 hv0 with h2 | h2
          · exact absurd (hA u0 v0 hu0T hv0T h1 h2) hne
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩
          · exact absurd (hB u0 v0 hu0T hv0T h1 h2) hne
        have two : ∀ w, w ∈ T → wval (gs ++ [g]) (Y w) (n + gs.length) = true →
            l w = l u0 ∨ l w = l v0 := by
          intro w hwT hw
          rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hy' w hw with h | h
            · exact Or.inl (hA w u0 hwT hu0T h h1)
            · exact Or.inr (hB w v0 hwT hv0T h h2)
          · rcases hy' w hw with h | h
            · exact Or.inr (hA w v0 hwT hv0T h h2)
            · exact Or.inl (hB w u0 hwT hu0T h h1)
        have hgate : g.op = GateOp.or ∧ g.inputs = [a, b] := by
          rcases hconv with hab' | h
          · rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd (hA u0 v0 hu0T hv0T h1 (by rw [hab']; exact h2)) hne
            · exact absurd (hB u0 v0 hu0T hv0T h1 (by rw [← hab']; exact h2)) hne
          · exact h
        have hota : ∃ u, u ∈ T ∧ wval gs (Y u) a = true := by
          rcases hsplit with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact ⟨u0, hu0T, h1⟩
          · exact ⟨v0, hv0T, h2⟩
        have hotb : ∃ u, u ∈ T ∧ wval gs (Y u) b = true := by
          rcases hsplit with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact ⟨v0, hv0T, h2⟩
          · exact ⟨u0, hu0T, h1⟩
        have lift : ∀ w, (∃ u, u ∈ T ∧ wval gs (Y u) w = true) →
            w < n + gs.length ∧ ∃ u : Fin n, u ∈ T ∧ wval (gs ++ [g]) (Y u) w = true := by
          rintro w ⟨u', hu'T, hu'⟩
          have hlt := wval_lt gs (Y u') w hu'
          refine ⟨hlt, u', hu'T, ?_⟩
          rw [wval_old gs g _ w (by omega)]
          exact hu'
        have red : ∀ w, w ∈ T → wval (gs ++ [g]) (Y w) (n + gs.length) = true →
            (if l w = l v0 then l u0 else l w) = l u0 := by
          intro w hwT hw
          rcases two w hwT hw with h | h
          · rw [h]
            split_ifs <;> rfl
          · rw [ite_eq_left h]
        refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
        · intro i u v huT hvT hiz hiu hiv
          by_cases hi : i = n + gs.length
          · subst hi
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [red u huT hiu, red v hvT hiv]
          · rw [wval_old gs g _ i hi] at hiz hiu hiv
            have hl := hinv i u v huT hvT hiz hiu hiv
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [hl]
        · have himg : T.image l ⊆
              insert (l v0) (T.image fun w => if l w = l v0 then l u0 else l w) := by
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
            by_cases h : l w = l v0
            · rw [h]
              exact Finset.mem_insert_self _ _
            · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
              rw [ite_eq_right h]
          have h1 : (T.image l).card ≤
              (T.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
            (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
          have hNin : n + gs.length ∈ Dset T Z Y (gs ++ [g]) := by
            simp only [Dset, Finset.mem_filter, Finset.mem_Ico, List.length_append,
              List.length_cons, List.length_nil]
            refine ⟨⟨by omega, by omega⟩, hz, ⟨u0, v0, hu0T, hv0T, ?_, hu0, hv0⟩, g, ?_,
              hgate.1, ?_⟩
            · intro h
              exact hne (by rw [h])
            · simp
            · intro w hw
              rw [hgate.2] at hw
              have hw' : w = a ∨ w = b := by simpa using hw
              rcases hw' with h | h
              · rw [h]
                exact lift a hota
              · rw [h]
                exact lift b hotb
          have hNnot : n + gs.length ∉ Dset T Z Y gs := by
            simp only [Dset, Finset.mem_filter, Finset.mem_Ico]
            intro h
            omega
          have h2 : (Dset T Z Y gs).card + 1 ≤ (Dset T Z Y (gs ++ [g])).card := by
            rw [← Finset.card_insert_of_notMem hNnot]
            apply Finset.card_le_card
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hNin
            · exact Dset_mono T Z Y gs g hi
          omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v huT hvT hiz hiu hiv
        by_cases hi : i = n + gs.length
        · subst hi
          by_contra hne
          exact hm ⟨hiz, u, v, huT, hvT, hiu, hiv, hne⟩
        · rw [wval_old gs g _ i hi] at hiz hiu hiv
          exact hinv i u v huT hvT hiz hiu hiv
      · have := Finset.card_le_card (Dset_mono T Z Y gs g)
        omega

def ln (w : Fin 13) : Finset (Fin 13) := {w, w + 1, w + 3, w + 9}

theorem ln_inter : ∀ w w' : Fin 13, w ≠ w' → (ln w ∩ ln w').card ≤ 1 := by decide

theorem ln_card : ∀ w : Fin 13, (ln w).card = 4 := by decide

theorem ln_two (w w' a b : Fin 13) (hne : w ≠ w') (ha : a ∈ ln w) (hb : b ∈ ln w)
    (ha' : a ∈ ln w') (hb' : b ∈ ln w') : a = b :=
  Finset.card_le_one.mp (ln_inter w w' hne) a (Finset.mem_inter.mpr ⟨ha, ha'⟩) b
    (Finset.mem_inter.mpr ⟨hb, hb'⟩)

def eof (u : Fin 13) : Fin 13 → Bool := fun c => decide (c = u)

def Zl (w : Fin 13) : Fin 13 → Bool := fun c => decide (c ∉ ln w)

def bse (t u v w : Fin 13) : Fin 13 := if t ∈ ln w then u else if u ∈ ln w then v else t

def Tl (s t u v w : Fin 13) : Finset (Fin 13) := if w = s then {t, u, v} else ln w

def Yl (s t u v w p : Fin 13) : Fin 13 → Bool :=
  fun c => decide (c = p ∨ (w ≠ s ∧ c = bse t u v w))

theorem bse_mem3 (t u v w : Fin 13) :
    bse t u v w = t ∨ bse t u v w = u ∨ bse t u v w = v := by
  unfold bse
  split_ifs
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl

theorem bse_not_mem (s t u v w : Fin 13) (hts : t ∈ ln s) (hus : u ∈ ln s) (hvs : v ∈ ln s)
    (htu : t ≠ u) (huv : u ≠ v) (hw : w ≠ s) : bse t u v w ∉ ln w := by
  unfold bse
  split_ifs with h1 h2
  · intro h
    exact htu (ln_two w s t u hw h1 h hts hus)
  · intro h
    exact huv (ln_two w s u v hw h2 h hus hvs)
  · exact h1

theorem bse_cross (s t u v w w' : Fin 13) (hts : t ∈ ln s) (hus : u ∈ ln s) (hvs : v ∈ ln s)
    (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v) (hw : w ≠ s) (hw' : w' ≠ s)
    (h1 : bse t u v w ∈ ln w') (h2 : bse t u v w' ∈ ln w) : False := by
  unfold bse at h1 h2
  by_cases a1 : t ∈ ln w
  · rw [ite_eq_left a1] at h1
    have a2 : t ∉ ln w' := fun a2 => htu (ln_two w' s t u hw' a2 h1 hts hus)
    rw [ite_eq_right a2, ite_eq_left h1] at h2
    exact htv (ln_two w s t v hw a1 h2 hts hvs)
  · rw [ite_eq_right a1] at h1
    by_cases a3 : u ∈ ln w
    · rw [ite_eq_left a3] at h1
      have a2 : t ∉ ln w' := fun a2 => htv (ln_two w' s t v hw' a2 h1 hts hvs)
      have a4 : u ∉ ln w' := fun a4 => huv (ln_two w' s u v hw' a4 h1 hus hvs)
      rw [ite_eq_right a2, ite_eq_right a4] at h2
      exact a1 h2
    · rw [ite_eq_right a3] at h1
      rw [ite_eq_left h1] at h2
      exact a3 h2

theorem tl_sub (s t u v w p : Fin 13) (hts : t ∈ ln s) (hus : u ∈ ln s) (hvs : v ∈ ln s)
    (hp : p ∈ Tl s t u v w) : p ∈ ln w := by
  unfold Tl at hp
  by_cases hw : w = s
  · rw [ite_eq_left hw] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [hw]
    rcases hp with h | h | h
    · rw [h]
      exact hts
    · rw [h]
      exact hus
    · rw [h]
      exact hvs
  · rw [ite_eq_right hw] at hp
    exact hp

theorem tl_card (s t u v w : Fin 13) (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v) :
    (Tl s t u v w).card = if w = s then 3 else 4 := by
  unfold Tl
  by_cases hw : w = s
  · rw [ite_eq_left hw, ite_eq_left hw, Finset.card_insert_of_notMem (by simp [htu, htv]),
      Finset.card_pair huv]
  · rw [ite_eq_right hw, ite_eq_right hw]
    exact ln_card w

theorem yl_h (gates : List Gate) (j h : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hjnot : (gates.get j).op = GateOp.not)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hhj : h < j) (hjin : ∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r)
    (s t u v : Fin 13)
    (ht : wval gates (eof t) (13 + (h : ℕ)) = true)
    (hu : wval gates (eof u) (13 + (h : ℕ)) = true)
    (hv : wval gates (eof v) (13 + (h : ℕ)) = true)
    (w p : Fin 13) (hp : p ∈ Tl s t u v w) :
    wval gates (Yl s t u v w p) (13 + (h : ℕ)) = true := by
  have h3 : ∀ b, b = t ∨ b = u ∨ b = v → wval gates (eof b) (13 + (h : ℕ)) = true := by
    intro b hb
    rcases hb with hb | hb | hb
    · rw [hb]
      exact ht
    · rw [hb]
      exact hu
    · rw [hb]
      exact hv
  by_cases hw : w = s
  · have hp' : p = t ∨ p = u ∨ p = v := by
      unfold Tl at hp
      rw [ite_eq_left hw] at hp
      simpa using hp
    refine h_above gates j h hg hjnot honly hhj hjin (eof p) _ ?_ (h3 p hp')
    intro c hc
    have hcp : c = p := of_decide_eq_true hc
    exact decide_eq_true (Or.inl hcp)
  · refine h_above gates j h hg hjnot honly hhj hjin (eof (bse t u v w)) _ ?_
      (h3 _ (bse_mem3 t u v w))
    intro c hc
    have hcp : c = bse t u v w := of_decide_eq_true hc
    exact decide_eq_true (Or.inr ⟨hw, hcp⟩)

theorem line_count (gates : List Gate) (o : Fin 13 → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      wval gates x (o w) = decide (∃ c ∈ ln w, x c = true))
    (s t u v : Fin 13) (hts : t ∈ ln s) (hus : u ∈ ln s) (hvs : v ∈ ln s)
    (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v)
    (hK : ∀ w p, p ∈ Tl s t u v w → ∀ (k : ℕ) (g : Gate), gates[k]? = some g →
      g.op = GateOp.not → wval gates (Yl s t u v w p) (13 + k) = false)
    (w : Fin 13) :
    (if w = s then 2 else 3) ≤ (Dset (Tl s t u v w) (Zl w) (Yl s t u v w) gates).card := by
  have hin : ∀ (c a b : Fin 13), a ∈ Tl s t u v w → b ∈ Tl s t u v w → Zl w c = false →
      Yl s t u v w a c = true → Yl s t u v w b c = true → a = b := by
    intro c a b _ _ hz ha hb
    have hc : c ∈ ln w := by
      by_contra hc'
      have hz' : Zl w c = true := decide_eq_true hc'
      rw [hz] at hz'
      exact Bool.false_ne_true hz'
    have key : ∀ p, Yl s t u v w p c = true → c = p := by
      intro p hp
      rcases (of_decide_eq_true hp : c = p ∨ (w ≠ s ∧ c = bse t u v w)) with h | ⟨hw, h⟩
      · exact h
      · exact absurd (h ▸ hc) (bse_not_mem s t u v w hts hus hvs htu huv hw)
    exact (key a ha).symm.trans (key b hb)
  obtain ⟨l, hinv, hcount⟩ := main_inv (Tl s t u v w) (Zl w) (Yl s t u v w) hin gates hg
    (fun k g hk hgn p hp => hK w p hp k g hk hgn)
  have hZout : wval gates (Zl w) (o w) = false := by
    rw [hev, decide_eq_false_iff_not]
    rintro ⟨c, hc, hzc⟩
    exact (of_decide_eq_true hzc : c ∉ ln w) hc
  have hYout : ∀ p ∈ Tl s t u v w, wval gates (Yl s t u v w p) (o w) = true := by
    intro p hp
    rw [hev, decide_eq_true_eq]
    exact ⟨p, tl_sub s t u v w p hts hus hvs hp, decide_eq_true (Or.inl rfl)⟩
  have himg : ((Tl s t u v w).image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact hinv (o w) p q hp hq hZout (hYout p hp) (hYout q hq)
  have hc := tl_card s t u v w htu huv htv
  by_cases hw : w = s
  · rw [ite_eq_left hw] at hc ⊢
    omega
  · rw [ite_eq_right hw] at hc ⊢
    omega

theorem cross (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (s t u v : Fin 13)
    (hK : ∀ w p, p ∈ Tl s t u v w → ∀ (k : ℕ) (g : Gate), gates[k]? = some g →
      g.op = GateOp.not → wval gates (Yl s t u v w p) (13 + k) = false)
    (w w' p : Fin 13) (hp : p ∈ Tl s t u v w) (i : ℕ)
    (hhot : wval gates (Yl s t u v w p) i = true) (hlow : wval gates (Zl w') i = false) :
    p ∈ ln w' ∨ (w ≠ s ∧ bse t u v w ∈ ln w') := by
  by_contra hcon
  rw [not_or] at hcon
  have hle : ∀ c, Yl s t u v w p c = true → Zl w' c = true := by
    intro c hc
    rcases (of_decide_eq_true hc : c = p ∨ (w ≠ s ∧ c = bse t u v w)) with h | ⟨hw, h⟩
    · rw [h]
      exact decide_eq_true hcon.1
    · rw [h]
      exact decide_eq_true (fun hm => hcon.2 ⟨hw, hm⟩)
  have hmono := wval_mono_lo gates hg _ _ hle (hK w p hp) i hhot
  rw [hlow] at hmono
  exact Bool.false_ne_true hmono

theorem line_disj (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (s t u v : Fin 13) (hts : t ∈ ln s) (hus : u ∈ ln s) (hvs : v ∈ ln s)
    (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v)
    (hK : ∀ w p, p ∈ Tl s t u v w → ∀ (k : ℕ) (g : Gate), gates[k]? = some g →
      g.op = GateOp.not → wval gates (Yl s t u v w p) (13 + k) = false)
    (w w' : Fin 13) (hne : w ≠ w') (i : ℕ)
    (hi : i ∈ Dset (Tl s t u v w) (Zl w) (Yl s t u v w) gates)
    (hi' : i ∈ Dset (Tl s t u v w') (Zl w') (Yl s t u v w') gates) : False := by
  classical
  simp only [Dset, Finset.mem_filter] at hi hi'
  obtain ⟨-, hz, ⟨p, p', hp, hp', hpp, hhp, hhp'⟩, -⟩ := hi
  obtain ⟨-, hz', ⟨q, q', hq, hq', hqq, hhq, hhq'⟩, -⟩ := hi'
  have X : w ≠ s ∧ bse t u v w ∈ ln w' := by
    rcases cross gates hg s t u v hK w w' p hp i hhp hz' with h1 | h1
    · rcases cross gates hg s t u v hK w w' p' hp' i hhp' hz' with h2 | h2
      · exact absurd (ln_two w w' p p' hne (tl_sub s t u v w p hts hus hvs hp)
          (tl_sub s t u v w p' hts hus hvs hp') h1 h2) hpp
      · exact h2
    · exact h1
  have X' : w' ≠ s ∧ bse t u v w' ∈ ln w := by
    rcases cross gates hg s t u v hK w' w q hq i hhq hz with h1 | h1
    · rcases cross gates hg s t u v hK w' w q' hq' i hhq' hz with h2 | h2
      · exact absurd (ln_two w' w q q' (Ne.symm hne) (tl_sub s t u v w' q hts hus hvs hq)
          (tl_sub s t u v w' q' hts hus hvs hq') h1 h2) hqq
      · exact h2
    · exact h1
  exact bse_cross s t u v w w' hts hus hvs htu huv htv X.1 X'.1 X.2 X'.2

theorem sum38 (s : Fin 13) (f : Fin 13 → ℕ) (hf : ∀ w, (if w = s then 2 else 3) ≤ f w) :
    38 ≤ ∑ w : Fin 13, f w := by
  have h1 : ∑ w : Fin 13, (if w = s then 2 else 3) ≤ ∑ w : Fin 13, f w :=
    Finset.sum_le_sum fun w _ => hf w
  have h2 : ∀ s : Fin 13, ∑ w : Fin 13, (if w = s then 2 else 3) = 38 := by decide
  rw [h2 s] at h1
  exact h1

theorem core (gates : List Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hjnot : (gates.get j).op = GateOp.not)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hhj : h < j) (hjin : ∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r)
    (hev : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      wval gates x (o w) = decide (∃ c ∈ ln w, x c = true))
    (s t u v : Fin 13) (hts : t ∈ ln s) (hus : u ∈ ln s) (hvs : v ∈ ln s)
    (htu : t ≠ u) (huv : u ≠ v) (htv : t ≠ v)
    (ht : wval gates (eof t) (13 + (h : ℕ)) = true)
    (hu : wval gates (eof u) (13 + (h : ℕ)) = true)
    (hv : wval gates (eof v) (13 + (h : ℕ)) = true)
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, (gates.get g).op = GateOp.and ∧ g < h) :
    38 + 1 + (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + I.card ≤ gates.length := by
  have hK : ∀ w p, p ∈ Tl s t u v w → ∀ (k : ℕ) (g : Gate), gates[k]? = some g →
      g.op = GateOp.not → wval gates (Yl s t u v w p) (13 + k) = false := by
    intro w p hp
    exact nf_of_h gates j h hjnot honly hhj hjin _ false
      (yl_h gates j h hg hjnot honly hhj hjin s t u v ht hu hv w p hp)
  have hjj : gates[(j : ℕ)]? = some (gates.get j) := by simp
  have hget : ∀ (k : Fin gates.length) (g : Gate), gates[(k : ℕ)]? = some g →
      gates.get k = g := by
    intro k g hk
    have hk' : gates[(k : ℕ)]? = some (gates.get k) := by simp
    rw [hk'] at hk
    exact Option.some.inj hk
  have hgate : ∀ (w : Fin 13) (k : Fin gates.length),
      13 + (k : ℕ) ∈ Dset (Tl s t u v w) (Zl w) (Yl s t u v w) gates →
      (gates.get k).op = GateOp.or ∧ 13 + (j : ℕ) ∉ (gates.get k).inputs := by
    intro w k hk
    obtain ⟨k', g, hkk, hgk, hor, hins⟩ := dset_gate _ _ _ gates _ hk
    have hk'k : k' = (k : ℕ) := by omega
    rw [hk'k] at hgk
    have hgg := hget k g hgk
    rw [hgg]
    refine ⟨hor, fun hmem => ?_⟩
    obtain ⟨p, hp, hpv⟩ := hins _ hmem
    have hf := hK w p hp (j : ℕ) (gates.get j) hjj hjnot
    rw [hf] at hpv
    exact Bool.false_ne_true hpv
  have hcount := fun w => line_count gates o hg hev s t u v hts hus hvs htu huv htv hK w
  have hdisj := fun w w' hne i => line_disj gates hg s t u v hts hus hvs htu huv htv hK w w' hne i
  let A : Fin 13 → Finset (Fin gates.length) := fun w =>
    Finset.univ.filter (fun k : Fin gates.length =>
      13 + (k : ℕ) ∈ Dset (Tl s t u v w) (Zl w) (Yl s t u v w) gates)
  have hAmem : ∀ w k, k ∈ A w ↔
      13 + (k : ℕ) ∈ Dset (Tl s t u v w) (Zl w) (Yl s t u v w) gates := by
    intro w k
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
  have hAcard : ∀ w, (if w = s then 2 else 3) ≤ (A w).card := by
    intro w
    refine (hcount w).trans ?_
    refine le_trans ?_ (Finset.card_image_le (f := fun k : Fin gates.length => 13 + (k : ℕ)))
    apply Finset.card_le_card
    intro i hi
    obtain ⟨k', g, hkk, hgk, -, -⟩ := dset_gate _ _ _ gates _ hi
    obtain ⟨hklt, -⟩ := List.getElem?_eq_some_iff.mp hgk
    rw [Finset.mem_image]
    refine ⟨⟨k', hklt⟩, (hAmem w _).mpr ?_, hkk.symm⟩
    rw [← hkk]
    exact hi
  have hAdisj : ∀ w ∈ (Finset.univ : Finset (Fin 13)), ∀ w' ∈ (Finset.univ : Finset (Fin 13)),
      w ≠ w' → Disjoint (A w) (A w') := by
    intro w _ w' _ hne
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact hdisj w w' hne _ ((hAmem w k).mp hk) ((hAmem w' k).mp hk')
  have hU : 38 ≤ ((Finset.univ : Finset (Fin 13)).biUnion A).card := by
    rw [Finset.card_biUnion hAdisj]
    exact sum38 s _ hAcard
  have hUmem : ∀ k, k ∈ (Finset.univ : Finset (Fin 13)).biUnion A →
      (gates.get k).op = GateOp.or ∧ 13 + (j : ℕ) ∉ (gates.get k).inputs := by
    intro k hk
    obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hk
    exact hgate w k ((hAmem w k).mp hw)
  have hUR : Disjoint ((Finset.univ : Finset (Fin 13)).biUnion A)
      (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact (hUmem k hk).2 (Finset.mem_filter.mp hk').2.2
  have hURI : Disjoint ((Finset.univ : Finset (Fin 13)).biUnion A ∪
      (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs))) I := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨hand, hlt⟩ := hI k hk'
    rcases Finset.mem_union.mp hk with h1 | h1
    · have hor := (hUmem k h1).1
      rw [hand] at hor
      exact GateOp.noConfusion hor
    · have h2 := (Finset.mem_filter.mp h1).2.1
      exact absurd (lt_trans (lt_trans hlt hhj) h2) (lt_irrefl _)
  have hjnotin : j ∉ ((Finset.univ : Finset (Fin 13)).biUnion A ∪
      (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs))) ∪ I := by
    intro hj
    rcases Finset.mem_union.mp hj with h1 | h1
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · have hor := (hUmem j h2).1
        rw [hjnot] at hor
        exact GateOp.noConfusion hor
      · exact absurd (Finset.mem_filter.mp h2).2.1 (lt_irrefl _)
    · have hand := (hI j h1).1
      rw [hjnot] at hand
      exact GateOp.noConfusion hand
  have hcardall := Finset.card_le_univ (insert j (((Finset.univ : Finset (Fin 13)).biUnion A ∪
      (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs))) ∪ I))
  rw [Finset.card_insert_of_notMem hjnotin, Finset.card_union_of_disjoint hURI,
    Finset.card_union_of_disjoint hUR, Fintype.card_fin] at hcardall
  omega

end PEqualNP.Outside.L_meta_1518_aux

theorem PEqualNP.Outside.L_meta_1518 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ (s t u v : Fin 13), t ∈ L s → u ∈ L s → v ∈ L s → t ≠ u → u ≠ v → t ≠ v →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = u))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = v))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      38 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 1 I.card ≤ gates.length := by
  intro L hL gates o j h hg hjnot honly hhj hjin hev _ s t u v hts hus hvs htu huv htv ht hu hv I hI
  have hLfun : L = PEqualNP.Outside.L_meta_1518_aux.ln := funext hL
  subst hLfun
  have hI' : ∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g < h := by
    intro g hgI
    obtain ⟨hand, hT⟩ := hI g hgI
    refine ⟨hand, ?_⟩
    have hmem : g ∈ Finset.univ.filter (fun g' : Fin gates.length => g' < h) := by
      apply hT
      intro i g' hi _ hlt
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hi with hi | hi
      · rw [← hi]
        exact hlt
      · exact lt_trans hlt (Finset.mem_filter.mp hi).2
    exact (Finset.mem_filter.mp hmem).2
  have hmain := PEqualNP.Outside.L_meta_1518_aux.core gates o j h hg hjnot honly hhj hjin
    (fun w x => hev w x) s t u v hts hus hvs htu huv htv ht hu hv I hI'
  omega
