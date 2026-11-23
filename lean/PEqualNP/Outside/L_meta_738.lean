import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_append (gs1 gs2 : List Gate) (w : List Bool) :
    run (gs1 ++ gs2) w = run gs2 (run gs1 w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma getD_snoc_lt {α : Type} (w : List α) (b d : α) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i d = w.getD i d :=
  List.getD_append _ _ _ _ hi

lemma getD_snoc_eq {α : Type} (w : List α) (b d : α) :
    (w ++ [b]).getD w.length d = b := by
  simp [List.getD]

lemma run_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact getD_snoc_lt _ _ _ _ hi

lemma run_snoc_getD (D : List Gate) (h : Gate) (x : List Bool) (P : ℕ) (hx : x.length = P) :
    (run (D ++ [h]) x).getD (P + D.length) false =
      h.op.eval (h.inputs.map fun i => (run D x).getD i false) := by
  rw [run_append]
  change (run D x ++ [_]).getD (P + D.length) false = _
  have hlen : (run D x).length = P + D.length := by rw [run_length, hx]
  rw [← hlen, getD_snoc_eq]

lemma and_eval (W : List Bool) (l : List ℕ) :
    GateOp.and.eval (l.map fun i => W.getD i false) = true ↔ ∀ k ∈ l, W.getD k false = true := by
  simp [GateOp.eval]

lemma or_eval (W : List Bool) (l : List ℕ) :
    GateOp.or.eval (l.map fun i => W.getD i false) = true ↔ ∃ k ∈ l, W.getD k false = true := by
  simp [GateOp.eval]

def degs (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) d

lemma degs_mem (gs : List Gate) (d : List ℕ) (e : ℕ) (he : e ∈ d) : e ∈ degs gs d := by
  induction gs generalizing d with
  | nil => exact he
  | cons g gs ih =>
    change e ∈ degs gs (d ++ [g.lineDegree d])
    exact ih _ (List.mem_append_left _ he)

lemma degs_length (gs : List Gate) (d : List ℕ) :
    (degs gs d).length = d.length + gs.length := by
  induction gs generalizing d with
  | nil => simp [degs]
  | cons g gs ih =>
    change (degs gs (d ++ [g.lineDegree d])).length = _
    rw [ih]
    simp
    omega

lemma degs_getD_of_lt (gs : List Gate) (d : List ℕ) (i : ℕ) (hi : i < d.length) :
    (degs gs d).getD i 0 = d.getD i 0 := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    change (degs gs (d ++ [g.lineDegree d])).getD i 0 = _
    rw [ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

lemma le_sum_of_mem (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.1 h with hab | h
    · rw [hab]; simp
    · have := ih h
      simp only [List.sum_cons]
      omega

lemma le_foldr_max_of_mem (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.1 h with hab | h
    · rw [hab]; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma input_deg_le (g : Gate) (d : List ℕ) (a : ℕ) (ha : a ∈ g.inputs) :
    d.getD a 0 ≤ g.lineDegree d := by
  have hm : d.getD a 0 ∈ g.inputs.map (fun i => d.getD i 0) := List.mem_map.2 ⟨a, ha, rfl⟩
  unfold Gate.lineDegree
  split
  · exact le_sum_of_mem _ _ hm
  · exact le_foldr_max_of_mem _ _ hm

def Rg (n : ℕ) (gs : List Gate) (a b : ℕ) : Prop :=
  a < b ∧ ∃ i : Fin gs.length, b = n + i.val ∧ a ∈ (gs.get i).inputs

lemma Rg_cons (n : ℕ) (g : Gate) (gs : List Gate) (a b : ℕ) (h : Rg n (g :: gs) a b) :
    (b = n ∧ a < n ∧ a ∈ g.inputs) ∨ Rg (n + 1) gs a b := by
  obtain ⟨hlt, ⟨i, hi⟩, hb, ha⟩ := h
  cases i with
  | zero =>
    left
    have hb' : b = n := by simpa using hb
    exact ⟨hb', by omega, by simpa using ha⟩
  | succ j =>
    right
    refine ⟨hlt, ⟨j, by simpa using hi⟩, ?_, ?_⟩
    · simp only at hb ⊢
      omega
    · simpa using ha

lemma reach_tail (n : ℕ) (g : Gate) (gs : List Gate) (out : ℕ) (a : ℕ)
    (h : Relation.ReflTransGen (Rg n (g :: gs)) a out) :
    n ≤ a → Relation.ReflTransGen (Rg (n + 1) gs) a out := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | head hab _ ih =>
    intro ha
    rcases Rg_cons _ _ _ _ _ hab with ⟨hb, hlt, _⟩ | h'
    · omega
    · have hlt := h'.1
      exact Relation.ReflTransGen.head h' (ih (by omega))

lemma reach_cons (n : ℕ) (g : Gate) (gs : List Gate) (out v : ℕ)
    (h : Relation.ReflTransGen (Rg n (g :: gs)) v out) :
    (v ∈ g.inputs ∧ v < n ∧ Relation.ReflTransGen (Rg (n + 1) gs) n out) ∨
      Relation.ReflTransGen (Rg (n + 1) gs) v out := by
  rcases Relation.ReflTransGen.cases_head h with hvo | ⟨b, hvb, hb⟩
  · right; rw [hvo]
  · rcases Rg_cons _ _ _ _ _ hvb with ⟨hbn, hlt, hin⟩ | h'
    · left
      rw [hbn] at hb
      exact ⟨hin, hlt, reach_tail _ _ _ _ _ hb le_rfl⟩
    · right
      have hge : n ≤ b := by
        obtain ⟨_, i, hi, _⟩ := h'
        omega
      exact Relation.ReflTransGen.head h' (reach_tail _ _ _ _ _ hb hge)

lemma deg_mono (gs : List Gate) : ∀ (d : List ℕ) (a b : ℕ), Rg d.length gs a b →
    (degs gs d).getD a 0 ≤ (degs gs d).getD b 0 := by
  induction gs with
  | nil =>
    intro d a b h
    obtain ⟨_, i, _⟩ := h
    exact absurd i.isLt (by simp)
  | cons g gs ih =>
    intro d a b h
    change (degs gs (d ++ [g.lineDegree d])).getD a 0 ≤ (degs gs (d ++ [g.lineDegree d])).getD b 0
    rcases Rg_cons _ _ _ _ _ h with ⟨hbn, hlt, hin⟩ | h'
    · rw [hbn, degs_getD_of_lt _ _ _ (by simp; omega), degs_getD_of_lt _ _ _ (by simp),
        getD_snoc_lt _ _ _ _ hlt, getD_snoc_eq]
      exact input_deg_le g d a hin
    · have hl : (d ++ [g.lineDegree d]).length = d.length + 1 := by simp
      exact ih _ a b (hl ▸ h')

lemma deg_mono_rtg (gs : List Gate) (d : List ℕ) (a b : ℕ)
    (h : Relation.ReflTransGen (Rg d.length gs) a b) :
    (degs gs d).getD a 0 ≤ (degs gs d).getD b 0 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (deg_mono gs d _ _ hbc)

lemma getD_le_one (l : List ℕ) (h : ∀ e ∈ l, e ≤ 1) (i : ℕ) : l.getD i 0 ≤ 1 := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

lemma lt_of_getD_eq_one (l : List ℕ) (i : ℕ) (h : l.getD i 0 = 1) : i < l.length := by
  by_contra hi
  rw [List.getD_eq_default _ _ (by omega)] at h
  omega

lemma singleton_of (l : List ℕ) (h1 : l.length ≤ 1) (h2 : l ≠ []) : ∃ k, l = [k] := by
  match l, h1, h2 with
  | [], _, h2 => exact absurd rfl h2
  | [k], _, _ => exact ⟨k, rfl⟩
  | _ :: _ :: _, h1, _ => simp at h1

abbrev cval (W : List Bool) (l : List ℕ) : Prop := ∀ k ∈ l, W.getD k false = true

abbrev GoodGates (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

abbrev Good (d0 : List ℕ) (P : ℕ) (D : List Gate) (N : Finset ℕ) (cx : ℕ → List ℕ) : Prop :=
  (∀ v ∈ N, v < d0.length ∧ d0.getD v 0 = 1) ∧
    (∀ v ∈ N, (cx v).length ≤ 1 ∧ ∀ k ∈ cx v, k < P + D.length)

abbrev Phi (D : List Gate) (N : Finset ℕ) (cx : ℕ → List ℕ) (x w : List Bool) : Prop :=
  ∃ v ∈ N, w.getD v false = true ∧ cval (run D x) (cx v)

lemma cval_stable (D ex : List Gate) (x : List Bool) (P : ℕ) (l : List ℕ) (hx : x.length = P)
    (hl : ∀ k ∈ l, k < P + D.length) : cval (run (D ++ ex) x) l ↔ cval (run D x) l := by
  constructor
  · intro h k hk
    have h1 := h k hk
    have h2 := hl k hk
    rwa [run_append, run_getD_of_lt _ _ _ (by rw [run_length]; omega)] at h1
  · intro h k hk
    have h2 := hl k hk
    rw [run_append, run_getD_of_lt _ _ _ (by rw [run_length]; omega)]
    exact h k hk

lemma Phi_stable (d0 : List ℕ) (P : ℕ) (D ex : List Gate) (N : Finset ℕ) (cx : ℕ → List ℕ)
    (x w : List Bool) (hG : Good d0 P D N cx) (hx : x.length = P) :
    Phi (D ++ ex) N cx x w ↔ Phi D N cx x w := by
  constructor
  · rintro ⟨v, hv, hw, hc⟩
    exact ⟨v, hv, hw, (cval_stable D ex x P _ hx (hG.2 v hv).2).1 hc⟩
  · rintro ⟨v, hv, hw, hc⟩
    exact ⟨v, hv, hw, (cval_stable D ex x P _ hx (hG.2 v hv).2).2 hc⟩

lemma Good_ext (d0 : List ℕ) (P : ℕ) (D ex : List Gate) (N : Finset ℕ) (cx : ℕ → List ℕ)
    (hG : Good d0 P D N cx) : Good d0 P (D ++ ex) N cx := by
  refine ⟨hG.1, fun v hv => ⟨(hG.2 v hv).1, fun k hk => ?_⟩⟩
  have := (hG.2 v hv).2 k hk
  simp only [List.length_append]
  omega

lemma p1 (E F K A : Prop) : ((E ∨ F ∧ K) ∨ A) ↔ ((E ∨ A) ∨ F ∧ K) := by tauto

lemma p2 (X a b c : Prop) : (X ∨ a ∧ c ∧ b) ↔ (X ∨ (a ∧ b) ∧ c) := by tauto

lemma p3 (X a b c : Prop) : (X ∨ (b ∧ a) ∧ c) ↔ (X ∨ (a ∧ b) ∧ c) := by tauto

lemma p4 (X a b c : Prop) : ((X ∨ a ∧ c) ∨ b ∧ c) ↔ (X ∨ (a ∨ b) ∧ c) := by tauto

lemma p5 (X c : Prop) : X ↔ (X ∨ False ∧ c) := by tauto

lemma and_eval1 (W : List Bool) (a : ℕ) :
    GateOp.and.eval ([a].map fun i => W.getD i false) = true ↔ W.getD a false = true := by
  simp [GateOp.eval]

lemma and_eval2 (W : List Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map fun i => W.getD i false) = true ↔
      (W.getD a false = true ∧ W.getD b false = true) := by
  simp [GateOp.eval]

lemma or_eval0 (W : List Bool) :
    GateOp.or.eval (([] : List ℕ).map fun i => W.getD i false) = true ↔ False := by
  simp [GateOp.eval]

lemma or_eval1 (W : List Bool) (a : ℕ) :
    GateOp.or.eval ([a].map fun i => W.getD i false) = true ↔ W.getD a false = true := by
  simp [GateOp.eval]

lemma or_eval2 (W : List Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map fun i => W.getD i false) = true ↔
      (W.getD a false = true ∨ W.getD b false = true) := by
  simp [GateOp.eval]

lemma absorb (d0 : List ℕ) (P : ℕ) (D : List Gate) (N : Finset ℕ) (cx : ℕ → List ℕ)
    (Cn : List Bool → List Bool → Prop) (a : ℕ) (kl : List ℕ)
    (hG : Good d0 P D N cx)
    (hkl : kl.length ≤ 1 ∧ ∀ k ∈ kl, k < P + D.length)
    (ha : d0.getD a 0 = 0 ∨ d0.getD a 0 = 1)
    (hX : d0.getD a 0 = 0 → ∀ x : List Bool, x.length = P →
      ∃ F : Prop, ∀ w, Cn x w → (w.getD a false = true ↔ F)) :
    ∃ (ex : List Gate) (N' : Finset ℕ) (cx' : ℕ → List ℕ),
      GoodGates ex ∧ N ⊆ N' ∧ (d0.getD a 0 = 1 → a ∈ N') ∧
      Good d0 P (D ++ ex) N' cx' ∧
      ex.length + N'.card ≤ N.card + 1 ∧
      ∀ x : List Bool, x.length = P → ∀ E : Prop, ∃ E' : Prop, ∀ w, Cn x w →
        ((E' ∨ Phi (D ++ ex) N' cx' x w) ↔
          ((E ∨ Phi D N cx x w) ∨ (w.getD a false = true ∧ cval (run D x) kl))) := by
  rcases ha with h0 | h1
  · refine ⟨[], N, cx, ?_, Finset.Subset.refl _, ?_, ?_, ?_, ?_⟩
    · intro g hg; cases hg
    · intro h; omega
    · rw [List.append_nil]; exact hG
    · simp
    · intro x hx E
      obtain ⟨F, hF⟩ := hX h0 x hx
      refine ⟨E ∨ (F ∧ cval (run D x) kl), ?_⟩
      intro w hw
      rw [hF w hw, List.append_nil]
      exact p1 _ _ _ _
  · have haL : a < d0.length := lt_of_getD_eq_one _ _ h1
    by_cases haN : a ∈ N
    · by_cases hc : cx a = [] ∨ kl = []
      · refine ⟨[], N, fun v => if v = a then [] else cx v, ?_, Finset.Subset.refl _,
          fun _ => haN, ?_, ?_, ?_⟩
        · intro g hg; cases hg
        · rw [List.append_nil]
          refine ⟨hG.1, ?_⟩
          intro v hv
          by_cases hva : v = a
          · simp [hva]
          · simp only [hva, ite_false]
            exact hG.2 v hv
        · simp
        · intro x hx E
          refine ⟨E, ?_⟩
          intro w hw
          rw [List.append_nil]
          constructor
          · rintro (hE | ⟨v, hv, hwv, hcv⟩)
            · exact Or.inl (Or.inl hE)
            · by_cases hva : v = a
              · rw [hva] at hwv
                rcases hc with hc | hc
                · exact Or.inl (Or.inr ⟨a, haN, hwv, by rw [hc]; intro k hk; cases hk⟩)
                · exact Or.inr ⟨hwv, by rw [hc]; intro k hk; cases hk⟩
              · simp only [hva, ite_false] at hcv
                exact Or.inl (Or.inr ⟨v, hv, hwv, hcv⟩)
          · rintro ((hE | ⟨v, hv, hwv, hcv⟩) | ⟨hwa, _⟩)
            · exact Or.inl hE
            · refine Or.inr ⟨v, hv, hwv, ?_⟩
              by_cases hva : v = a
              · simp only [hva, ite_true]
                intro k hk; cases hk
              · simp only [hva, ite_false]
                exact hcv
            · refine Or.inr ⟨a, haN, hwa, ?_⟩
              simp only [ite_true]
              intro k hk; cases hk
      · have hc1 : cx a ≠ [] := fun h => hc (Or.inl h)
        have hc2 : kl ≠ [] := fun h => hc (Or.inr h)
        obtain ⟨k1, hk1⟩ := singleton_of _ (hG.2 a haN).1 hc1
        obtain ⟨k2, hk2⟩ := singleton_of _ hkl.1 hc2
        refine ⟨[(⟨GateOp.or, [k1, k2]⟩ : Gate)], N,
          fun v => if v = a then [P + D.length] else cx v, ?_, Finset.Subset.refl _,
          fun _ => haN, ?_, ?_, ?_⟩
        · intro g hg
          rw [List.mem_singleton] at hg
          rw [hg]
          exact ⟨Or.inr rfl, by simp⟩
        · refine ⟨hG.1, ?_⟩
          intro v hv
          by_cases hva : v = a
          · simp [hva]
          · simp only [hva, ite_false]
            refine ⟨(hG.2 v hv).1, fun k hk => ?_⟩
            have := (hG.2 v hv).2 k hk
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
        · simp
          omega
        · intro x hx E
          refine ⟨E, ?_⟩
          intro w hw
          have hidx : (run (D ++ [(⟨GateOp.or, [k1, k2]⟩ : Gate)]) x).getD (P + D.length) false = true ↔
              ((run D x).getD k1 false = true ∨ (run D x).getD k2 false = true) := by
            rw [run_snoc_getD _ _ _ _ hx, or_eval]
            simp
          have hst : ∀ v ∈ N, (cval (run (D ++ [(⟨GateOp.or, [k1, k2]⟩ : Gate)]) x) (cx v) ↔
              cval (run D x) (cx v)) :=
            fun v hv => cval_stable D _ x P _ hx (hG.2 v hv).2
          constructor
          · rintro (hE | ⟨v, hv, hwv, hcv⟩)
            · exact Or.inl (Or.inl hE)
            · by_cases hva : v = a
              · rw [hva] at hwv
                simp only [hva, ite_true] at hcv
                have h3 := hcv (P + D.length) (by simp)
                rcases hidx.1 h3 with h4 | h4
                · refine Or.inl (Or.inr ⟨a, haN, hwv, ?_⟩)
                  rw [hk1]
                  intro k hk
                  rw [List.mem_singleton] at hk
                  rw [hk]; exact h4
                · refine Or.inr ⟨hwv, ?_⟩
                  rw [hk2]
                  intro k hk
                  rw [List.mem_singleton] at hk
                  rw [hk]; exact h4
              · simp only [hva, ite_false] at hcv
                exact Or.inl (Or.inr ⟨v, hv, hwv, (hst v hv).1 hcv⟩)
          · rintro ((hE | ⟨v, hv, hwv, hcv⟩) | ⟨hwa, hck⟩)
            · exact Or.inl hE
            · by_cases hva : v = a
              · refine Or.inr ⟨v, hv, hwv, ?_⟩
                simp only [hva, ite_true]
                intro k hk
                rw [List.mem_singleton] at hk
                rw [hk]
                rw [hva, hk1] at hcv
                exact hidx.2 (Or.inl (hcv k1 (by simp)))
              · refine Or.inr ⟨v, hv, hwv, ?_⟩
                simp only [hva, ite_false]
                exact (hst v hv).2 hcv
            · refine Or.inr ⟨a, haN, hwa, ?_⟩
              simp only [ite_true]
              intro k hk
              rw [List.mem_singleton] at hk
              rw [hk]
              rw [hk2] at hck
              exact hidx.2 (Or.inr (hck k2 (by simp)))
    · refine ⟨[], insert a N, fun v => if v = a then kl else cx v, ?_, Finset.subset_insert _ _,
        fun _ => Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
      · intro g hg; cases hg
      · rw [List.append_nil]
        refine ⟨?_, ?_⟩
        · intro v hv
          rcases Finset.mem_insert.1 hv with hva | hv
          · rw [hva]; exact ⟨haL, h1⟩
          · exact hG.1 v hv
        · intro v hv
          by_cases hva : v = a
          · simp only [hva, ite_true]
            exact hkl
          · simp only [hva, ite_false]
            exact hG.2 v ((Finset.mem_insert.1 hv).resolve_left hva)
      · simpa using Finset.card_insert_le a N
      · intro x hx E
        refine ⟨E, ?_⟩
        intro w hw
        rw [List.append_nil]
        constructor
        · rintro (hE | ⟨v, hv, hwv, hcv⟩)
          · exact Or.inl (Or.inl hE)
          · by_cases hva : v = a
            · rw [hva] at hwv
              simp only [hva, ite_true] at hcv
              exact Or.inr ⟨hwv, hcv⟩
            · simp only [hva, ite_false] at hcv
              exact Or.inl (Or.inr ⟨v, (Finset.mem_insert.1 hv).resolve_left hva, hwv, hcv⟩)
        · rintro ((hE | ⟨v, hv, hwv, hcv⟩) | ⟨hwa, hck⟩)
          · exact Or.inl hE
          · have hva : v ≠ a := fun h => haN (h ▸ hv)
            refine Or.inr ⟨v, Finset.mem_insert_of_mem hv, hwv, ?_⟩
            simp only [hva, ite_false]
            exact hcv
          · refine Or.inr ⟨a, Finset.mem_insert_self _ _, hwa, ?_⟩
            simp only [ite_true]
            exact hck

lemma yand (d0 : List ℕ) (P : ℕ) (D : List Gate) (N : Finset ℕ) (cx : ℕ → List ℕ)
    (Cn : List Bool → List Bool → Prop) (aY bX : ℕ) (c : List ℕ) (r : ℕ → ℕ)
    (hG : Good d0 P D N cx)
    (hc : c.length ≤ 1 ∧ ∀ k ∈ c, k < P + D.length)
    (hY : d0.getD aY 0 = 1) (hXb : d0.getD bX 0 = 0)
    (hX : ∀ a, d0.getD a 0 = 0 → ∀ x : List Bool, x.length = P → ∀ w, Cn x w →
      w.getD a false = (run D x).getD (r a) false) :
    ∃ (ex : List Gate) (N' : Finset ℕ) (cx' : ℕ → List ℕ),
      GoodGates ex ∧ N ⊆ N' ∧ aY ∈ N' ∧
      Good d0 P (D ++ ex) N' cx' ∧
      ex.length + N'.card ≤ N.card + 2 ∧
      ∀ x : List Bool, x.length = P → ∀ E : Prop, ∃ E' : Prop, ∀ w, Cn x w →
        ((E' ∨ Phi (D ++ ex) N' cx' x w) ↔
          ((E ∨ Phi D N cx x w) ∨
            ((w.getD aY false = true ∧ w.getD bX false = true) ∧ cval (run D x) c))) := by
  obtain ⟨h, hh⟩ : ∃ h : Gate, h = ⟨GateOp.and, c ++ [r bX]⟩ := ⟨_, rfl⟩
  have hG1 : Good d0 P (D ++ [h]) N cx := Good_ext d0 P D [h] N cx hG
  have hkl : [P + D.length].length ≤ 1 ∧ ∀ k ∈ [P + D.length], k < P + (D ++ [h]).length := by
    refine ⟨by simp, ?_⟩
    intro k hk
    rw [List.mem_singleton] at hk
    rw [hk]
    simp
  obtain ⟨ex, N', cx', h1, h2, h3, h4, h5, h6⟩ :=
    absorb d0 P (D ++ [h]) N cx Cn aY [P + D.length] hG1 hkl (Or.inr hY) (fun h0 => by omega)
  have e : D ++ h :: ex = (D ++ [h]) ++ ex := by simp
  refine ⟨h :: ex, N', cx', ?_, h2, h3 hY, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.1 hg with hgh | hg
    · rw [hgh, hh]
      refine ⟨Or.inl rfl, ?_⟩
      have := hc.1
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · exact h1 g hg
  · rw [e]; exact h4
  · simp only [List.length_cons]
    omega
  · intro x hx E
    obtain ⟨E', hE'⟩ := h6 x hx E
    refine ⟨E', fun w hw => ?_⟩
    have hidx : cval (run (D ++ [h]) x) [P + D.length] ↔
        (cval (run D x) c ∧ w.getD bX false = true) := by
      rw [hX bX hXb x hx w hw]
      have hv : (run (D ++ [h]) x).getD (P + D.length) false = true ↔
          (cval (run D x) c ∧ (run D x).getD (r bX) false = true) := by
        rw [run_snoc_getD _ _ _ _ hx, hh, and_eval]
        constructor
        · intro h7
          exact ⟨fun k hk => h7 k (List.mem_append_left _ hk),
            h7 (r bX) (List.mem_append_right _ (List.mem_singleton_self _))⟩
        · rintro ⟨h7, h8⟩ k hk
          rcases List.mem_append.1 hk with hk | hk
          · exact h7 k hk
          · rw [List.mem_singleton] at hk
            rw [hk]; exact h8
      constructor
      · intro h7
        exact hv.1 (h7 _ (List.mem_singleton_self _))
      · intro h7 k hk
        rw [List.mem_singleton] at hk
        rw [hk]
        exact hv.2 h7
    rw [e, hE' w hw, Phi_stable d0 P D [h] N cx x w hG hx, hidx]
    exact p2 _ _ _ _

lemma ygate (d0 : List ℕ) (P : ℕ) (D : List Gate) (N : Finset ℕ) (cx : ℕ → List ℕ)
    (Cn : List Bool → List Bool → Prop) (g : Gate) (c : List ℕ) (r : ℕ → ℕ)
    (hG : Good d0 P D N cx)
    (hc : c.length ≤ 1 ∧ ∀ k ∈ c, k < P + D.length)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hfan : g.inputs.length ≤ 2)
    (hd : ∀ a ∈ g.inputs, d0.getD a 0 = 0 ∨ d0.getD a 0 = 1)
    (hδ : g.lineDegree d0 = 1)
    (hX : ∀ a, d0.getD a 0 = 0 → ∀ x : List Bool, x.length = P → ∀ w, Cn x w →
      w.getD a false = (run D x).getD (r a) false) :
    ∃ (ex : List Gate) (N' : Finset ℕ) (cx' : ℕ → List ℕ),
      GoodGates ex ∧ N ⊆ N' ∧ (∀ a ∈ g.inputs, d0.getD a 0 = 1 → a ∈ N') ∧
      Good d0 P (D ++ ex) N' cx' ∧
      ex.length + N'.card ≤ N.card + 2 ∧
      ∀ x : List Bool, x.length = P → ∀ E : Prop, ∃ E' : Prop, ∀ w, Cn x w →
        ((E' ∨ Phi (D ++ ex) N' cx' x w) ↔
          ((E ∨ Phi D N cx x w) ∨
            (g.op.eval (g.inputs.map fun i => w.getD i false) = true ∧ cval (run D x) c))) := by
  have hXa : ∀ a, d0.getD a 0 = 0 → ∀ x : List Bool, x.length = P →
      ∃ F : Prop, ∀ w, Cn x w → (w.getD a false = true ↔ F) :=
    fun a h0 x hx => ⟨(run D x).getD (r a) false = true, fun w hw => by rw [hX a h0 x hx w hw]⟩
  obtain ⟨op, ins⟩ := g
  simp only at hop hfan hd hδ ⊢
  rcases hop with hop | hop
  · subst hop
    match ins, hfan, hd, hδ with
    | [], _, _, hδ => simp [Gate.lineDegree] at hδ
    | [a], _, hd, _ =>
      obtain ⟨ex, N', cx', h1, h2, h3, h4, h5, h6⟩ :=
        absorb d0 P D N cx Cn a c hG hc (hd a (by simp)) (hXa a)
      refine ⟨ex, N', cx', h1, h2, ?_, h4, by omega, ?_⟩
      · intro a' ha'
        rw [List.mem_singleton] at ha'
        rw [ha']; exact h3
      · intro x hx E
        obtain ⟨E', hE'⟩ := h6 x hx E
        refine ⟨E', fun w hw => ?_⟩
        rw [hE' w hw, and_eval1]
    | [a, b], _, hd, hδ =>
      have hda := hd a (by simp)
      have hdb := hd b (by simp)
      have hsum : d0.getD a 0 + d0.getD b 0 = 1 := by simpa [Gate.lineDegree] using hδ
      rcases hda with hda | hda
      · have hdb1 : d0.getD b 0 = 1 := by omega
        obtain ⟨ex, N', cx', h1, h2, h3, h4, h5, h6⟩ :=
          yand d0 P D N cx Cn b a c r hG hc hdb1 hda hX
        refine ⟨ex, N', cx', h1, h2, ?_, h4, h5, ?_⟩
        · intro a' ha' hd'
          rcases List.mem_pair.1 ha' with h | h
          · rw [h] at hd'; omega
          · rw [h]; exact h3
        · intro x hx E
          obtain ⟨E', hE'⟩ := h6 x hx E
          refine ⟨E', fun w hw => ?_⟩
          rw [hE' w hw, and_eval2]
          exact p3 _ _ _ _
      · have hdb0 : d0.getD b 0 = 0 := by omega
        obtain ⟨ex, N', cx', h1, h2, h3, h4, h5, h6⟩ :=
          yand d0 P D N cx Cn a b c r hG hc hda hdb0 hX
        refine ⟨ex, N', cx', h1, h2, ?_, h4, h5, ?_⟩
        · intro a' ha' hd'
          rcases List.mem_pair.1 ha' with h | h
          · rw [h]; exact h3
          · rw [h] at hd'; omega
        · intro x hx E
          obtain ⟨E', hE'⟩ := h6 x hx E
          refine ⟨E', fun w hw => ?_⟩
          rw [hE' w hw, and_eval2]
    | _ :: _ :: _ :: _, hfan, _, _ => simp at hfan
  · subst hop
    match ins, hfan, hd with
    | [], _, _ =>
      refine ⟨[], N, cx, ?_, Finset.Subset.refl _, ?_, ?_, by simp, ?_⟩
      · intro g hg; cases hg
      · intro a ha; cases ha
      · rw [List.append_nil]; exact hG
      · intro x hx E
        refine ⟨E, fun w hw => ?_⟩
        rw [List.append_nil, or_eval0]
        exact p5 _ _
    | [a], _, hd =>
      obtain ⟨ex, N', cx', h1, h2, h3, h4, h5, h6⟩ :=
        absorb d0 P D N cx Cn a c hG hc (hd a (by simp)) (hXa a)
      refine ⟨ex, N', cx', h1, h2, ?_, h4, by omega, ?_⟩
      · intro a' ha'
        rw [List.mem_singleton] at ha'
        rw [ha']; exact h3
      · intro x hx E
        obtain ⟨E', hE'⟩ := h6 x hx E
        refine ⟨E', fun w hw => ?_⟩
        rw [hE' w hw, or_eval1]
    | [a, b], _, hd =>
      obtain ⟨ex1, N1, cx1, a1, a2, a3, a4, a5, a6⟩ :=
        absorb d0 P D N cx Cn a c hG hc (hd a (by simp)) (hXa a)
      have hc' : c.length ≤ 1 ∧ ∀ k ∈ c, k < P + (D ++ ex1).length := by
        refine ⟨hc.1, fun k hk => ?_⟩
        have := hc.2 k hk
        simp only [List.length_append]
        omega
      obtain ⟨ex2, N2, cx2, b1, b2, b3, b4, b5, b6⟩ :=
        absorb d0 P (D ++ ex1) N1 cx1 Cn b c a4 hc' (hd b (by simp)) (hXa b)
      refine ⟨ex1 ++ ex2, N2, cx2, ?_, a2.trans b2, ?_, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with h | h
        · exact a1 g h
        · exact b1 g h
      · intro a' ha' hd'
        rcases List.mem_pair.1 ha' with h | h
        · rw [h] at hd' ⊢; exact b2 (a3 hd')
        · rw [h] at hd' ⊢; exact b3 hd'
      · rw [← List.append_assoc]; exact b4
      · simp only [List.length_append]
        omega
      · intro x hx E
        obtain ⟨E1, hE1⟩ := a6 x hx E
        obtain ⟨E2, hE2⟩ := b6 x hx E1
        refine ⟨E2, fun w hw => ?_⟩
        have e : D ++ (ex1 ++ ex2) = (D ++ ex1) ++ ex2 := (List.append_assoc D ex1 ex2).symm
        rw [e, hE2 w hw, hE1 w hw, cval_stable D ex1 x P c hx hc.2, or_eval2]
        exact p4 _ _ _ _
    | _ :: _ :: _ :: _, hfan, _ => simp at hfan

abbrev Cons (d0 : List ℕ) (Dpre : List Gate) (ρ : ℕ → ℕ) (x w : List Bool) : Prop :=
  w.length = d0.length ∧
    ∀ v, v < d0.length → d0.getD v 0 = 0 → w.getD v false = (run Dpre x).getD (ρ v) false

lemma xgate_val (g : Gate) (d0 : List ℕ) (P : ℕ) (Dpre : List Gate) (ρ : ℕ → ℕ)
    (x w : List Bool) (hx : x.length = P) (hw : Cons d0 Dpre ρ x w)
    (hin0 : ∀ a ∈ g.inputs, d0.getD a 0 = 0) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      (run (Dpre ++ [(⟨g.op, g.inputs.map fun a =>
        if a < d0.length then ρ a else P + Dpre.length⟩ : Gate)]) x).getD (P + Dpre.length) false := by
  rw [run_snoc_getD _ _ _ _ hx]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hW : (run Dpre x).length = P + Dpre.length := by rw [run_length, hx]
  by_cases hlt : a < d0.length
  · simp only [Function.comp, hlt, ite_true]
    exact hw.2 a hlt (hin0 a ha)
  · simp only [Function.comp, hlt, ite_false]
    rw [List.getD_eq_default _ _ (by rw [hw.1]; omega), List.getD_eq_default _ _ (by rw [hW])]

lemma main (gs : List Gate) : ∀ (d0 : List ℕ) (out P : ℕ) (Dpre : List Gate) (ρ : ℕ → ℕ),
    GoodGates gs → (∀ e ∈ degs gs d0, e ≤ 1) →
    (∀ v, v < d0.length → d0.getD v 0 = 0 → ρ v < P + Dpre.length) →
    ∃ (Dext : List Gate) (N : Finset ℕ) (cx : ℕ → List ℕ),
      GoodGates Dext ∧ Good d0 P (Dpre ++ Dext) N cx ∧
      (∀ v, v < d0.length → d0.getD v 0 = 1 →
        Relation.ReflTransGen (Rg d0.length gs) v out → v ∈ N) ∧
      Dext.length + N.card ≤ gs.length + 1 ∧
      ∀ x : List Bool, x.length = P → ∃ E : Prop, ∀ w, Cons d0 Dpre ρ x w →
        ((run gs w).getD out false = true ↔ (E ∨ Phi (Dpre ++ Dext) N cx x w)) := by
  induction gs with
  | nil =>
    intro d0 out P Dpre ρ _ hdeg hρ
    have hd0 : ∀ e ∈ d0, e ≤ 1 := hdeg
    have hle := getD_le_one d0 hd0 out
    have hreach : ∀ v, Relation.ReflTransGen (Rg d0.length []) v out → v = out := by
      intro v h
      rcases Relation.ReflTransGen.cases_head h with h | ⟨b, hvb, _⟩
      · exact h
      · obtain ⟨_, i, _⟩ := hvb
        exact absurd i.isLt (by simp)
    by_cases h1 : d0.getD out 0 = 1
    · refine ⟨[], {out}, fun _ => [], ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg; cases hg
      · refine ⟨?_, ?_⟩
        · intro v hv
          rw [Finset.mem_singleton] at hv
          rw [hv]
          exact ⟨lt_of_getD_eq_one _ _ h1, h1⟩
        · intro v hv
          exact ⟨by simp, by intro k hk; cases hk⟩
      · intro v _ _ h
        rw [hreach v h]
        exact Finset.mem_singleton_self _
      · simp
      · intro x hx
        refine ⟨False, fun w hw => ?_⟩
        change w.getD out false = true ↔ _
        constructor
        · intro h
          exact Or.inr ⟨out, Finset.mem_singleton_self _, h, by intro k hk; cases hk⟩
        · rintro (h | ⟨v, hv, hwv, _⟩)
          · exact h.elim
          · rw [Finset.mem_singleton] at hv
            rw [← hv]; exact hwv
    · have h0 : d0.getD out 0 = 0 := by omega
      refine ⟨[], ∅, fun _ => [], ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg; cases hg
      · exact ⟨by simp, by simp⟩
      · intro v hv hv1 h
        rw [hreach v h] at hv1
        omega
      · simp
      · intro x hx
        refine ⟨out < d0.length ∧ (run Dpre x).getD (ρ out) false = true, fun w hw => ?_⟩
        change w.getD out false = true ↔ _
        by_cases ho : out < d0.length
        · rw [hw.2 out ho h0]
          constructor
          · intro h; exact Or.inl ⟨ho, h⟩
          · rintro (h | ⟨v, hv, _⟩)
            · exact h.2
            · simp at hv
        · rw [List.getD_eq_default _ _ (by rw [hw.1]; omega)]
          constructor
          · intro h; cases h
          · rintro (h | ⟨v, hv, _⟩)
            · exact absurd h.1 ho
            · simp at hv
  | cons g rest ih =>
    intro d0 out P Dpre ρ hgs hdeg hρ
    have hg := hgs g (by simp)
    have hrest : GoodGates rest := fun q hq => hgs q (List.mem_cons_of_mem _ hq)
    have hdeg' : ∀ e ∈ degs rest (d0 ++ [g.lineDegree d0]), e ≤ 1 := hdeg
    have hd0 : ∀ e ∈ d0, e ≤ 1 := fun e he => hdeg e (degs_mem _ _ _ he)
    have hδ : g.lineDegree d0 ≤ 1 := hdeg' _ (degs_mem _ _ _ (by simp))
    have hlen' : (d0 ++ [g.lineDegree d0]).length = d0.length + 1 := by simp
    have hgetlt : ∀ v, v < d0.length →
        (d0 ++ [g.lineDegree d0]).getD v 0 = d0.getD v 0 :=
      fun v hv => getD_snoc_lt _ _ _ _ hv
    have hgeteq : (d0 ++ [g.lineDegree d0]).getD d0.length 0 = g.lineDegree d0 :=
      getD_snoc_eq _ _ _
    have hstepget : ∀ (w : List Bool), w.length = d0.length → ∀ v, v < d0.length →
        (step w g).getD v false = w.getD v false :=
      fun w hw v hv => getD_snoc_lt _ _ _ _ (by omega)
    have hstepeq : ∀ (w : List Bool), w.length = d0.length →
        (step w g).getD d0.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      intro w hw
      unfold step
      rw [← hw, getD_snoc_eq]
    have hsteplen : ∀ (w : List Bool), w.length = d0.length →
        (step w g).length = (d0 ++ [g.lineDegree d0]).length := by
      intro w hw
      simp [step, hw]
    rcases Nat.eq_zero_or_pos (g.lineDegree d0) with hδ0 | hδpos
    · have hin0 : ∀ a ∈ g.inputs, d0.getD a 0 = 0 := fun a ha => by
        have := input_deg_le g d0 a ha
        omega
      obtain ⟨g', hg'⟩ : ∃ g' : Gate, g' = ⟨g.op, g.inputs.map fun a =>
          if a < d0.length then ρ a else P + Dpre.length⟩ := ⟨_, rfl⟩
      obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℕ → ℕ,
          ρ' = fun v => if v = d0.length then P + Dpre.length else ρ v := ⟨_, rfl⟩
      obtain ⟨Dext, N, cx, i1, i2, i3, i4, i5⟩ :=
        ih (d0 ++ [g.lineDegree d0]) out P (Dpre ++ [g']) ρ' hrest hdeg' (by
          intro v hv h0
          rw [hlen'] at hv
          rw [hρ']
          by_cases hvn : v = d0.length
          · simp [hvn]
          · have hv' : v < d0.length := by omega
            rw [hgetlt v hv'] at h0
            have := hρ v hv' h0
            simp only [hvn, ite_false, List.length_append, List.length_cons, List.length_nil]
            omega)
      have hNlt : ∀ v ∈ N, v < d0.length ∧ d0.getD v 0 = 1 := by
        intro v hv
        obtain ⟨hv1, hv2⟩ := i2.1 v hv
        rw [hlen'] at hv1
        have hvn : v ≠ d0.length := by
          intro h
          rw [h, hgeteq, hδ0] at hv2
          omega
        have hv' : v < d0.length := by omega
        exact ⟨hv', by rwa [hgetlt v hv'] at hv2⟩
      have e : Dpre ++ g' :: Dext = (Dpre ++ [g']) ++ Dext := by simp
      refine ⟨g' :: Dext, N, cx, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with hqg | hq
        · rw [hqg, hg']
          exact ⟨hg.1, by simpa using hg.2⟩
        · exact i1 q hq
      · rw [e]
        exact ⟨hNlt, i2.2⟩
      · intro v hv hv1 hr
        apply i3 v (by rw [hlen']; omega) (by rw [hgetlt v hv]; exact hv1)
        rw [hlen']
        rcases reach_cons _ _ _ _ _ hr with ⟨hin, _, _⟩ | h
        · have := hin0 v hin
          omega
        · exact h
      · simp only [List.length_cons] at i4 ⊢
        omega
      · intro x hx
        obtain ⟨E, hE⟩ := i5 x hx
        refine ⟨E, fun w hw => ?_⟩
        have hW : (run Dpre x).length = P + Dpre.length := by rw [run_length, hx]
        have hcons : Cons (d0 ++ [g.lineDegree d0]) (Dpre ++ [g']) ρ' x (step w g) := by
          refine ⟨hsteplen w hw.1, ?_⟩
          intro v hv h0
          rw [hlen'] at hv
          by_cases hvn : v = d0.length
          · rw [hvn, hstepeq w hw.1, hρ', hg']
            simp only [ite_true]
            exact xgate_val g d0 P Dpre ρ x w hx hw hin0
          · have hv' : v < d0.length := by omega
            rw [hgetlt v hv'] at h0
            rw [hstepget w hw.1 v hv', hw.2 v hv' h0, hρ']
            simp only [hvn, ite_false]
            rw [run_append, run_getD_of_lt [g'] (run Dpre x) _ (by rw [hW]; exact hρ v hv' h0)]
        change (run rest (step w g)).getD out false = true ↔ _
        rw [hE _ hcons, e]
        apply or_congr Iff.rfl
        constructor
        · rintro ⟨v, hv, hwv, hc⟩
          exact ⟨v, hv, by rwa [hstepget w hw.1 v (hNlt v hv).1] at hwv, hc⟩
        · rintro ⟨v, hv, hwv, hc⟩
          exact ⟨v, hv, by rwa [hstepget w hw.1 v (hNlt v hv).1], hc⟩
    · have hδ1 : g.lineDegree d0 = 1 := by omega
      obtain ⟨Dext, N, cx, i1, i2, i3, i4, i5⟩ :=
        ih (d0 ++ [g.lineDegree d0]) out P Dpre ρ hrest hdeg' (by
          intro v hv h0
          rw [hlen'] at hv
          have hvn : v ≠ d0.length := by
            intro h
            rw [h, hgeteq] at h0
            omega
          have hv' : v < d0.length := by omega
          rw [hgetlt v hv'] at h0
          exact hρ v hv' h0)
      have hconsT : ∀ x w, Cons d0 Dpre ρ x w →
          Cons (d0 ++ [g.lineDegree d0]) Dpre ρ x (step w g) := by
        intro x w hw
        refine ⟨hsteplen w hw.1, ?_⟩
        intro v hv h0
        rw [hlen'] at hv
        have hvn : v ≠ d0.length := by
          intro h
          rw [h, hgeteq] at h0
          omega
        have hv' : v < d0.length := by omega
        rw [hgetlt v hv'] at h0
        rw [hstepget w hw.1 v hv']
        exact hw.2 v hv' h0
      by_cases hn : d0.length ∈ N
      · obtain ⟨N0, hN0⟩ : ∃ N0 : Finset ℕ, N0 = N.erase d0.length := ⟨_, rfl⟩
        have hcard : N0.card + 1 = N.card := by
          rw [hN0]
          exact Finset.card_erase_add_one hn
        have hN0lt : ∀ v ∈ N0, v < d0.length ∧ d0.getD v 0 = 1 := by
          intro v hv
          rw [hN0] at hv
          obtain ⟨hvn, hvN⟩ := Finset.mem_erase.1 hv
          obtain ⟨hv1, hv2⟩ := i2.1 v hvN
          rw [hlen'] at hv1
          have hv' : v < d0.length := by omega
          exact ⟨hv', by rwa [hgetlt v hv'] at hv2⟩
        have hG0 : Good d0 P (Dpre ++ Dext) N0 cx :=
          ⟨hN0lt, fun v hv => i2.2 v (by rw [hN0] at hv; exact Finset.mem_of_mem_erase hv)⟩
        have hc := i2.2 d0.length hn
        obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ,
            r = fun a => if a < d0.length then ρ a else P + (Dpre ++ Dext).length := ⟨_, rfl⟩
        have hX : ∀ a, d0.getD a 0 = 0 → ∀ x : List Bool, x.length = P →
            ∀ w, Cons d0 Dpre ρ x w →
              w.getD a false = (run (Dpre ++ Dext) x).getD (r a) false := by
          intro a h0 x hx w hw
          have hW : (run (Dpre ++ Dext) x).length = P + (Dpre ++ Dext).length := by
            rw [run_length, hx]
          have hW0 : (run Dpre x).length = P + Dpre.length := by rw [run_length, hx]
          rw [hr]
          by_cases hlt : a < d0.length
          · simp only [hlt, ite_true]
            rw [hw.2 a hlt h0, run_append,
              run_getD_of_lt Dext (run Dpre x) _ (by rw [hW0]; exact hρ a hlt h0)]
          · simp only [hlt, ite_false]
            rw [List.getD_eq_default _ _ (by rw [hw.1]; omega),
              List.getD_eq_default _ _ (by rw [hW])]
        obtain ⟨ex, N', cx', y1, y2, y3, y4, y5, y6⟩ :=
          ygate d0 P (Dpre ++ Dext) N0 cx (Cons d0 Dpre ρ) g (cx d0.length) r hG0 hc hg.1 hg.2
            (fun a _ => by have := getD_le_one d0 hd0 a; omega) hδ1 hX
        have e : Dpre ++ (Dext ++ ex) = (Dpre ++ Dext) ++ ex := (List.append_assoc _ _ _).symm
        refine ⟨Dext ++ ex, N', cx', ?_, ?_, ?_, ?_, ?_⟩
        · intro q hq
          rcases List.mem_append.1 hq with h | h
          · exact i1 q h
          · exact y1 q h
        · rw [e]; exact y4
        · intro v hv hv1 hr'
          rcases reach_cons _ _ _ _ _ hr' with ⟨hin, _, _⟩ | h
          · exact y3 v hin hv1
          · apply y2
            rw [hN0]
            exact Finset.mem_erase.2 ⟨by omega,
              i3 v (by rw [hlen']; omega) (by rw [hgetlt v hv]; exact hv1) (by rw [hlen']; exact h)⟩
        · simp only [List.length_append, List.length_cons] at i4 ⊢
          omega
        · intro x hx
          obtain ⟨E, hE⟩ := i5 x hx
          obtain ⟨E', hE'⟩ := y6 x hx E
          refine ⟨E', fun w hw => ?_⟩
          change (run rest (step w g)).getD out false = true ↔ _
          rw [hE _ (hconsT x w hw), e, hE' w hw]
          constructor
          · rintro (hE0 | ⟨v, hv, hwv, hcv⟩)
            · exact Or.inl (Or.inl hE0)
            · by_cases hvn : v = d0.length
              · right
                rw [hvn] at hwv hcv
                rw [hstepeq w hw.1] at hwv
                exact ⟨hwv, hcv⟩
              · left; right
                have hv0 : v ∈ N0 := by
                  rw [hN0]
                  exact Finset.mem_erase.2 ⟨hvn, hv⟩
                exact ⟨v, hv0, by rwa [hstepget w hw.1 v (hN0lt v hv0).1] at hwv, hcv⟩
          · rintro ((hE0 | ⟨v, hv, hwv, hcv⟩) | ⟨hgv, hcv⟩)
            · exact Or.inl hE0
            · right
              have hvN : v ∈ N := by
                rw [hN0] at hv
                exact Finset.mem_of_mem_erase hv
              exact ⟨v, hvN, by rwa [hstepget w hw.1 v (hN0lt v hv).1], hcv⟩
            · right
              refine ⟨d0.length, hn, ?_, hcv⟩
              rw [hstepeq w hw.1]
              exact hgv
      · have hNlt : ∀ v ∈ N, v < d0.length ∧ d0.getD v 0 = 1 := by
          intro v hv
          obtain ⟨hv1, hv2⟩ := i2.1 v hv
          rw [hlen'] at hv1
          have hvn : v ≠ d0.length := fun h => hn (h ▸ hv)
          have hv' : v < d0.length := by omega
          exact ⟨hv', by rwa [hgetlt v hv'] at hv2⟩
        refine ⟨Dext, N, cx, i1, ⟨hNlt, i2.2⟩, ?_, ?_, ?_⟩
        · intro v hv hv1 hr
          rcases reach_cons _ _ _ _ _ hr with ⟨_, _, h⟩ | h
          · exfalso
            apply hn
            exact i3 d0.length (by rw [hlen']; omega) (by rw [hgeteq]; exact hδ1)
              (by rw [hlen']; exact h)
          · exact i3 v (by rw [hlen']; omega) (by rw [hgetlt v hv]; exact hv1)
              (by rw [hlen']; exact h)
        · simp only [List.length_cons]
          omega
        · intro x hx
          obtain ⟨E, hE⟩ := i5 x hx
          refine ⟨E, fun w hw => ?_⟩
          change (run rest (step w g)).getD out false = true ↔ _
          rw [hE _ (hconsT x w hw)]
          apply or_congr Iff.rfl
          constructor
          · rintro ⟨v, hv, hwv, hc⟩
            exact ⟨v, hv, by rwa [hstepget w hw.1 v (hNlt v hv).1] at hwv, hc⟩
          · rintro ⟨v, hv, hwv, hc⟩
            exact ⟨v, hv, by rwa [hstepget w hw.1 v (hNlt v hv).1], hc⟩

lemma d0_getD (P L v : ℕ) :
    ((List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0).getD v 0 =
      if P ≤ v ∧ v < P + L then 1 else 0 := by
  by_cases hv : v < P + L
  · rw [List.getD_eq_getElem _ _ (by simpa using hv)]
    simp [Finset.mem_Ico, hv]
  · rw [List.getD_eq_default _ _ (by simpa using hv)]
    have hn : ¬ (P ≤ v ∧ v < P + L) := fun h => hv h.2
    rw [if_neg hn]

lemma eval_eq_run (C : Circuit) (w : List Bool) :
    C.eval w = (run C.gates w).getD C.output false := rfl

lemma wires_eq_run (C : Circuit) (w : List Bool) : C.wires w = run C.gates w := rfl

lemma top (P1 L1 : ℕ) (C1 : Circuit) (N1 : Finset (Fin L1))
    (hmono : IsMonotoneCircuit C1) (hfan : ∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2)
    (hdeg : HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1)
    (hreach : ∀ j1 : Fin C1.gates.length,
      Relation.ReflTransGen (Rg (P1 + L1) C1.gates) (P1 + L1 + j1.val) C1.output)
    (hN : ∀ w1 : Fin L1, w1 ∈ N1 →
      Relation.ReflTransGen (Rg (P1 + L1) C1.gates) (P1 + w1.val) C1.output) :
    ∃ (D1 : Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ),
      IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧
      D1.size + N1.card ≤ C1.size + 1 ∧
      ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool),
        (C1.eval (List.ofFn x1 ++ List.ofFn y1) = true ↔
          (C1.eval (List.ofFn x1 ++ List.ofFn (fun _ : Fin L1 => false)) = true ∨
            ∃ u1 : Fin L1, y1 u1 = true ∧
              (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true))) := by
  obtain ⟨d0, hd0def⟩ : ∃ d0 : List ℕ, d0 = (List.range (P1 + L1)).map fun i =>
      if i ∈ Finset.Ico P1 (P1 + L1) then 1 else 0 := ⟨_, rfl⟩
  have hd0len : d0.length = P1 + L1 := by rw [hd0def]; simp
  have hd0get : ∀ v, d0.getD v 0 = if P1 ≤ v ∧ v < P1 + L1 then 1 else 0 := by
    rw [hd0def]; exact d0_getD P1 L1
  have hreach' : ∀ j : Fin C1.gates.length,
      Relation.ReflTransGen (Rg d0.length C1.gates) (d0.length + j.val) C1.output := by
    rw [hd0len]; exact hreach
  have hout : (degs C1.gates d0).getD C1.output 0 ≤ 1 := by rw [hd0def]; exact hdeg
  have hdegs : ∀ e ∈ degs C1.gates d0, e ≤ 1 := by
    intro e he
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
    have hi' := hi
    rw [degs_length] at hi'
    rw [← hie, ← List.getD_eq_getElem _ 0 hi]
    by_cases hlt : i < d0.length
    · rw [degs_getD_of_lt _ _ _ hlt, hd0get]
      split <;> omega
    · obtain ⟨j, hj⟩ : ∃ j, i = d0.length + j := ⟨i - d0.length, by omega⟩
      have hjlt : j < C1.gates.length := by omega
      have h2 := deg_mono_rtg _ _ _ _ (hreach' ⟨j, hjlt⟩)
      rw [hj]
      exact le_trans h2 hout
  have hgood : GoodGates C1.gates := fun g hg => ⟨hmono g hg, hfan g hg⟩
  obtain ⟨Dext, N, cx, m1, m2, m3, m4, m5⟩ :=
    main C1.gates d0 C1.output P1 [] id hgood hdegs (by
      intro v hv h0
      rw [hd0get] at h0
      rw [hd0len] at hv
      by_cases hc : P1 ≤ v ∧ v < P1 + L1
      · rw [if_pos hc] at h0
        omega
      · simp only [id, List.length_nil]
        omega)
  simp only [List.nil_append] at m2 m5
  have hNrange : ∀ v ∈ N, P1 ≤ v ∧ v < P1 + L1 := by
    intro v hv
    have h := (m2.1 v hv).2
    rw [hd0get] at h
    by_contra hc
    rw [if_neg hc] at h
    omega
  refine ⟨⟨Dext, 0⟩,
    Finset.univ.filter (fun u : Fin L1 => P1 + u.val ∈ N ∧ cx (P1 + u.val) = []),
    fun u => if P1 + u.val ∈ N then (cx (P1 + u.val)).headD (P1 + Dext.length)
      else P1 + Dext.length, ?_, ?_, ?_, ?_⟩
  · exact fun g hg => (m1 g hg).1
  · exact fun g hg => (m1 g hg).2
  · change Dext.length + N1.card ≤ C1.gates.length + 1
    have hcard : N1.card ≤ N.card := by
      apply Finset.card_le_card_of_injOn (fun u : Fin L1 => P1 + u.val)
      · intro u hu
        have hul := u.isLt
        have hu' := hN u (by simpa using hu)
        apply m3 (P1 + u.val) (by rw [hd0len]; omega)
          (by rw [hd0get, if_pos ⟨by omega, by omega⟩])
        rw [hd0len]
        exact hu'
      · intro u _ u' _ h
        apply Fin.ext
        simp only at h
        omega
    omega
  · intro x y
    obtain ⟨E, hE⟩ := m5 (List.ofFn x) (by simp)
    have hcons : ∀ y' : Fin L1 → Bool,
        Cons d0 [] id (List.ofFn x) (List.ofFn x ++ List.ofFn y') := by
      intro y'
      refine ⟨by simp [hd0len], ?_⟩
      intro v hv h0
      rw [hd0get] at h0
      rw [hd0len] at hv
      have hvP : v < P1 := by
        by_contra hc
        rw [if_pos ⟨by omega, hv⟩] at h0
        omega
      change _ = (List.ofFn x).getD v false
      exact List.getD_append _ _ _ _ (by simpa using hvP)
    have hline : ∀ (y' : Fin L1 → Bool) (u : ℕ) (hu : u < L1),
        (List.ofFn x ++ List.ofFn y').getD (P1 + u) false = y' ⟨u, hu⟩ := by
      intro y' u hu
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp [List.getD, hu]
    have h1 := hE _ (hcons y)
    have h0 := hE _ (hcons fun _ => false)
    have hE0 : (run C1.gates (List.ofFn x ++ List.ofFn fun _ : Fin L1 => false)).getD
        C1.output false = true ↔ E := by
      rw [h0]
      constructor
      · rintro (h | ⟨v, hv, hwv, _⟩)
        · exact h
        · obtain ⟨hv1, hv2⟩ := hNrange v hv
          have h3 := hline (fun _ => false) (v - P1) (by omega)
          rw [show P1 + (v - P1) = v by omega] at h3
          rw [h3] at hwv
          cases hwv
      · exact Or.inl
    rw [eval_eq_run, eval_eq_run, wires_eq_run, h1, hE0]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨v, hv, hwv, hcv⟩
      obtain ⟨hv1, hv2⟩ := hNrange v hv
      have hvu : P1 + (v - P1) = v := by omega
      have h3 := hline y (v - P1) (by omega)
      rw [hvu] at h3
      refine ⟨⟨v - P1, by omega⟩, by rw [← h3]; exact hwv, ?_⟩
      have hlen1 := (m2.2 v hv).1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hvu, hv, ite_true]
      rcases hcx : cx v with _ | ⟨k, _ | ⟨k', t⟩⟩
      · left; trivial
      · right
        rw [hcx] at hcv
        simpa using hcv k (by simp)
      · rw [hcx] at hlen1
        simp at hlen1
    · rintro ⟨u, hyu, hu⟩
      have hul := u.isLt
      by_cases huN : P1 + u.val ∈ N
      · refine ⟨P1 + u.val, huN, by rw [hline y u.val hul]; exact hyu, ?_⟩
        rcases hu with hu | hu
        · have h4 := (Finset.mem_filter.1 hu).2.2
          rw [h4]
          intro k hk; cases hk
        · simp only [huN, ite_true] at hu
          have hlen1 := (m2.2 _ huN).1
          rcases hcx : cx (P1 + u.val) with _ | ⟨k, _ | ⟨k', t⟩⟩
          · intro k hk; cases hk
          · rw [hcx] at hu
            intro k2 hk2
            rw [List.mem_singleton] at hk2
            rw [hk2]
            simpa using hu
          · rw [hcx] at hlen1
            simp at hlen1
      · exfalso
        rcases hu with hu | hu
        · exact huN (Finset.mem_filter.1 hu).2.1
        · simp only [huN, ite_false] at hu
          rw [List.getD_eq_default _ _ (by rw [run_length]; simp)] at hu
          cases hu

end PEqualNP.Outside.L_meta_738_aux

open PEqualNP.Outside.L_meta_738_aux in
theorem PEqualNP.Outside.L_meta_738 :
    ∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true))) := by
  intro P1 L1 C1 N1 hmono hfan hdeg hreach hN
  obtain ⟨D1, T1, o1, k1, k2, k3, k4⟩ :=
    top P1 L1 C1 N1 hmono hfan hdeg hreach (fun w1 hw1 => (hN w1).1 hw1)
  refine ⟨D1, T1, o1, k1, k2, k3, fun x1 y1 => ?_⟩
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact k4 x1 y1
