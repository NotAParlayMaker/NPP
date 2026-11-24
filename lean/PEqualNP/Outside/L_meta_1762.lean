import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1762

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


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

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
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


theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

open PEqualNP.EdgeOwnership in
theorem inCone_lt (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i h
    obtain ⟨w, hw, hn, hlt, h | h⟩ := (inCone_iff n C i k hk).1 h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

open PEqualNP.EdgeOwnership in
theorem pi_symm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput, or_comm]

open PEqualNP.EdgeOwnership in
theorem pi_val {n : ℕ} (u v : Fin n) (w : Fin n) : pairInput u v w = true ↔ (w = u ∨ w = v) := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
theorem pi_le {n : ℕ} (x u v : Fin n) (h : x = u ∨ x = v) :
    ∀ w, pairInput x x w = true → pairInput u v w = true := by
  intro w hw
  rw [pi_val] at hw ⊢
  rw [or_self] at hw
  rw [hw]
  exact h

open PEqualNP.EdgeOwnership in
def NA (n : ℕ) (C : Circuit) (X : Fin n → Bool) (w : ℕ) : Prop :=
  ∀ i, (n + i = w ∨ ∃ j, j < C.gates.length ∧ w = n + j ∧ InCone n C i j) →
    (gateAt C i).op = GateOp.and → val C.gates (n + i) X = false

open PEqualNP.EdgeOwnership in
theorem na_down (n : ℕ) (C : Circuit) (X : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (h : NA n C X (n + k)) (p : ℕ) (hp : p ∈ C.gates[k].inputs) (hlt : p < n + k) :
    NA n C X p := by
  have hp2 : p ∈ (gateAt C k).inputs := by rw [gateAt_eq C k hk]; exact hp
  intro i hi hand
  rcases hi with hi | ⟨j, hj, hpj, hc⟩
  · exact h i (Or.inr ⟨k, hk, rfl, (inCone_iff n C i k hk).2
      ⟨p, hp2, by omega, hlt, Or.inl (by omega)⟩⟩) hand
  · exact h i (Or.inr ⟨k, hk, rfl, (inCone_iff n C i k hk).2
      ⟨p, hp2, by omega, hlt, Or.inr (by rw [show p - n = j by omega]; exact hc)⟩⟩) hand

open PEqualNP.EdgeOwnership in
theorem descent (n : ℕ) (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (u v : Fin n) : ∀ w, val C.gates w (pairInput u v) = true → NA n C (pairInput u v) w →
      val C.gates w (pairInput u u) = true ∨ val C.gates w (pairInput v v) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h hna
    by_cases hwn : w < n
    · rw [val_input C.gates _ w hwn, pi_val] at h
      rw [val_input C.gates _ w hwn, val_input C.gates _ w hwn, pi_val, pi_val]
      rcases h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · by_cases hbig : n + C.gates.length ≤ w
      · rw [val_big C.gates _ w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < C.gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h hna ⊢
        rcases (legal C.gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · have := hna (w - n) (Or.inl rfl) (by rw [gateAt_eq C _ hi]; exact ha)
          rw [this] at h
          exact Bool.noConfusion h
        · obtain ⟨p, hp, hplt, hv⟩ := (val_or C.gates _ (w - n) hi ho).1 h
          rcases ih p (by omega) hv (na_down n C _ (w - n) hi hna p hp hplt) with h1 | h1
          · exact Or.inl ((val_or C.gates _ (w - n) hi ho).2 ⟨p, hp, hplt, h1⟩)
          · exact Or.inr ((val_or C.gates _ (w - n) hi ho).2 ⟨p, hp, hplt, h1⟩)

open PEqualNP.EdgeOwnership in
def TS (gs : List Gate) {n : ℕ} (w : ℕ) (v : Fin n) : Prop :=
  ∀ x : Fin n, val gs w (pairInput x x) = true ↔ x = v

def inp (C : Circuit) (h k : ℕ) : ℕ := (gateAt C h).inputs.getD k 0

open PEqualNP.EdgeOwnership in
def Rel {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (e : Sym2 (Fin n)) (t : ℕ × ℕ) : Prop :=
  ∃ c v : Fin n, e = s(c, v) ∧ TS C.gates (inp C t.1 t.2) v ∧
    (((gateAt C t.1).op = GateOp.or ∧
        (∃ x y : Fin n, x ≠ y ∧ val C.gates (n + t.1) (pairInput x x) = true ∧
          val C.gates (n + t.1) (pairInput y y) = true) ∧
        ∀ x : Fin n, val C.gates (n + t.1) (pairInput x x) = true → G.Adj c x) ∨
      ((gateAt C t.1).op = GateOp.and ∧ TS C.gates (inp C t.1 (1 - t.2)) c))

theorem idx_of (l : List ℕ) (hl : l.length ≤ 2) (p : ℕ) (hp : p ∈ l) :
    ∃ i, i < 2 ∧ l.getD i 0 = p := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  exact ⟨i, by omega, List.getD_eq_getElem _ _ hi⟩

open PEqualNP.EdgeOwnership in
theorem climb (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (c v : Fin n) : ∀ w, val C.gates w (pairInput c v) = true →
      (∀ x : Fin n, val C.gates w (pairInput x x) = true → G.Adj c x) →
      NA n C (pairInput c v) w →
      TS C.gates w v ∨ ∃ t : ℕ × ℕ, t.1 < C.gates.length ∧ t.2 < 2 ∧ Rel G C s(c, v) t := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h hadj hna
    by_cases hwn : w < n
    · left
      rw [val_input C.gates _ w hwn, pi_val] at h
      rcases h with h | h
      · exfalso
        have : val C.gates w (pairInput c c) = true := by
          rw [val_input C.gates _ w hwn, pi_val]; exact Or.inl h
        exact (hadj c this).ne rfl
      · intro x
        rw [val_input C.gates _ w hwn, pi_val, or_self, h]
        exact eq_comm
    · by_cases hbig : n + C.gates.length ≤ w
      · rw [val_big C.gates _ w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < C.gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h hna hadj ⊢
        rcases (legal C.gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · have := hna (w - n) (Or.inl rfl) (by rw [gateAt_eq C _ hi]; exact ha)
          rw [this] at h
          exact Bool.noConfusion h
        · obtain ⟨p, hp, hplt, hv⟩ := (val_or C.gates _ (w - n) hi ho).1 h
          have hsub : ∀ x : Fin n, val C.gates p (pairInput x x) = true →
              val C.gates (n + (w - n)) (pairInput x x) = true := fun x hx =>
            (val_or C.gates _ (w - n) hi ho).2 ⟨p, hp, hplt, hx⟩
          rcases ih p (by omega) hv (fun x hx => hadj x (hsub x hx))
            (na_down n C _ (w - n) hi hna p hp hplt) with h1 | h1
          · by_cases hall : ∀ x : Fin n, val C.gates (n + (w - n)) (pairInput x x) = true → x = v
            · left
              intro x
              refine ⟨hall x, fun hx => ?_⟩
              rw [hx]
              exact hsub v ((h1 v).2 rfl)
            · right
              rw [not_forall] at hall
              obtain ⟨x, hx⟩ := hall
              rw [Classical.not_imp] at hx
              obtain ⟨k, hk2, hkp⟩ := idx_of _ (legal C.gates[w - n] (List.getElem_mem hi)).2 p hp
              refine ⟨(w - n, k), hi, hk2, c, v, rfl, ?_, Or.inl ⟨?_, ⟨x, v, hx.2, hx.1, ?_⟩, hadj⟩⟩
              · show TS C.gates (inp C (w - n) k) v
                unfold inp
                rw [gateAt_eq C _ hi, hkp]
                exact h1
              · rw [gateAt_eq C _ hi]; exact ho
              · exact hsub v ((h1 v).2 rfl)
          · exact Or.inr h1

theorem no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

theorem rel_fun {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (e e2 : Sym2 (Fin n)) (t : ℕ × ℕ) (h : Rel G C e t) (h2 : Rel G C e2 t) :
    e = e2 := by
  obtain ⟨c, v, rfl, hv, hc⟩ := h
  obtain ⟨c2, v2, rfl, hv2, hc2⟩ := h2
  have hvv : v = v2 := (hv2 v).1 ((hv v).2 rfl)
  subst hvv
  rcases hc with ⟨h1, ⟨x, y, hxy, hx, hy⟩, hA⟩ | ⟨h1, hT⟩
  · rcases hc2 with ⟨-, -, hA2⟩ | ⟨h3, -⟩
    · by_contra hne
      have hcc : c ≠ c2 := fun h => hne (by rw [h])
      exact no4 G hg c x c2 y (hA x hx) (hA2 x hx).symm (hA2 y hy) (hA y hy).symm hcc hxy
    · rw [h1] at h3; cases h3
  · rcases hc2 with ⟨h3, -, -⟩ | ⟨-, hT2⟩
    · rw [h1] at h3; cases h3
    · have : c = c2 := (hT2 c).1 ((hT c).2 rfl)
      rw [this]

open PEqualNP.EdgeOwnership in
theorem star_case (n : ℕ) (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (g : ℕ) (hgl : g < C.gates.length) (hop : (gateAt C g).op = GateOp.and)
    (ka kb a b : ℕ) (hk : (ka = 0 ∧ kb = 1) ∨ (ka = 1 ∧ kb = 0))
    (hia : inp C g ka = a) (hib : inp C g kb = b) (c v : Fin n)
    (hac : val C.gates a (pairInput c c) = true) (hbv : val C.gates b (pairInput v v) = true)
    (ha : val C.gates a (pairInput c v) = true) (hb : val C.gates b (pairInput c v) = true)
    (hna : NA n C (pairInput c v) a) (hnb : NA n C (pairInput c v) b)
    (hprod : ∀ x y : Fin n, val C.gates a (pairInput x x) = true →
      val C.gates b (pairInput y y) = true → G.Adj x y) :
    ∃ t : ℕ × ℕ, t.1 < C.gates.length ∧ t.2 < 2 ∧ Rel G C s(c, v) t := by
  have hka : 1 - kb = ka := by omega
  have hkb : 1 - ka = kb := by omega
  by_cases hA : ∀ x : Fin n, val C.gates a (pairInput x x) = true → x = c
  · have hTa : TS C.gates a c := fun x => ⟨hA x, fun hx => by rw [hx]; exact hac⟩
    rcases climb n G C legal c v b hb (fun x hx => hprod c x hac hx) hnb with h1 | h1
    · refine ⟨(g, kb), hgl, by omega, c, v, rfl, ?_, Or.inr ⟨hop, ?_⟩⟩
      · show TS C.gates (inp C g kb) v
        rw [hib]; exact h1
      · show TS C.gates (inp C g (1 - kb)) c
        rw [hka, hia]; exact hTa
    · exact h1
  · rw [not_forall] at hA
    obtain ⟨x, hx⟩ := hA
    rw [Classical.not_imp] at hx
    have hB : ∀ y : Fin n, val C.gates b (pairInput y y) = true → y = v := by
      intro y hy
      by_contra hne
      exact no4 G hg c v x y (hprod c v hac hbv) (hprod x v hx.1 hbv).symm (hprod x y hx.1 hy)
        (hprod c y hac hy).symm (Ne.symm hx.2) (Ne.symm hne)
    have hTb : TS C.gates b v := fun y => ⟨hB y, fun hy => by rw [hy]; exact hbv⟩
    rw [pi_symm c v] at ha hna
    rw [Sym2.eq_swap]
    rcases climb n G C legal v c a ha (fun y hy => (hprod y v hy hbv).symm) hna with h1 | h1
    · refine ⟨(g, ka), hgl, by omega, v, c, rfl, ?_, Or.inr ⟨hop, ?_⟩⟩
      · show TS C.gates (inp C g ka) c
        rw [hia]; exact h1
      · show TS C.gates (inp C g (1 - ka)) v
        rw [hkb, hib]; exact hTb
    · exact h1

open PEqualNP.EdgeOwnership in
theorem exists_rel (n : ℕ) (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hm : Monotone2 C) (u v : Fin n) (g : ℕ) (hown : Owns n C g u v)
    (hclean : ∀ x y : Fin n, gateVal n C g (pairInput x y) = true → G.Adj x y) :
    ∃ t : ℕ × ℕ, t.1 < C.gates.length ∧ t.2 < 2 ∧ Rel G C s(u, v) t := by
  have legal := legal_of C hm
  obtain ⟨hgl, hop, hval, hcone⟩ := hown
  have hop2 : C.gates[g].op = GateOp.and := by rw [← gateAt_eq C g hgl]; exact hop
  have hlen := (legal C.gates[g] (List.getElem_mem hgl)).2
  have hcl : ∀ x y : Fin n, val C.gates (n + g) (pairInput x y) = true → G.Adj x y := hclean
  have hval2 : val C.gates (n + g) (pairInput u v) = true := hval
  have hT : ∀ x : Fin n, val C.gates (n + g) (pairInput x x) = true → False :=
    fun x hx => (hcl x x hx).ne rfl
  have hall := (val_and C.gates (pairInput u v) g hgl hop2).1 hval2
  have hna : ∀ p ∈ C.gates[g].inputs, p < n + g → NA n C (pairInput u v) p := by
    intro p hp hlt i hi hand
    have hp2 : p ∈ (gateAt C g).inputs := by rw [gateAt_eq C g hgl]; exact hp
    rcases hi with hi | ⟨j, hj, hpj, hc⟩
    · exact hcone i (by omega) ((inCone_iff n C i g hgl).2
        ⟨p, hp2, by omega, hlt, Or.inl (by omega)⟩) hand
    · have hij := inCone_lt n C j hj i hc
      exact hcone i (by omega) ((inCone_iff n C i g hgl).2
        ⟨p, hp2, by omega, hlt, Or.inr (by rw [show p - n = j by omega]; exact hc)⟩) hand
  rcases hin : C.gates[g].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exfalso
    apply hT u
    apply (val_and C.gates _ g hgl hop2).2
    intro i hi
    rw [hin] at hi
    simp at hi
  · exfalso
    have ha := hall a (by rw [hin]; simp)
    have hna2 := hna a (by rw [hin]; simp) ha.1
    rcases descent n C legal u v a ha.2 hna2 with h1 | h1
    · apply hT u
      apply (val_and C.gates _ g hgl hop2).2
      intro i hi
      rw [hin] at hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact ⟨ha.1, h1⟩
    · apply hT v
      apply (val_and C.gates _ g hgl hop2).2
      intro i hi
      rw [hin] at hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact ⟨ha.1, h1⟩
  · have ha := hall a (by rw [hin]; simp)
    have hb := hall b (by rw [hin]; simp)
    have hnaa := hna a (by rw [hin]; simp) ha.1
    have hnab := hna b (by rw [hin]; simp) hb.1
    have hboth : ∀ x y : Fin n, val C.gates a (pairInput x y) = true →
        val C.gates b (pairInput x y) = true → val C.gates (n + g) (pairInput x y) = true := by
      intro x y hx hy
      apply (val_and C.gates _ g hgl hop2).2
      intro i hi
      rw [hin] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ⟨ha.1, hx⟩
      · exact ⟨hb.1, hy⟩
    have hprod : ∀ x y : Fin n, val C.gates a (pairInput x x) = true →
        val C.gates b (pairInput y y) = true → G.Adj x y := by
      intro x y hx hy
      apply hcl x y
      exact hboth x y (val_mono C.gates legal _ _ (pi_le x x y (Or.inl rfl)) a hx)
        (val_mono C.gates legal _ _ (pi_le y x y (Or.inr rfl)) b hy)
    have hi0 : inp C g 0 = a := by
      unfold inp
      rw [gateAt_eq C g hgl, hin]
      rfl
    have hi1 : inp C g 1 = b := by
      unfold inp
      rw [gateAt_eq C g hgl, hin]
      rfl
    rcases descent n C legal u v a ha.2 hnaa with h1 | h1
    · rcases descent n C legal u v b hb.2 hnab with h2 | h2
      · exact (hT u (hboth u u h1 h2)).elim
      · exact star_case n G hg C legal g hgl hop 0 1 a b (Or.inl ⟨rfl, rfl⟩) hi0 hi1 u v h1 h2
          ha.2 hb.2 hnaa hnab hprod
    · rcases descent n C legal u v b hb.2 hnab with h2 | h2
      · rw [Sym2.eq_swap]
        rw [pi_symm u v] at ha hb hnaa hnab
        exact star_case n G hg C legal g hgl hop 0 1 a b (Or.inl ⟨rfl, rfl⟩) hi0 hi1 v u h1 h2
          ha.2 hb.2 hnaa hnab hprod
      · exact (hT v (hboth v v h1 h2)).elim
  · exfalso
    rw [hin] at hlen
    simp at hlen

end PEqualNP.Outside.L_meta_1762

theorem PEqualNP.Outside.L_meta_1762 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x2 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → {x10 ∈ x3.edgeFinset | ∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ (x13 : Fin x7.gates.length), PEqualNP.EdgeOwnership.Owns x2 x7 (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x7 (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → x3.Adj x14 x15}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  refine ⟨2, ?_⟩
  intro n G _ hdeg hg C hm hfun
  refine le_trans (Finset.card_le_card_of_forall_subsingleton
    (PEqualNP.Outside.L_meta_1762.Rel G C)
    (t := Finset.range C.gates.length ×ˢ Finset.range 2) ?_ ?_) ?_
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨-, u, v, rfl, g, hown, hclean⟩ := he
    obtain ⟨t, h1, h2, hR⟩ :=
      PEqualNP.Outside.L_meta_1762.exists_rel n G hg C hm u v g hown hclean
    exact ⟨t, Finset.mem_product.2 ⟨Finset.mem_range.2 h1, Finset.mem_range.2 h2⟩, hR⟩
  · intro t _ e he e2 he2
    exact PEqualNP.Outside.L_meta_1762.rel_fun G hg C e e2 t he.2 he2.2
  · rw [Finset.card_product, Finset.card_range, Finset.card_range]
    show C.gates.length * 2 ≤ 2 * (C.gates.length + 1)
    omega
