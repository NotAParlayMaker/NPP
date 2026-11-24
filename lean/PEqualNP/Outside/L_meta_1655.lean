import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1655
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

-- The value of wire `w` on input `x`.
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

lemma mono_with_not (gs : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (b : ℕ)
    (hnot : ∀ k : Fin gs.length, n + (k : ℕ) < b → (gs.get k).op = GateOp.not →
      val gs (n + (k : ℕ)) x = true → val gs (n + (k : ℕ)) y = true)
    (w : ℕ) (hw : w < b) : val gs w x = true → val gs w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · simpa only [val_input gs _ w hin] using hxy ⟨w, hin⟩
    by_cases hlen : w < n + gs.length
    · have hk : w - n < gs.length := by omega
      have he : n + (w - n) = w := by omega
      rcases (legal gs[w - n] (List.getElem_mem hk)).1 with ha | ho | hn
      · intro ht
        have hs := (val_and gs x (w - n) hk ha).1 (by simpa only [he] using ht)
        rw [← he]
        apply (val_and gs y (w - n) hk ha).2
        intro r hr
        obtain ⟨hlt, hit⟩ := hs r hr
        exact ⟨hlt, ih r (by omega) (by omega) hit⟩
      · intro ht
        obtain ⟨r, hr, hlt, hit⟩ := (val_or gs x (w - n) hk ho).1
          (by simpa only [he] using ht)
        rw [← he]
        exact (val_or gs y (w - n) hk ho).2 ⟨r, hr, hlt, ih r (by omega) (by omega) hit⟩
      · simpa only [he] using hnot ⟨w - n, hk⟩ (by simpa only [he] using hw) hn
    · simp [val_big gs x w (by omega)]

lemma val_not (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (j : Fin gs.length)
    (hop : (gs.get j).op = GateOp.not) (h : ℕ) (r : List ℕ)
    (hinputs : (gs.get j).inputs = h :: r) (hh : h < n + (j : ℕ)) :
    val gs (n + (j : ℕ)) x = !(val gs h x) := by
  have hv := gate_val gs (List.ofFn x) j j.isLt
  rw [List.length_ofFn] at hv
  change (wf gs (List.ofFn x)).getD (n + (j : ℕ)) false = _
  rw [hv]
  change (gs.get j).op.eval ((gs.get j).inputs.map _) = _
  rw [hop, hinputs]
  simp only [List.map_cons, GateOp.eval, List.headD_cons]
  congr 1
  exact (wire_take gs (List.ofFn x) j h (by simpa using hh) (Nat.le_of_lt j.isLt)).symm

end PEqualNP.Outside.L_meta_1655

open PEqualNP.Outside.L_meta_1655
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1655 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    ∀ Sm Dm : Fin N → ℕ → Prop,
    (∀ (t : Fin N) (w : ℕ), Sm t w ↔ ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true → ∃ v ∈ L t, x v = true) →
    (∀ (t : Fin N) (w : ℕ), Dm t w ↔ (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t)) →
    ∀ Vs : Fin N → ℕ → Fin N → Prop,
    (∀ (t : Fin N) (w : ℕ) (v : Fin N), Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨ (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true))) →
    ∀ t : Fin N,
    (∀ (w : ℕ) (v : Fin N), Dm t w → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → (Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e) ∧ (Dm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Dm t e)) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and → Sm t (N + (g : ℕ)) → ∃ e ∈ (gates.get g).inputs, Sm t e) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → Vs t w v → v ∈ L t) := by
  classical
  intro q N L i0 p0 p1 hq hN hcard hinter hjoin hp01 hp0 hp1 gates o j h
    legal hback hj hone hh hinputs computes ev hev h0 h1 hother hlow Sm Dm hSm hDm Vs hVs t
  have heq : ev = fun w x => val gates w x := by
    funext w x
    exact hev w x
  subst ev
  obtain ⟨r, hr⟩ := hinputs
  let off : Fin N → Bool := fun v => decide (v ∉ L i0)
  have hprefix (x z : Fin N → Bool) (hxz : ∀ v, x v = true → z v = true) :
      val gates (N + (h : ℕ)) x = true → val gates (N + (h : ℕ)) z = true := by
    apply mono_with_not gates legal x z hxz (N + (j : ℕ))
    · intro k hk hn
      have he := hone k hn
      subst k
      omega
    · exact Nat.add_lt_add_left hh N
  have not_true (x : Fin N → Bool) (hx : ∀ v, x v = true → v ∉ L i0) :
      val gates (N + (j : ℕ)) x = true := by
    have hf : val gates (N + (h : ℕ)) x = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have ht' := hprefix x off (by intro v hv; exact decide_eq_true (hx v hv)) ht
      change val gates (N + (h : ℕ)) off = false at hlow
      rw [hlow] at ht'
      contradiction
    rw [val_not gates x j hj (N + (h : ℕ)) r hr (Nat.add_lt_add_left hh N), hf]
    rfl
  have off_mono (x z : Fin N → Bool) (hz : ∀ v, z v = true → v ∉ L i0)
      (hxz : ∀ v, x v = true → z v = true) (w : ℕ) :
      val gates w x = true → val gates w z = true := by
    apply mono_with_not gates legal x z hxz (w + 1) ?_ w (by omega)
    intro k _ hn _
    have he := hone k hn
    subst k
    exact not_true z hz
  have sm_point (w : ℕ) (v : Fin N) (hs : Sm t w) (hv : v ∉ L i0)
      (ht : val gates w (fun u : Fin N => decide (u = v)) = true) : v ∈ L t := by
    obtain ⟨p, hp, he⟩ := (hSm t w).1 hs _ (by
      intro u hu
      have : u = v := by simpa using hu
      simpa [this] using hv) ht
    have : p = v := by simpa using he
    simpa [this] using hp
  have dm_point (w : ℕ) (v : Fin N) (hs : Dm t w)
      (ht : val gates w (fun u : Fin N => decide (u = v)) = true) : v ∈ L t := by
    by_cases hv : v ∈ L i0
    · exact ((hDm t w).1 hs).2 v hv ht
    · exact sm_point w v ((hDm t w).1 hs).1 hv ht
  let outside : Fin N → Bool := fun v => decide (v ∉ L i0 ∧ v ∉ L t)
  have sm_iff (w : ℕ) : Sm t w ↔ val gates w outside = false := by
    constructor
    · intro hs
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨v, hv, hvt⟩ := (hSm t w).1 hs outside
        (by intro v hv; exact (of_decide_eq_true hv).1) ht
      exact (of_decide_eq_true hvt).2 hv
    · intro hf
      apply (hSm t w).2
      intro x hx ht
      by_contra hn
      have hle (v : Fin N) (hv : x v = true) : outside v = true := by
        exact decide_eq_true ⟨hx v hv, fun hvt => hn ⟨v, hvt, hv⟩⟩
      have htrue := off_mono x outside (by intro v hv; exact (of_decide_eq_true hv).1) hle w ht
      rw [hf] at htrue
      contradiction
  refine ⟨dm_point, sm_point, ?_, ?_, ?_⟩
  · intro g hop
    have hor (e : ℕ) (he : e ∈ (gates.get g).inputs) (x : Fin N → Bool)
        (ht : val gates e x = true) : val gates (N + (g : ℕ)) x = true :=
      (val_or gates x g g.isLt hop).2 ⟨e, he, hback g e he, ht⟩
    have hs (hsg : Sm t (N + (g : ℕ))) (e : ℕ) (he : e ∈ (gates.get g).inputs) : Sm t e := by
      apply (hSm t e).2
      intro x hx ht
      exact (hSm t _).1 hsg x hx (hor e he x ht)
    refine ⟨hs, ?_⟩
    intro hd e he
    apply (hDm t e).2
    refine ⟨hs ((hDm t _).1 hd).1 e he, ?_⟩
    intro p hp ht
    exact ((hDm t _).1 hd).2 p hp (hor e he _ ht)
  · intro g hop hs
    by_contra hn
    have hall : ∀ e ∈ (gates.get g).inputs, val gates e outside = true := by
      intro e he
      cases hv : val gates e outside with
      | false => exact False.elim (hn ⟨e, he, (sm_iff e).2 hv⟩)
      | true => rfl
    have ht := (val_and gates outside g g.isLt hop).2
      (fun e he => ⟨hback g e he, hall e he⟩)
    rw [(sm_iff _).1 hs] at ht
    contradiction
  · intro w v hs hv
    rcases (hVs t w v).1 hv with ⟨hd, ht⟩ | ⟨_, hvo, ht⟩
    · exact dm_point w v hd ht
    · exact sm_point w v hs hvo ht
