import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1642
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

def St (gates : List Gate) (N : ℕ) (w p : ℕ) : Prop :=
  ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs →
    (gates.get k).op = GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → p ∈ Zs

theorem st_refl (gates : List Gate) (N w : ℕ) : St gates N w w := fun _ h _ => h

theorem st_down (gates : List Gate) (N w : ℕ) (k : Fin gates.length)
    (hop : (gates.get k).op = GateOp.or) (e : ℕ) (he : e ∈ (gates.get k).inputs)
    (h : St gates N w (N + (k : ℕ))) : St gates N w e :=
  fun Zs h1 h2 => h2 k (h Zs h1 h2) hop e he

theorem st_up (gates : List Gate) (N : ℕ) (k : Fin gates.length)
    (hop : (gates.get k).op = GateOp.or) (e : ℕ) (he : e ∈ (gates.get k).inputs) (p : ℕ)
    (h : St gates N e p) : St gates N (N + (k : ℕ)) p :=
  fun Zs h1 h2 => h Zs (h2 k h1 hop e he) h2

theorem st_atom (gates : List Gate) (N w p : ℕ)
    (hno : ∀ k : Fin gates.length, w = N + (k : ℕ) → (gates.get k).op ≠ GateOp.or)
    (h : St gates N w p) : p = w := by
  have h1 : p ∈ ({w} : Set ℕ) := h {w} (Set.mem_singleton w)
    (fun k hk hop => absurd hop (hno k (Set.mem_singleton_iff.1 hk).symm))
  exact Set.mem_singleton_iff.1 h1

theorem st_or (gates : List Gate) (N : ℕ) (k : Fin gates.length) (p : ℕ)
    (h : St gates N (N + (k : ℕ)) p) :
    p = N + (k : ℕ) ∨ ∃ e ∈ (gates.get k).inputs, St gates N e p := by
  have h1 : p ∈ {u : ℕ | u = N + (k : ℕ) ∨ ∃ e ∈ (gates.get k).inputs, St gates N e u} := by
    refine h _ ?_ ?_
    · show N + (k : ℕ) = N + (k : ℕ) ∨ _
      exact Or.inl rfl
    · intro k' hk' hop e' he'
      have hk'' : N + (k' : ℕ) = N + (k : ℕ) ∨
          ∃ e ∈ (gates.get k).inputs, St gates N e (N + (k' : ℕ)) := hk'
      show e' = N + (k : ℕ) ∨ ∃ e ∈ (gates.get k).inputs, St gates N e e'
      rcases hk'' with hk'' | ⟨e, he, hs⟩
      · have hkk : k' = k := Fin.ext (by omega)
        subst hkk
        exact Or.inr ⟨e', he', st_refl gates N e'⟩
      · exact Or.inr ⟨e, he, st_down gates N e k' hop e' he' hs⟩
  exact h1

theorem st_false (gates : List Gate) (N : ℕ)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (x : Fin N → Bool) (w p : ℕ) (hw : val gates w x = false) (h : St gates N w p) :
    val gates p x = false := by
  have h1 : p ∈ {u : ℕ | val gates u x = false} := by
    refine h _ hw ?_
    intro k hk hop e he
    show val gates e x = false
    have hk' : val gates (N + (k : ℕ)) x = false := hk
    cases hv : val gates e x with
    | false => rfl
    | true =>
      have ht := (val_or gates x (k : ℕ) k.2 hop).2 ⟨e, he, hin k e he, hv⟩
      rw [ht] at hk'
      exact Bool.noConfusion hk'
  exact h1

def E (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N) (w : ℕ) (v : Fin N) :
    Prop :=
  (v ∈ M ∧ v ≠ p0 ∧ v ≠ p1 ∧ St gates N w (v : ℕ)) ∨
  (v = p0 ∧ (val gates w (fun u : Fin N => decide (u = p0)) = true ∨
    val gates w (fun u : Fin N => decide (u = p1)) = true))

def Inv (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N) (z : Fin N → Bool)
    (k : ℕ) (f : Fin N → Fin N) : Prop :=
  ∀ g : Fin gates.length, (g : ℕ) < k → (gates.get g).op = GateOp.or →
    val gates (N + (g : ℕ)) z = false → ∀ v v' : Fin N,
    E gates N M p0 p1 (N + (g : ℕ)) v → E gates N M p0 p1 (N + (g : ℕ)) v' → f v = f v'

theorem anchor_input (gates : List Gate) {N : ℕ} (u p : Fin N)
    (h : val gates (u : ℕ) (fun t : Fin N => decide (t = p)) = true) : u = p := by
  rw [val_input gates _ (u : ℕ) u.2] at h
  exact of_decide_eq_true h

theorem E_same (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N)
    (z : Fin N → Bool) (k : ℕ) (f : Fin N → Fin N) (hI : Inv gates N M p0 p1 z k f)
    (w : ℕ) (hw : w < N + k) (hz : val gates w z = false) (v v' : Fin N)
    (hv : E gates N M p0 p1 w v) (hv' : E gates N M p0 p1 w v') : f v = f v' := by
  by_cases hor : ∃ g : Fin gates.length, w = N + (g : ℕ) ∧ (gates.get g).op = GateOp.or
  · obtain ⟨g, hg, hop⟩ := hor
    subst hg
    exact hI g (by omega) hop hz v v' hv hv'
  · have hno : ∀ g : Fin gates.length, w = N + (g : ℕ) → (gates.get g).op ≠ GateOp.or :=
      fun g hg hop => hor ⟨g, hg, hop⟩
    rcases hv with ⟨_, h0, h1, hs⟩ | ⟨e0, ha⟩
    · have e1 : (v : ℕ) = w := st_atom gates N w _ hno hs
      rcases hv' with ⟨_, h0', h1', hs'⟩ | ⟨e0', ha'⟩
      · have e2 : (v' : ℕ) = w := st_atom gates N w _ hno hs'
        have : v = v' := Fin.ext (e1.trans e2.symm)
        rw [this]
      · exfalso
        rw [← e1] at ha'
        rcases ha' with h | h
        · exact h0 (anchor_input gates v _ h)
        · exact h1 (anchor_input gates v _ h)
    · rcases hv' with ⟨_, h0', h1', hs'⟩ | ⟨e0', ha'⟩
      · exfalso
        have e2 : (v' : ℕ) = w := st_atom gates N w _ hno hs'
        rw [← e2] at ha
        rcases ha with h | h
        · exact h0' (anchor_input gates v' _ h)
        · exact h1' (anchor_input gates v' _ h)
      · rw [e0, e0']

theorem E_down (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N)
    (k : Fin gates.length) (hop : (gates.get k).op = GateOp.or) (v : Fin N)
    (h : E gates N M p0 p1 (N + (k : ℕ)) v) :
    ∃ e ∈ (gates.get k).inputs, E gates N M p0 p1 e v := by
  rcases h with ⟨hM, h0, h1, hs⟩ | ⟨hv, ha⟩
  · rcases st_or gates N k _ hs with h | ⟨e, he, hse⟩
    · exact absurd h (by have := v.2; omega)
    · exact ⟨e, he, Or.inl ⟨hM, h0, h1, hse⟩⟩
  · rcases ha with h | h
    · obtain ⟨e, he, _, hv'⟩ := (val_or gates _ (k : ℕ) k.2 hop).1 h
      exact ⟨e, he, Or.inr ⟨hv, Or.inl hv'⟩⟩
    · obtain ⟨e, he, _, hv'⟩ := (val_or gates _ (k : ℕ) k.2 hop).1 h
      exact ⟨e, he, Or.inr ⟨hv, Or.inr hv'⟩⟩

theorem E_wit (gates : List Gate) (N : ℕ) (M : Finset (Fin N)) (p0 p1 : Fin N)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hp0 : p0 ∈ M) (hp1 : p1 ∈ M) (w : ℕ) (v : Fin N)
    (h : E gates N M p0 p1 w v) :
    ∃ x : Fin N, x ∈ M ∧ ((x = v ∧ v ≠ p0 ∧ v ≠ p1) ∨ (v = p0 ∧ (x = p0 ∨ x = p1))) ∧
      ∀ X : Fin N → Bool, X x = true → val gates w X = true := by
  rcases h with ⟨hM, h0, h1, hs⟩ | ⟨hv, ha⟩
  · refine ⟨v, hM, Or.inl ⟨rfl, h0, h1⟩, ?_⟩
    intro X hX
    cases hw : val gates w X with
    | true => rfl
    | false =>
      have h2 := st_false gates N hin X w _ hw hs
      rw [val_input gates X (v : ℕ) v.2] at h2
      exact Bool.noConfusion (hX.symm.trans h2)
  · rcases ha with h | h
    · refine ⟨p0, hp0, Or.inr ⟨hv, Or.inl rfl⟩, ?_⟩
      intro X hX
      exact val_mono gates legal _ X
        (fun u hu => by have h3 := of_decide_eq_true hu; rw [h3]; exact hX) w h
    · refine ⟨p1, hp1, Or.inr ⟨hv, Or.inr rfl⟩, ?_⟩
      intro X hX
      exact val_mono gates legal _ X
        (fun u hu => by have h3 := of_decide_eq_true hu; rw [h3]; exact hX) w h

theorem two_cases (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ e ∈ l, e = a ∨ e = b := by
  match l, hl, ha, hb with
  | [], _, ha, _ => exact absurd ha (by simp)
  | [x], _, ha, hb =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [x, y], _, ha, hb =>
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb he
    omega
  | _ :: _ :: _ :: _, hl, _, _ =>
    simp only [List.length_cons] at hl
    omega

theorem cover (gates : List Gate) (N : ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z xr : Fin N → Bool) (r : Fin N)
    (hzr : ∀ v, z v = false → xr v = true → v = r)
    (ch : Fin gates.length → ℕ)
    (hch : ∀ a : Fin gates.length, (gates.get a).op = GateOp.and →
      val gates (N + (a : ℕ)) z = false → val gates (N + (a : ℕ)) xr = true →
      ch a ∈ (gates.get a).inputs ∧ val gates (ch a) z = false) :
    ∀ w, val gates w z = false → val gates w xr = true →
      St gates N w (r : ℕ) ∨ ∃ a : Fin gates.length, (gates.get a).op = GateOp.and ∧
        val gates (N + (a : ℕ)) z = false ∧ val gates (N + (a : ℕ)) xr = true ∧
        St gates N (ch a) (r : ℕ) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h0 hr
    by_cases hwn : w < N
    · left
      rw [val_input gates _ w hwn] at h0 hr
      have h1 := hzr _ h0 hr
      rw [← h1]
      exact st_refl gates N w
    · by_cases hbig : N + gates.length ≤ w
      · rw [val_big gates xr w hbig] at hr
        exact Bool.noConfusion hr
      · have hi : w - N < gates.length := by omega
        have he : N + (w - N) = w := by omega
        rw [← he] at h0 hr ⊢
        rcases (legal gates[w - N] (List.getElem_mem hi)).1 with ha | ho
        · obtain ⟨hcm, hc0⟩ := hch ⟨w - N, hi⟩ ha h0 hr
          obtain ⟨hclt, hcr⟩ := (val_and gates xr (w - N) hi ha).1 hr _ hcm
          rcases ih (ch ⟨w - N, hi⟩) (by omega) hc0 hcr with h | h
          · exact Or.inr ⟨⟨w - N, hi⟩, ha, h0, hr, h⟩
          · exact Or.inr h
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates xr (w - N) hi ho).1 hr
          have hj0 : val gates j z = false := by
            cases hv0 : val gates j z with
            | false => rfl
            | true =>
              have ht := (val_or gates z (w - N) hi ho).2 ⟨j, hj, hjlt, hv0⟩
              rw [ht] at h0
              exact Bool.noConfusion h0
          rcases ih j (by omega) hj0 hv with h | h
          · exact Or.inl (st_up gates N ⟨w - N, hi⟩ ho j hj _ h)
          · exact Or.inr h

theorem step (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hint : ∀ t : Fin N, t ≠ i0 → (L i0 ∩ L t).card = 1)
    (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (Xs : Finset (Fin gates.length))
    (hXs : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
      val gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      (∀ t : Fin N, t ≠ i0 → val gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
      ¬ ∀ e ∈ (gates.get g).inputs, (val gates e (fun v : Fin N => decide (v = p0)) = true ∨
        val gates e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs)
    (V : Finset (Fin N)) :
    ∀ k : ℕ, k ≤ gates.length → ∃ f : Fin N → Fin N,
      Inv gates N (L i0) p0 p1 (fun v : Fin N => decide (v ∉ L i0)) k f ∧
      V.card ≤ (V.image f).card + (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k)).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, fun g hg => absurd hg (Nat.not_lt_zero _), ?_⟩
    rw [Finset.image_id]
    exact Nat.le_add_right _ _
  | succ k ih =>
    intro hk
    obtain ⟨f, hI, hc⟩ := ih (by omega)
    have hmono : (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k)).card
        ≤ (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k + 1)).card := by
      apply Finset.card_le_card
      intro g hg
      rw [Finset.mem_filter] at hg ⊢
      exact ⟨hg.1, by omega⟩
    have hklt : k < gates.length := by omega
    by_cases hor : (gates.get ⟨k, hklt⟩).op = GateOp.or ∧
        val gates (N + k) (fun v : Fin N => decide (v ∉ L i0)) = false
    swap
    · refine ⟨f, ?_, by omega⟩
      intro g hg hop hz v v' hv hv'
      by_cases hgk : (g : ℕ) < k
      · exact hI g hgk hop hz v v' hv hv'
      · have hgeq : g = ⟨k, hklt⟩ := Fin.ext (show (g : ℕ) = k by omega)
        subst hgeq
        exact absurd ⟨hop, hz⟩ hor
    obtain ⟨hop, hz⟩ := hor
    by_cases hgood : ∀ v v' : Fin N, E gates N (L i0) p0 p1 (N + k) v →
        E gates N (L i0) p0 p1 (N + k) v' → f v = f v'
    · refine ⟨f, ?_, by omega⟩
      intro g hg hop' hz' v v' hv hv'
      by_cases hgk : (g : ℕ) < k
      · exact hI g hgk hop' hz' v v' hv hv'
      · have hgeq : g = ⟨k, hklt⟩ := Fin.ext (show (g : ℕ) = k by omega)
        subst hgeq
        exact hgood v v' hv hv'
    · push_neg at hgood
      obtain ⟨v, v', hv, hv', hne⟩ := hgood
      have hinz : ∀ e ∈ (gates.get ⟨k, hklt⟩).inputs,
          val gates e (fun v : Fin N => decide (v ∉ L i0)) = false := by
        intro e he
        cases hv0 : val gates e (fun v : Fin N => decide (v ∉ L i0)) with
        | false => rfl
        | true =>
          have ht := (val_or gates (fun v : Fin N => decide (v ∉ L i0)) k hklt hop).2
            ⟨e, he, hin ⟨k, hklt⟩ e he, hv0⟩
          rw [ht] at hz
          exact Bool.noConfusion hz
      have hsame : ∀ e ∈ (gates.get ⟨k, hklt⟩).inputs, ∀ a b : Fin N,
          E gates N (L i0) p0 p1 e a → E gates N (L i0) p0 p1 e b → f a = f b :=
        fun e he a b ha hb => E_same gates N (L i0) p0 p1 _ k f hI e (hin ⟨k, hklt⟩ e he)
          (hinz e he) a b ha hb
      obtain ⟨ea, hea, hEa⟩ := E_down gates N (L i0) p0 p1 ⟨k, hklt⟩ hop v hv
      obtain ⟨eb, heb, hEb⟩ := E_down gates N (L i0) p0 p1 ⟨k, hklt⟩ hop v' hv'
      have hab : ea ≠ eb := by
        intro h
        rw [← h] at hEb
        exact hne (hsame ea hea v v' hEa hEb)
      have hall := two_cases _ (legal _ (List.get_mem gates ⟨k, hklt⟩)).2 ea eb hea heb hab
      have hcl : ∀ u : Fin N, E gates N (L i0) p0 p1 (N + k) u → f u = f v ∨ f u = f v' := by
        intro u hu
        obtain ⟨eu, heu, hEu⟩ := E_down gates N (L i0) p0 p1 ⟨k, hklt⟩ hop u hu
        rcases hall eu heu with h | h
        · rw [h] at hEu
          exact Or.inl (hsame ea hea u v hEu hEa)
        · rw [h] at hEu
          exact Or.inr (hsame eb heb u v' hEu hEb)
      have hmem : (⟨k, hklt⟩ : Fin gates.length) ∈ Xs := by
        apply hXs
        refine ⟨hop, hz, ?_, ?_⟩
        · intro t ht
          obtain ⟨x, hxM, hxc, hxv⟩ :=
            E_wit gates N (L i0) p0 p1 legal hin hp0 hp1 (N + k) v hv
          obtain ⟨x', hxM', hxc', hxv'⟩ :=
            E_wit gates N (L i0) p0 p1 legal hin hp0 hp1 (N + k) v' hv'
          have hvv : v ≠ v' := fun h => hne (by rw [h])
          have hxx : x ≠ x' := by
            intro h
            rcases hxc with ⟨e1, a0, a1⟩ | ⟨e1, a⟩
            · rcases hxc' with ⟨e2, b0, b1⟩ | ⟨e2, b⟩
              · exact hvv (e1.symm.trans (h.trans e2))
              · rcases b with b | b
                · exact a0 (e1.symm.trans (h.trans b))
                · exact a1 (e1.symm.trans (h.trans b))
            · rcases hxc' with ⟨e2, b0, b1⟩ | ⟨e2, b⟩
              · rcases a with a | a
                · exact b0 (e2.symm.trans (h.symm.trans a))
                · exact b1 (e2.symm.trans (h.symm.trans a))
              · exact hvv (e1.trans e2.symm)
          have hoff : x ∉ L t ∨ x' ∉ L t := by
            by_contra hcon
            push_neg at hcon
            have h1 := hint t ht
            exact hxx (Finset.card_le_one.1 (le_of_eq h1) x (Finset.mem_inter.2 ⟨hxM, hcon.1⟩)
              x' (Finset.mem_inter.2 ⟨hxM', hcon.2⟩))
          rcases hoff with h | h
          · exact hxv _ (decide_eq_true h)
          · exact hxv' _ (decide_eq_true h)
        · intro hanch
          have h1 : f v = f p0 := hsame ea hea v p0 hEa (Or.inr ⟨rfl, hanch ea hea⟩)
          have h2 : f v' = f p0 := hsame eb heb v' p0 hEb (Or.inr ⟨rfl, hanch eb heb⟩)
          exact hne (h1.trans h2.symm)
      have hf' : ∃ f' : Fin N → Fin N, ∀ x, f' x = if f x = f v' then f v else f x :=
        ⟨_, fun _ => rfl⟩
      obtain ⟨f', hf'⟩ := hf'
      have hnew : ∀ u : Fin N, E gates N (L i0) p0 p1 (N + k) u → f' u = f v := by
        intro u hu
        rw [hf']
        rcases hcl u hu with h | h
        · rw [h]
          exact ite_self _
        · rw [if_pos h]
      refine ⟨f', ?_, ?_⟩
      · intro g hg hop' hz' a b ha hb
        by_cases hgk : (g : ℕ) < k
        · have h3 := hI g hgk hop' hz' a b ha hb
          rw [hf', hf', h3]
        · have hgeq : g = ⟨k, hklt⟩ := Fin.ext (show (g : ℕ) = k by omega)
          subst hgeq
          rw [hnew a ha, hnew b hb]
      · have hA : (V.image f).card ≤ (V.image f').card + 1 := by
          refine (Finset.card_le_card ?_).trans (Finset.card_insert_le (f v') _)
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
          by_cases h : f x = f v'
          · rw [h]
            exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨x, hx, ?_⟩)
            rw [hf', if_neg h]
        have hB : (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k)).card + 1
            ≤ (Xs.filter (fun g : Fin gates.length => (g : ℕ) < k + 1)).card := by
          have hnot : (⟨k, hklt⟩ : Fin gates.length) ∉
              Xs.filter (fun g : Fin gates.length => (g : ℕ) < k) := by
            intro h
            exact Nat.lt_irrefl k (Finset.mem_filter.1 h).2
          rw [← Finset.card_insert_of_notMem hnot]
          apply Finset.card_le_card
          intro g hg
          rcases Finset.mem_insert.1 hg with h | h
          · rw [h]
            exact Finset.mem_filter.2 ⟨hmem, Nat.lt_succ_self k⟩
          · rw [Finset.mem_filter] at h ⊢
            exact ⟨h.1, by omega⟩
        omega

theorem main (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hcard : (L i0).card = q + 1)
    (hint : ∀ t : Fin N, t ≠ i0 → (L i0 ∩ L t).card = 1)
    (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (o0 : ℕ)
    (hoz : val gates o0 (fun v : Fin N => decide (v ∉ L i0)) = false)
    (ho0 : val gates o0 (fun v : Fin N => decide (v = p0)) = true)
    (hor : ∀ r ∈ L i0, r ≠ p0 → r ≠ p1 →
      val gates o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true)
    (ch : Fin gates.length → ℕ)
    (hch : ∀ a : Fin gates.length, ((gates.get a).op = GateOp.and ∧
      val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
        val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
      ch a ∈ (gates.get a).inputs ∧ val gates (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false)
    (Au Xs : Finset (Fin gates.length))
    (hAu : ∀ a : Fin gates.length, (((gates.get a).op = GateOp.and ∧
      val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
        val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) ∧
      ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
        val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true ∧
        St gates N (ch a) (r : ℕ)) → a ∈ Au)
    (hXs : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
      val gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
      (∀ t : Fin N, t ≠ i0 → val gates (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
      ¬ ∀ e ∈ (gates.get g).inputs, (val gates e (fun v : Fin N => decide (v = p0)) = true ∨
        val gates e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs) :
    q - 1 ≤ Au.card + Xs.card := by
  classical
  obtain ⟨f, hI, hc⟩ := step N L i0 p0 p1 hint hp0 hp1 gates legal hin Xs hXs
    ((L i0).erase p1) gates.length le_rfl
  have hVc := Finset.card_erase_of_mem hp1
  have hfil : (Xs.filter (fun g : Fin gates.length => (g : ℕ) < gates.length)).card ≤ Xs.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hex : ∃ ρ : Fin gates.length → Fin N, ∀ a : Fin gates.length, ∀ r : Fin N,
      r ∈ L i0 → r ≠ p0 → r ≠ p1 → St gates N (ch a) (r : ℕ) →
      (ρ a ∈ L i0 ∧ ρ a ≠ p0 ∧ ρ a ≠ p1 ∧ St gates N (ch a) (ρ a : ℕ)) := by
    refine ⟨fun a => if h : ∃ r : Fin N, r ∈ L i0 ∧ r ≠ p0 ∧ r ≠ p1 ∧
      St gates N (ch a) (r : ℕ) then h.choose else p0, ?_⟩
    intro a r h1 h2 h3 h4
    have h : ∃ r : Fin N, r ∈ L i0 ∧ r ≠ p0 ∧ r ≠ p1 ∧ St gates N (ch a) (r : ℕ) :=
      ⟨r, h1, h2, h3, h4⟩
    simp only [dif_pos h]
    exact h.choose_spec
  obtain ⟨ρ, hρ⟩ := hex
  have himg : ((L i0).erase p1).image f ⊆ insert (f p0) (Au.image (fun a => f (ρ a))) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hx1, hxM⟩ := Finset.mem_erase.1 hx
    by_cases hx0 : x = p0
    · rw [hx0]
      exact Finset.mem_insert_self _ _
    · have hzr : ∀ v : Fin N, (fun v : Fin N => decide (v ∉ L i0)) v = false →
          (fun v : Fin N => decide (v ∉ L i0 ∨ v = x)) v = true → v = x := by
        intro v h1 h2
        have a1 : ¬ (v ∉ L i0) := of_decide_eq_false h1
        have a2 : v ∉ L i0 ∨ v = x := of_decide_eq_true h2
        exact a2.resolve_left a1
      rcases cover gates N legal _ _ x hzr ch
        (fun a ha h0 hr => hch a ⟨ha, h0, x, hxM, hx0, hx1, hr⟩) o0 hoz (hor x hxM hx0 hx1)
        with hs | ⟨a, ha, h0, hr, hs⟩
      · have ho_lt : o0 < N + gates.length := by
          by_contra hcon
          rw [val_big gates _ o0 (by omega)] at ho0
          exact Bool.noConfusion ho0
        have h5 := E_same gates N (L i0) p0 p1 _ gates.length f hI o0 ho_lt hoz x p0
          (Or.inl ⟨hxM, hx0, hx1, hs⟩) (Or.inr ⟨rfl, Or.inl ho0⟩)
        rw [h5]
        exact Finset.mem_insert_self _ _
      · have hrim : (gates.get a).op = GateOp.and ∧
            val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧
            ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧
              val gates (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true :=
          ⟨ha, h0, x, hxM, hx0, hx1, hr⟩
        have haA : a ∈ Au := hAu a ⟨hrim, x, hxM, hx0, hx1, hr, hs⟩
        obtain ⟨hcm, hc0⟩ := hch a hrim
        obtain ⟨r1, r2, r3, r4⟩ := hρ a x hxM hx0 hx1 hs
        have hlt : ch a < N + gates.length := by
          have h6 := hin a _ hcm
          have h7 := a.2
          omega
        have h5 := E_same gates N (L i0) p0 p1 _ gates.length f hI (ch a) hlt hc0 x (ρ a)
          (Or.inl ⟨hxM, hx0, hx1, hs⟩) (Or.inl ⟨r1, r2, r3, r4⟩)
        rw [h5]
        exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨a, haA, rfl⟩)
  have h1 := (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
  have h2 : (Au.image (fun a => f (ρ a))).card ≤ Au.card := Finset.card_image_le
  omega

end PEqualNP.Outside.L_meta_1642

theorem PEqualNP.Outside.L_meta_1642 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ ch : Fin gates.length → ℕ, (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) → ch a ∈ (gates.get a).inputs ∧ ev (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false) →
    ∀ Au Xs : Finset (Fin gates.length), (∀ a : Fin gates.length, (((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true ∧ St (ch a) r) → a ∈ Au) →
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs) → q - 1 ≤ Au.card + Xs.card := by
  intro q N L i0 p0 p1 _ _ hcard hint _ _ hp0 hp1 gates legal _ hin ev he o0 hoz ho0 _ hor St hSt ch hch Au Xs hAu hXs
  have hev : ev = fun w x => PEqualNP.Outside.L_meta_1642.val gates w x := by
    funext w x
    rw [he]
    exact PEqualNP.Outside.L_meta_1642.eval_eq gates w _
  subst hev
  exact PEqualNP.Outside.L_meta_1642.main q N L i0 p0 p1 (hcard i0)
    (fun t ht => hint i0 t (Ne.symm ht)) hp0 hp1 gates legal hin o0 hoz ho0 hor ch hch Au Xs
    (fun a h => hAu a ⟨h.1, by
      obtain ⟨r, h1, h2, h3, h4, h5⟩ := h.2
      exact ⟨r, h1, h2, h3, h4, (hSt _ _).2 h5⟩⟩) hXs
