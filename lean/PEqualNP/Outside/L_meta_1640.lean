import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1640
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

-- The value of wire `w` on input `x`.
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


theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem or_closed (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) (e : ℕ) (he : e ∈ gates[k].inputs) (hlt : e < n + k)
    (h : val gates (n + k) x = false) : val gates e x = false := by
  by_contra hc
  have hc' : val gates e x = true := by simpa using hc
  have h2 := (val_or gates x k hk hop).2 ⟨e, he, hlt, hc'⟩
  rw [h2] at h
  exact absurd h (by simp)

def SS (gates : List Gate) {n : ℕ} (f g : Fin n → Bool) : Set ℕ :=
  {w | val gates w f = false ∧ val gates w g = false}

theorem mem_SS (gates : List Gate) {n : ℕ} (f g : Fin n → Bool) (w : ℕ) :
    w ∈ SS gates f g ↔ (val gates w f = false ∧ val gates w g = false) := Iff.rfl

def Reach (gates : List Gate) (N : ℕ) (w y : ℕ) : Prop :=
  ∀ S : Set ℕ, w ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S →
    (gates.get i).op = GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → y ∈ S

theorem key (N : ℕ) (gates : List Gate) (z zr : Fin N → Bool) (r : Fin N)
    (hleg : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hread : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (hz : ∀ p : Fin N, z p = false → zr p = true → p = r)
    (ch : Fin gates.length → ℕ)
    (hch : ∀ a : Fin gates.length, (gates.get a).op = GateOp.and →
      val gates (N + (a : ℕ)) z = false → val gates (N + (a : ℕ)) zr = true →
      ch a ∈ (gates.get a).inputs ∧ val gates (ch a) z = false) :
    ∀ w : ℕ, val gates w z = false → val gates w zr = true →
      Reach gates N w r.val ∨ ∃ a : Fin gates.length,
        ((gates.get a).op = GateOp.and ∧ val gates (N + (a : ℕ)) z = false ∧
          val gates (N + (a : ℕ)) zr = true) ∧ Reach gates N (ch a) r.val := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h1 h2
    rcases Nat.lt_or_ge w N with hw | hw
    · rw [val_input gates _ w hw] at h1 h2
      have hpr := hz ⟨w, hw⟩ h1 h2
      left
      intro S hS _
      rw [← hpr]
      exact hS
    · rcases Nat.lt_or_ge w (N + gates.length) with hw2 | hw2
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < gates.length := by omega
        rcases (hleg gates[k] (List.getElem_mem hk)).1 with hop | hop
        · have hc := hch ⟨k, hk⟩ hop h1 h2
          have hin := (val_and gates zr k hk hop).1 h2 (ch ⟨k, hk⟩) hc.1
          rcases ih (ch ⟨k, hk⟩) hin.1 hc.2 hin.2 with h | h
          · right
            exact ⟨⟨k, hk⟩, ⟨hop, h1, h2⟩, h⟩
          · right
            exact h
        · obtain ⟨e, he, hlt, hv⟩ := (val_or gates zr k hk hop).1 h2
          have hez := or_closed gates z k hk hop e he hlt h1
          rcases ih e hlt hez hv with h | h
          · left
            intro S hS hcl
            exact h S (hcl ⟨k, hk⟩ hS hop e he) hcl
          · right
            exact h
      · rw [val_big gates zr w hw2] at h2
        exact absurd h2 (by simp)

end PEqualNP.Outside.L_meta_1640

open PEqualNP.Outside.L_meta_1640 in

theorem PEqualNP.Outside.L_meta_1640 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (ch : Fin gates.length → ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) →
    (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) → ch a ∈ (gates.get a).inputs ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, ch a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) →
    (∀ r ∈ L i0 \ T0, (∀ S : Set ℕ, o ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨
      ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) ∧ (∀ S : Set ℕ, ch a ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S)) ∧
    (∀ a : Fin gates.length, o = N + (a : ℕ) → (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true)) := by
  classical
  intro q m N L i0 T0 _ _ hmq _ hcard _ _ hT0 hT0c gates o ch hleg _ hread h0 hR hch
  have hne : (L i0 \ T0).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hsub : L i0 ⊆ T0 := Finset.sdiff_eq_empty_iff_subset.1 he
    have hle := Finset.card_le_card hsub
    rw [hcard i0, hT0c] at hle
    omega
  refine ⟨?_, ?_⟩
  · intro r hr
    have hk := key N gates (fun v : Fin N => decide (v ∉ L i0))
      (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) r hleg hread (by
        intro p hp1 hp2
        have a1 : p ∈ L i0 := by simpa using hp1
        have a2 : p ∉ L i0 ∨ p = r := by simpa using hp2
        rcases a2 with a2 | a2
        · exact absurd a1 a2
        · exact a2) ch (by
        intro a hop ha1 ha2
        exact hch a ⟨hop, ha1, r, hr, ha2⟩) o h0 (hR r hr)
    rcases hk with h | ⟨a, ⟨hop, ha1, ha2⟩, h⟩
    · left
      exact h
    · right
      exact ⟨a, ⟨hop, ha1, r, hr, ha2⟩, h⟩
  · intro a ha hop
    obtain ⟨r2, hr2⟩ := hne
    refine ⟨hop, ?_, r2, hr2, ?_⟩
    · rw [← ha]
      exact h0
    · rw [← ha]
      exact hR r2 hr2
