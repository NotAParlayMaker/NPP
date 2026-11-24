import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1696
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

def ind {N : ℕ} (S : Finset (Fin N)) : Fin N → Bool := fun m => decide (m ∈ S)

def sg {N : ℕ} (l : Fin N) : Fin N → Bool := fun m => decide (m = l)

theorem ind_mono {N : ℕ} (S S' : Finset (Fin N)) (h : S ⊆ S') :
    ∀ v, ind S v = true → ind S' v = true := by
  intro v hv
  simp only [ind, decide_eq_true_eq] at hv ⊢
  exact h hv

def Own {N : ℕ} (gates : List Gate) (P : Fin N → Prop) (w : ℕ) : Prop :=
  (∀ d : Fin N, val gates w (sg d) = true → P d) ∧
    ∃ l l' : Fin N, l ≠ l' ∧ val gates w (sg l) = true ∧ val gates w (sg l') = true

def WitT {N : ℕ} (P : Fin N → Prop) (D : Finset (Fin N)) (T : (Fin N → Bool) → Prop) : Prop :=
  ∃ β : Fin N, ¬ P β ∧ T (ind (insert β D))

def BlkT {N : ℕ} (P : Fin N → Prop) (f : Fin N → ℕ) (T : (Fin N → Bool) → Prop) : Prop :=
  ∀ l l' : Fin N, P l → P l' → T (sg l) → T (sg l') → f l = f l'

def Inv {N : ℕ} (gates : List Gate) (P : Fin N → Prop) (PS : Finset (Fin N)) (q : ℕ)
    (K : Finset ℕ) (k : ℕ) : Prop :=
  ∃ (D : Finset (Fin N)) (f : Fin N → ℕ), (∀ d ∈ D, ¬ P d) ∧
    D.card + (q + 1) ≤ (K.filter (fun i => i < k)).card + (PS.image f).card ∧
    ∀ w, w < N + k → WitT P D (fun x => val gates w x = true) ∨
      BlkT P f (fun x => val gates w x = true)

theorem step {N : ℕ} (gates : List Gate) (P : Fin N → Prop) (PS : Finset (Fin N)) (q : ℕ)
    (K : Finset ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hK : ∀ i, i < gates.length → Own gates P (N + i) → i ∈ K)
    (k : ℕ) (hk : k < gates.length) (h : Inv gates P PS q K k) : Inv gates P PS q K (k + 1) := by
  obtain ⟨D, f, hD, hcnt, hw⟩ := h
  have legal' : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨(legal g hg).1, le_of_eq (legal g hg).2⟩
  have hmonoK : (K.filter (fun i => i < k)).card ≤ (K.filter (fun i => i < k + 1)).card := by
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, by omega⟩
  have keep : (WitT P D (fun x => val gates (N + k) x = true) ∨
      BlkT P f (fun x => val gates (N + k) x = true)) → Inv gates P PS q K (k + 1) := by
    intro hnew
    refine ⟨D, f, hD, le_trans hcnt (Nat.add_le_add_right hmonoK _), ?_⟩
    intro w hwlt
    by_cases e : w = N + k
    · rw [e]
      exact hnew
    · exact hw w (by omega)
  by_cases hA : ∀ d : Fin N, val gates (N + k) (sg d) = true → P d
  swap
  · have hex : ∃ d : Fin N, val gates (N + k) (sg d) = true ∧ ¬ P d := by
      by_contra hne
      apply hA
      intro d hd
      by_contra hPd
      exact hne ⟨d, hd, hPd⟩
    obtain ⟨d, hd, hPd⟩ := hex
    apply keep
    left
    refine ⟨d, hPd, ?_⟩
    exact val_mono gates legal' (sg d) (ind (insert d D)) (by
      intro v hv
      have e : v = d := of_decide_eq_true hv
      rw [e]
      simp [ind]) _ hd
  by_cases hB : ∃ l l' : Fin N, l ≠ l' ∧ val gates (N + k) (sg l) = true ∧
      val gates (N + k) (sg l') = true
  swap
  · apply keep
    right
    intro l l' _ _ h1 h2
    by_cases e : l = l'
    · rw [e]
    · exact absurd ⟨l, l', e, h1, h2⟩ hB
  have hkK : k ∈ K := hK k hk ⟨hA, hB⟩
  have hKs : (K.filter (fun i => i < k + 1)).card = (K.filter (fun i => i < k)).card + 1 := by
    have hins : K.filter (fun i => i < k + 1) = insert k (K.filter (fun i => i < k)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases e : i = k
        · exact Or.inl e
        · exact Or.inr ⟨h1, by omega⟩
      · rintro (e | ⟨h1, h2⟩)
        · rw [e]
          exact ⟨hkK, by omega⟩
        · exact ⟨h1, by omega⟩
    rw [hins, Finset.card_insert_of_notMem (by simp)]
  have hlen := (legal gates[k] (List.getElem_mem hk)).2
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, gates[k].inputs = [a, b] := by
    rcases hinp : gates[k].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
    · rw [hinp] at hlen
      simp at hlen
    · rw [hinp] at hlen
      simp at hlen
    · exact ⟨a, b, rfl⟩
    · rw [hinp] at hlen
      simp at hlen
  have child : ∀ a : ℕ, (∃ β : Fin N, ¬ P β ∧ a < N + k ∧ val gates a (ind (insert β D)) = true) ∨
      (∀ l l' : Fin N, P l → P l' → (a < N + k ∧ val gates a (sg l) = true) →
        (a < N + k ∧ val gates a (sg l') = true) → f l = f l') := by
    intro a
    by_cases ha : a < N + k
    · rcases hw a ha with ⟨β, hβ, hv⟩ | hb
      · exact Or.inl ⟨β, hβ, ha, hv⟩
      · exact Or.inr (fun l l' hl hl' h1 h2 => hb l l' hl hl' h1.2 h2.2)
    · exact Or.inr (fun l l' _ _ h1 _ => absurd h1.1 ha)
  rcases (legal gates[k] (List.getElem_mem hk)).1 with hand | hor
  · have hv : ∀ x : Fin N → Bool, val gates (N + k) x = true ↔
        (a < N + k ∧ val gates a x = true) ∧ (b < N + k ∧ val gates b x = true) := by
      intro x
      rw [val_and gates x k hk hand, hab]
      simp
    rcases child a with ⟨β1, hβ1, ha1, hv1⟩ | hba
    swap
    · apply keep
      right
      intro l l' hl hl' h1 h2
      exact hba l l' hl hl' ((hv _).1 h1).1 ((hv _).1 h2).1
    rcases child b with ⟨β2, hβ2, hb1, hv2⟩ | hbb
    swap
    · apply keep
      right
      intro l l' hl hl' h1 h2
      exact hbb l l' hl hl' ((hv _).1 h1).2 ((hv _).1 h2).2
    refine ⟨insert β2 D, f, ?_, ?_, ?_⟩
    · intro d hd
      rcases Finset.mem_insert.1 hd with e | hd'
      · rw [e]
        exact hβ2
      · exact hD d hd'
    · have hc : (insert β2 D).card ≤ D.card + 1 := Finset.card_insert_le _ _
      omega
    · intro w hwlt
      by_cases e : w = N + k
      · left
        refine ⟨β1, hβ1, ?_⟩
        rw [e]
        apply (hv _).2
        refine ⟨⟨ha1, ?_⟩, ⟨hb1, ?_⟩⟩
        · exact val_mono gates legal' _ _ (ind_mono _ _
            (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) a hv1
        · exact val_mono gates legal' _ _ (ind_mono _ _ (Finset.subset_insert _ _)) b hv2
      · rcases hw w (by omega) with ⟨β, hβ, hvβ⟩ | hb
        · left
          exact ⟨β, hβ, val_mono gates legal' _ _ (ind_mono _ _
            (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) w hvβ⟩
        · right
          exact hb
  · have hv : ∀ x : Fin N → Bool, val gates (N + k) x = true ↔
        (a < N + k ∧ val gates a x = true) ∨ (b < N + k ∧ val gates b x = true) := by
      intro x
      rw [val_or gates x k hk hor, hab]
      simp
    rcases child a with ⟨β1, hβ1, ha1, hv1⟩ | hba
    · apply keep
      left
      exact ⟨β1, hβ1, (hv _).2 (Or.inl ⟨ha1, hv1⟩)⟩
    rcases child b with ⟨β2, hβ2, hb1, hv2⟩ | hbb
    · apply keep
      left
      exact ⟨β2, hβ2, (hv _).2 (Or.inr ⟨hb1, hv2⟩)⟩
    by_cases hm : ∃ l1 l2 : Fin N, P l1 ∧ P l2 ∧ (a < N + k ∧ val gates a (sg l1) = true) ∧
        (b < N + k ∧ val gates b (sg l2) = true)
    swap
    · apply keep
      right
      intro l l' hl hl' h1 h2
      rcases (hv _).1 h1 with h1 | h1 <;> rcases (hv _).1 h2 with h2 | h2
      · exact hba l l' hl hl' h1 h2
      · exact absurd ⟨l, l', hl, hl', h1, h2⟩ hm
      · exact absurd ⟨l', l, hl', hl, h2, h1⟩ hm
      · exact hbb l l' hl hl' h1 h2
    obtain ⟨l1, l2, hl1, hl2, h1a, h2b⟩ := hm
    refine ⟨D, fun l => if f l = f l2 then f l1 else f l, hD, ?_, ?_⟩
    · have hsub : (PS.image f).erase (f l2) ⊆
          PS.image (fun l => if f l = f l2 then f l1 else f l) := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_image] at hx
        obtain ⟨hne, l, hl, rfl⟩ := hx
        rw [Finset.mem_image]
        exact ⟨l, hl, if_neg hne⟩
      have hc1 := Finset.card_le_card hsub
      have hc2 := Finset.pred_card_le_card_erase (s := PS.image f) (a := f l2)
      omega
    · have key : ∀ l, P l → val gates (N + k) (sg l) = true →
          (if f l = f l2 then f l1 else f l) = f l1 := by
        intro l hl h
        rcases (hv _).1 h with h | h
        · have e1 := hba l l1 hl hl1 h h1a
          rw [e1]
          split_ifs <;> rfl
        · have e2 := hbb l l2 hl hl2 h h2b
          rw [if_pos e2]
      intro w hwlt
      by_cases e : w = N + k
      · right
        rw [e]
        intro l l' hl hl' h1 h2
        show (if f l = f l2 then f l1 else f l) = (if f l' = f l2 then f l1 else f l')
        rw [key l hl h1, key l' hl' h2]
      · rcases hw w (by omega) with hwit | hb
        · left
          exact hwit
        · right
          intro l l' hl hl' h1 h2
          show (if f l = f l2 then f l1 else f l) = (if f l' = f l2 then f l1 else f l')
          rw [hb l l' hl hl' h1 h2]

theorem inv_all {N : ℕ} (gates : List Gate) (P : Fin N → Prop) (PS : Finset (Fin N)) (q : ℕ)
    (K : Finset ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hK : ∀ i, i < gates.length → Own gates P (N + i) → i ∈ K)
    (hPS : PS.card = q + 1) :
    ∀ k, k ≤ gates.length → Inv gates P PS q K k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨∅, fun l => l.val, by simp, ?_, ?_⟩
    · have hc : (PS.image (fun l : Fin N => l.val)).card = PS.card :=
        Finset.card_image_of_injective _ Fin.val_injective
      rw [hc, hPS]
      simp
    · intro w hwlt
      have hwN : w < N := by omega
      by_cases hP : P ⟨w, hwN⟩
      · right
        intro l l' _ _ h1 h2
        rw [val_input gates _ w hwN] at h1 h2
        have e1 : (⟨w, hwN⟩ : Fin N) = l := of_decide_eq_true h1
        have e2 : (⟨w, hwN⟩ : Fin N) = l' := of_decide_eq_true h2
        rw [← e1, ← e2]
      · left
        refine ⟨⟨w, hwN⟩, hP, ?_⟩
        show val gates w (ind (insert ⟨w, hwN⟩ ∅)) = true
        rw [val_input gates _ w hwN]
        simp [ind]
  | succ k ih =>
    intro hk
    exact step gates P PS q K legal hK k hk (ih (by omega))

open Classical in
noncomputable def KK {N : ℕ} (gates : List Gate) (P : Fin N → Prop) : Finset ℕ :=
  (Finset.range gates.length).filter (fun i => Own gates P (N + i))

open Classical in
theorem mem_KK {N : ℕ} (gates : List Gate) (P : Fin N → Prop) (i : ℕ) :
    i ∈ KK gates P ↔ i < gates.length ∧ Own gates P (N + i) := by
  unfold KK
  rw [Finset.mem_filter, Finset.mem_range]

theorem point {N : ℕ} (gates : List Gate) (P : Fin N → Prop) [DecidablePred P] (q : ℕ) (cp : ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hcard : (Finset.univ.filter (fun l : Fin N => P l)).card = q + 1)
    (htrue : ∀ l : Fin N, P l → val gates cp (sg l) = true)
    (hsound : ∀ y : Fin N → Bool, (Finset.univ.filter (fun m : Fin N => y m = true)).card ≤ q →
      (∀ l : Fin N, P l → y l = false) → val gates cp y = false) :
    q ≤ (KK gates P).card := by
  obtain ⟨D, f, hD, hcnt, hw⟩ := inv_all gates P (Finset.univ.filter (fun l : Fin N => P l)) q
    (KK gates P) legal (fun i hi ho => (mem_KK gates P i).2 ⟨hi, ho⟩) hcard gates.length le_rfl
  have hne : (Finset.univ.filter (fun l : Fin N => P l)).Nonempty :=
    Finset.card_pos.1 (by omega)
  obtain ⟨l0, hl0⟩ := hne
  have hPl0 : P l0 := (Finset.mem_filter.1 hl0).2
  have hlt : cp < N + gates.length := by
    by_contra h
    have hb := val_big gates (sg l0) cp (by omega)
    rw [htrue l0 hPl0] at hb
    exact Bool.noConfusion hb
  have hKle : ((KK gates P).filter (fun i => i < gates.length)).card ≤ (KK gates P).card :=
    Finset.card_filter_le _ _
  have hi0 : ((Finset.univ.filter (fun l : Fin N => P l)).image f).card
      ≤ (Finset.univ.filter (fun l : Fin N => P l)).card := Finset.card_image_le
  rcases hw cp hlt with ⟨β, hβ, hv⟩ | hb
  · have hs : ¬ (insert β D).card ≤ q := by
      intro hle
      have e : Finset.univ.filter (fun m : Fin N => ind (insert β D) m = true) = insert β D := by
        ext m
        simp [ind]
      have hfalse := hsound (ind (insert β D)) (by rw [e]; exact hle) (by
        intro l hl
        simp only [ind, decide_eq_false_iff_not, Finset.mem_insert, not_or]
        exact ⟨fun e => hβ (e ▸ hl), fun h => hD l h hl⟩)
      rw [hfalse] at hv
      exact Bool.noConfusion hv
    have hc : (insert β D).card ≤ D.card + 1 := Finset.card_insert_le _ _
    omega
  · have hi : ((Finset.univ.filter (fun l : Fin N => P l)).image f).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨l', hl', rfl⟩ := hy
      have h1 := (Finset.mem_filter.1 hl).2
      have h2 := (Finset.mem_filter.1 hl').2
      exact hb l l' h1 h2 (htrue l h1) (htrue l' h2)
    omega

theorem final (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (c : Fin N → ℕ)
    (hcard : ∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hleg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (htrue : ∀ p l : Fin N,
      (C.wires (List.ofFn (fun m : Fin N => decide (m = l)))).getD (c p) false = true ↔ I p l)
    (hsound : ∀ (p : Fin N) (y : Fin N → Bool),
      (Finset.univ.filter (fun m : Fin N => y m = true)).card ≤ q →
      (∀ l : Fin N, I p l → y l = false) → (C.wires (List.ofFn y)).getD (c p) false = false) :
    N * q ≤ C.size := by
  have hq : ∀ p : Fin N, q ≤ (KK C.gates (I p)).card := fun p =>
    point C.gates (I p) q (c p) hleg (hcard p) (fun l hl => (htrue p l).2 hl) (hsound p)
  have hdisj : ∀ p p' : Fin N, p ≠ p' → Disjoint (KK C.gates (I p)) (KK C.gates (I p')) := by
    intro p p' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨hA, l, l', hll, h1, h2⟩ := ((mem_KK C.gates (I p) i).1 hi).2
    obtain ⟨hA', _⟩ := ((mem_KK C.gates (I p') i).1 hi').2
    obtain ⟨m, _, hm⟩ := huniq p p' hne
    exact hll ((hm l ⟨hA l h1, hA' l h1⟩).trans (hm l' ⟨hA l' h2, hA' l' h2⟩).symm)
  have hsub : (Finset.univ.biUnion (fun p : Fin N => KK C.gates (I p)))
      ⊆ Finset.range C.gates.length := by
    intro i hi
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hi
    exact Finset.mem_range.2 ((mem_KK C.gates (I p) i).1 hp).1
  have hcardU := Finset.card_biUnion (s := (Finset.univ : Finset (Fin N)))
    (t := fun p : Fin N => KK C.gates (I p)) (fun p _ p' _ hne => hdisj p p' hne)
  have h1 := Finset.card_le_card hsub
  rw [hcardU, Finset.card_range] at h1
  have h2 : ∑ _p : Fin N, q ≤ ∑ p : Fin N, (KK C.gates (I p)).card :=
    Finset.sum_le_sum (fun p _ => hq p)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  exact le_trans h2 h1

end PEqualNP.Outside.L_meta_1696

theorem PEqualNP.Outside.L_meta_1696 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : Fin N → ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p l : Fin N, (C.wires (List.ofFn (fun m : Fin N => decide (m = l)))).getD (c p) false = true ↔ I p l) → (∀ (p : Fin N) (y : Fin N → Bool), (Finset.univ.filter (fun m : Fin N => y m = true)).card ≤ q → (∀ l : Fin N, I p l → y l = false) → (C.wires (List.ofFn y)).getD (c p) false = false) → N * q ≤ C.size := by
  intro q N I _ C c _ _ h3 h4 h5 h6 h7
  exact PEqualNP.Outside.L_meta_1696.final q N I C c h3 h4 h5 h6 h7
