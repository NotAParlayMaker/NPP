import Mathlib
import PEqualNP.Defs

-- The component count adapts L-meta-1512, and monotonicity follows L-meta-1521.
namespace PEqualNP.Outside.L_meta_1525_aux
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

/-- The value of wire `w` on input `x`. -/
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

/-- Collapsing one colour loses at most one colour. -/
theorem merge_card {n : ℕ} (A : Finset (Fin n)) (c : Fin n → Fin n) (x y : Fin n) :
    (A.image c).card ≤ (A.image fun p => if c p = y then x else c p).card + 1 := by
  classical
  have h1 : ((A.image c).erase y) ⊆ A.image fun p => if c p = y then x else c p := by
    intro v hv
    rw [Finset.mem_erase] at hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv.2
    exact Finset.mem_image.2 ⟨p, hp, by simp [hv.1]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := A.image c) (a := y)
  omega

theorem two_list (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = [a, b] ∨ l = [b, a] := by
  match l, hl with
  | [], _ => simp at ha
  | [u], _ =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [u, v], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hab

theorem main (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hAM : A ⊆ M) (htau : ∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p)
    (I : Finset (Fin gates.length))
    (hI : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
        val gates (n + (g : ℕ)) (fun v : Fin n => decide (v ∉ M)) = false ∧
        ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          val gates (n + g.val) (tau p) = true ∧ val gates (n + g.val) (tau p') = true) → g ∈ I) :
    ∀ k, k ≤ gates.length → ∃ c : Fin n → Fin n,
      A.card ≤ (A.image c).card + (I.filter fun g => g.val < k).card ∧
      ∀ w < n + k, val gates w (fun v : Fin n => decide (v ∉ M)) = false →
        ∀ p ∈ A, ∀ p' ∈ A, val gates w (tau p) = true → val gates w (tau p') = true →
          c p = c p' := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, by simp, ?_⟩
    intro w hw hz p hp p' hp' h1 h2
    have hw' : w < n := by omega
    rw [val_input gates _ w hw'] at hz h1 h2
    have hM : (⟨w, hw'⟩ : Fin n) ∈ M := by simpa using hz
    have e1 := (htau p hp _ hM).1 h1
    have e2 := (htau p' hp' _ hM).1 h2
    exact e1.symm.trans e2
  | succ k ih =>
    intro hk
    have hk' : k < gates.length := hk
    obtain ⟨c, hcard, hc⟩ := ih (Nat.le_of_lt hk')
    have hmono : (I.filter fun g => g.val < k).card ≤ (I.filter fun g => g.val < k + 1).card :=
      Finset.card_le_card (fun g hg => by
        rw [Finset.mem_filter] at hg ⊢; exact ⟨hg.1, by omega⟩)
    -- the old colouring works whenever the new wire needs nothing new
    have keep : (val gates (n + k) (fun v : Fin n => decide (v ∉ M)) = false →
        ∀ p ∈ A, ∀ p' ∈ A, val gates (n + k) (tau p) = true → val gates (n + k) (tau p') = true →
          c p = c p') →
        ∃ c : Fin n → Fin n,
          A.card ≤ (A.image c).card + (I.filter fun g => g.val < k + 1).card ∧
          ∀ w < n + (k + 1), val gates w (fun v : Fin n => decide (v ∉ M)) = false →
            ∀ p ∈ A, ∀ p' ∈ A, val gates w (tau p) = true → val gates w (tau p') = true →
              c p = c p' := by
      intro hnew
      refine ⟨c, by omega, ?_⟩
      intro w hw hz p hp p' hp' h1 h2
      by_cases hwk : w = n + k
      · subst hwk; exact hnew hz p hp p' hp' h1 h2
      · exact hc w (by omega) hz p hp p' hp' h1 h2
    have hlegk := hleg gates[k] (List.getElem_mem hk')
    rcases hlegk.1 with hop | hop
    · -- an AND gate false off M has an input false off M
      apply keep
      intro hz p hp p' hp' h1 h2
      have hz' : ¬ ∀ i ∈ gates[k].inputs, i < n + k ∧
          val gates i (fun v : Fin n => decide (v ∉ M)) = true := by
        intro h; rw [(val_and gates _ k hk' hop).2 h] at hz; exact absurd hz (by simp)
      push Not at hz'
      obtain ⟨i, hi, hiz⟩ := hz'
      have a1 := (val_and gates (tau p) k hk' hop).1 h1 i hi
      have a2 := (val_and gates (tau p') k hk' hop).1 h2 i hi
      have hzi : val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
        simpa using hiz a1.1
      exact hc i a1.1 hzi p hp p' hp' a1.2 a2.2
    · -- an OR gate
      by_cases hkI : (⟨k, hk'⟩ : Fin gates.length) ∈ I
      · -- a gate of `I`: merge two colours if needed
        by_cases hsame : val gates (n + k) (fun v : Fin n => decide (v ∉ M)) = false →
            ∀ p ∈ A, ∀ p' ∈ A, val gates (n + k) (tau p) = true →
              val gates (n + k) (tau p') = true → c p = c p'
        · exact keep hsame
        · push Not at hsame
          obtain ⟨hz, a, ha, b, hb, hva, hvb, hne⟩ := hsame
          obtain ⟨ia, hia, hia1, hia2⟩ := (val_or gates (tau a) k hk' hop).1 hva
          obtain ⟨ib, hib, hib1, hib2⟩ := (val_or gates (tau b) k hk' hop).1 hvb
          have hzall : ∀ i ∈ gates[k].inputs, i < n + k →
              val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
            intro i hi hlt
            by_contra hcon
            have : val gates i (fun v : Fin n => decide (v ∉ M)) = true := by simpa using hcon
            rw [(val_or gates _ k hk' hop).2 ⟨i, hi, hlt, this⟩] at hz
            exact absurd hz (by simp)
          have hiab : ia ≠ ib := by
            intro h; subst h
            exact hne (hc ia hia1 (hzall ia hia hia1) a ha b hb hia2 hib2)
          have hcount : (I.filter fun g => g.val < k).card + 1 ≤
              (I.filter fun g => g.val < k + 1).card := by
            have hsub : insert (⟨k, hk'⟩ : Fin gates.length) (I.filter fun g => g.val < k) ⊆
                I.filter fun g => g.val < k + 1 := by
              intro g hg
              rw [Finset.mem_insert] at hg
              rcases hg with rfl | hg
              · exact Finset.mem_filter.2 ⟨hkI, by simp⟩
              · rw [Finset.mem_filter] at hg ⊢; exact ⟨hg.1, by omega⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem (by simp)] at this
            exact this
          refine ⟨fun p => if c p = c b then c a else c p, ?_, ?_⟩
          · have := merge_card A c (c a) (c b)
            omega
          · intro w hw hzw p hp p' hp' h1 h2
            by_cases hwk : w = n + k
            · subst hwk
              have col : ∀ q ∈ A, val gates (n + k) (tau q) = true → c q = c a ∨ c q = c b := by
                intro q hq hvq
                obtain ⟨iq, hiq, hiq1, hiq2⟩ := (val_or gates (tau q) k hk' hop).1 hvq
                rcases two_list _ hlegk.2 ia ib hia hib hiab with hl | hl
                · rw [hl] at hiq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiq
                  rcases hiq with rfl | rfl
                  · exact Or.inl (hc _ hiq1 (hzall _ hia hiq1) q hq a ha hiq2 hia2)
                  · exact Or.inr (hc _ hiq1 (hzall _ hib hiq1) q hq b hb hiq2 hib2)
                · rw [hl] at hiq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiq
                  rcases hiq with rfl | rfl
                  · exact Or.inr (hc _ hiq1 (hzall _ hib hiq1) q hq b hb hiq2 hib2)
                  · exact Or.inl (hc _ hiq1 (hzall _ hia hiq1) q hq a ha hiq2 hia2)
              have fin : ∀ q ∈ A, val gates (n + k) (tau q) = true →
                  (if c q = c b then c a else c q) = c a := by
                intro q hq hvq
                rcases col q hq hvq with h | h
                · rw [h]; split_ifs <;> rfl
                · rw [ite_eq_left h]
              show (if c p = c b then c a else c p) = (if c p' = c b then c a else c p')
              rw [fin p hp h1, fin p' hp' h2]
            · have := hc w (by omega) hzw p hp p' hp' h1 h2
              show (if c p = c b then c a else c p) = (if c p' = c b then c a else c p')
              rw [this]
      · -- not in `I`: the gate does not join two different points
        apply keep
        intro hz p hp p' hp' h1 h2
        obtain ⟨ia, hia, hia1, hia2⟩ := (val_or gates (tau p) k hk' hop).1 h1
        obtain ⟨ib, hib, hib1, hib2⟩ := (val_or gates (tau p') k hk' hop).1 h2
        have hzall : ∀ i ∈ gates[k].inputs, i < n + k →
            val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
          intro i hi hlt
          by_contra hcon
          have : val gates i (fun v : Fin n => decide (v ∉ M)) = true := by simpa using hcon
          rw [(val_or gates _ k hk' hop).2 ⟨i, hi, hlt, this⟩] at hz
          exact absurd hz (by simp)
        by_cases hiab : ia = ib
        · subst hiab
          exact hc ia hia1 (hzall ia hia hia1) p hp p' hp' hia2 hib2
        · by_contra hcne
          have hpp : p ≠ p' := fun h => hcne (by rw [h])
          apply hkI
          apply hI ⟨k, hk'⟩
          exact ⟨hop, hz, p, hp, p', hp', hpp, h1, h2⟩

theorem cover : ∀ (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    A ⊆ M →
    (∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    (∀ p ∈ A, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (tau p)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          val gates (n + g.val) (tau p) = true ∧ val gates (n + g.val) (tau p') = true) → g ∈ I) →
      A.card ≤ 1 + I.card := by
  classical
  intro n M A tau gates o hleg hAM htau hout htrue I hI
  obtain ⟨c, hcard, hc⟩ := main n M A tau gates hleg hAM htau I hI gates.length le_rfl
  have hJ : (I.filter fun g => g.val < gates.length).card ≤ I.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rcases A.eq_empty_or_nonempty with hA | ⟨p0, hp0⟩
  · subst hA; simp
  · have ho : o < n + gates.length := by
      by_contra hcon
      have := htrue p0 hp0
      rw [eval_eq] at this
      have h2 := val_big gates (tau p0) o (by omega)
      rw [val] at h2
      rw [h2] at this
      exact absurd this (by simp)
    have hconst : ∀ p ∈ A, c p = c p0 := fun p hp =>
      hc o ho hout p hp p0 hp0 (htrue p hp) (htrue p0 hp0)
    have himg : (A.image c).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [hconst p hp, hconst q hq]
    omega

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


abbrev Point := Fin 13
abbrev Job := Point × Bool

def line (s : Point) : Finset Point := {s, s + 1, s + 3, s + 9}
def anchors : Finset Point := {0, 1, 3}
def anchor (i : Job) : Point :=
  if i.2 then (![0,3,1,1,3,3,1,1,1,1,3,3,3] : Point → Point) i.1
  else (![0,0,0,0,1,0,0,0,0,0,1,0,1] : Point → Point) i.1

lemma geometry : (∀ s : Point, (line s).card = 4) ∧
    (∀ s t : Point, s ≠ t → (line s ∩ line t).card ≤ 1) ∧
    (∀ i : Job, i.1 ≠ 0 → anchor i ∈ anchors ∧ anchor i ∉ line i.1) ∧
    anchors ⊆ line 0 := by decide +kernel

def candidates (full : Bool) (i : Job) := if i.1 = 0 ∧ full = false then anchors else line i.1
def outside (s : Point) (v : Point) := decide (v ∉ line s)
def tag (i : Job) (p v : Point) := decide (v = p ∨ (i.1 ≠ 0 ∧ v = anchor i))

def fits (i j : Job) : Prop := i.1 = j.1 ∨ (i.1 ≠ 0 ∧ anchor i ∈ line j.1)

lemma no_three : ∀ i j k : Job, i ≠ j → i ≠ k → j ≠ k →
    fits i j → fits i k → fits j i → fits j k → fits k i → ¬ fits k j := by
  unfold fits
  decide +kernel

def legal (gs : List Gate) := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def charged (gs : List Gate) (full : Bool) (i : Job) (g : Fin gs.length) : Prop :=
  (gs.get g).op = GateOp.or ∧ val gs (13 + g.val) (outside i.1) = false ∧
  ∃ p ∈ candidates full i, ∃ q ∈ candidates full i, p ≠ q ∧
    val gs (13 + g.val) (tag i p) = true ∧ val gs (13 + g.val) (tag i q) = true

lemma cand_sub (full : Bool) (i : Job) : candidates full i ⊆ line i.1 := by
  unfold candidates
  split
  next h => rw [h.1]; exact geometry.2.2.2
  next => rfl

lemma tag_line (i : Job) (p v : Point) (hv : v ∈ line i.1) :
    tag i p v = true ↔ v = p := by
  simp only [tag, decide_eq_true_eq]
  refine ⟨?_, Or.inl⟩
  rintro (h | ⟨h, e⟩)
  · exact h
  · exact ((geometry.2.2.1 i h).2 (e ▸ hv)).elim

lemma compatible {gs : List Gate} (hg : legal gs) {full : Bool} {i j : Job} {g : Fin gs.length}
    (h : charged gs full i g) (h' : charged gs full j g) : fits i j := by
  by_contra hbad
  have hne : i.1 ≠ j.1 := fun e => hbad (Or.inl e)
  obtain ⟨_, _, p, hp, q, hq, hdiff, h1, h2⟩ := h
  have force (v : Point) (hy : val gs (13 + g.val) (tag i v) = true) : v ∈ line j.1 := by
    by_contra hv
    have imp (u : Point) (hu : tag i v u = true) : outside j.1 u = true := by
      apply decide_eq_true
      rcases of_decide_eq_true hu with e | ⟨hne0, e⟩
      · simpa [e] using hv
      · exact fun hh => hbad (Or.inr ⟨hne0, e ▸ hh⟩)
    have hy' := mono2 gs hg _ _ (by simp) (ofFn_mono _ _ _ imp) (13 + g.val) hy
    change val gs (13 + g.val) (outside j.1) = true at hy'
    rw [h'.2.1] at hy'
    contradiction
  have lim := Finset.card_le_one.mp (geometry.2.1 _ _ hne)
  exact hdiff (lim p (Finset.mem_inter.mpr ⟨cand_sub _ _ hp, force _ h1⟩)
    q (Finset.mem_inter.mpr ⟨cand_sub _ _ hq, force _ h2⟩))

open Classical in
lemma capacity {gs : List Gate} (hg : legal gs) (full : Bool) (g : Fin gs.length) :
    (Finset.univ.filter (fun i : Job => charged gs full i g)).card ≤
      (if (gs.get g).op = GateOp.or then 2 else 0) := by
  split
  · by_contra! h
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp h
    have ai := (Finset.mem_filter.mp hi).2
    have aj := (Finset.mem_filter.mp hj).2
    have ak := (Finset.mem_filter.mp hk).2
    exact no_three i j k hij hik hjk (compatible hg ai aj) (compatible hg ai ak)
      (compatible hg aj ai) (compatible hg aj ak) (compatible hg ak ai) (compatible hg ak aj)
  next hn =>
    have h : (Finset.univ.filter (fun i : Job => charged gs full i g)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hn (Finset.mem_filter.mp hi).2.1
    simp [h]

def domain (x : Point → Bool) := (∃ a ∈ anchors, x a = true) ∨
  ∃ s : Point, ∀ v, x v = false → v ∈ line s

def correct (gs : List Gate) (o : Point → ℕ) := ∀ s x, domain x →
  val gs (o s) x = decide (∃ p ∈ line s, x p = true)

lemma outside_domain (s : Point) : domain (outside s) := by
  right
  exact ⟨s, fun p hp => by simpa [outside] using hp⟩

lemma row_neg {gs : List Gate} {o} (hc : correct gs o) (s : Point) :
    val gs (o s) (outside s) = false := by
  rw [hc _ _ (outside_domain s)]
  simp [outside]

def join (x y : Point → Bool) (p : Point) := x p || y p

lemma or_join (gs : List Gate) (hor : ∀ g ∈ gs, g.op = GateOp.or) (x y : Point → Bool) :
    ∀ w, val gs w (join x y) = (val gs w x || val gs w y) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    by_cases h : w < 13
    · rw [val_input _ _ _ h, val_input _ _ _ h, val_input _ _ _ h]; rfl
    · have h' : 13 + ([] : List Gate).length ≤ w := by simp; omega
      rw [val_big _ _ _ h', val_big _ _ _ h', val_big _ _ _ h']; rfl
  | append_singleton gs g ih =>
    have ho := hor g (by simp)
    have hprev := ih (fun f hf => hor f (by simp [hf]))
    intro w
    by_cases hn : w = 13 + gs.length
    · subst w
      simp only [val, wf_snoc]
      rw [show 13 + gs.length = (wf gs (List.ofFn (join x y))).length by simp [wf_len],
        getD_snoc_eq]
      rw [show (wf gs (List.ofFn (join x y))).length = (wf gs (List.ofFn x)).length by simp [wf_len],
        getD_snoc_eq]
      rw [show (wf gs (List.ofFn x)).length = (wf gs (List.ofFn y)).length by simp [wf_len],
        getD_snoc_eq]
      rw [ho]
      apply Bool.eq_iff_iff.mpr
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, Bool.or_eq_true]
      constructor
      · rintro ⟨_, ⟨i, hi, rfl⟩, hv⟩
        change val gs i (join x y) = true at hv
        rw [hprev] at hv
        simp only [Bool.or_eq_true] at hv
        rcases hv with a | b
        · exact Or.inl ⟨_, ⟨i, hi, rfl⟩, a⟩
        · exact Or.inr ⟨_, ⟨i, hi, rfl⟩, b⟩
      · rintro (⟨_, ⟨i, hi, rfl⟩, hv⟩ | ⟨_, ⟨i, hi, rfl⟩, hv⟩)
        · exact ⟨_, ⟨i, hi, rfl⟩, (hprev i).trans (by simp [show val gs i x = true from hv])⟩
        · exact ⟨_, ⟨i, hi, rfl⟩, (hprev i).trans (by simp [show val gs i y = true from hv])⟩
    · have keep (u : Point → Bool) : val (gs ++ [g]) w u = val gs w u := by
        change (wf (gs ++ [g]) (List.ofFn u)).getD w false = _
        rw [wf_snoc]
        by_cases h : w < 13 + gs.length
        · exact getD_snoc_lt _ _ _ (by simpa [wf_len] using h)
        · rw [getD_snoc_gt _ _ _ (by simp [wf_len]; omega), val_big _ _ _ (by omega)]
      rw [keep, keep, keep, hprev]

lemma row_pos {gs : List Gate} {o} (hc : correct gs o) (full : Bool)
    (hf : full = true → ∀ g ∈ gs, g.op = GateOp.or) (i : Job) (p : Point)
    (hp : p ∈ candidates full i) : val gs (o i.1) (tag i p) = true := by
  have hline := cand_sub _ _ hp
  have hptrue : tag i p p = true := by simp [tag]
  by_cases hd : domain (tag i p)
  · rw [hc _ _ hd]
    exact decide_eq_true ⟨p, hline, hptrue⟩
  · have hi : i.1 = 0 := by
      by_contra hi
      exact hd (Or.inl ⟨anchor i, (geometry.2.2.1 i hi).1, by simp [tag, hi]⟩)
    have hfull : full = true := by
      cases h : full with
      | true => rfl
      | false =>
        have ha : p ∈ anchors := by simpa [candidates, hi, h] using hp
        exact (hd (Or.inl ⟨p, ha, hptrue⟩)).elim
    let x := join (outside i.1) (tag i p)
    have hdom : domain x := by
      right
      refine ⟨i.1, fun v hv => ?_⟩
      by_contra hnot
      simp [x, join, outside, hnot] at hv
    have hh := hc i.1 x hdom
    have hp' : x p = true := by simp [x, join, hptrue]
    rw [show decide (∃ v ∈ line i.1, x v = true) = true from decide_eq_true ⟨p, hline, hp'⟩] at hh
    change val gs (o i.1) (join (outside i.1) (tag i p)) = true at hh
    rwa [or_join gs (hf hfull), row_neg hc, Bool.false_or] at hh

open Classical in
lemma total (gs : List Gate) (o : Point → ℕ) (hg : legal gs) (hc : correct gs o)
    (full : Bool) (hf : full = true → ∀ g ∈ gs, g.op = GateOp.or) :
    (∑ i : Job, ((candidates full i).card - 1)) ≤
      2 * (Finset.univ.filter (fun g : Fin gs.length => (gs.get g).op = GateOp.or)).card := by
  classical
  let rel := charged gs full
  have per (i : Job) : (candidates full i).card - 1 ≤
        (Finset.univ.filter fun g => rel i g).card := by
    have h := cover 13 (line i.1) (candidates full i) (tag i) gs (o i.1) hg
      (cand_sub _ _) (fun p _ v hv => tag_line i p v hv) (row_neg hc _) (row_pos hc full hf i)
      (Finset.univ.filter fun g => rel i g) (fun g h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  calc
    _ ≤ ∑ i : Job, (Finset.univ.filter fun g => rel i g).card := Finset.sum_le_sum fun i _ => per i
    _ = ∑ g : Fin gs.length, (Finset.univ.filter fun i : Job => rel i g).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ g : Fin gs.length, (if (gs.get g).op = GateOp.or then 2 else 0) :=
      Finset.sum_le_sum fun g _ => capacity hg full g
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]

lemma totals : (∑ i : Job, ((candidates true i).card - 1)) = 78 ∧
    (∑ i : Job, ((candidates false i).card - 1)) = 76 := by decide +kernel

lemma finish (gs : List Gate) (o : Point → ℕ) (hg : legal gs) (hc : correct gs o) :
    39 ≤ gs.length := by
  classical
  let O := Finset.univ.filter fun g : Fin gs.length => (gs.get g).op = GateOp.or
  by_cases h : ∀ g ∈ gs, g.op = GateOp.or
  · have q := total gs o hg hc true (fun _ => h)
    rw [totals.1] at q
    have ub : O.card ≤ gs.length := by simpa [O] using (Finset.card_le_univ O)
    change 78 ≤ 2 * O.card at q
    omega
  · have q := total gs o hg hc false (by simp)
    rw [totals.2] at q
    push Not at h
    obtain ⟨g, hmem, hn⟩ := h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
    have absent : (⟨j, hj⟩ : Fin gs.length) ∉ O := fun h => hn (Finset.mem_filter.mp h).2
    have strict : O ⊂ Finset.univ :=
      Finset.ssubset_univ_iff.mpr fun heq => absent (heq ▸ Finset.mem_univ _)
    have ub : O.card < gs.length := by simpa using Finset.card_lt_card strict
    change 76 ≤ 2 * O.card at q
    omega

end PEqualNP.Outside.L_meta_1525_aux

theorem PEqualNP.Outside.L_meta_1525 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    39 ≤ gates.length := by
  intro L hL gs o hg hc
  apply PEqualNP.Outside.L_meta_1525_aux.finish gs o hg
  intro s x hx
  rw [← show L s = PEqualNP.Outside.L_meta_1525_aux.line s from hL s]
  apply hc
  rcases hx with h | ⟨t, ht⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, fun v hv => hL t ▸ ht v hv⟩
