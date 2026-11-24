import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572
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

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

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

theorem eval_val (gates : List Gate) (o : ℕ) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = val gates o x := by
  rw [eval_eq]; rfl

theorem mono (gates : List Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin 13 → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, val gates w x = true → val gates w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hw : w < 13
    · rw [val_input gates x w hw] at hx
      rw [val_input gates y w hw]
      exact hxy ⟨w, hw⟩ hx
    · by_cases hbig : 13 + gates.length ≤ w
      · rw [val_big gates x w hbig] at hx
        exact Bool.noConfusion hx
      · have hk : w - 13 < gates.length := by omega
        have hwk : w = 13 + (w - 13) := by omega
        let k : Fin gates.length := ⟨w - 13, hk⟩
        have hkval : k.val = w - 13 := rfl
        have hmem : gates[k.val] ∈ gates := by
          rw [← List.get_eq_getElem]
          exact List.get_mem gates k
        rcases (hleg _ hmem).1 with hop | hop
        · rw [hwk] at hx
          have hall := (val_and gates x k.val hk hop).1 hx
          rw [hwk]
          apply (val_and gates y k.val hk hop).2
          intro i hi
          rcases hall i hi with ⟨hlt, hix⟩
          rw [hkval] at hlt
          exact ⟨by omega, ih i (by omega) hix⟩
        · rw [hwk] at hx
          obtain ⟨i, hi, hlt, hix⟩ := (val_or gates x k.val hk hop).1 hx
          rw [hwk]
          rw [hkval] at hlt
          exact (val_or gates y k.val hk hop).2 ⟨i, hi, by omega, ih i (by omega) hix⟩

def Forced (gates : List Gate) (g w : ℕ) : Prop :=
  ∀ S : Set ℕ, g ∈ S →
    (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) →
    w ∈ S

theorem forced_input (gates : List Gate) (g : ℕ) (i : Fin gates.length)
    (hw : Forced gates g (13 + (i : ℕ))) (hop : (gates.get i).op = GateOp.or)
    (a : ℕ) (ha : a ∈ (gates.get i).inputs) : Forced gates g a := by
  intro S hgS hcl
  exact hcl i (hw S hgS hcl) hop a ha

theorem forced_false (gates : List Gate)
    (hwell : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (gout : ℕ) (x : Fin 13 → Bool) (hg : val gates gout x = false)
    (w : ℕ) (hw : Forced gates gout w) : val gates w x = false := by
  classical
  let S : Set ℕ := { t | val gates t x = false }
  have hgS : gout ∈ S := hg
  have hcl : ∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S := by
    intro i hiS hop a ha
    have hgate : val gates (13 + (i : ℕ)) x = false := hiS
    have hlt : a < 13 + (i : ℕ) := hwell i a ha
    have hop' : gates[i.val].op = GateOp.or := by
      rw [← List.get_eq_getElem]
      exact hop
    cases hva : val gates a x with
    | false => exact hva
    | true =>
      exfalso
      have ha' : a ∈ gates[i.val].inputs := by
        rw [← List.get_eq_getElem]
        exact ha
      have htrue := (val_or gates x i.val i.isLt hop').2 ⟨a, ha', hlt, hva⟩
      rw [hgate] at htrue
      exact Bool.noConfusion htrue
  exact hw S hgS hcl

theorem descend (gates : List Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (gout : ℕ) (x : Fin 13 → Bool) (w : ℕ) (hw : Forced gates gout w)
    (hx : val gates w x = true) :
    ∃ Y, Forced gates gout Y ∧ val gates Y x = true ∧
      (Y < 13 ∨ ∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) := by
  classical
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw13 : w < 13
    · exact ⟨w, hw, hx, Or.inl hw13⟩
    · by_cases hbig : 13 + gates.length ≤ w
      · rw [val_big gates x w hbig] at hx
        exact Bool.noConfusion hx
      · have hk : w - 13 < gates.length := by omega
        have hwk : w = 13 + (w - 13) := by omega
        let k : Fin gates.length := ⟨w - 13, hk⟩
        have hkval : k.val = w - 13 := rfl
        have hmem : gates[k.val] ∈ gates := by
          rw [← List.get_eq_getElem]
          exact List.get_mem gates k
        rcases (hleg _ hmem).1 with hop | hop
        · have hop' : (gates.get k).op = GateOp.and := by
            rw [List.get_eq_getElem]
            exact hop
          exact ⟨w, hw, hx, Or.inr ⟨k, by rw [hkval]; exact hwk, hop'⟩⟩
        · rw [hwk] at hx
          have hop' : (gates.get k).op = GateOp.or := by
            rw [List.get_eq_getElem]
            exact hop
          obtain ⟨a, ha, hlt, hax⟩ := (val_or gates x k.val hk hop).1 hx
          have ha' : a ∈ (gates.get k).inputs := by
            rw [List.get_eq_getElem]
            exact ha
          have hw' : Forced gates gout (13 + k.val) := by
            rw [hkval, ← hwk]
            exact hw
          have hFa : Forced gates gout a := forced_input gates gout k hw' hop' a ha'
          rw [hkval] at hlt
          obtain ⟨Y, hY, hYv, hkind⟩ := ih a (by omega) hFa hax
          exact ⟨Y, hY, hYv, hkind⟩

theorem zero_off_m : ∀ m : Fin 13, m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (0 : Fin 13) ∉ ({m, m + 1, m + 3, m + 9} : Finset (Fin 13)) := by
  decide

theorem one_off_l : ∀ l : Fin 13, l ∈ ({4, 10, 12} : Finset (Fin 13)) →
    (1 : Fin 13) ∉ ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)) := by
  decide

end PEqualNP.Outside.L_meta_1572

open PEqualNP.Outside.L_meta_1572 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  classical
  intro L hL gates g l m c hleg hwell hl hm hint hfL hfM
  have hwell' : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ) :=
    fun i => (hwell i).2
  have h0m : (0 : Fin 13) ∉ L m := by rw [hL m]; exact zero_off_m m hm
  have h1l : (1 : Fin 13) ∉ L l := by rw [hL l]; exact one_off_l l hl
  have hcL : c ∈ L l := by
    have hc : c ∈ L l ∩ L m := by simp [hint]
    exact (Finset.mem_inter.mp hc).1
  have hcM : c ∈ L m := by
    have hc : c ∈ L l ∩ L m := by simp [hint]
    exact (Finset.mem_inter.mp hc).2
  have hc0 : c ≠ 0 := fun h => h0m (h ▸ hcM)
  have hc1 : c ≠ 1 := fun h => h1l (h ▸ hcL)
  have hfLv : val gates g (fun v : Fin 13 => decide (v ∉ L l)) = false := by
    rw [← eval_val]; exact hfL
  have hfMv : val gates g (fun v : Fin 13 => decide (v ∉ L m)) = false := by
    rw [← eval_val]; exact hfM
  constructor
  · intro hcard
    let F := (L l).filter (fun p => Circuit.eval ⟨gates, g⟩
      (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)
    have h0out : (0 : Fin 13) ∉ F := by
      intro h0
      have hev : Circuit.eval ⟨gates, g⟩
          (List.ofFn (fun v : Fin 13 => decide (v = 0 ∨ ((0 : Fin 13) ≠ 0 ∧ v = 1)))) = true :=
        (Finset.mem_filter.mp h0).2
      let x0 : Fin 13 → Bool := fun v => decide (v = 0 ∨ ((0 : Fin 13) ≠ 0 ∧ v = 1))
      let xm : Fin 13 → Bool := fun v => decide (v ∉ L m)
      have hxy : ∀ v, x0 v = true → xm v = true := by
        intro v hv
        have hv' : v = 0 ∨ ((0 : Fin 13) ≠ 0 ∧ v = 1) := by simpa [x0, decide_eq_true_eq] using hv
        rcases hv' with hv0 | hv0
        · subst hv0
          simpa [xm, decide_eq_true_eq] using h0m
        · exact (hv0.1 rfl).elim
      have hx0 : val gates g x0 = true := by
        unfold x0
        rw [← eval_val]
        exact hev
      have hxm : val gates g xm = false := by
        unfold xm
        exact hfMv
      have := mono gates hleg x0 xm hxy g hx0
      rw [hxm] at this
      exact Bool.noConfusion this
    have hex : ∃ p ∈ F, p ≠ c := by
      by_contra h
      have hsub : F ⊆ ({c} : Finset (Fin 13)) := by
        intro p hp
        have hpeq : p = c := by
          by_contra hne
          exact h ⟨p, hp, hne⟩
        exact Finset.mem_singleton.mpr hpeq
      have hle : F.card ≤ 1 := by
        have := Finset.card_le_card hsub
        simp at this
        exact this
      have hcardF : 2 ≤ F.card := hcard
      omega
    obtain ⟨p, hpF, hpc⟩ := hex
    have hp0 : p ≠ 0 := fun e => h0out (e ▸ hpF)
    have hpL : p ∈ L l := (Finset.mem_filter.mp hpF).1
    have hev : Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true :=
      (Finset.mem_filter.mp hpF).2
    let x : Fin 13 → Bool := fun v => decide (v = p ∨ (p ≠ 0 ∧ v = 1))
    have hx : val gates g x = true := by
      unfold x
      rw [← eval_val]
      exact hev
    have hFg : Forced gates g g := fun _ hgS _ => hgS
    obtain ⟨Y, hYF, hYv, hkind⟩ := descend gates hleg g x g hFg hx
    rcases hkind with hYin | ⟨i, hiY, hop⟩
    · exfalso
      have hxY : x ⟨Y, hYin⟩ = true := by rw [← val_input gates x Y hYin]; exact hYv
      have hYL : (⟨Y, hYin⟩ : Fin 13) ∈ L l := by
        have hf : val gates Y (fun v : Fin 13 => decide (v ∉ L l)) = false :=
          forced_false gates hwell' g _ hfLv Y hYF
        rw [val_input gates (fun v : Fin 13 => decide (v ∉ L l)) Y hYin] at hf
        rw [decide_eq_false_iff_not] at hf
        exact not_not.mp hf
      have hYM : (⟨Y, hYin⟩ : Fin 13) ∈ L m := by
        have hf : val gates Y (fun v : Fin 13 => decide (v ∉ L m)) = false :=
          forced_false gates hwell' g _ hfMv Y hYF
        rw [val_input gates (fun v : Fin 13 => decide (v ∉ L m)) Y hYin] at hf
        rw [decide_eq_false_iff_not] at hf
        exact not_not.mp hf
      have hYc : (⟨Y, hYin⟩ : Fin 13) = c := by
        have : (⟨Y, hYin⟩ : Fin 13) ∈ L l ∩ L m := Finset.mem_inter.mpr ⟨hYL, hYM⟩
        rw [hint] at this
        exact Finset.mem_singleton.mp this
      have hbit : decide (c = p ∨ (p ≠ 0 ∧ c = 1)) = false := by
        rw [decide_eq_false_iff_not]
        intro h
        rcases h with h | h
        · exact hpc h.symm
        · exact hc1 h.2
      rw [hYc] at hxY
      simp only [x, hbit] at hxY
      exact Bool.noConfusion hxY
    · refine ⟨Y, hYF, ⟨i, hiY, hop⟩, p, hpL, hp0, hpc, ?_⟩
      unfold x at hYv
      rw [← eval_val] at hYv
      exact hYv
  · intro hcard
    let F := (L m).filter (fun p => Circuit.eval ⟨gates, g⟩
      (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)
    have h1out : (1 : Fin 13) ∉ F := by
      intro h1
      have hev : Circuit.eval ⟨gates, g⟩
          (List.ofFn (fun v : Fin 13 => decide (v = 1 ∨ ((1 : Fin 13) ≠ 1 ∧ v = 0)))) = true :=
        (Finset.mem_filter.mp h1).2
      let x1 : Fin 13 → Bool := fun v => decide (v = 1 ∨ ((1 : Fin 13) ≠ 1 ∧ v = 0))
      let xl : Fin 13 → Bool := fun v => decide (v ∉ L l)
      have hxy : ∀ v, x1 v = true → xl v = true := by
        intro v hv
        have hv' : v = 1 ∨ ((1 : Fin 13) ≠ 1 ∧ v = 0) := by simpa [x1, decide_eq_true_eq] using hv
        rcases hv' with hv1 | hv1
        · subst hv1
          simpa [xl, decide_eq_true_eq] using h1l
        · exact (hv1.1 rfl).elim
      have hx1 : val gates g x1 = true := by
        unfold x1
        rw [← eval_val]
        exact hev
      have hxl : val gates g xl = false := by
        unfold xl
        exact hfLv
      have := mono gates hleg x1 xl hxy g hx1
      rw [hxl] at this
      exact Bool.noConfusion this
    have hex : ∃ p ∈ F, p ≠ c := by
      by_contra h
      have hsub : F ⊆ ({c} : Finset (Fin 13)) := by
        intro p hp
        have hpeq : p = c := by
          by_contra hne
          exact h ⟨p, hp, hne⟩
        exact Finset.mem_singleton.mpr hpeq
      have hle : F.card ≤ 1 := by
        have := Finset.card_le_card hsub
        simp at this
        exact this
      have hcardF : 2 ≤ F.card := hcard
      omega
    obtain ⟨p, hpF, hpc⟩ := hex
    have hp1 : p ≠ 1 := fun e => h1out (e ▸ hpF)
    have hpM : p ∈ L m := (Finset.mem_filter.mp hpF).1
    have hev : Circuit.eval ⟨gates, g⟩
        (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true :=
      (Finset.mem_filter.mp hpF).2
    let x : Fin 13 → Bool := fun v => decide (v = p ∨ (p ≠ 1 ∧ v = 0))
    have hx : val gates g x = true := by
      unfold x
      rw [← eval_val]
      exact hev
    have hFg : Forced gates g g := fun _ hgS _ => hgS
    obtain ⟨Y, hYF, hYv, hkind⟩ := descend gates hleg g x g hFg hx
    rcases hkind with hYin | ⟨i, hiY, hop⟩
    · exfalso
      have hxY : x ⟨Y, hYin⟩ = true := by rw [← val_input gates x Y hYin]; exact hYv
      have hYL : (⟨Y, hYin⟩ : Fin 13) ∈ L l := by
        have hf : val gates Y (fun v : Fin 13 => decide (v ∉ L l)) = false :=
          forced_false gates hwell' g _ hfLv Y hYF
        rw [val_input gates (fun v : Fin 13 => decide (v ∉ L l)) Y hYin] at hf
        rw [decide_eq_false_iff_not] at hf
        exact not_not.mp hf
      have hYM : (⟨Y, hYin⟩ : Fin 13) ∈ L m := by
        have hf : val gates Y (fun v : Fin 13 => decide (v ∉ L m)) = false :=
          forced_false gates hwell' g _ hfMv Y hYF
        rw [val_input gates (fun v : Fin 13 => decide (v ∉ L m)) Y hYin] at hf
        rw [decide_eq_false_iff_not] at hf
        exact not_not.mp hf
      have hYc : (⟨Y, hYin⟩ : Fin 13) = c := by
        have : (⟨Y, hYin⟩ : Fin 13) ∈ L l ∩ L m := Finset.mem_inter.mpr ⟨hYL, hYM⟩
        rw [hint] at this
        exact Finset.mem_singleton.mp this
      have hbit : decide (c = p ∨ (p ≠ 1 ∧ c = 0)) = false := by
        rw [decide_eq_false_iff_not]
        intro h
        rcases h with h | h
        · exact hpc h.symm
        · exact hc0 h.2
      rw [hYc] at hxY
      simp only [x, hbit] at hxY
      exact Bool.noConfusion hxY
    · refine ⟨Y, hYF, ⟨i, hiY, hop⟩, p, hpM, hp1, hpc, ?_⟩
      unfold x at hYv
      rw [← eval_val] at hYv
      exact hYv
