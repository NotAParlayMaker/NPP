import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5636

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def evalW {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl stepWire (List.ofFn x)).getD w false

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (stepWire w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false)
      else false := by
  unfold stepWire
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma evalW_append_lt {n : ℕ} (gs : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length)
    (x : Fin n → Bool) : evalW (gs ++ [g]) w x = evalW gs w x := by
  unfold evalW
  have hl := foldl_len gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [step_getD, hl, if_pos hw]

lemma evalW_append_eq {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    evalW (gs ++ [g]) (n + gs.length) x = g.op.eval (g.inputs.map fun k => evalW gs k x) := by
  unfold evalW
  have hl := foldl_len gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [step_getD, hl, if_neg (Nat.lt_irrefl _), if_pos rfl]

lemma evalW_ge_false {n : ℕ} (gs : List Gate) (w : ℕ) (hw : n + gs.length ≤ w) (x : Fin n → Bool) :
    evalW gs w x = false := by
  unfold evalW
  have hl := foldl_len gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma op_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ (l1 l2 : List Bool), List.Forall₂ (fun a b => a = true → b = true) l1 l2 →
      op.eval l1 = true → op.eval l2 = true := by
  intro l1 l2 hrel
  rcases hop with rfl | rfl
  · induction hrel with
    | nil => intro h; exact h
    | cons hhd htl ih =>
      simp only [GateOp.eval, List.all_cons, Bool.and_eq_true]
      rintro ⟨h1, h2⟩
      exact ⟨hhd h1, ih h2⟩
  · induction hrel with
    | nil => intro h; exact h
    | cons hhd htl ih =>
      simp only [GateOp.eval, List.any_cons, Bool.or_eq_true]
      rintro (h1 | h2)
      · exact Or.inl (hhd h1)
      · exact Or.inr (ih h2)

lemma map_forall2 {α : Type*} (f g : α → Bool) (l : List α)
    (h : ∀ a ∈ l, f a = true → g a = true) :
    List.Forall₂ (fun a b => a = true → b = true) (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih =>
    exact List.Forall₂.cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

def MonoDep {n : ℕ} (gs : List Gate) (W : Finset ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = true → y i = true) →
    ∀ w ∈ W, evalW gs w x = true → evalW gs w y = true

lemma monoDep_mono_S {n : ℕ} {gs : List Gate} {W : Finset ℕ} {S1 S2 : Finset (Fin n)}
    (hsub : S1 ⊆ S2) (h : MonoDep gs W S1) : MonoDep gs W S2 :=
  fun x y hxy => h x y (fun i hi => hxy i (hsub hi))

lemma monoDep_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (W W' : Finset ℕ) (S : Finset (Fin n))
    (hlow : ∀ w ∈ W, w < n + gs.length → w ∈ W')
    (hin : n + gs.length ∈ W → ∀ k ∈ g.inputs, k ∈ W')
    (hval : MonoDep gs W' S) :
    MonoDep (gs ++ [g]) W S := by
  intro x y hxy w hw htrue
  by_cases hlt : w < n + gs.length
  · rw [evalW_append_lt gs g w hlt] at htrue ⊢
    exact hval x y hxy w (hlow w hw hlt) htrue
  · by_cases heq : w = n + gs.length
    · subst heq
      rw [evalW_append_eq] at htrue ⊢
      refine op_eval_mono g.op hg _ _ ?_ htrue
      exact map_forall2 _ _ g.inputs (fun k hk => hval x y hxy k (hin hw k hk))
    · have hge : n + (gs ++ [g]).length ≤ w := by simp; omega
      rw [evalW_ge_false (gs ++ [g]) w hge] at htrue
      exact False.elim (Bool.false_ne_true htrue)

lemma mono_core (n : ℕ) (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ W : Finset ℕ, ∃ S : Finset (Fin n), S.card ≤ W.card + gs.length ∧ MonoDep gs W S := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro W
    refine ⟨Finset.univ.filter (fun i : Fin n => i.val ∈ W), ?_, ?_⟩
    · simp only [List.length_nil, add_zero]
      apply Finset.card_le_card_of_injOn (fun i => i.val)
      · intro i hi; simpa using hi
      · intro i _ j _ h; exact Fin.ext h
    · intro x y hxy w hw hval
      unfold evalW at hval ⊢
      simp only [List.foldl_nil, List.getD_eq_getElem?_getD] at hval ⊢
      by_cases hwn : w < n
      · have hx : (List.ofFn x)[w]? = some (x ⟨w, hwn⟩) := by
          rw [List.getElem?_eq_getElem (by simpa using hwn)]; simp
        have hy : (List.ofFn y)[w]? = some (y ⟨w, hwn⟩) := by
          rw [List.getElem?_eq_getElem (by simpa using hwn)]; simp
        rw [hx] at hval; rw [hy]
        simp only [Option.getD_some] at hval ⊢
        exact hxy ⟨w, hwn⟩ (by simp [hw]) hval
      · rw [List.getElem?_eq_none (by simp; omega)] at hval
        simp at hval
  | append_singleton gs g ih =>
    intro W
    have hmono' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (by simp [hg'])
    have hg := hmono g (by simp)
    by_cases hin : n + gs.length ∈ W
    · obtain ⟨S, hS, hval⟩ := ih hmono' (W.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨S, ?_, monoDep_step gs g hg.1 W _ S ?_ ?_ hval⟩
      · have h1 : (W.erase (n + gs.length) ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_erase_of_mem hin]
          have := List.toFinset_card_le g.inputs
          omega
        have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, hin⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · intro w hw hlt
        simp only [Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨by omega, hw⟩
      · intro _ k hk; simp [hk]
    · obtain ⟨S, hS, hval⟩ := ih hmono' W
      refine ⟨S, ?_, monoDep_step gs g hg.1 W W S (fun _ hw _ => hw) (fun h => absurd h hin) hval⟩
      simp only [List.length_append, List.length_singleton]
      omega

def Tight {n : ℕ} (gs : List Gate) (W : Finset ℕ) : Prop :=
  ∀ S : Finset (Fin n), MonoDep gs W S → W.card + gs.length ≤ S.card

def SplitsOnce {n : ℕ} (gs : List Gate) (w : ℕ) (S : Finset (Fin n)) : Prop :=
  ∃ (op : GateOp) (a b : ℕ) (Sa Sb : Finset (Fin n)),
    (op = GateOp.and ∨ op = GateOp.or) ∧
    a < n + gs.length ∧ b < n + gs.length ∧
    Sa.Nonempty ∧ Sb.Nonempty ∧ Disjoint Sa Sb ∧ Sa ∪ Sb = S ∧
    MonoDep gs {a} Sa ∧ MonoDep gs {b} Sb ∧
    (∀ x : Fin n → Bool, evalW gs w x = op.eval [evalW gs a x, evalW gs b x])

def SplitsTwice {n : ℕ} (gs : List Gate) (w : ℕ) (S : Finset (Fin n)) : Prop :=
  1 < S.card →
  ∃ (op : GateOp) (a b : ℕ) (Sa Sb : Finset (Fin n)),
    (op = GateOp.and ∨ op = GateOp.or) ∧
    a < n + gs.length ∧ b < n + gs.length ∧
    Sa.Nonempty ∧ Sb.Nonempty ∧ Disjoint Sa Sb ∧ Sa ∪ Sb = S ∧
    MonoDep gs {a} Sa ∧ MonoDep gs {b} Sb ∧
    (∀ x : Fin n → Bool, evalW gs w x = op.eval [evalW gs a x, evalW gs b x]) ∧
    (1 < Sa.card → SplitsOnce gs a Sa) ∧
    (1 < Sb.card → SplitsOnce gs b Sb)

lemma splitsOnce_append {n : ℕ} (gs : List Gate) (g : Gate) (w : ℕ) (S : Finset (Fin n))
    (hw : w < n + gs.length) (h : SplitsOnce gs w S) : SplitsOnce (gs ++ [g]) w S := by
  obtain ⟨op, a, b, Sa, Sb, hop, ha, hb, hSa, hSb, hdisj, hunion, hda, hdb, hev⟩ := h
  refine ⟨op, a, b, Sa, Sb, hop, by simp; omega, by simp; omega, hSa, hSb, hdisj, hunion, ?_, ?_, ?_⟩
  · intro x y hxy u hu htr
    rw [Finset.mem_singleton.mp hu] at htr ⊢
    rw [evalW_append_lt gs g a ha] at htr ⊢
    exact hda x y hxy a (by simp) htr
  · intro x y hxy u hu htr
    rw [Finset.mem_singleton.mp hu] at htr ⊢
    rw [evalW_append_lt gs g b hb] at htr ⊢
    exact hdb x y hxy b (by simp) htr
  · intro x
    rw [evalW_append_lt gs g w hw, evalW_append_lt gs g a ha, evalW_append_lt gs g b hb]
    exact hev x

lemma splitsTwice_append {n : ℕ} (gs : List Gate) (g : Gate) (w : ℕ) (S : Finset (Fin n))
    (hw : w < n + gs.length) (h : SplitsTwice gs w S) : SplitsTwice (gs ++ [g]) w S := by
  intro hlt
  obtain ⟨op, a, b, Sa, Sb, hop, ha, hb, hSa, hSb, hdisj, hunion, hda, hdb, hev, hsa, hsb⟩ := h hlt
  refine ⟨op, a, b, Sa, Sb, hop, by simp; omega, by simp; omega, hSa, hSb, hdisj, hunion, ?_, ?_, ?_,
    fun h1 => splitsOnce_append gs g a Sa ha (hsa h1),
    fun h1 => splitsOnce_append gs g b Sb hb (hsb h1)⟩
  · intro x y hxy u hu htr
    rw [Finset.mem_singleton.mp hu] at htr ⊢
    rw [evalW_append_lt gs g a ha] at htr ⊢
    exact hda x y hxy a (by simp) htr
  · intro x y hxy u hu htr
    rw [Finset.mem_singleton.mp hu] at htr ⊢
    rw [evalW_append_lt gs g b hb] at htr ⊢
    exact hdb x y hxy b (by simp) htr
  · intro x
    rw [evalW_append_lt gs g w hw, evalW_append_lt gs g a ha, evalW_append_lt gs g b hb]
    exact hev x

lemma tight_lt_len {n : ℕ} (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset ℕ) (ht : Tight (n := n) gs W) : ∀ w ∈ W, w < n + gs.length := by
  intro w hw
  by_contra hge
  push_neg at hge
  obtain ⟨S, hS, hdep⟩ := mono_core n gs hmono (W.erase w)
  have hdepW : MonoDep gs W S := by
    intro x y hxy u hu htr
    by_cases huw : u = w
    · subst huw
      rw [evalW_ge_false gs u hge] at htr
      exact False.elim (Bool.false_ne_true htr)
    · exact hdep x y hxy u (Finset.mem_erase.mpr ⟨huw, hu⟩) htr
  have h1 := ht S hdepW
  have h2 := Finset.card_erase_of_mem hw
  have hpos : 0 < W.card := Finset.card_pos.mpr ⟨w, hw⟩
  omega

lemma mono_tight_tree (n : ℕ) (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ W : Finset ℕ, Tight (n := n) gs W →
      ∃ F : ℕ → Finset (Fin n),
        (∀ w ∈ W, MonoDep gs {w} (F w)) ∧
        (∀ w ∈ W, (F w).Nonempty) ∧
        (∀ w1 ∈ W, ∀ w2 ∈ W, w1 ≠ w2 → Disjoint (F w1) (F w2)) ∧
        (∀ w ∈ W, 1 < (F w).card → SplitsOnce gs w (F w)) ∧
        (∀ w ∈ W, SplitsTwice gs w (F w)) ∧
        (W.biUnion F).card = W.card + gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro W ht
    have hlt := tight_lt_len [] hmono W ht
    refine ⟨fun w => if hw : w < n then {⟨w, hw⟩} else ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw x y hxy u hu htr
      rw [Finset.mem_singleton.mp hu] at htr ⊢
      have hwn : w < n := by simpa using hlt w hw
      unfold evalW at htr ⊢
      simp only [List.foldl_nil, List.getD_eq_getElem?_getD] at htr ⊢
      have hx : (List.ofFn x)[w]? = some (x ⟨w, hwn⟩) := by
        rw [List.getElem?_eq_getElem (by simpa using hwn)]; simp
      have hy : (List.ofFn y)[w]? = some (y ⟨w, hwn⟩) := by
        rw [List.getElem?_eq_getElem (by simpa using hwn)]; simp
      rw [hx] at htr; rw [hy]
      simp only [Option.getD_some] at htr ⊢
      exact hxy ⟨w, hwn⟩ (by simp [hwn]) htr
    · intro w hw
      have hwn : w < n := by simpa using hlt w hw
      simp [hwn]
    · intro w1 hw1 w2 hw2 hne
      have h1 : w1 < n := by simpa using hlt w1 hw1
      have h2 : w2 < n := by simpa using hlt w2 hw2
      simp only [h1, h2, ↓reduceDIte, Finset.disjoint_singleton]
      intro e
      exact hne (congrArg Fin.val e)
    · intro w hw hcard
      have hwn : w < n := by simpa using hlt w hw
      simp [hwn] at hcard
    · intro w hw hcard
      have hwn : w < n := by simpa using hlt w hw
      simp [hwn] at hcard
    · simp only [List.length_nil, add_zero]
      rw [Finset.card_biUnion]
      · have hsum : ∀ w ∈ W, (if hw : w < n then ({⟨w, hw⟩} : Finset (Fin n)) else ∅).card = 1 := by
          intro w hw
          have hwn : w < n := by simpa using hlt w hw
          simp [hwn]
        rw [Finset.sum_congr rfl hsum]
        simp
      · intro w1 hw1 w2 hw2 hne
        have h1 : w1 < n := by simpa using hlt w1 hw1
        have h2 : w2 < n := by simpa using hlt w2 hw2
        dsimp only [Function.onFun]
        simp only [h1, h2, ↓reduceDIte, Finset.disjoint_singleton]
        intro e
        exact hne (congrArg Fin.val e)
  | append_singleton gs g ih =>
    intro W ht
    have hmono' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (by simp [hg'])
    have hg := hmono g (by simp)
    have htop_mem : n + gs.length ∈ W := by
      by_contra hnot
      obtain ⟨S, hS, hdep⟩ := mono_core n gs hmono' W
      have hdep' : MonoDep (gs ++ [g]) W S :=
        monoDep_step gs g hg.1 W W S (fun _ hw _ => hw) (fun h => absurd h hnot) hdep
      have h1 := ht S hdep'
      simp only [List.length_append, List.length_singleton] at h1
      omega
    set W' : Finset ℕ := W.erase (n + gs.length) ∪ g.inputs.toFinset
    have hstepW : ∀ S : Finset (Fin n), MonoDep gs W' S → MonoDep (gs ++ [g]) W S := by
      intro S hdep
      refine monoDep_step gs g hg.1 W W' S ?_ ?_ hdep
      · intro w hw hlt
        simp only [W', Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨by omega, hw⟩
      · intro _ k hk
        simp only [W', Finset.mem_union, List.mem_toFinset]
        exact Or.inr hk
    have hW'_card : W'.card = W.card + 1 := by
      obtain ⟨S, hS, hdep⟩ := mono_core n gs hmono' W'
      have h1 := ht S (hstepW S hdep)
      simp only [List.length_append, List.length_singleton] at h1
      have h2 : W'.card ≤ (W.erase (n + gs.length)).card + g.inputs.toFinset.card :=
        Finset.card_union_le _ _
      have h3 := Finset.card_erase_of_mem htop_mem
      have h4 := List.toFinset_card_le g.inputs
      have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, htop_mem⟩
      omega
    have ht' : Tight (n := n) gs W' := by
      intro S hdep
      have h1 := ht S (hstepW S hdep)
      simp only [List.length_append, List.length_singleton] at h1
      omega
    have hgin_len : g.inputs.length = 2 := by
      have h2 : W'.card ≤ (W.erase (n + gs.length)).card + g.inputs.toFinset.card :=
        Finset.card_union_le _ _
      have h3 := Finset.card_erase_of_mem htop_mem
      have h4 := List.toFinset_card_le g.inputs
      have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, htop_mem⟩
      omega
    obtain ⟨a, b, hab_eq⟩ : ∃ a b, g.inputs = [a, b] := by
      cases hgi : g.inputs with
      | nil => simp [hgi] at hgin_len
      | cons a t =>
        cases t with
        | nil => simp [hgi] at hgin_len
        | cons b t2 =>
          cases t2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => simp [hgi] at hgin_len
    have hab_ne : a ≠ b := by
      intro e
      subst e
      have h2 : W'.card ≤ (W.erase (n + gs.length)).card + g.inputs.toFinset.card :=
        Finset.card_union_le _ _
      have h3 := Finset.card_erase_of_mem htop_mem
      have h4 : g.inputs.toFinset.card = 1 := by simp [hab_eq]
      have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, htop_mem⟩
      omega
    have ha_not : a ∉ W.erase (n + gs.length) := by
      intro ha
      have hsub : W' ⊆ W.erase (n + gs.length) ∪ {b} := by
        intro x hx
        simp only [W', hab_eq, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with hx | rfl | rfl
        · exact Or.inl hx
        · exact Or.inl ha
        · exact Or.inr rfl
      have h2 := Finset.card_le_card hsub
      have h3 := Finset.card_union_le (W.erase (n + gs.length)) {b}
      have h4 := Finset.card_erase_of_mem htop_mem
      have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, htop_mem⟩
      simp only [Finset.card_singleton] at h3
      omega
    have hb_not : b ∉ W.erase (n + gs.length) := by
      intro hb
      have hsub : W' ⊆ W.erase (n + gs.length) ∪ {a} := by
        intro x hx
        simp only [W', hab_eq, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with hx | rfl | rfl
        · exact Or.inl hx
        · exact Or.inr rfl
        · exact Or.inl hb
      have h2 := Finset.card_le_card hsub
      have h3 := Finset.card_union_le (W.erase (n + gs.length)) {a}
      have h4 := Finset.card_erase_of_mem htop_mem
      have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, htop_mem⟩
      simp only [Finset.card_singleton] at h3
      omega
    obtain ⟨F', hFdep, hFne, hFdisj, hFonce, hFtwice, hFcard⟩ := ih hmono' W' ht'
    have hW'_lt := tight_lt_len gs hmono' W' ht'
    have ha_mem : a ∈ W' := by simp [W', hab_eq]
    have hb_mem : b ∈ W' := by simp [W', hab_eq]
    have ha_lt : a < n + gs.length := hW'_lt a ha_mem
    have hb_lt : b < n + gs.length := hW'_lt b hb_mem
    have hdep_a : MonoDep (gs ++ [g]) {a} (F' a) := by
      intro x y hxy u hu htr
      rw [Finset.mem_singleton.mp hu] at htr ⊢
      rw [evalW_append_lt gs g a ha_lt] at htr ⊢
      exact hFdep a ha_mem x y hxy a (by simp) htr
    have hdep_b : MonoDep (gs ++ [g]) {b} (F' b) := by
      intro x y hxy u hu htr
      rw [Finset.mem_singleton.mp hu] at htr ⊢
      rw [evalW_append_lt gs g b hb_lt] at htr ⊢
      exact hFdep b hb_mem x y hxy b (by simp) htr
    have hev_top : ∀ x : Fin n → Bool,
        evalW (gs ++ [g]) (n + gs.length) x =
          g.op.eval [evalW (gs ++ [g]) a x, evalW (gs ++ [g]) b x] := by
      intro x
      rw [evalW_append_eq, hab_eq, evalW_append_lt gs g a ha_lt, evalW_append_lt gs g b hb_lt]
      rfl
    refine ⟨fun w => if w = n + gs.length then F' a ∪ F' b else F' w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      by_cases hwe : w = n + gs.length
      · subst hwe
        simp only [↓reduceIte]
        intro x y hxy u hu htr
        rw [Finset.mem_singleton.mp hu] at htr ⊢
        rw [hev_top] at htr ⊢
        refine op_eval_mono g.op hg.1 _ _ ?_ htr
        exact List.Forall₂.cons
          (hdep_a x y (fun i hi => hxy i (Finset.mem_union_left _ hi)) a (by simp))
          (List.Forall₂.cons
            (hdep_b x y (fun i hi => hxy i (Finset.mem_union_right _ hi)) b (by simp))
            List.Forall₂.nil)
      · simp only [hwe, ↓reduceIte]
        have hw' : w ∈ W' := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwe, hw⟩)
        have hwlt : w < n + gs.length := hW'_lt w hw'
        intro x y hxy u hu htr
        rw [Finset.mem_singleton.mp hu] at htr ⊢
        rw [evalW_append_lt gs g w hwlt] at htr ⊢
        exact hFdep w hw' x y hxy w (by simp) htr
    · intro w hw
      by_cases hwe : w = n + gs.length
      · simp [hwe, (hFne a ha_mem).mono Finset.subset_union_left]
      · simp [hwe, hFne w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwe, hw⟩))]
    · intro w1 hw1 w2 hw2 hne
      by_cases h1 : w1 = n + gs.length
      · subst h1
        have h2 : w2 ≠ n + gs.length := hne.symm
        simp only [h2, ↓reduceIte]
        have hw2e : w2 ∈ W.erase (n + gs.length) := Finset.mem_erase.mpr ⟨h2, hw2⟩
        have hw2' : w2 ∈ W' := Finset.mem_union_left _ hw2e
        exact Finset.disjoint_union_left.mpr
          ⟨hFdisj a ha_mem w2 hw2' (fun e => ha_not (e ▸ hw2e)),
           hFdisj b hb_mem w2 hw2' (fun e => hb_not (e ▸ hw2e))⟩
      · by_cases h2 : w2 = n + gs.length
        · subst h2
          simp only [h1, ↓reduceIte]
          have hw1e : w1 ∈ W.erase (n + gs.length) := Finset.mem_erase.mpr ⟨h1, hw1⟩
          have hw1' : w1 ∈ W' := Finset.mem_union_left _ hw1e
          exact Finset.disjoint_union_right.mpr
            ⟨hFdisj w1 hw1' a ha_mem (fun e => ha_not (e ▸ hw1e)),
             hFdisj w1 hw1' b hb_mem (fun e => hb_not (e ▸ hw1e))⟩
        · simp only [h1, h2, ↓reduceIte]
          exact hFdisj w1 (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h1, hw1⟩))
            w2 (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h2, hw2⟩)) hne
    · intro w hw hcard
      by_cases hwe : w = n + gs.length
      · subst hwe
        simp only [↓reduceIte]
        exact ⟨g.op, a, b, F' a, F' b, hg.1, by simp; omega, by simp; omega,
          hFne a ha_mem, hFne b hb_mem, hFdisj a ha_mem b hb_mem hab_ne, rfl,
          hdep_a, hdep_b, hev_top⟩
      · simp only [hwe, ↓reduceIte] at hcard ⊢
        have hw' : w ∈ W' := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwe, hw⟩)
        exact splitsOnce_append gs g w (F' w) (hW'_lt w hw') (hFonce w hw' hcard)
    · intro w hw hcard
      by_cases hwe : w = n + gs.length
      · subst hwe
        simp only [↓reduceIte]
        exact ⟨g.op, a, b, F' a, F' b, hg.1, by simp; omega, by simp; omega,
          hFne a ha_mem, hFne b hb_mem, hFdisj a ha_mem b hb_mem hab_ne, rfl,
          hdep_a, hdep_b, hev_top,
          fun h1 => splitsOnce_append gs g a (F' a) ha_lt (hFonce a ha_mem h1),
          fun h1 => splitsOnce_append gs g b (F' b) hb_lt (hFonce b hb_mem h1)⟩
      · simp only [hwe, ↓reduceIte] at hcard ⊢
        have hw' : w ∈ W' := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwe, hw⟩)
        exact splitsTwice_append gs g w (F' w) (hW'_lt w hw') (hFtwice w hw') hcard
    · have hbiu : W.biUnion (fun w => if w = n + gs.length then F' a ∪ F' b else F' w) =
          W'.biUnion F' := by
        ext i
        simp only [Finset.mem_biUnion]
        constructor
        · rintro ⟨w, hw, hi⟩
          by_cases hwe : w = n + gs.length
          · subst hwe
            simp only [↓reduceIte, Finset.mem_union] at hi
            rcases hi with ha | hb
            · exact ⟨a, ha_mem, ha⟩
            · exact ⟨b, hb_mem, hb⟩
          · simp only [hwe, ↓reduceIte] at hi
            exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwe, hw⟩), hi⟩
        · rintro ⟨w, hw, hi⟩
          simp only [W', hab_eq, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
            Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with ⟨hne, hwm⟩ | rfl | rfl
          · exact ⟨w, hwm, by simp [hne, hi]⟩
          · exact ⟨n + gs.length, htop_mem, by simp [hi]⟩
          · exact ⟨n + gs.length, htop_mem, by simp [hi]⟩
      rw [hbiu, hFcard, hW'_card]
      simp only [List.length_append, List.length_singleton]
      omega

def oneEachFn (u v : Fin 4) : Fin 8 → Bool :=
  fun i => decide (i.val = u.val ∨ i.val = 4 + v.val)

lemma ofFn_oneEachFn (u v : Fin 4) : List.ofFn (oneEachFn u v) = oneEach u v := by
  revert u v; decide

def E6 : Finset (Fin 8) := {0, 1, 2, 4, 5, 6}
def E5 : Finset (Fin 8) := {1, 2, 4, 5, 6}

lemma need_six (S : Finset (Fin 8))
    (h : ∀ u v u' v' : Fin 4,
      (∀ i ∈ S, oneEachFn u v i = true → oneEachFn u' v' i = true) →
      (895 : ℕ).testBit (4 * u.val + v.val) = true →
      (895 : ℕ).testBit (4 * u'.val + v'.val) = true) :
    E6 ⊆ S := by
  have d0 : ∀ i : Fin 8, i ≠ 0 → oneEachFn 0 3 i = true → oneEachFn 3 3 i = true := by decide
  have d1 : ∀ i : Fin 8, i ≠ 1 → oneEachFn 1 2 i = true → oneEachFn 3 2 i = true := by decide
  have d2 : ∀ i : Fin 8, i ≠ 2 → oneEachFn 2 0 i = true → oneEachFn 3 0 i = true := by decide
  have d4 : ∀ i : Fin 8, i ≠ 4 → oneEachFn 2 0 i = true → oneEachFn 2 2 i = true := by decide
  have d5 : ∀ i : Fin 8, i ≠ 5 → oneEachFn 2 1 i = true → oneEachFn 2 2 i = true := by decide
  have d6 : ∀ i : Fin 8, i ≠ 6 → oneEachFn 1 2 i = true → oneEachFn 1 3 i = true := by decide
  have h0 : (0 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 0 3 3 3 (fun i hi h1 => d0 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h1 : (1 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 1 2 3 2 (fun i hi h1 => d1 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h2 : (2 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 2 0 3 0 (fun i hi h1 => d2 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h4 : (4 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 2 0 2 2 (fun i hi h1 => d4 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h5 : (5 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 2 1 2 2 (fun i hi h1 => d5 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h6 : (6 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 1 2 1 3 (fun i hi h1 => d6 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  intro i hi
  simp only [E6, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

lemma need_five (S : Finset (Fin 8))
    (h : ∀ u v u' v' : Fin 4, u ≠ 0 → u' ≠ 0 →
      (∀ i ∈ S, oneEachFn u v i = true → oneEachFn u' v' i = true) →
      (895 : ℕ).testBit (4 * u.val + v.val) = true →
      (895 : ℕ).testBit (4 * u'.val + v'.val) = true) :
    E5 ⊆ S := by
  have d1 : ∀ i : Fin 8, i ≠ 1 → oneEachFn 1 2 i = true → oneEachFn 3 2 i = true := by decide
  have d2 : ∀ i : Fin 8, i ≠ 2 → oneEachFn 2 0 i = true → oneEachFn 3 0 i = true := by decide
  have d4 : ∀ i : Fin 8, i ≠ 4 → oneEachFn 2 0 i = true → oneEachFn 2 2 i = true := by decide
  have d5 : ∀ i : Fin 8, i ≠ 5 → oneEachFn 2 1 i = true → oneEachFn 2 2 i = true := by decide
  have d6 : ∀ i : Fin 8, i ≠ 6 → oneEachFn 1 2 i = true → oneEachFn 1 3 i = true := by decide
  have h1 : (1 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 1 2 3 2 (by decide) (by decide) (fun i hi h1 => d1 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h2 : (2 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 2 0 3 0 (by decide) (by decide) (fun i hi h1 => d2 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h4 : (4 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 2 0 2 2 (by decide) (by decide) (fun i hi h1 => d4 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h5 : (5 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 2 1 2 2 (by decide) (by decide) (fun i hi h1 => d5 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  have h6 : (6 : Fin 8) ∈ S := by
    by_contra hn; exact absurd (h 1 2 1 3 (by decide) (by decide) (fun i hi h1 => d6 i (fun e => hn (e ▸ hi)) h1) (by decide)) (by decide)
  intro i hi
  simp only [E5, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption

lemma zero_on_E6 : ∀ i ∈ E6, oneEachFn 3 3 i = false := by decide

lemma eval_true_of_zero {gs : List Gate} {w : ℕ} {S : Finset (Fin 8)}
    (hsub : S ⊆ E6) (hdep : MonoDep gs {w} S) (hz : evalW gs w (oneEachFn 3 3) = true)
    (x : Fin 8 → Bool) : evalW gs w x = true := by
  refine hdep (oneEachFn 3 3) x (fun i hi h1 => ?_) w (by simp) hz
  have hf := zero_on_E6 i (hsub hi)
  rw [hf] at h1
  exact False.elim (Bool.false_ne_true h1)

lemma or_no_split_edge {gs : List Gate} {w a b : ℕ} {Sa Sb : Finset (Fin 8)}
    (hdisj : Disjoint Sa Sb)
    (hda : MonoDep gs {a} Sa) (hdb : MonoDep gs {b} Sb)
    (hor : ∀ x : Fin 8 → Bool, evalW gs w x = (evalW gs a x || evalW gs b x))
    (hrep : ∀ u v : Fin 4, u ≠ 0 → evalW gs w (oneEachFn u v) = (895 : ℕ).testBit (4 * u.val + v.val))
    (u v : Fin 4) (hu0 : u ≠ 0)
    (hedge : (895 : ℕ).testBit (4 * u.val + v.val) = true)
    (hu_in : (⟨u.val, by omega⟩ : Fin 8) ∈ Sa) (hv_in : (⟨4 + v.val, by omega⟩ : Fin 8) ∈ Sb) :
    False := by
  have hev : evalW gs w (oneEachFn u v) = true := (hrep u v hu0).trans hedge
  rw [hor, Bool.or_eq_true] at hev
  rcases hev with ha | hb
  · have hv_not : (⟨4 + v.val, by omega⟩ : Fin 8) ∉ Sa :=
      Finset.disjoint_right.mp hdisj hv_in
    have ha3 : evalW gs a (oneEachFn u 3) = true := by
      refine hda (oneEachFn u v) (oneEachFn u 3) (fun i hi h1 => ?_) a (by simp) ha
      have hne : i ≠ ⟨4 + v.val, by omega⟩ := fun e => hv_not (e ▸ hi)
      unfold oneEachFn at h1 ⊢
      simp only [decide_eq_true_eq] at h1 ⊢
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact False.elim (hne (Fin.ext h1))
    have hw3 : evalW gs w (oneEachFn u 3) = true := by rw [hor, ha3]; rfl
    rw [hrep u 3 hu0] at hw3
    have hbad : ∀ u' : Fin 4, u' ≠ 0 → (895 : ℕ).testBit (4 * u'.val + (3 : Fin 4).val) = false := by decide
    rw [hbad u hu0] at hw3
    exact Bool.false_ne_true hw3
  · have hu_not : (⟨u.val, by omega⟩ : Fin 8) ∉ Sb :=
      Finset.disjoint_left.mp hdisj hu_in
    have hb3 : evalW gs b (oneEachFn 3 v) = true := by
      refine hdb (oneEachFn u v) (oneEachFn 3 v) (fun i hi h1 => ?_) b (by simp) hb
      have hne : i ≠ ⟨u.val, by omega⟩ := fun e => hu_not (e ▸ hi)
      unfold oneEachFn at h1 ⊢
      simp only [decide_eq_true_eq] at h1 ⊢
      rcases h1 with h1 | h1
      · exact False.elim (hne (Fin.ext h1))
      · exact Or.inr h1
    have hw3 : evalW gs w (oneEachFn 3 v) = true := by rw [hor, hb3]; simp
    rw [hrep 3 v (by decide)] at hw3
    have hbad : ∀ v' : Fin 4, (895 : ℕ).testBit (4 * (3 : Fin 4).val + v'.val) = false := by decide
    rw [hbad v] at hw3
    exact Bool.false_ne_true hw3

lemma E5_same_side {gs : List Gate} {w a b : ℕ} {Sa Sb : Finset (Fin 8)}
    (hdisj : Disjoint Sa Sb) (hcov : E5 ⊆ Sa ∪ Sb)
    (hda : MonoDep gs {a} Sa) (hdb : MonoDep gs {b} Sb)
    (hor : ∀ x : Fin 8 → Bool, evalW gs w x = (evalW gs a x || evalW gs b x))
    (hrep : ∀ u v : Fin 4, u ≠ 0 → evalW gs w (oneEachFn u v) = (895 : ℕ).testBit (4 * u.val + v.val)) :
    E5 ⊆ Sa ∨ E5 ⊆ Sb := by
  have edge_same : ∀ (u v : Fin 4), u ≠ 0 → u ≠ 3 → v ≠ 3 →
      (895 : ℕ).testBit (4 * u.val + v.val) = true →
      ((⟨u.val, by omega⟩ : Fin 8) ∈ Sa ↔ (⟨4 + v.val, by omega⟩ : Fin 8) ∈ Sa) := by
    intro u v hu0 hu3 hv3 he
    have hu_in : (⟨u.val, by omega⟩ : Fin 8) ∈ Sa ∪ Sb := by
      apply hcov
      have : ∀ u' : Fin 4, u' ≠ 0 → u' ≠ 3 → (⟨u'.val, by omega⟩ : Fin 8) ∈ E5 := by decide
      exact this u hu0 hu3
    have hv_in : (⟨4 + v.val, by omega⟩ : Fin 8) ∈ Sa ∪ Sb := by
      apply hcov
      have : ∀ v' : Fin 4, v' ≠ 3 → (⟨4 + v'.val, by omega⟩ : Fin 8) ∈ E5 := by decide
      exact this v hv3
    simp only [Finset.mem_union] at hu_in hv_in
    constructor
    · intro hua
      rcases hv_in with hva | hvb
      · exact hva
      · exact False.elim (or_no_split_edge hdisj hda hdb hor hrep u v hu0 he hua hvb)
    · intro hva
      rcases hu_in with hua | hub
      · exact hua
      · exact False.elim (or_no_split_edge hdisj.symm hdb hda
          (fun x => by rw [hor, Bool.or_comm]) hrep u v hu0 he hub hva)
  have e14 := edge_same 1 0 (by decide) (by decide) (by decide) (by decide)
  have e24 := edge_same 2 0 (by decide) (by decide) (by decide) (by decide)
  have e25 := edge_same 2 1 (by decide) (by decide) (by decide) (by decide)
  have e16 := edge_same 1 2 (by decide) (by decide) (by decide) (by decide)
  by_cases h1 : (1 : Fin 8) ∈ Sa
  · left
    have h4 : (4 : Fin 8) ∈ Sa := e14.mp h1
    have h2 : (2 : Fin 8) ∈ Sa := e24.mpr h4
    have h5 : (5 : Fin 8) ∈ Sa := e25.mp h2
    have h6 : (6 : Fin 8) ∈ Sa := e16.mp h1
    intro i hi
    simp only [E5, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption
  · right
    have h4 : (4 : Fin 8) ∉ Sa := fun h => h1 (e14.mpr h)
    have h2 : (2 : Fin 8) ∉ Sa := fun h => h4 (e24.mp h)
    have h5 : (5 : Fin 8) ∉ Sa := fun h => h2 (e25.mpr h)
    have h6 : (6 : Fin 8) ∉ Sa := fun h => h1 (e16.mpr h)
    intro i hi
    have hmem := Finset.mem_union.mp (hcov hi)
    simp only [E5, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact hmem.resolve_left h1
    · exact hmem.resolve_left h2
    · exact hmem.resolve_left h4
    · exact hmem.resolve_left h5
    · exact hmem.resolve_left h6

lemma kill_and_E5 {gs : List Gate} {w a b : ℕ} {Ta Tb : Finset (Fin 8)}
    (hdisj : Disjoint Ta Tb) (hunion : Ta ∪ Tb = E5)
    (hda : MonoDep gs {a} Ta) (hdb : MonoDep gs {b} Tb)
    (hand : ∀ x : Fin 8 → Bool, evalW gs w x = (evalW gs a x && evalW gs b x))
    (hrep : ∀ u v : Fin 4, u ≠ 0 → evalW gs w (oneEachFn u v) = (895 : ℕ).testBit (4 * u.val + v.val))
    (hzb : evalW gs b (oneEachFn 3 3) = false)
    (h1a : (1 : Fin 8) ∈ Ta) : False := by
  have h1notb : (1 : Fin 8) ∉ Tb := Finset.disjoint_left.mp hdisj h1a
  have h12 : evalW gs a (oneEachFn 1 2) = true ∧ evalW gs b (oneEachFn 1 2) = true := by
    have h := hrep 1 2 (by decide)
    rw [hand] at h
    exact Bool.and_eq_true _ _ |>.mp (h.trans (by decide))
  have h10 : evalW gs a (oneEachFn 1 0) = true ∧ evalW gs b (oneEachFn 1 0) = true := by
    have h := hrep 1 0 (by decide)
    rw [hand] at h
    exact Bool.and_eq_true _ _ |>.mp (h.trans (by decide))
  have h20 : evalW gs a (oneEachFn 2 0) = true ∧ evalW gs b (oneEachFn 2 0) = true := by
    have h := hrep 2 0 (by decide)
    rw [hand] at h
    exact Bool.and_eq_true _ _ |>.mp (h.trans (by decide))
  have h4b : (4 : Fin 8) ∈ Tb := by
    by_contra h4not
    have htr : evalW gs b (oneEachFn 3 3) = true := by
      refine hdb (oneEachFn 1 0) (oneEachFn 3 3) (fun i hi h1 => ?_) b (by simp) h10.2
      have hi5 : i ∈ E5 := hunion ▸ Finset.mem_union_right _ hi
      have hne1 : i ≠ 1 := fun e => h1notb (e ▸ hi)
      have hne4 : i ≠ 4 := fun e => h4not (e ▸ hi)
      have hdec : ∀ j : Fin 8, j ∈ E5 → j ≠ 1 → j ≠ 4 → oneEachFn 1 0 j = false := by decide
      rw [hdec i hi5 hne1 hne4] at h1
      exact False.elim (Bool.false_ne_true h1)
    rw [hzb] at htr
    exact Bool.false_ne_true htr
  have h4nota : (4 : Fin 8) ∉ Ta := Finset.disjoint_right.mp hdisj h4b
  have ha22 : evalW gs a (oneEachFn 2 2) = true := by
    refine hda (oneEachFn 2 0) (oneEachFn 2 2) (fun i hi h1 => ?_) a (by simp) h20.1
    have hne4 : i ≠ 4 := fun e => h4nota (e ▸ hi)
    have hdec : ∀ j : Fin 8, j ≠ 4 → oneEachFn 2 0 j = true → oneEachFn 2 2 j = true := by decide
    exact hdec i hne4 h1
  have hb22 : evalW gs b (oneEachFn 2 2) = true := by
    refine hdb (oneEachFn 1 2) (oneEachFn 2 2) (fun i hi h1 => ?_) b (by simp) h12.2
    have hne1 : i ≠ 1 := fun e => h1notb (e ▸ hi)
    have hdec : ∀ j : Fin 8, j ≠ 1 → oneEachFn 1 2 j = true → oneEachFn 2 2 j = true := by decide
    exact hdec i hne1 h1
  have hw22 : evalW gs w (oneEachFn 2 2) = true := by rw [hand, ha22, hb22]; rfl
  rw [hrep 2 2 (by decide)] at hw22
  exact absurd hw22 (by decide)

lemma kill_core {gs : List Gate} {w : ℕ}
    (hsp : SplitsOnce gs w E5)
    (hrep : ∀ u v : Fin 4, u ≠ 0 → evalW gs w (oneEachFn u v) = (895 : ℕ).testBit (4 * u.val + v.val)) :
    False := by
  obtain ⟨op, a, b, Ta, Tb, hop, _, _, hTa, hTb, hdisj, hunion, hda, hdb, hev⟩ := hsp
  have hE56 : E5 ⊆ E6 := by decide
  have hsubA : Ta ⊆ E6 := (hunion ▸ Finset.subset_union_left).trans hE56
  have hsubB : Tb ⊆ E6 := (hunion ▸ Finset.subset_union_right).trans hE56
  rcases hop with rfl | rfl
  · have hand : ∀ x : Fin 8 → Bool, evalW gs w x = (evalW gs a x && evalW gs b x) := by
      intro x; simpa [GateOp.eval] using hev x
    have hza : evalW gs a (oneEachFn 3 3) = false := by
      cases h : evalW gs a (oneEachFn 3 3)
      · rfl
      · exfalso
        have hall : ∀ x, evalW gs a x = true := eval_true_of_zero hsubA hda h
        have hsub : E5 ⊆ Tb := by
          apply need_five Tb
          intro u v u' v' hu hu' hle huv
          have hb1 : evalW gs b (oneEachFn u v) = true := by
            have := (hrep u v hu).trans huv
            rw [hand, hall, Bool.true_and] at this
            exact this
          have hb2 := hdb (oneEachFn u v) (oneEachFn u' v') hle b (by simp) hb1
          have hw2 : evalW gs w (oneEachFn u' v') = true := by rw [hand, hall, hb2]; rfl
          exact (hrep u' v' hu').symm.trans hw2
        obtain ⟨i, hi⟩ := hTa
        exact Finset.disjoint_left.mp hdisj hi (hsub (hunion ▸ Finset.mem_union_left _ hi))
    have hzb : evalW gs b (oneEachFn 3 3) = false := by
      cases h : evalW gs b (oneEachFn 3 3)
      · rfl
      · exfalso
        have hall : ∀ x, evalW gs b x = true := eval_true_of_zero hsubB hdb h
        have hsub : E5 ⊆ Ta := by
          apply need_five Ta
          intro u v u' v' hu hu' hle huv
          have ha1 : evalW gs a (oneEachFn u v) = true := by
            have := (hrep u v hu).trans huv
            rw [hand, hall, Bool.and_true] at this
            exact this
          have ha2 := hda (oneEachFn u v) (oneEachFn u' v') hle a (by simp) ha1
          have hw2 : evalW gs w (oneEachFn u' v') = true := by rw [hand, ha2, hall]; rfl
          exact (hrep u' v' hu').symm.trans hw2
        obtain ⟨i, hi⟩ := hTb
        exact Finset.disjoint_right.mp hdisj hi (hsub (hunion ▸ Finset.mem_union_right _ hi))
    have h1mem : (1 : Fin 8) ∈ Ta ∪ Tb := by rw [hunion]; decide
    rcases Finset.mem_union.mp h1mem with h1a | h1b
    · exact kill_and_E5 hdisj hunion hda hdb hand hrep hzb h1a
    · exact kill_and_E5 hdisj.symm (Finset.union_comm Ta Tb ▸ hunion) hdb hda
        (fun x => by rw [hand, Bool.and_comm]) hrep hza h1b
  · have hor : ∀ x : Fin 8 → Bool, evalW gs w x = (evalW gs a x || evalW gs b x) := by
      intro x; simpa [GateOp.eval] using hev x
    rcases E5_same_side hdisj (by rw [hunion]) hda hdb hor hrep with hA | hB
    · obtain ⟨i, hi⟩ := hTb
      exact Finset.disjoint_right.mp hdisj hi (hA (hunion ▸ Finset.mem_union_right _ hi))
    · obtain ⟨i, hi⟩ := hTa
      exact Finset.disjoint_left.mp hdisj hi (hB (hunion ▸ Finset.mem_union_left _ hi))

def witness : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [4, 5] }
      , { op := GateOp.or, inputs := [8, 6] }
      , { op := GateOp.and, inputs := [1, 9] }
      , { op := GateOp.and, inputs := [2, 8] }
      , { op := GateOp.or, inputs := [0, 10] }
      , { op := GateOp.or, inputs := [12, 11] } ]
    output := 13 }

end PEqualNP.Outside.L_meta_5636

open PEqualNP.Outside.L_meta_5636 in
theorem PEqualNP.Outside.L_meta_5636 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (895 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (895 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  constructor
  · refine ⟨PEqualNP.Outside.L_meta_5636.witness, ?_, le_rfl, ?_⟩
    · simp [PEqualNP.Outside.L_meta_5636.witness, PEqualNP.MetaComplexity.Monotone2]
    · decide
  · rintro ⟨C, hC, hsize, hrep⟩
    have hmono : ∀ g ∈ C.gates,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length ≤ 2 := by
      intro g hg
      have ⟨hop, hlen⟩ := hC g hg
      exact ⟨by simpa using hop, hlen⟩
    have hrepW : ∀ u v : Fin 4, evalW C.gates C.output (oneEachFn u v) =
        (895 : ℕ).testBit (4 * u.val + v.val) := by
      intro u v
      change (C.gates.foldl stepWire (List.ofFn (oneEachFn u v))).getD C.output false = _
      rw [ofFn_oneEachFn]
      exact hrep u v
    have hE6_sub : ∀ S : Finset (Fin 8), MonoDep C.gates {C.output} S → E6 ⊆ S := by
      intro S hdep
      apply need_six S
      intro u v u' v' hle huv
      have h1 := (hrepW u v).trans huv
      have h2 := hdep (oneEachFn u v) (oneEachFn u' v') hle C.output (by simp) h1
      exact (hrepW u' v').symm.trans h2
    have hE6_card : E6.card = 6 := by decide
    have hlen5 : C.gates.length = 5 := by
      obtain ⟨S, hS, hdep⟩ := mono_core 8 C.gates hmono {C.output}
      have hsub := hE6_sub S hdep
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hS
      unfold PEqualNP.CircuitLowerBounds.Circuit.size at hsize
      omega
    have ht : Tight (n := 8) C.gates {C.output} := by
      intro S hdep
      have hc := Finset.card_le_card (hE6_sub S hdep)
      simp only [Finset.card_singleton]
      omega
    obtain ⟨F, hFdep, _, _, _, hFtwice, hFcard⟩ := mono_tight_tree 8 C.gates hmono {C.output} ht
    have hFout : F C.output = E6 := by
      have hsub := hE6_sub (F C.output) (hFdep C.output (by simp))
      have hcard : (F C.output).card = 6 := by
        simp only [Finset.singleton_biUnion, Finset.card_singleton] at hFcard
        omega
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    have htw := hFtwice C.output (by simp) (by rw [hFout, hE6_card]; omega)
    rw [hFout] at htw
    obtain ⟨op, a, b, Sa, Sb, hop, _, _, hSa, hSb, hdisj, hunion, hda, hdb, hev, hsa, hsb⟩ := htw
    have hsubA : Sa ⊆ E6 := hunion ▸ Finset.subset_union_left
    have hsubB : Sb ⊆ E6 := hunion ▸ Finset.subset_union_right
    rcases hop with rfl | rfl
    · have hand : ∀ x : Fin 8 → Bool, evalW C.gates C.output x = (evalW C.gates a x && evalW C.gates b x) := by
        intro x; simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hev x
      have hza : evalW C.gates a (oneEachFn 3 3) = false := by
        cases h : evalW C.gates a (oneEachFn 3 3)
        · rfl
        · exfalso
          have hall := eval_true_of_zero hsubA hda h
          have hsub := hE6_sub Sb (fun x y hxy u hu htr => by
            rw [Finset.mem_singleton.mp hu] at htr ⊢
            rw [hand, hall, Bool.true_and] at htr ⊢
            exact hdb x y hxy b (by simp) htr)
          obtain ⟨i, hi⟩ := hSa
          exact Finset.disjoint_left.mp hdisj hi (hsub (hsubA hi))
      have hzb : evalW C.gates b (oneEachFn 3 3) = false := by
        cases h : evalW C.gates b (oneEachFn 3 3)
        · rfl
        · exfalso
          have hall := eval_true_of_zero hsubB hdb h
          have hsub := hE6_sub Sa (fun x y hxy u hu htr => by
            rw [Finset.mem_singleton.mp hu] at htr ⊢
            rw [hand, hall, Bool.and_true] at htr ⊢
            exact hda x y hxy a (by simp) htr)
          obtain ⟨i, hi⟩ := hSb
          exact Finset.disjoint_right.mp hdisj hi (hsub (hsubB hi))
      have h03 : evalW C.gates a (oneEachFn 0 3) = true ∧ evalW C.gates b (oneEachFn 0 3) = true := by
        have h := hrepW 0 3
        rw [hand] at h
        exact Bool.and_eq_true _ _ |>.mp (h.trans (by decide))
      by_cases h0a : (0 : Fin 8) ∈ Sa
      · have h0notb : (0 : Fin 8) ∉ Sb := Finset.disjoint_left.mp hdisj h0a
        have htr : evalW C.gates b (oneEachFn 3 3) = true := by
          refine hdb (oneEachFn 0 3) (oneEachFn 3 3) (fun i hi h1 => ?_) b (by simp) h03.2
          have hne0 : i ≠ 0 := fun e => h0notb (e ▸ hi)
          have hdec : ∀ j : Fin 8, j ∈ E6 → j ≠ 0 → oneEachFn 0 3 j = false := by decide
          rw [hdec i (hsubB hi) hne0] at h1
          exact False.elim (Bool.false_ne_true h1)
        rw [hzb] at htr; exact Bool.false_ne_true htr
      · have htr : evalW C.gates a (oneEachFn 3 3) = true := by
          refine hda (oneEachFn 0 3) (oneEachFn 3 3) (fun i hi h1 => ?_) a (by simp) h03.1
          have hne0 : i ≠ 0 := fun e => h0a (e ▸ hi)
          have hdec : ∀ j : Fin 8, j ∈ E6 → j ≠ 0 → oneEachFn 0 3 j = false := by decide
          rw [hdec i (hsubA hi) hne0] at h1
          exact False.elim (Bool.false_ne_true h1)
        rw [hza] at htr; exact Bool.false_ne_true htr
    · have hor : ∀ x : Fin 8 → Bool, evalW C.gates C.output x = (evalW C.gates a x || evalW C.gates b x) := by
        intro x; simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hev x
      have hE56 : E5 ⊆ E6 := by decide
      have hrep5 : ∀ u v : Fin 4, u ≠ 0 → evalW C.gates C.output (oneEachFn u v) =
          (895 : ℕ).testBit (4 * u.val + v.val) := fun u v _ => hrepW u v
      have h0_out_eq : ∀ (x y : ℕ) (Sx Sy : Finset (Fin 8)),
          Disjoint Sx Sy → Sx ∪ Sy = E6 → E5 ⊆ Sy → Sx.Nonempty →
          MonoDep C.gates {x} Sx →
          (∀ z : Fin 8 → Bool, evalW C.gates C.output z = (evalW C.gates x z || evalW C.gates y z)) →
          Sy = E5 ∧ ∀ u v : Fin 4, u ≠ 0 → evalW C.gates y (oneEachFn u v) =
            (895 : ℕ).testBit (4 * u.val + v.val) := by
        intro x y Sx Sy hdj hun h5 hne hdx horxy
        have hSx0 : Sx = {0} := by
          ext i
          simp only [Finset.mem_singleton]
          constructor
          · intro hi
            have hi6 : i ∈ E6 := hun ▸ Finset.mem_union_left _ hi
            have hi5 : i ∉ E5 := fun h => Finset.disjoint_left.mp hdj hi (h5 h)
            have hdec : ∀ j : Fin 8, j ∈ E6 → j ∉ E5 → j = 0 := by decide
            exact hdec i hi6 hi5
          · rintro rfl
            obtain ⟨j, hj⟩ := hne
            have hj6 : j ∈ E6 := hun ▸ Finset.mem_union_left _ hj
            have hj5 : j ∉ E5 := fun h => Finset.disjoint_left.mp hdj hj (h5 h)
            have hdec : ∀ k : Fin 8, k ∈ E6 → k ∉ E5 → k = 0 := by decide
            exact (hdec j hj6 hj5) ▸ hj
        have hSy5 : Sy = E5 := by
          ext i
          constructor
          · intro hi
            have hi6 : i ∈ E6 := hun ▸ Finset.mem_union_right _ hi
            have hne0 : i ≠ 0 := fun e => Finset.disjoint_right.mp hdj hi (by rw [hSx0, e]; exact Finset.mem_singleton_self 0)
            have hdec : ∀ j : Fin 8, j ∈ E6 → j ≠ 0 → j ∈ E5 := by decide
            exact hdec i hi6 hne0
          · exact fun hi => h5 hi
        refine ⟨hSy5, fun u v hu0 => ?_⟩
        have hx_z : evalW C.gates x (oneEachFn 3 3) = false := by
          have hz := hrepW 3 3
          rw [horxy] at hz
          cases h : evalW C.gates x (oneEachFn 3 3)
          · rfl
          · rw [h] at hz; simp only [Bool.true_or] at hz; exact absurd hz (by decide)
        have hx_f : evalW C.gates x (oneEachFn u v) = false := by
          cases h : evalW C.gates x (oneEachFn u v)
          · rfl
          · exfalso
            have htr : evalW C.gates x (oneEachFn 3 3) = true := by
              refine hdx (oneEachFn u v) (oneEachFn 3 3) (fun i hi h1 => ?_) x (by simp) h
              rw [hSx0, Finset.mem_singleton] at hi; subst hi
              unfold oneEachFn at h1
              simp only [Fin.val_zero, decide_eq_true_eq] at h1
              rcases h1 with h1 | h1
              · exact False.elim (hu0 (Fin.ext h1.symm))
              · omega
            rw [hx_z] at htr; exact Bool.false_ne_true htr
        have htot := hrepW u v
        rw [horxy, hx_f, Bool.false_or] at htot
        exact htot
      rcases E5_same_side hdisj (by rw [hunion]; exact hE56) hda hdb hor hrep5 with hA5 | hB5
      · obtain ⟨hSa5, hrepa⟩ := h0_out_eq b a Sb Sa hdisj.symm (Finset.union_comm Sa Sb ▸ hunion)
          hA5 hSb hdb (fun z => by rw [hor, Bool.or_comm])
        have hcard5 : 1 < Sa.card := by rw [hSa5]; decide
        exact kill_core (hSa5 ▸ hsa hcard5) hrepa
      · obtain ⟨hSb5, hrepb⟩ := h0_out_eq a b Sa Sb hdisj hunion hB5 hSa hda hor
        have hcard5 : 1 < Sb.card := by rw [hSb5]; decide
        exact kill_core (hSb5 ▸ hsb hcard5) hrepb
