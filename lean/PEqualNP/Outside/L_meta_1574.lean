import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1574

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl step acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]
    omega

lemma foldl_getD_lt (gs : List Gate) (acc : List Bool) (k : ℕ) (hk : k < acc.length) :
    (gs.foldl step acc).getD k false = acc.getD k false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (step acc g).length := by
      simp only [step, List.length_append, List.length_singleton]
      omega
    rw [ih (step acc g) hk']
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma eval_input (gates : List Gate) (f : Fin 13 → Bool) (v : Fin 13) :
    Circuit.eval ⟨gates, v.val⟩ (List.ofFn f) = f v := by
  unfold Circuit.eval Circuit.wires
  have hlen : v.val < (List.ofFn f).length := by simp
  have h := foldl_getD_lt gates (List.ofFn f) v.val hlen
  change (gates.foldl step (List.ofFn f)).getD v.val false = f v
  rw [h, List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]

lemma eval_gate (gates : List Gate) (f : Fin 13 → Bool) (i : Fin gates.length)
    (hback : ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) :
    Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn f) =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => Circuit.eval ⟨gates, a⟩ (List.ofFn f)) := by
  unfold Circuit.eval Circuit.wires
  change (gates.foldl step (List.ofFn f)).getD (13 + i.val) false =
    (gates.get i).op.eval ((gates.get i).inputs.map fun a => (gates.foldl step (List.ofFn f)).getD a false)
  have hsplit : gates = gates.take i.val ++ gates.get i :: gates.drop (i.val + 1) := by
    have h1 := List.take_append_drop i.val gates
    have h2 : gates.drop i.val = gates.get i :: gates.drop (i.val + 1) := by
      rw [← List.cons_getElem_drop_succ (h := i.isLt)]
      rfl
    rw [← h2, h1]
  let acc := (gates.take i.val).foldl step (List.ofFn f)
  have hacc_len : acc.length = 13 + i.val := by
    dsimp [acc]
    rw [foldl_length]
    simp [Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  have hfold : gates.foldl step (List.ofFn f) = (gates.drop (i.val + 1)).foldl step (step acc (gates.get i)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hstep_len : 13 + i.val < (step acc (gates.get i)).length := by
    simp only [step, List.length_append, List.length_singleton, hacc_len]
    omega
  rw [hfold, foldl_getD_lt _ _ (13 + i.val) hstep_len]
  have hlhs : (step acc (gates.get i)).getD (13 + i.val) false =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => acc.getD a false) := by
    simp only [step, List.getD_eq_getElem?_getD, ← hacc_len, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hlhs]
  congr 1
  apply List.map_congr_left
  intro a ha
  have ha_lt : a < acc.length := by rw [hacc_len]; exact hback a ha
  have ha_lt2 : a < (step acc (gates.get i)).length := by
    simp only [step, List.length_append, List.length_singleton]
    omega
  rw [foldl_getD_lt _ _ a ha_lt2]
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left ha_lt]

def InOrCone (gates : List Gate) (root w : ℕ) : Prop :=
  ∀ S : Set ℕ, root ∈ S →
    (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) → w ∈ S

lemma inOrCone_refl (gates : List Gate) (w : ℕ) : InOrCone gates w w :=
  fun _ h _ => h

lemma inOrCone_step (gates : List Gate) (i : Fin gates.length) (a w : ℕ)
    (hor : (gates.get i).op = GateOp.or) (ha : a ∈ (gates.get i).inputs)
    (hw : InOrCone gates a w) : InOrCone gates (13 + (i : ℕ)) w :=
  fun S hroot hcl => hw S (hcl i hroot hor a ha) hcl

lemma inOrCone_le (gates : List Gate)
    (hback : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    {root w : ℕ} (h : InOrCone gates root w) : w ≤ root := by
  exact h {x | x ≤ root} (le_refl root) (fun i hi _ a ha => le_trans (le_of_lt ((hback i).2 a ha)) hi)

lemma inOrCone_false (gates : List Gate)
    (hback : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (f : Fin 13 → Bool) {root w : ℕ} (hc : InOrCone gates root w)
    (hf : Circuit.eval ⟨gates, root⟩ (List.ofFn f) = false) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn f) = false := by
  apply hc {x | Circuit.eval ⟨gates, x⟩ (List.ofFn f) = false} hf
  intro i hi hor a ha
  change Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn f) = false at hi
  rw [eval_gate gates f i (hback i).2, hor] at hi
  simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq] at hi
  have hne := hi (Circuit.eval ⟨gates, a⟩ (List.ofFn f)) ⟨a, ha, rfl⟩
  cases hval : Circuit.eval ⟨gates, a⟩ (List.ofFn f)
  · exact hval
  · exact absurd hval hne

lemma inOrCone_true_up (gates : List Gate)
    (hback : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (f : Fin 13 → Bool) {root w : ℕ} (hc : InOrCone gates root w)
    (ht : Circuit.eval ⟨gates, w⟩ (List.ofFn f) = true) :
    Circuit.eval ⟨gates, root⟩ (List.ofFn f) = true := by
  by_contra hne
  have hf : Circuit.eval ⟨gates, root⟩ (List.ofFn f) = false := Bool.eq_false_iff.mpr hne
  have hwf := inOrCone_false gates hback f hc hf
  rw [ht] at hwf
  exact Bool.noConfusion hwf

lemma find_atom (gates : List Gate)
    (hmon : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (f : Fin 13 → Bool) (w : ℕ) (hw : w < 13 + gates.length)
    (ht : Circuit.eval ⟨gates, w⟩ (List.ofFn f) = true) :
    ∃ A : ℕ, InOrCone gates w A ∧ Circuit.eval ⟨gates, A⟩ (List.ofFn f) = true ∧
      (A < 13 ∨ ∃ i : Fin gates.length, A = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < 13
    · exact ⟨w, inOrCone_refl gates w, ht, Or.inl hlt⟩
    · have hi_lt : w - 13 < gates.length := by omega
      let i : Fin gates.length := ⟨w - 13, hi_lt⟩
      have hw_eq : w = 13 + (i : ℕ) := by dsimp [i]; omega
      have hop := (hmon (gates.get i) (List.get_mem gates i)).1
      rcases hop with hand | hor
      · exact ⟨w, inOrCone_refl gates w, ht, Or.inr ⟨i, hw_eq, hand⟩⟩
      · rw [hw_eq, eval_gate gates f i (hback i).2, hor] at ht
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht
        obtain ⟨b, ⟨a, ha, rfl⟩, hba⟩ := ht
        have ha_lt : a < w := by rw [hw_eq]; exact (hback i).2 a ha
        have ha_bound : a < 13 + gates.length := lt_trans ha_lt hw
        obtain ⟨A, hAcone, hAt, hAatom⟩ := ih a ha_lt ha_bound hba
        refine ⟨A, ?_, hAt, hAatom⟩
        rw [hw_eq]
        exact inOrCone_step gates i a A hor ha hAcone

lemma atom_is_and (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool)
    (gates : List Gate) (l m c : Fin 13)
    (hT : ∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p)
    (hback : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hinter : L l ∩ L m = {c})
    {root A : ℕ} (hcone : InOrCone gates root A)
    (hfl : Circuit.eval ⟨gates, root⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false)
    (hfm : Circuit.eval ⟨gates, root⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false)
    {p : Fin 13} (hp : p ∈ L l) (hpc : p ≠ c)
    (hAt : Circuit.eval ⟨gates, A⟩ (List.ofFn (T l p)) = true)
    (hAatom : A < 13 ∨ ∃ i : Fin gates.length, A = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) :
    ∃ i : Fin gates.length, A = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and := by
  rcases hAatom with hlt | hand
  · exfalso
    let v : Fin 13 := ⟨A, hlt⟩
    have hflA := inOrCone_false gates hback (fun v : Fin 13 => decide (v ∉ L l)) hcone hfl
    have hfmA := inOrCone_false gates hback (fun v : Fin 13 => decide (v ∉ L m)) hcone hfm
    change Circuit.eval ⟨gates, v.val⟩ _ = false at hflA hfmA
    rw [eval_input] at hflA hfmA
    have hvl : v ∈ L l := by
      by_contra hnv
      have : decide (v ∉ L l) = true := decide_eq_true hnv
      rw [this] at hflA
      exact Bool.noConfusion hflA
    have hvm : v ∈ L m := by
      by_contra hnv
      have : decide (v ∉ L m) = true := decide_eq_true hnv
      rw [this] at hfmA
      exact Bool.noConfusion hfmA
    have hvc : v = c := by
      have hmem : v ∈ L l ∩ L m := Finset.mem_inter.mpr ⟨hvl, hvm⟩
      rw [hinter, Finset.mem_singleton] at hmem
      exact hmem
    change Circuit.eval ⟨gates, v.val⟩ (List.ofFn (T l p)) = true at hAt
    rw [eval_input] at hAt
    have hvp : v = p := (hT l p hp v hvl).mp hAt
    exact hpc (hvp.symm.trans hvc)
  · exact hand

lemma no_bridge (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool)
    (gates : List Gate) (l : Fin 13) (g : Fin gates.length) (X : Finset (Fin 13))
    (hT : ∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p)
    (hmon : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hX : ∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
      Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
      ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
      (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) →
      (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) →
      (y ∈ X ↔ y' ∈ X))
    (w : ℕ) (hw : w < 13 + (g : ℕ))
    (hf : Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false)
    (y : Fin 13) (hy : y ∈ L l) (y' : Fin 13) (hy' : y' ∈ L l)
    (hty : Circuit.eval ⟨gates, w⟩ (List.ofFn (T l y)) = true)
    (hty' : Circuit.eval ⟨gates, w⟩ (List.ofFn (T l y')) = true) :
    y ∈ X ↔ y' ∈ X := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < 13
    · let v : Fin 13 := ⟨w, hlt⟩
      change Circuit.eval ⟨gates, v.val⟩ _ = false at hf
      change Circuit.eval ⟨gates, v.val⟩ _ = true at hty hty'
      rw [eval_input] at hf hty hty'
      have hvl : v ∈ L l := by
        by_contra hnv
        have : decide (v ∉ L l) = true := decide_eq_true hnv
        rw [this] at hf
        exact Bool.noConfusion hf
      have h1 : v = y := (hT l y hy v hvl).mp hty
      have h2 : v = y' := (hT l y' hy' v hvl).mp hty'
      rw [← h1, ← h2]
    · have hi_lt : w - 13 < gates.length := by omega
      let i : Fin gates.length := ⟨w - 13, hi_lt⟩
      have hw_eq : w = 13 + (i : ℕ) := by dsimp [i]; omega
      have hig : i < g := by change w - 13 < g.val; omega
      have hm := hmon (gates.get i) (List.get_mem gates i)
      rcases hm.1 with hand | hor
      · rw [hw_eq, eval_gate gates _ i (hback i).2, hand] at hf hty hty'
        simp only [GateOp.eval, List.all_eq_false, List.mem_map, id_eq, Bool.not_eq_true] at hf
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hty hty'
        obtain ⟨b, ⟨a, ha, rfl⟩, hba⟩ := hf
        have ha_lt : a < w := by rw [hw_eq]; exact (hback i).2 a ha
        exact ih a ha_lt (lt_trans ha_lt hw) hba (hty _ ⟨a, ha, rfl⟩) (hty' _ ⟨a, ha, rfl⟩)
      · have hlen1 := (hback i).1
        have hlen2 := hm.2
        cases hinp : (gates.get i).inputs with
        | nil => rw [hinp] at hlen1; simp at hlen1
        | cons a rest =>
          cases rest with
          | nil =>
            have ha_mem : a ∈ (gates.get i).inputs := by rw [hinp]; simp
            have ha_lt : a < w := by rw [hw_eq]; exact (hback i).2 a ha_mem
            rw [hw_eq, eval_gate gates _ i (hback i).2, hor, hinp] at hf hty hty'
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false] at hf hty hty'
            exact ih a ha_lt (lt_trans ha_lt hw) hf hty hty'
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              rw [hw_eq] at hf hty hty'
              rw [eval_gate gates _ i (hback i).2, hor, hinp] at hty hty'
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, Bool.or_eq_true] at hty hty'
              exact hX i hig hor hf a b hinp y hy y' hy' hty hty'
            | cons c0 rest3 =>
              rw [hinp] at hlen2; simp at hlen2

lemma half_ordered (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool)
    (gates : List Gate) (l m c : Fin 13) (g g' : Fin gates.length)
    (hT : ∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p)
    (hmon : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hinter : L l ∩ L m = {c}) (hgg' : g < g')
    (hgl : (gates.get g).op = GateOp.or ∧
      Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
      ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l,
        Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧
        Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧
          (∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
            Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
            ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
            (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) →
            (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) →
            (y ∈ X ↔ y' ∈ X)))
    (hgm_f : Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false)
    (hg'l : (gates.get g').op = GateOp.or ∧
      Circuit.eval ⟨gates, 13 + (g' : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
      ∃ u1 u2 : ℕ, (gates.get g').inputs = [u1, u2] ∧ ∃ s ∈ L l, ∃ s' ∈ L l,
        Circuit.eval ⟨gates, u1⟩ (List.ofFn (T l s)) = true ∧
        Circuit.eval ⟨gates, u2⟩ (List.ofFn (T l s')) = true ∧
        ∃ X' : Finset (Fin 13), s ∈ X' ∧ s' ∉ X' ∧
          (∀ i : Fin gates.length, i < g' → (gates.get i).op = GateOp.or →
            Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
            ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
            (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) →
            (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) →
            (y ∈ X' ↔ y' ∈ X')))
    (hg'm_f : Circuit.eval ⟨gates, 13 + (g' : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false) :
    ∃ A1 A2 : ℕ, A1 ≠ A2 ∧
      (InOrCone gates (13 + (g : ℕ)) A1 ∨ InOrCone gates (13 + (g' : ℕ)) A1) ∧
      (InOrCone gates (13 + (g : ℕ)) A2 ∨ InOrCone gates (13 + (g' : ℕ)) A2) ∧
      (∃ i : Fin gates.length, A1 = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      (∃ i : Fin gates.length, A2 = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      (∃ p ∈ L l, p ≠ c ∧ Circuit.eval ⟨gates, A1⟩ (List.ofFn (T l p)) = true) ∧
      (∃ p ∈ L l, p ≠ c ∧ Circuit.eval ⟨gates, A2⟩ (List.ofFn (T l p)) = true) := by
  obtain ⟨hg_or, hgl_f, w1, w2, hgw, r, hrL, r', hr'L, hw1r, hw2r', X, hrX, hr'X, hX⟩ := hgl
  obtain ⟨hg'_or, hg'l_f, u1, u2, hg'u, s, hsL, s', hs'L, hu1s, hu2s', X', hsX', hs'X', hX'⟩ := hg'l
  have hw1_mem : w1 ∈ (gates.get g).inputs := by rw [hgw]; simp
  have hw2_mem : w2 ∈ (gates.get g).inputs := by rw [hgw]; simp
  have hw1_lt : w1 < 13 + (g : ℕ) := (hback g).2 w1 hw1_mem
  have hw2_lt : w2 < 13 + (g : ℕ) := (hback g).2 w2 hw2_mem
  have hw1_bound : w1 < 13 + gates.length := lt_trans hw1_lt (Nat.add_lt_add_left g.isLt 13)
  have hw2_bound : w2 < 13 + gates.length := lt_trans hw2_lt (Nat.add_lt_add_left g.isLt 13)
  have hu1_mem : u1 ∈ (gates.get g').inputs := by rw [hg'u]; simp
  have hu2_mem : u2 ∈ (gates.get g').inputs := by rw [hg'u]; simp
  have hu1_lt : u1 < 13 + (g' : ℕ) := (hback g').2 u1 hu1_mem
  have hu2_lt : u2 < 13 + (g' : ℕ) := (hback g').2 u2 hu2_mem
  have hu1_bound : u1 < 13 + gates.length := lt_trans hu1_lt (Nat.add_lt_add_left g'.isLt 13)
  have hu2_bound : u2 < 13 + gates.length := lt_trans hu2_lt (Nat.add_lt_add_left g'.isLt 13)
  have hcL : c ∈ L l := (Finset.mem_inter.mp (by rw [hinter]; exact Finset.mem_singleton_self c)).1
  by_cases hgc : Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (T l c)) = false
  · have hrc : r ≠ c := by
      intro h; subst h
      have ht := inOrCone_true_up gates hback (T l r) (inOrCone_step gates g w1 w1 hg_or hw1_mem (inOrCone_refl gates w1)) hw1r
      rw [ht] at hgc; exact Bool.noConfusion hgc
    have hr'c : r' ≠ c := by
      intro h; subst h
      have ht := inOrCone_true_up gates hback (T l r') (inOrCone_step gates g w2 w2 hg_or hw2_mem (inOrCone_refl gates w2)) hw2r'
      rw [ht] at hgc; exact Bool.noConfusion hgc
    obtain ⟨A1, hA1c, hA1t, hA1a⟩ := find_atom gates hmon hback (T l r) w1 hw1_bound hw1r
    obtain ⟨A2, hA2c, hA2t, hA2a⟩ := find_atom gates hmon hback (T l r') w2 hw2_bound hw2r'
    have hA1g : InOrCone gates (13 + (g : ℕ)) A1 := inOrCone_step gates g w1 A1 hg_or hw1_mem hA1c
    have hA2g : InOrCone gates (13 + (g : ℕ)) A2 := inOrCone_step gates g w2 A2 hg_or hw2_mem hA2c
    have hA1and := atom_is_and L T gates l m c hT hback hinter hA1g hgl_f hgm_f hrL hrc hA1t hA1a
    have hA2and := atom_is_and L T gates l m c hT hback hinter hA2g hgl_f hgm_f hr'L hr'c hA2t hA2a
    have hA1_lt : A1 < 13 + (g : ℕ) := lt_of_le_of_lt (inOrCone_le gates hback hA1c) hw1_lt
    have hne : A1 ≠ A2 := by
      intro heq; subst heq
      have hA1f := inOrCone_false gates hback (fun v : Fin 13 => decide (v ∉ L l)) hA1g hgl_f
      have hiff := no_bridge L T gates l g X hT hmon hback hX A1 hA1_lt hA1f r hrL r' hr'L hA1t hA2t
      exact hr'X (hiff.mp hrX)
    exact ⟨A1, A2, hne, Or.inl hA1g, Or.inl hA2g, hA1and, hA2and, ⟨r, hrL, hrc, hA1t⟩, ⟨r', hr'L, hr'c, hA2t⟩⟩
  · have hgc_t : Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (T l c)) = true :=
      Bool.eq_true_of_not_eq_false hgc
    have hrr' : r ≠ r' := fun h => hr'X (h ▸ hrX)
    have hA1_ex : ∃ A1 : ℕ, InOrCone gates (13 + (g : ℕ)) A1 ∧
        (∃ i : Fin gates.length, A1 = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
        (∃ p ∈ L l, p ≠ c ∧ Circuit.eval ⟨gates, A1⟩ (List.ofFn (T l p)) = true) := by
      by_cases hrc : r ≠ c
      · obtain ⟨A1, hA1c, hA1t, hA1a⟩ := find_atom gates hmon hback (T l r) w1 hw1_bound hw1r
        have hA1g := inOrCone_step gates g w1 A1 hg_or hw1_mem hA1c
        exact ⟨A1, hA1g, atom_is_and L T gates l m c hT hback hinter hA1g hgl_f hgm_f hrL hrc hA1t hA1a, ⟨r, hrL, hrc, hA1t⟩⟩
      · have hr'c : r' ≠ c := fun h => hrr' ((not_not.mp hrc).trans h.symm)
        obtain ⟨A1, hA1c, hA1t, hA1a⟩ := find_atom gates hmon hback (T l r') w2 hw2_bound hw2r'
        have hA1g := inOrCone_step gates g w2 A1 hg_or hw2_mem hA1c
        exact ⟨A1, hA1g, atom_is_and L T gates l m c hT hback hinter hA1g hgl_f hgm_f hr'L hr'c hA1t hA1a, ⟨r', hr'L, hr'c, hA1t⟩⟩
    obtain ⟨A1, hA1g, hA1and, hA1p⟩ := hA1_ex
    have hg_disj : ∀ y ∈ L l, Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (T l y)) = true →
        Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l y)) = true ∨ Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l y)) = true := by
      intro y _ hy
      rw [eval_gate gates _ g (hback g).2, hg_or, hgw] at hy
      simpa [GateOp.eval] using hy
    have hgc_disj := hg_disj c hcL hgc_t
    have hA2_ex : ∃ A2 : ℕ, InOrCone gates (13 + (g' : ℕ)) A2 ∧
        (∃ i : Fin gates.length, A2 = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
        ∃ p ∈ L l, p ≠ c ∧ Circuit.eval ⟨gates, A2⟩ (List.ofFn (T l p)) = true ∧
          Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (T l p)) = false := by
      by_cases hcX' : c ∈ X'
      · have hs'c : s' ≠ c := fun h => hs'X' (h ▸ hcX')
        have hgs'_f : Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (T l s')) = false := by
          by_contra hne
          have ht := Bool.eq_true_of_not_eq_false hne
          have hiff := hX' g hgg' hg_or hgl_f w1 w2 hgw c hcL s' hs'L hgc_disj (hg_disj s' hs'L ht)
          exact hs'X' (hiff.mp hcX')
        obtain ⟨A2, hA2c, hA2t, hA2a⟩ := find_atom gates hmon hback (T l s') u2 hu2_bound hu2s'
        have hA2g' := inOrCone_step gates g' u2 A2 hg'_or hu2_mem hA2c
        exact ⟨A2, hA2g', atom_is_and L T gates l m c hT hback hinter hA2g' hg'l_f hg'm_f hs'L hs'c hA2t hA2a,
          ⟨s', hs'L, hs'c, hA2t, hgs'_f⟩⟩
      · have hsc : s ≠ c := fun h => hcX' (h ▸ hsX')
        have hgs_f : Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (T l s)) = false := by
          by_contra hne
          have ht := Bool.eq_true_of_not_eq_false hne
          have hiff := hX' g hgg' hg_or hgl_f w1 w2 hgw s hsL c hcL (hg_disj s hsL ht) hgc_disj
          exact hcX' (hiff.mp hsX')
        obtain ⟨A2, hA2c, hA2t, hA2a⟩ := find_atom gates hmon hback (T l s) u1 hu1_bound hu1s
        have hA2g' := inOrCone_step gates g' u1 A2 hg'_or hu1_mem hA2c
        exact ⟨A2, hA2g', atom_is_and L T gates l m c hT hback hinter hA2g' hg'l_f hg'm_f hsL hsc hA2t hA2a,
          ⟨s, hsL, hsc, hA2t, hgs_f⟩⟩
    obtain ⟨A2, hA2g', hA2and, p2, hp2L, hp2c, hA2t, hgp2_f⟩ := hA2_ex
    have hne : A1 ≠ A2 := by
      intro heq; subst heq
      have ht := inOrCone_true_up gates hback (T l p2) hA1g hA2t
      rw [ht] at hgp2_f
      exact Bool.noConfusion hgp2_f
    exact ⟨A1, A2, hne, Or.inl hA1g, Or.inr hA2g', hA1and, hA2and, hA1p, ⟨p2, hp2L, hp2c, hA2t⟩⟩

lemma half (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool)
    (gates : List Gate) (l m c : Fin 13) (g g' : Fin gates.length)
    (hT : ∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p)
    (hmon : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (hinter : L l ∩ L m = {c}) (hgg' : g ≠ g')
    (hgl : (gates.get g).op = GateOp.or ∧
      Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
      ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l,
        Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧
        Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧
          (∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
            Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
            ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
            (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) →
            (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) →
            (y ∈ X ↔ y' ∈ X)))
    (hgm_f : Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false)
    (hg'l : (gates.get g').op = GateOp.or ∧
      Circuit.eval ⟨gates, 13 + (g' : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
      ∃ u1 u2 : ℕ, (gates.get g').inputs = [u1, u2] ∧ ∃ s ∈ L l, ∃ s' ∈ L l,
        Circuit.eval ⟨gates, u1⟩ (List.ofFn (T l s)) = true ∧
        Circuit.eval ⟨gates, u2⟩ (List.ofFn (T l s')) = true ∧
        ∃ X' : Finset (Fin 13), s ∈ X' ∧ s' ∉ X' ∧
          (∀ i : Fin gates.length, i < g' → (gates.get i).op = GateOp.or →
            Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
            ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
            (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) →
            (Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) →
            (y ∈ X' ↔ y' ∈ X')))
    (hg'm_f : Circuit.eval ⟨gates, 13 + (g' : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false) :
    ∃ A1 A2 : ℕ, A1 ≠ A2 ∧
      (InOrCone gates (13 + (g : ℕ)) A1 ∨ InOrCone gates (13 + (g' : ℕ)) A1) ∧
      (InOrCone gates (13 + (g : ℕ)) A2 ∨ InOrCone gates (13 + (g' : ℕ)) A2) ∧
      (∃ i : Fin gates.length, A1 = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      (∃ i : Fin gates.length, A2 = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      (∃ p ∈ L l, p ≠ c ∧ Circuit.eval ⟨gates, A1⟩ (List.ofFn (T l p)) = true) ∧
      (∃ p ∈ L l, p ≠ c ∧ Circuit.eval ⟨gates, A2⟩ (List.ofFn (T l p)) = true) := by
  rcases lt_or_gt_of_ne hgg' with hlt | hgt
  · exact half_ordered L T gates l m c g g' hT hmon hback hinter hlt hgl hgm_f hg'l hg'm_f
  · obtain ⟨A1, A2, hne, h1, h2, ha1, ha2, hp1, hp2⟩ :=
      half_ordered L T gates l m c g' g hT hmon hback hinter hgt hg'l hg'm_f hgl hgm_f
    exact ⟨A1, A2, hne, h1.symm, h2.symm, ha1, ha2, hp1, hp2⟩

end PEqualNP.Outside.L_meta_1574

theorem PEqualNP.Outside.L_meta_1574 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate) (l m c : Fin 13) (g g' : Fin gates.length),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ≠ m → L l ∩ L m = {c} → g ≠ g' →
    ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X))) → ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T m r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T m r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X))) →
    ((gates.get g').op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g' : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g').inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g' → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X))) → ((gates.get g').op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g' : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g').inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T m r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T m r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g' → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X))) →
    (∃ A1 A2 : ℕ, A1 ≠ A2 ∧ ((∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A1 ∈ S) ∨ (∀ S : Set ℕ, 13 + (g' : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A1 ∈ S)) ∧
        ((∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A2 ∈ S) ∨ (∀ S : Set ℕ, 13 + (g' : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A2 ∈ S)) ∧ (∃ i : Fin gates.length, A1 = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (∃ i : Fin gates.length, A2 = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        (∃ p ∈ L l, p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, A1⟩ (List.ofFn (T l p)) = true) ∧ (∃ p ∈ L l, p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, A2⟩ (List.ofFn (T l p)) = true)) ∧
    (∃ A1 A2 : ℕ, A1 ≠ A2 ∧ ((∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A1 ∈ S) ∨ (∀ S : Set ℕ, 13 + (g' : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A1 ∈ S)) ∧
        ((∀ S : Set ℕ, 13 + (g : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A2 ∈ S) ∨ (∀ S : Set ℕ, 13 + (g' : ℕ) ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → A2 ∈ S)) ∧ (∃ i : Fin gates.length, A1 = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (∃ i : Fin gates.length, A2 = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        (∃ p ∈ L m, p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, A1⟩ (List.ofFn (T m p)) = true) ∧ (∃ p ∈ L m, p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, A2⟩ (List.ofFn (T m p)) = true)) := by
  intro L _ T gates l m c g g' hT hmon hback _ hinter hgg' hgl hgm hg'l hg'm
  refine ⟨?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_1574.half L T gates l m c g g' hT hmon hback hinter hgg' hgl hgm.2.1 hg'l hg'm.2.1
  · have hinter' : L m ∩ L l = {c} := by rw [Finset.inter_comm]; exact hinter
    exact PEqualNP.Outside.L_meta_1574.half L T gates m l c g g' hT hmon hback hinter' hgg' hgm hgl.2.1 hg'm hg'l.2.1
