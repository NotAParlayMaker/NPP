import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2986_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma W_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    W (g :: gs) x = W gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma W_append (as bs : List Gate) (x : List Bool) : W (as ++ bs) x = W bs (W as x) := by
  unfold W; rw [List.foldl_append]

lemma W_len (gs : List Gate) : ∀ x : List Bool, (W gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; rfl
  | cons g gs ih => intro x; rw [W_cons, ih]; simp; omega

lemma W_prefix (gs : List Gate) : ∀ x : List Bool, ∃ t, W gs x = x ++ t := by
  induction gs with
  | nil => intro x; exact ⟨[], by simp [W]⟩
  | cons g gs ih =>
    intro x
    obtain ⟨t, ht⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    exact ⟨_ :: t, by rw [W_cons, ht, List.append_assoc]; rfl⟩

lemma W_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  obtain ⟨t, ht⟩ := W_prefix gs x
  rw [ht, List.getD_append _ _ _ _ hi]

lemma W_getD_ge (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (W gs x).getD i false = false := by
  rw [List.getD_eq_default]
  rw [W_len]; exact hi

lemma W_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < x.length + j) :
    (W gs x).getD (x.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map
        fun i => (W gs x).getD i false) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j+1)) := by
    simp
  have hg : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := by simp [List.getElem?_eq_getElem hj]
  rw [hg] at hr ⊢
  have hA : (W (gs.take j) x).length = x.length + j := by
    rw [W_len]; simp; omega
  have key : ∀ i, i < x.length + j → (W gs x).getD i false = (W (gs.take j) x).getD i false := by
    intro i hi
    conv_lhs => rw [hsplit, W_append]
    rw [W_getD_lt]; omega
  have e2 : (W gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map
      fun i => (W (gs.take j) x).getD i false) := by
    conv_lhs => rw [hsplit, W_append, W_cons]
    rw [W_getD_lt]
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hA]
    · simp [hA]
  rw [e2]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [key i (hr i hi)]

def Fr (n : ℕ) (C : Circuit) : ℕ → Finset ℕ
  | 0 => ({C.output} : Finset ℕ).filter (fun w => w < n + C.gates.length)
  | t+1 => if n + (C.gates.length - 1 - t) ∈ Fr n C t then
      ((Fr n C t).erase (n + (C.gates.length - 1 - t))) ∪
        (gateAt C (C.gates.length - 1 - t)).inputs.toFinset
    else Fr n C t

def V (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (W C.gates (List.ofFn x)).getD w false

lemma V_out (n : ℕ) (C : Circuit) (x : Fin n → Bool) : circuitFun n C x = V C x C.output := rfl

lemma V_gate (n : ℕ) (C : Circuit) (hR : ReadsBack n C) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) :
    V C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (V C x)) := by
  have h := W_gate C.gates (List.ofFn x) k hk (by
    intro i hi; rw [List.length_ofFn]; exact hR k hk i hi)
  rw [List.length_ofFn] at h
  exact h

lemma V_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    V C x w = false := by
  unfold V; apply W_getD_ge; rw [List.length_ofFn]; exact hw

lemma V_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    V C x w = x ⟨w, hw⟩ := by
  unfold V; rw [W_getD_lt _ _ _ (by rw [List.length_ofFn]; exact hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma Fr_inv (n : ℕ) (C : Circuit) (hR : ReadsBack n C) (hM : Monotone2 C) :
    ∀ t, t ≤ C.gates.length →
      (∀ w ∈ Fr n C t, w < n + (C.gates.length - t)) ∧ (Fr n C t).card ≤ 1 + t ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ Fr n C t, V C x w = V C y w) →
        V C x C.output = V C y C.output := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro w hw; simp [Fr] at hw; omega
    · simp only [Fr]
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    · intro x y h
      by_cases ho : C.output < n + C.gates.length
      · apply h; simp [Fr, ho]
      · rw [V_ge _ _ _ _ (by omega), V_ge _ _ _ _ (by omega)]
  | succ t ih =>
    intro ht
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hk : C.gates.length - 1 - t < C.gates.length := by omega
    have hin : (gateAt C (C.gates.length - 1 - t)) ∈ C.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    have hlen := (hM _ hin).2
    by_cases hm : n + (C.gates.length - 1 - t) ∈ Fr n C t
    · have e : Fr n C (t+1) = ((Fr n C t).erase (n + (C.gates.length - 1 - t))) ∪
          (gateAt C (C.gates.length - 1 - t)).inputs.toFinset := by
        simp only [Fr, if_pos hm]
      rw [e]
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · have := Finset.ne_of_mem_erase hw
          have := h1 w (Finset.mem_of_mem_erase hw)
          omega
        · have := hR _ hk w (List.mem_toFinset.1 hw)
          omega
      · have c1 := Finset.card_union_le ((Fr n C t).erase (n + (C.gates.length - 1 - t)))
          (gateAt C (C.gates.length - 1 - t)).inputs.toFinset
        have c2 := Finset.card_erase_of_mem hm
        have c3 := List.toFinset_card_le (gateAt C (C.gates.length - 1 - t)).inputs
        have c4 : 1 ≤ (Fr n C t).card := Finset.card_pos.2 ⟨_, hm⟩
        omega
      · intro x y h
        apply h3
        intro w hw
        by_cases hwe : w = n + (C.gates.length - 1 - t)
        · rw [hwe, V_gate n C hR x _ hk, V_gate n C hR y _ hk]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact h i (Finset.mem_union_right _ (List.mem_toFinset.2 hi))
        · exact h w (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwe, hw⟩))
    · have e : Fr n C (t+1) = Fr n C t := by
        simp only [Fr, if_neg hm]
      rw [e]
      refine ⟨?_, by omega, h3⟩
      intro w hw
      have := h1 w hw
      have : w ≠ n + (C.gates.length - 1 - t) := fun h => hm (h ▸ hw)
      omega

end PEqualNP.Outside.L_meta_2986_aux

theorem PEqualNP.Outside.L_meta_2986 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (x2 + x2) x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → (2 : ℕ) * x2 ≤ x5.size + (1 : ℕ) := by
  intro q N P _ C hq hN hline hpair hM hR hacc hrej
  obtain ⟨h1, h2, h3⟩ := PEqualNP.Outside.L_meta_2986_aux.Fr_inv (N + N) C hR hM C.gates.length le_rfl
  rw [Nat.sub_self, Nat.add_zero] at h1
  have key : ∀ i, i ∉ PEqualNP.Outside.L_meta_2986_aux.Fr (N + N) C C.gates.length →
      ∀ x y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C x = true →
      PEqualNP.MetaComplexity.circuitFun (N + N) C y = false →
      (∀ j : Fin (N + N), j.val ≠ i → x j = y j) → False := by
    intro i hni x y hx hy hxy
    have := h3 x y (by
      intro w hw
      have hw' := h1 w hw
      rw [PEqualNP.Outside.L_meta_2986_aux.V_lt _ _ _ _ hw',
        PEqualNP.Outside.L_meta_2986_aux.V_lt _ _ _ _ hw']
      exact hxy _ (fun h => hni (h ▸ hw)))
    rw [← PEqualNP.Outside.L_meta_2986_aux.V_out, ← PEqualNP.Outside.L_meta_2986_aux.V_out,
      hx, hy] at this
    exact absurd this (by simp)
  have hN7 : 7 ≤ N := by subst hN; nlinarith
  have hall : ∀ i < N + N, i ∈ PEqualNP.Outside.L_meta_2986_aux.Fr (N + N) C C.gates.length := by
    intro i hi
    by_contra hni
    by_cases hiN : i < N
    · let p : Fin N := ⟨i, hiN⟩
      let p' : Fin N := if i = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : p ≠ p' := by
        intro h
        have := congrArg Fin.val h
        by_cases h0 : i = 0
        · simp [p, p', h0] at this
        · simp [p, p', h0] at this
      obtain ⟨l, ⟨hpl, _⟩, _⟩ := hpair p p' hne
      refine key i hni (fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l))
        (fun j => decide (j = Fin.natAdd N l)) (hacc p l hpl) (hrej _ ?_ ?_) ?_
      · refine le_trans (Fintype.card_le_one_iff.2 ?_) (by omega)
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        simp at ha hb
        exact Subtype.ext (ha.trans hb.symm)
      · rintro ⟨u, v, _, hu, _⟩
        simp [Fin.ext_iff] at hu
        have := u.isLt
        omega
      · intro j hj
        have : ¬ (j = Fin.castAdd N p) := fun h => hj (by rw [h]; rfl)
        simp [this]
    · let l : Fin N := ⟨i - N, by omega⟩
      have hpos : 0 < Fintype.card { x9 : Fin N // P x9 l } := by rw [hline]; omega
      obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.1 hpos
      refine key i hni (fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l))
        (fun j => decide (j = Fin.castAdd N p)) (hacc p l hp) (hrej _ ?_ ?_) ?_
      · refine le_trans (Fintype.card_eq_zero_iff.2 ⟨?_⟩).le (Nat.zero_le _)
        rintro ⟨z, hz⟩
        simp [Fin.ext_iff] at hz
        have := p.isLt
        omega
      · rintro ⟨u, v, _, _, hv⟩
        simp [Fin.ext_iff] at hv
        have := v.isLt
        omega
      · intro j hj
        have : ¬ (j = Fin.natAdd N l) := fun h => hj (by rw [h]; simp [l]; omega)
        simp only [this, or_false]
  have hsub : Finset.range (N + N) ⊆ PEqualNP.Outside.L_meta_2986_aux.Fr (N + N) C C.gates.length := by
    intro i hi
    exact hall i (Finset.mem_range.1 hi)
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  show 2 * N ≤ C.gates.length + 1
  omega
