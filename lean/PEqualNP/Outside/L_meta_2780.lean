import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2780_aux
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

lemma mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt gs x i h1] at hi
      rw [val_lt gs x' i h1]
      exact hle _ hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge gs x i h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk] at hi
        rw [val_gate gs x' k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hi hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hi hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = true →
            (if a < n + k then val gs x' a else false) = true := by
          intro a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)
        match ins, hlen with
        | [], _ =>
          rcases hop with rfl | rfl
          · simp [GateOp.eval]
          · simp [GateOp.eval] at hi
        | [a], _ =>
          rcases hop with rfl | rfl
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
        | [a, b], _ =>
          rcases hop with rfl | rfl
          · have h : (if a < n + k then val gs x a else false) = true ∧
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            have h1 := rd a h.1
            have h2 := rd b h.2
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true]
            exact ⟨h1, h2⟩
          · have h : (if a < n + k then val gs x a else false) = true ∨
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq, Bool.or_eq_true]
            rcases h with h | h
            · exact Or.inl (rd a h)
            · exact Or.inr (rd b h)
        | _ :: _ :: _ :: _, h => simp at h


lemma zero {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x : Fin n → Bool) (hx : ∀ v, x v = false) : ∀ i, val gs x i = false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [val_lt gs x i h1]
      exact hx _
    · by_cases h2 : n + gs.length ≤ i
      · exact val_ge gs x i h2
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = false := by
          intro a
          by_cases hlt : a < n + k
          · rw [if_pos hlt]
            exact ih a hlt
          · rw [if_neg hlt]
        obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
        rcases hop with rfl | rfl <;> simp [GateOp.eval, rd]

def pl {n : ℕ} (P L : Fin n → Bool) : Fin (n + n) → Bool := Fin.append P L

lemma ofFn_pl {n : ℕ} (P L : Fin n → Bool) :
    List.ofFn (pl P L) = List.ofFn P ++ List.ofFn L := by
  unfold pl
  exact List.ofFn_fin_append P L

lemma wvL {n : ℕ} (C : Circuit) (P : Fin n → Bool) (b : Bool) (w : ℕ) :
    wireValue C (List.ofFn P ++ List.replicate n b) w = val C.gates (pl P (fun _ => b)) w := by
  rw [← List.ofFn_const n b, ← ofFn_pl]
  rfl

lemma wvR {n : ℕ} (C : Circuit) (L : Fin n → Bool) (b : Bool) (w : ℕ) :
    wireValue C (List.replicate n b ++ List.ofFn L) w = val C.gates (pl (fun _ => b) L) w := by
  rw [← List.ofFn_const n b, ← ofFn_pl]
  rfl

lemma wvI {n : ℕ} (C : Circuit) (X Y : Finset (Fin n)) (w : ℕ) :
    wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) w
      = val C.gates (pl (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))) w := by
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [← ofFn_pl]
  rfl

lemma pl_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (P P' L L' : Fin n → Bool) (hP : ∀ p, P p = true → P' p = true)
    (hL : ∀ l, L l = true → L' l = true) (i : ℕ) :
    val gs (pl P L) i = true → val gs (pl P' L') i = true := by
  apply mono gs hg
  intro v
  refine Fin.addCases (fun p => ?_) (fun l => ?_) v
  · simp only [pl, Fin.append_left]
    exact hP p
  · simp only [pl, Fin.append_right]
    exact hL l

lemma sandL {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) (a : ℕ)
    (h : ∀ P : Fin n → Bool,
      val gs (pl P (fun _ => false)) a = val gs (pl P (fun _ => true)) a)
    (P L : Fin n → Bool) : val gs (pl P L) a = val gs (pl P (fun _ => false)) a := by
  have h1 := pl_mono gs hg P P (fun _ => false) L (fun _ hp => hp)
    (fun _ hl => absurd hl (by simp)) a
  have h2 := pl_mono gs hg P P L (fun _ => true) (fun _ hp => hp) (fun _ _ => rfl) a
  rw [← h P] at h2
  cases hv : val gs (pl P L) a <;> cases hw : val gs (pl P (fun _ => false)) a <;> simp_all

lemma sandR {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) (b : ℕ)
    (h : ∀ L : Fin n → Bool,
      val gs (pl (fun _ => false) L) b = val gs (pl (fun _ => true) L) b)
    (P L : Fin n → Bool) : val gs (pl P L) b = val gs (pl (fun _ => false) L) b := by
  have h1 := pl_mono gs hg (fun _ => false) P L L (fun _ hp => absurd hp (by simp))
    (fun _ hl => hl) b
  have h2 := pl_mono gs hg P (fun _ => true) L L (fun _ _ => rfl) (fun _ hl => hl) b
  rw [← h L] at h2
  cases hv : val gs (pl P L) b <;> cases hw : val gs (pl (fun _ => false) L) b <;> simp_all

def Bad (n : ℕ) (C : Circuit) (g : Gate) : Prop :=
  g.op = GateOp.and ∧
    ((∀ x4 ∈ g.inputs, ∃ x6 : Fin n → Bool,
        wireValue C (List.ofFn x6 ++ List.replicate n false) x4
          ≠ wireValue C (List.ofFn x6 ++ List.replicate n true) x4) ∨
     ∀ x4 ∈ g.inputs, ∃ x6 : Fin n → Bool,
        wireValue C (List.replicate n false ++ List.ofFn x6) x4
          ≠ wireValue C (List.replicate n true ++ List.ofFn x6) x4)

theorem main (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : PEqualNP.TopForm.IsAO2 (n + n) C)
    (h : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → Bad n C g → j ∈ S)
    (k : ℕ) (hk : k < C.size) (hkS : k ∉ S)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and) :
    ∃ (f1 f2 : Finset (Fin n) → Bool), ∀ X Y : Finset (Fin n),
      wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) (n + n + k)
        = (f1 X && f2 Y) := by
  obtain ⟨hao, hrb, hlen⟩ := hAO
  have hkl : k < C.gates.length := hk
  have hgk : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hkl
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem?_getD, hgk]
    rfl
  rw [hga] at hop
  have hnb : ¬ Bad n C C.gates[k] := fun hb => hkS (h k _ hgk hb)
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hkl
  have hl2 := hlen _ hmem
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hao g hg, hlen g hg⟩
  have hg' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨hao g hg, (hlen g hg).le⟩
  have hrbk : ∀ i ∈ C.gates[k].inputs, i < n + n + k := by
    intro i hi
    exact hrb k hkl i (by rw [hga]; exact hi)
  have hnb' : ¬ ((∀ x4 ∈ C.gates[k].inputs, ∃ x6 : Fin n → Bool,
        wireValue C (List.ofFn x6 ++ List.replicate n false) x4
          ≠ wireValue C (List.ofFn x6 ++ List.replicate n true) x4) ∨
     ∀ x4 ∈ C.gates[k].inputs, ∃ x6 : Fin n → Bool,
        wireValue C (List.replicate n false ++ List.ofFn x6) x4
          ≠ wireValue C (List.replicate n true ++ List.ofFn x6) x4) :=
    fun hh => hnb ⟨hop, hh⟩
  rw [not_or] at hnb'
  obtain ⟨hA, hB⟩ := hnb'
  have exA : ∃ a ∈ C.gates[k].inputs, ∀ P : Fin n → Bool,
      val C.gates (pl P (fun _ => false)) a = val C.gates (pl P (fun _ => true)) a := by
    by_contra hc
    apply hA
    intro a ha
    by_contra hne
    apply hc
    refine ⟨a, ha, fun P => ?_⟩
    by_contra hneq
    exact hne ⟨P, by rw [wvL, wvL]; exact hneq⟩
  have exB : ∃ b ∈ C.gates[k].inputs, ∀ L : Fin n → Bool,
      val C.gates (pl (fun _ => false) L) b = val C.gates (pl (fun _ => true) L) b := by
    by_contra hc
    apply hB
    intro b hb
    by_contra hne
    apply hc
    refine ⟨b, hb, fun L => ?_⟩
    by_contra hneq
    exact hne ⟨L, by rw [wvR, wvR]; exact hneq⟩
  obtain ⟨a, ha, hAa⟩ := exA
  obtain ⟨b, hb, hBb⟩ := exB
  obtain ⟨i1, i2, hin⟩ := List.length_eq_two.mp hl2
  have h1 : i1 < n + n + k := hrbk i1 (by rw [hin]; simp)
  have h2 : i2 < n + n + k := hrbk i2 (by rw [hin]; simp)
  have gv : ∀ f : Fin (n + n) → Bool,
      val C.gates f (n + n + k) = (val C.gates f i1 && val C.gates f i2) := by
    intro f
    rw [val_gate C.gates f k hkl, hop, hin]
    simp [GateOp.eval, h1, h2]
  have cA := sandL C.gates hg' a hAa
  have cB := sandR C.gates hg' b hBb
  have z0 : ∀ i, val C.gates (pl (fun _ : Fin n => false) (fun _ : Fin n => false)) i = false := by
    apply zero C.gates hg
    intro v
    refine Fin.addCases (fun p => ?_) (fun l => ?_) v
    · simp only [pl, Fin.append_left]
    · simp only [pl, Fin.append_right]
  have same : a = b → ∀ P L : Fin n → Bool, val C.gates (pl P L) a = false := by
    intro hab P L
    rw [cA P L, hab, cB P (fun _ => false)]
    exact z0 b
  rw [hin] at ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · refine ⟨fun _ => false, fun _ => false, fun X Y => ?_⟩
    have e := same (ha.trans hb.symm) (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
    rw [ha] at e
    rw [wvI, gv, e]
    rfl
  · refine ⟨fun X => val C.gates (pl (fun p => decide (p ∈ X)) (fun _ => false)) i1,
      fun Y => val C.gates (pl (fun _ => false) (fun l => decide (l ∈ Y))) i2, fun X Y => ?_⟩
    have e1 := cA (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
    have e2 := cB (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
    rw [ha] at e1
    rw [hb] at e2
    rw [wvI, gv, e1, e2]
  · refine ⟨fun X => val C.gates (pl (fun p => decide (p ∈ X)) (fun _ => false)) i2,
      fun Y => val C.gates (pl (fun _ => false) (fun l => decide (l ∈ Y))) i1, fun X Y => ?_⟩
    have e1 := cA (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
    have e2 := cB (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
    rw [ha] at e1
    rw [hb] at e2
    rw [wvI, gv, e1, e2]
    exact Bool.and_comm _ _
  · refine ⟨fun _ => false, fun _ => false, fun X Y => ?_⟩
    have e := same (ha.trans hb.symm) (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
    rw [ha] at e
    rw [wvI, gv, e]
    simp

end PEqualNP.Outside.L_meta_2780_aux

theorem PEqualNP.Outside.L_meta_2780 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.false) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.true) x4) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.false ++ List.ofFn x6) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.true ++ List.ofFn x6) x4); ∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x2 + x2) x3 → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 → x1 x2 x3 x7 → x6 ∈ x4) → ∀ x7 < x3.size, x7 ∉ x4 → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : Finset (Fin x2) → Bool) (x12 : Finset (Fin x2) → Bool), ∀ (x13 x14 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x3 (PEqualNP.GenericRejection.incidenceInput x13 x14) (x2 + x2 + x7) = (x11 x13 && x12 x14) := by
  exact PEqualNP.Outside.L_meta_2780_aux.main
