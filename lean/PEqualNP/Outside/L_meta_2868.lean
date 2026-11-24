import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2868_aux
open PEqualNP.CircuitLowerBounds

-- evaluation toolkit copied from L_meta_2780 (step, val, mono, zero, pl, sandL, sandR)
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

lemma wvL {n : ℕ} (C : Circuit) (P : Fin n → Bool) (b : Bool) (w : ℕ) :
    (C.wires (List.ofFn P ++ List.replicate n b)).getD w false
      = val C.gates (pl P (fun _ => b)) w := by
  rw [← List.ofFn_const n b, ← ofFn_pl]
  rfl

lemma wvR {n : ℕ} (C : Circuit) (L : Fin n → Bool) (b : Bool) (w : ℕ) :
    (C.wires (List.replicate n b ++ List.ofFn L)).getD w false
      = val C.gates (pl (fun _ => b) L) w := by
  rw [← List.ofFn_const n b, ← ofFn_pl]
  rfl

def Bad (n : ℕ) (C : Circuit) (g : Gate) : Prop :=
  g.op = GateOp.and ∧
    ((∀ x4 ∈ g.inputs, ∃ x6 : Fin n → Bool,
        (C.wires (List.ofFn x6 ++ List.replicate n false)).getD x4 false
          ≠ (C.wires (List.ofFn x6 ++ List.replicate n true)).getD x4 false) ∨
     ∀ x4 ∈ g.inputs, ∃ x6 : Fin n → Bool,
        (C.wires (List.replicate n false ++ List.ofFn x6)).getD x4 false
          ≠ (C.wires (List.replicate n true ++ List.ofFn x6)).getD x4 false)

def gin (gs : List Gate) (j t : ℕ) : ℕ := (((gs[j]?).map Gate.inputs).getD []).getD t 0

def sg {n : ℕ} (p : Fin n) : Fin n → Bool := fun p' => decide (p' = p)

def Sp {n : ℕ} (gs : List Gate) (w : ℕ) (p : Fin n) : Prop :=
  val gs (pl (sg p) (fun _ => false)) w = true

def Sl {n : ℕ} (gs : List Gate) (w : ℕ) (l : Fin n) : Prop :=
  val gs (pl (fun _ => false) (sg l)) w = true

lemma input_cases {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n + n) :
    (∃ p0 : Fin n, ∀ P L : Fin n → Bool, val gs (pl P L) w = P p0) ∨
    (∃ l0 : Fin n, ∀ P L : Fin n → Bool, val gs (pl P L) w = L l0) := by
  obtain ⟨v, hv⟩ : ∃ v : Fin (n + n), ∀ f : Fin (n + n) → Bool, val gs f w = f v :=
    ⟨⟨w, hw⟩, fun f => val_lt gs f w hw⟩
  induction v using Fin.addCases with
  | left p =>
    left
    refine ⟨p, fun P L => ?_⟩
    rw [hv]
    simp only [pl, Fin.append_left]
  | right l =>
    right
    refine ⟨l, fun P L => ?_⟩
    rw [hv]
    simp only [pl, Fin.append_right]

lemma epl {n : ℕ} (p l : Fin n) :
    (fun k : Fin (n + n) => decide (k = Fin.castAdd n p ∨ k = Fin.natAdd n l))
      = pl (sg p) (sg l) := by
  funext k
  induction k using Fin.addCases with
  | left i =>
    have h1 : ¬ (Fin.castAdd n i = Fin.natAdd n l) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    have h0 : Fin.castAdd n i = Fin.castAdd n p ↔ i = p :=
      ⟨fun h => Fin.ext (by
        have := congrArg Fin.val h
        simp only [Fin.val_castAdd] at this
        exact this), fun h => h ▸ rfl⟩
    show decide (_ ∨ _) = Fin.append (sg p) (sg l) (Fin.castAdd n i)
    rw [Fin.append_left]
    simp only [sg, h0, h1, or_false]
  | right i =>
    have h1 : ¬ (Fin.natAdd n i = Fin.castAdd n p) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    have h0 : Fin.natAdd n i = Fin.natAdd n l ↔ i = l :=
      ⟨fun h => Fin.ext (by
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd] at this
        omega), fun h => h ▸ rfl⟩
    show decide (_ ∨ _) = Fin.append (sg p) (sg l) (Fin.natAdd n i)
    rw [Fin.append_right]
    simp only [sg, h0, h1, false_or]

lemma card_sg {n : ℕ} (P : Fin n → Bool) (l : Fin n) :
    Fintype.card {l' : Fin n // pl P (sg l) (Fin.natAdd n l') = true} ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [pl, Fin.append_right, sg, decide_eq_true_eq] at ha hb
  exact Subtype.ext (ha.trans hb.symm)

lemma card_zero {n : ℕ} (P : Fin n → Bool) :
    Fintype.card {l' : Fin n // pl P (fun _ => false) (Fin.natAdd n l') = true} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨a, ha⟩ => ?_⟩
  simp only [pl, Fin.append_right] at ha
  exact absurd ha (by simp)

lemma gate_cases {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h7 : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      ∃ i j, g.inputs = [i, j] ∧ i < j ∧ j < n + n + k)
    (hnb : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → ¬ Bad n C g)
    (k : ℕ) (hk : k < C.gates.length) :
    gin C.gates k 0 < n + n + k ∧ gin C.gates k 1 < n + n + k ∧
    ((∀ f : Fin (n + n) → Bool, val C.gates f (n + n + k)
        = (val C.gates f (gin C.gates k 0) || val C.gates f (gin C.gates k 1))) ∨
     (∃ a b, ∀ P L : Fin n → Bool, val C.gates (pl P L) (n + n + k)
        = (val C.gates (pl P (fun _ => false)) a && val C.gates (pl (fun _ => false) L) b))) := by
  have hgk : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
  obtain ⟨i1, i2, hin, h12, h2⟩ := h7 k _ hgk
  have e0 : gin C.gates k 0 = i1 := by simp [gin, hgk, hin]
  have e1 : gin C.gates k 1 = i2 := by simp [gin, hgk, hin]
  rw [e0, e1]
  have h1 : i1 < n + n + k := by omega
  refine ⟨h1, h2, ?_⟩
  have hg' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g h => ⟨(hg g h).1, (hg g h).2.le⟩
  rcases (hg _ (List.getElem_mem hk)).1 with hop | hop
  · right
    have hnb' : ¬ ((∀ x4 ∈ C.gates[k].inputs, ∃ x6 : Fin n → Bool,
          (C.wires (List.ofFn x6 ++ List.replicate n false)).getD x4 false
            ≠ (C.wires (List.ofFn x6 ++ List.replicate n true)).getD x4 false) ∨
       ∀ x4 ∈ C.gates[k].inputs, ∃ x6 : Fin n → Bool,
          (C.wires (List.replicate n false ++ List.ofFn x6)).getD x4 false
            ≠ (C.wires (List.replicate n true ++ List.ofFn x6)).getD x4 false) :=
      fun hh => hnb k _ hgk ⟨hop, hh⟩
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
    have gv : ∀ f : Fin (n + n) → Bool,
        val C.gates f (n + n + k) = (val C.gates f i1 && val C.gates f i2) := by
      intro f
      rw [val_gate C.gates f k hk, hop, hin]
      simp [GateOp.eval, h1, h2]
    have cA := sandL C.gates hg' a hAa
    have cB := sandR C.gates hg' b hBb
    have z0 : ∀ i, val C.gates (pl (fun _ : Fin n => false) (fun _ : Fin n => false)) i
        = false := by
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
    · have e := same (ha.trans hb.symm)
      refine ⟨a, a, fun P L => ?_⟩
      rw [gv, ← ha, e P L, e P (fun _ => false)]
      rfl
    · refine ⟨a, b, fun P L => ?_⟩
      rw [gv, ← ha, ← hb, cA P L, cB P L]
    · refine ⟨a, b, fun P L => ?_⟩
      rw [gv, ← ha, ← hb, cA P L, cB P L]
      exact Bool.and_comm _ _
    · have e := same (ha.trans hb.symm)
      refine ⟨a, a, fun P L => ?_⟩
      rw [gv, ← ha, e P L, e P (fun _ => false)]
      simp
  · left
    intro f
    rw [val_gate C.gates f k hk, hop, hin]
    simp [GateOp.eval, h1, h2]

lemma tops {n : ℕ} (gs : List Gate)
    (gc : ∀ k, k < gs.length → gin gs k 0 < n + n + k ∧ gin gs k 1 < n + n + k ∧
      ((∀ f : Fin (n + n) → Bool, val gs f (n + n + k)
          = (val gs f (gin gs k 0) || val gs f (gin gs k 1))) ∨
       (∃ a b, ∀ P L : Fin n → Bool, val gs (pl P L) (n + n + k)
          = (val gs (pl P (fun _ => false)) a && val gs (pl (fun _ => false) L) b))))
    (P L : Fin n → Bool) :
    ∀ w, val gs (pl P L) w = true →
      val gs (pl P (fun _ => false)) w = true ∨ val gs (pl (fun _ => false) L) w = true ∨
      ∃ k a b, k < gs.length ∧ (∀ P' L' : Fin n → Bool, val gs (pl P' L') (n + n + k)
          = (val gs (pl P' (fun _ => false)) a && val gs (pl (fun _ => false) L') b)) ∧
        val gs (pl P L) (n + n + k) = true ∧
        ∀ f : Fin (n + n) → Bool, val gs f (n + n + k) = true → val gs f w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n + n
    · rcases input_cases gs w h1 with ⟨p0, hp⟩ | ⟨l0, hl⟩
      · left
        rw [hp] at hw ⊢
        exact hw
      · right
        left
        rw [hl] at hw ⊢
        exact hw
    · by_cases h2 : n + n + gs.length ≤ w
      · rw [val_ge gs _ w h2] at hw
        exact absurd hw (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + n + k := ⟨w - (n + n), by omega⟩
        have hk : k < gs.length := by omega
        obtain ⟨g0, g1, hor | ⟨a, b, hab⟩⟩ := gc k hk
        · have key : ∀ u, u < n + n + k →
              (∀ f : Fin (n + n) → Bool, val gs f u = true → val gs f (n + n + k) = true) →
              val gs (pl P L) u = true →
              (val gs (pl P (fun _ => false)) (n + n + k) = true ∨
                val gs (pl (fun _ => false) L) (n + n + k) = true ∨
                ∃ k' a b, k' < gs.length ∧ (∀ P' L' : Fin n → Bool,
                  val gs (pl P' L') (n + n + k')
                    = (val gs (pl P' (fun _ => false)) a && val gs (pl (fun _ => false) L') b)) ∧
                  val gs (pl P L) (n + n + k') = true ∧
                  ∀ f : Fin (n + n) → Bool, val gs f (n + n + k') = true →
                    val gs f (n + n + k) = true) := by
            intro u hu hsub hu1
            rcases ih u hu hu1 with h | h | ⟨k', a, b, hk', hab, ht, himp⟩
            · exact Or.inl (hsub _ h)
            · exact Or.inr (Or.inl (hsub _ h))
            · exact Or.inr (Or.inr ⟨k', a, b, hk', hab, ht, fun f hf => hsub f (himp f hf)⟩)
          rw [hor] at hw
          simp only [Bool.or_eq_true] at hw
          rcases hw with hw | hw
          · exact key _ g0 (fun f hf => by rw [hor f, hf, Bool.true_or]) hw
          · exact key _ g1 (fun f hf => by rw [hor f, hf, Bool.or_true]) hw
        · exact Or.inr (Or.inr ⟨k, a, b, hk, hab, hw, fun f hf => hf⟩)

lemma descent {α : Type} (gs : List Gate) (m : ℕ) (T : ℕ → α → Prop)
    (hin : ∀ w, w < m → ∀ x y, T w x → T w y → x = y)
    (hge : ∀ w, m + gs.length ≤ w → ∀ x, ¬ T w x)
    (hgate : ∀ k, k < gs.length → gin gs k 0 < m + k ∧ gin gs k 1 < m + k ∧
      ((∀ x, T (m + k) x ↔ (T (gin gs k 0) x ∨ T (gin gs k 1) x)) ∨ (∀ x, ¬ T (m + k) x))) :
    ∀ w x, T w x → (∃ y, y ≠ x ∧ T w y) →
      ∃ j t, j < gs.length ∧ t < 2 ∧ (∀ y, T (m + j) y → T w y) ∧
        (∃ y1 y2, y1 ≠ y2 ∧ T (m + j) y1 ∧ T (m + j) y2) ∧ (∀ y, T (gin gs j t) y ↔ y = x) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rintro x hx ⟨y, hyx, hy⟩
    by_cases h1 : w < m
    · exact absurd (hin w h1 y x hy hx) hyx
    · by_cases h2 : m + gs.length ≤ w
      · exact absurd hx (hge w h2 x)
      · obtain ⟨k, rfl⟩ : ∃ k, w = m + k := ⟨w - m, by omega⟩
        have hk : k < gs.length := by omega
        obtain ⟨g0, g1, hor | hno⟩ := hgate k hk
        · have key : ∀ t, t < 2 → gin gs k t < m + k → T (gin gs k t) x →
              (∀ z, T (gin gs k t) z → T (m + k) z) →
              ∃ j t, j < gs.length ∧ t < 2 ∧ (∀ z, T (m + j) z → T (m + k) z) ∧
                (∃ y1 y2, y1 ≠ y2 ∧ T (m + j) y1 ∧ T (m + j) y2) ∧
                (∀ z, T (gin gs j t) z ↔ z = x) := by
            intro t ht hlt htx hsub
            by_cases hex : ∃ z, z ≠ x ∧ T (gin gs k t) z
            · obtain ⟨j, t', hj, ht', hs, htwo, hsing⟩ := ih _ hlt x htx hex
              exact ⟨j, t', hj, ht', fun z hz => hsub z (hs z hz), htwo, hsing⟩
            · refine ⟨k, t, hk, ht, fun z hz => hz, ⟨x, y, fun h => hyx h.symm, hx, hy⟩,
                fun z => ⟨fun hz => ?_, fun hz => hz ▸ htx⟩⟩
              by_contra hne
              exact hex ⟨z, hne, hz⟩
          rcases (hor x).mp hx with h | h
          · exact key 0 (by omega) g0 h (fun z hz => (hor z).mpr (Or.inl hz))
          · exact key 1 (by omega) g1 h (fun z hz => (hor z).mpr (Or.inr hz))
        · exact absurd hx (hno x)

lemma count {α : Type} (E : Finset α) (m : ℕ) (R : ℕ → ℕ → α → Prop)
    (hex : ∀ x ∈ E, ∃ j t, j < m ∧ t < 5 ∧ R j t x)
    (hinj : ∀ j t x y, R j t x → R j t y → x = y) : E.card ≤ m * 5 := by
  classical
  have hex' : ∀ x, ∃ jt : ℕ × ℕ, x ∈ E → jt.1 < m ∧ jt.2 < 5 ∧ R jt.1 jt.2 x := by
    intro x
    by_cases hx : x ∈ E
    · obtain ⟨j, t, h⟩ := hex x hx
      exact ⟨(j, t), fun _ => h⟩
    · exact ⟨(0, 0), fun h => absurd h hx⟩
  choose f hf using hex'
  have h := Finset.card_le_card_of_injOn (s := E) (t := Finset.range m ×ˢ Finset.range 5) f
    (fun x hx => by
      have h0 := hf x (Finset.mem_coe.mp hx)
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr h0.1, Finset.mem_range.mpr h0.2.1⟩))
    (fun x hx y hy hxy => by
      have h1 := (hf x (Finset.mem_coe.mp hx)).2.2
      have h2 := (hf y (Finset.mem_coe.mp hy)).2.2
      rw [hxy] at h1
      exact hinj _ _ x y h1 h2)
  rwa [Finset.card_product, Finset.card_range, Finset.card_range] at h

def R0 {n : ℕ} (gs : List Gate) (j : ℕ) (p l : Fin n) : Prop :=
  ∀ p' l' : Fin n, val gs (pl (sg p') (sg l')) (n + n + j) = true ↔ (p' = p ∧ l' = l)

def R1 {n : ℕ} (gs : List Gate) (I : Fin n → Fin n → Prop) (j s : ℕ) (p l : Fin n) : Prop :=
  (∀ p' : Fin n, Sp gs (gin gs j s) p' ↔ p' = p) ∧
    (∃ p1 p2 : Fin n, p1 ≠ p2 ∧ Sp gs (n + n + j) p1 ∧ Sp gs (n + n + j) p2) ∧
    (∀ p' : Fin n, Sp gs (n + n + j) p' → I p' l)

def R3 {n : ℕ} (gs : List Gate) (I : Fin n → Fin n → Prop) (j s : ℕ) (p l : Fin n) : Prop :=
  (∀ l' : Fin n, Sl gs (gin gs j s) l' ↔ l' = l) ∧
    (∃ l1 l2 : Fin n, l1 ≠ l2 ∧ Sl gs (n + n + j) l1 ∧ Sl gs (n + n + j) l2) ∧
    (∀ l' : Fin n, Sl gs (n + n + j) l' → I p l')

def R {n : ℕ} (gs : List Gate) (I : Fin n → Fin n → Prop) (j t : ℕ) (p l : Fin n) : Prop :=
  (t = 0 ∧ R0 gs j p l) ∨ (∃ s, t = 1 + s ∧ s < 2 ∧ R1 gs I j s p l) ∨
    (∃ s, t = 3 + s ∧ s < 2 ∧ R3 gs I j s p l)

lemma R_inj {n : ℕ} (gs : List Gate) (I : Fin n → Fin n → Prop)
    (huniq : ∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, I p l ∧ I p' l)
    (j t : ℕ) (p l p' l' : Fin n) (h : R gs I j t p l) (h' : R gs I j t p' l') :
    p = p' ∧ l = l' := by
  rcases h with ⟨ht, h⟩ | ⟨s, ht, hs, h⟩ | ⟨s, ht, hs, h⟩ <;>
  rcases h' with ⟨ht', h'⟩ | ⟨s', ht', hs', h'⟩ | ⟨s', ht', hs', h'⟩
  · exact (h' p l).mp ((h p l).mpr ⟨rfl, rfl⟩)
  · omega
  · omega
  · omega
  · obtain rfl : s = s' := by omega
    obtain ⟨hs1, ⟨p1, p2, hne, hp1, hp2⟩, hI⟩ := h
    obtain ⟨hs1', _, hI'⟩ := h'
    have hpp : p = p' := (hs1' p).mp ((hs1 p).mpr rfl)
    refine ⟨hpp, ?_⟩
    obtain ⟨l0, _, hl0⟩ := huniq p1 p2 hne
    rw [hl0 l ⟨hI p1 hp1, hI p2 hp2⟩, hl0 l' ⟨hI' p1 hp1, hI' p2 hp2⟩]
  · omega
  · omega
  · omega
  · obtain rfl : s = s' := by omega
    obtain ⟨hs1, ⟨l1, l2, hne, hl1, hl2⟩, hI⟩ := h
    obtain ⟨hs1', _, hI'⟩ := h'
    have hll : l = l' := (hs1' l).mp ((hs1 l).mpr rfl)
    refine ⟨?_, hll⟩
    by_contra hpp
    obtain ⟨l0, _, hl0⟩ := huniq p p' hpp
    exact hne ((hl0 l1 ⟨hI l1 hl1, hI' l1 hl1⟩).trans (hl0 l2 ⟨hI l2 hl2, hI' l2 hl2⟩).symm)

theorem main : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    100 < q → N = q ^ 2 + q + 1 →
    (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
    PEqualNP.MetaComplexity.Monotone2 C →
    C.output < N + N + C.size →
    (∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      ∃ i j, g.inputs = [i, j] ∧ i < j ∧ j < N + N + k) →
    (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C
      (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
    (∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
    ∀ S ⊆ Finset.range C.size, S.card = 0 →
    (∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → (k ∈ S ↔ Bad N C g)) →
    100 * S.card < N * q → N * q ≤ 100 * C.size := by
  intro q N I _ C hq hN hline huniq hM hout h7 hacc hsound S hS hS0 hbad _
  have hSe : S = ∅ := Finset.card_eq_zero.mp hS0
  have hnb : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → ¬ Bad N C g := by
    intro k g hg hb
    have hmem := (hbad k g hg).mpr hb
    rw [hSe] at hmem
    simp at hmem
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    refine ⟨by simpa using (hM g hg).1, ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨a, b, hab, _⟩ := h7 j _ (List.getElem?_eq_getElem hj)
    rw [hab]
    rfl
  have gc := gate_cases C hg h7 hnb
  have z0 : ∀ i, val C.gates (pl (fun _ : Fin N => false) (fun _ : Fin N => false)) i
      = false := by
    apply zero C.gates hg
    intro v
    refine Fin.addCases (fun p => ?_) (fun l => ?_) v
    · simp only [pl, Fin.append_left]
    · simp only [pl, Fin.append_right]
  have hO : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = val C.gates z C.output := fun z => rfl
  have s1 : ∀ p : Fin N, val C.gates (pl (sg p) (fun _ => false)) C.output = false := by
    intro p
    rw [← hO]
    apply hsound
    · rw [card_zero]
      exact Nat.zero_le _
    · rintro ⟨p', l', _, _, h⟩
      simp only [pl, Fin.append_right] at h
      exact absurd h (by simp)
  have s2 : ∀ l : Fin N, val C.gates (pl (fun _ => false) (sg l)) C.output = false := by
    intro l
    rw [← hO]
    apply hsound
    · exact (card_sg _ l).trans (by omega)
    · rintro ⟨p', l', _, h, _⟩
      simp only [pl, Fin.append_left] at h
      exact absurd h (by simp)
  have s3 : ∀ p l : Fin N, val C.gates (pl (sg p) (sg l)) C.output = true → I p l := by
    intro p l h
    by_contra hI
    have hf : val C.gates (pl (sg p) (sg l)) C.output = false := by
      rw [← hO]
      apply hsound
      · exact (card_sg _ l).trans (by omega)
      · rintro ⟨p', l', hI', h1, h2⟩
        simp only [pl, Fin.append_left, Fin.append_right, sg, decide_eq_true_eq] at h1 h2
        subst h1
        subst h2
        exact hI hI'
    rw [hf] at h
    exact absurd h (by simp)
  have s4 : ∀ p l : Fin N, I p l → val C.gates (pl (sg p) (sg l)) C.output = true := by
    intro p l h
    rw [← epl p l]
    exact hacc p l h
  have dinP : ∀ w, w < N + N → ∀ x y : Fin N, Sp C.gates w x → Sp C.gates w y → x = y := by
    intro w hw x y hx hy
    unfold Sp at hx hy
    rcases input_cases C.gates w hw with ⟨p0, hp⟩ | ⟨l0, hl⟩
    · rw [hp] at hx hy
      simp only [sg, decide_eq_true_eq] at hx hy
      exact hx.symm.trans hy
    · rw [hl] at hx
      exact absurd hx (by simp)
  have dinL : ∀ w, w < N + N → ∀ x y : Fin N, Sl C.gates w x → Sl C.gates w y → x = y := by
    intro w hw x y hx hy
    unfold Sl at hx hy
    rcases input_cases C.gates w hw with ⟨p0, hp⟩ | ⟨l0, hl⟩
    · rw [hp] at hx
      exact absurd hx (by simp)
    · rw [hl] at hx hy
      simp only [sg, decide_eq_true_eq] at hx hy
      exact hx.symm.trans hy
  have dgeP : ∀ w, N + N + C.gates.length ≤ w → ∀ x : Fin N, ¬ Sp C.gates w x := by
    intro w hw x hx
    unfold Sp at hx
    rw [val_ge _ _ w hw] at hx
    exact absurd hx (by simp)
  have dgeL : ∀ w, N + N + C.gates.length ≤ w → ∀ x : Fin N, ¬ Sl C.gates w x := by
    intro w hw x hx
    unfold Sl at hx
    rw [val_ge _ _ w hw] at hx
    exact absurd hx (by simp)
  have dgP : ∀ k, k < C.gates.length →
      gin C.gates k 0 < N + N + k ∧ gin C.gates k 1 < N + N + k ∧
      ((∀ x : Fin N, Sp C.gates (N + N + k) x ↔
          (Sp C.gates (gin C.gates k 0) x ∨ Sp C.gates (gin C.gates k 1) x)) ∨
        (∀ x : Fin N, ¬ Sp C.gates (N + N + k) x)) := by
    intro k hk
    obtain ⟨g0, g1, hor | ⟨a, b, hab⟩⟩ := gc k hk
    · refine ⟨g0, g1, Or.inl fun x => ?_⟩
      unfold Sp
      rw [hor]
      simp only [Bool.or_eq_true]
    · refine ⟨g0, g1, Or.inr fun x hx => ?_⟩
      unfold Sp at hx
      rw [hab, z0 b] at hx
      simp at hx
  have dgL : ∀ k, k < C.gates.length →
      gin C.gates k 0 < N + N + k ∧ gin C.gates k 1 < N + N + k ∧
      ((∀ x : Fin N, Sl C.gates (N + N + k) x ↔
          (Sl C.gates (gin C.gates k 0) x ∨ Sl C.gates (gin C.gates k 1) x)) ∨
        (∀ x : Fin N, ¬ Sl C.gates (N + N + k) x)) := by
    intro k hk
    obtain ⟨g0, g1, hor | ⟨a, b, hab⟩⟩ := gc k hk
    · refine ⟨g0, g1, Or.inl fun x => ?_⟩
      unfold Sl
      rw [hor]
      simp only [Bool.or_eq_true]
    · refine ⟨g0, g1, Or.inr fun x hx => ?_⟩
      unfold Sl at hx
      rw [hab, z0 a] at hx
      simp at hx
  have hex : ∀ p l : Fin N, I p l →
      ∃ j t, j < C.gates.length ∧ t < 5 ∧ R C.gates I j t p l := by
    intro p l hI
    have ho := s4 p l hI
    rcases tops C.gates gc (sg p) (sg l) C.output ho with h | h | ⟨k, a, b, hk, hab, hkt, himp⟩
    · rw [s1 p] at h
      exact absurd h (by simp)
    · rw [s2 l] at h
      exact absurd h (by simp)
    · have hrect : ∀ p' l' : Fin N, Sp C.gates a p' → Sl C.gates b l' → I p' l' := by
        intro p' l' h1 h2
        apply s3
        apply himp
        unfold Sp at h1
        unfold Sl at h2
        rw [hab, h1, h2]
        rfl
      rw [hab] at hkt
      simp only [Bool.and_eq_true] at hkt
      obtain ⟨hap, hbl⟩ := hkt
      by_cases hc1 : ∃ p2, p2 ≠ p ∧ Sp C.gates a p2
      · obtain ⟨j, t, hj, ht, hsub, htwo, hsing⟩ :=
          descent C.gates (N + N) (Sp C.gates) dinP dgeP dgP a p hap hc1
        exact ⟨j, 1 + t, hj, by omega, Or.inr (Or.inl ⟨t, rfl, ht, hsing, htwo,
          fun p' hp' => hrect p' l (hsub p' hp') hbl⟩)⟩
      · by_cases hc2 : ∃ l2, l2 ≠ l ∧ Sl C.gates b l2
        · obtain ⟨j, t, hj, ht, hsub, htwo, hsing⟩ :=
            descent C.gates (N + N) (Sl C.gates) dinL dgeL dgL b l hbl hc2
          exact ⟨j, 3 + t, hj, by omega, Or.inr (Or.inr ⟨t, rfl, ht, hsing, htwo,
            fun l' hl' => hrect p l' hap (hsub l' hl')⟩)⟩
        · refine ⟨k, 0, hk, by omega, Or.inl ⟨rfl, fun p' l' => ?_⟩⟩
          rw [hab]
          simp only [Bool.and_eq_true]
          constructor
          · rintro ⟨h1, h2⟩
            constructor
            · by_contra hne
              exact hc1 ⟨p', hne, h1⟩
            · by_contra hne
              exact hc2 ⟨l', hne, h2⟩
          · rintro ⟨rfl, rfl⟩
            exact ⟨hap, hbl⟩
  have hcount : (Finset.univ.sigma
      (fun l : Fin N => Finset.univ.filter (fun p : Fin N => I p l))).card
        ≤ C.gates.length * 5 := by
    refine count _ _ (fun j t (x : Σ _ : Fin N, Fin N) => R C.gates I j t x.2 x.1) ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hx
      exact hex x.2 x.1 hx
    · rintro j t ⟨l, p⟩ ⟨l', p'⟩ h h'
      obtain ⟨rfl, rfl⟩ := R_inj C.gates I huniq j t p l p' l' h h'
      rfl
  rw [Finset.card_sigma] at hcount
  have hc : ∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
    intro l
    rw [← hline l, Fintype.card_subtype]
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hcount
  have hle : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (by omega)
  show N * q ≤ 100 * C.gates.length
  omega

end PEqualNP.Outside.L_meta_2868_aux

theorem PEqualNP.Outside.L_meta_2868 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, x16.card = (0 : ℕ) → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  exact PEqualNP.Outside.L_meta_2868_aux.main
