import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open Finset PEqualNP.CircuitLowerBounds

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def single {n : ℕ} (a : Fin n) : Fin n → Bool :=
  fun b => decide (b = a)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]
  simp [hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem fold_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]
  rw [fold_length]
  exact h

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (g i : ℕ) : Bool :=
  if i < g then val C x i else false

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, wires_eq, fold_getD_lt _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ}
    (hw : n + C.gates.length ≤ w) : val C x w = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wires_length] using hw)]

theorem wires_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (n + j) = C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
      operand C x (n + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step (List.ofFn x) with hA
  have hAl : A.length = n + j := by
    rw [hA, fold_length]
    simp
    omega
  have hw : C.wires (List.ofFn x) = (C.gates.drop (j + 1)).foldl step
      (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hstepLength : (step A C.gates[j]).length = n + j + 1 := by simp [step, hAl]
  have hreadA : ∀ i, A.getD i false = operand C x (n + j) i := by
    intro i
    unfold operand
    split_ifs with hi
    · symm
      rw [val, hw, fold_getD_lt _ _ _ (by omega), step, List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  rw [val, hw, fold_getD_lt _ _ _ (by omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self, List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

def LeL (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i ∈ l, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i hi (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hi hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k _ => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 :=
            ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

theorem wires_mono (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (a b : List Bool) (hl : a.length = b.length) (h : LeL a b) :
    LeL (C.wires a) (C.wires b) := by
  rw [wires_eq, wires_eq]
  exact fold_mono C.gates (fun g hg => (hC g hg).1) a b hl h

theorem val_mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ w, val C x w = true → val C y w = true := by
  have hxy' : LeL (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases hi' : i < n
    · have hx : x ⟨i, hi'⟩ = true := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi'] using hi
      have hy := hxy ⟨i, hi'⟩ hx
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi'] using hy
    · simp [List.getD_eq_getElem?_getD, hi'] at hi
  have hm := wires_mono C hC (List.ofFn x) (List.ofFn y) (by simp) hxy'
  intro w hw
  exact hm w hw

theorem val_gate_imp {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hxy : ∀ i ∈ g.inputs, i < n + j → val C x i = true → val C y i = true)
    (hx : val C x (n + j) = true) : val C y (n + j) = true := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.1 hg).1
  have hgeq : C.gates[j] = g := (List.getElem?_eq_some_iff.1 hg).2
  have hmem : g ∈ C.gates := List.mem_of_getElem? hg
  have hop := (hC g hmem).1
  rw [wires_gate C x j hj] at hx
  rw [wires_gate C y j hj]
  rw [hgeq] at hx ⊢
  have hread : ∀ i, i ∈ g.inputs →
      (fun a => operand C x (n + j) a) i = true →
        (fun a => operand C y (n + j) a) i = true := by
    intro i hi hxi
    change operand C x (n + j) i = true at hxi
    change operand C y (n + j) i = true
    by_cases hi' : i < n + j
    · rw [show operand C x (n + j) i = val C x i by simp [operand, hi']] at hxi
      rw [show operand C y (n + j) i = val C y i by simp [operand, hi']]
      exact hxy i hi hi' hxi
    · simp [operand, hi'] at hxi ⊢
  exact eval_mono g.op hop g.inputs (operand C x (n + j))
    (operand C y (n + j)) hread hx

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => val C (single a) w = true)

def privateWires {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.gates.length)).filter
    (fun w => 2 ≤ (support (n := n) C w).card ∧ support (n := n) C w ⊆ S)

lemma privateWires_subset (n : ℕ) (C : Circuit) (S : Finset (Fin n)) :
    privateWires (n := n) C S ⊆ Finset.Ico n (n + C.gates.length) := by
  intro w hw
  exact (Finset.mem_filter.mp hw).1

lemma privateWires_mem_data (n : ℕ) (C : Circuit) (S : Finset (Fin n)) {w : ℕ}
    (hw : w ∈ privateWires (n := n) C S) :
    2 ≤ (support (n := n) C w).card ∧ support (n := n) C w ⊆ S := by
  exact (Finset.mem_filter.mp hw).2

lemma privateWires_pairwise_disjoint {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => privateWires (n := n) C (S i)) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro i hi j hj hne
  by_contra hij
  obtain ⟨w, hw⟩ := hne
  have ⟨hwi, hwj⟩ := Finset.mem_inter.mp hw
  have hwi' := privateWires_mem_data n C (S i) hwi
  have hwj' := privateWires_mem_data n C (S j) hwj
  have hsub : support (n := n) C w ⊆ S i ∩ S j :=
    Finset.subset_inter hwi'.2 hwj'.2
  have hcard : (support (n := n) C w).card ≤ (S i ∩ S j).card :=
    Finset.card_le_card hsub
  have hsmall := hinter i j hij
  omega

lemma privateWires_union_subset {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) :
    (Finset.univ : Finset (Fin m)).biUnion (fun i => privateWires (n := n) C (S i)) ⊆
      Finset.Ico n (n + C.gates.length) := by
  intro w hw
  obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp hw
  exact privateWires_subset n C (S i) hwi

theorem sum_private_le {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∑ i : Fin m, (privateWires (n := n) C (S i)).card ≤ C.size := by
  let F : Fin m → Finset ℕ := fun i => privateWires (n := n) C (S i)
  have hdisj : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint F := by
    simpa [F] using privateWires_pairwise_disjoint C S hinter
  have hcard :
      ((Finset.univ : Finset (Fin m)).biUnion F).card =
        ∑ i : Fin m, (F i).card := by
    rw [Finset.card_biUnion hdisj]
  have hsub : (Finset.univ : Finset (Fin m)).biUnion F ⊆
      Finset.Ico n (n + C.gates.length) := by
    simpa [F] using privateWires_union_subset C S
  calc
    ∑ i : Fin m, (privateWires (n := n) C (S i)).card =
        ((Finset.univ : Finset (Fin m)).biUnion F).card := by
          simpa [F] using hcard.symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card := Finset.card_le_card hsub
    _ = C.size := by
      rw [Nat.card_Ico]
      simp [Circuit.size]

-- The local assembly statement isolates the one-output private-closure lemma.
theorem assembly
    (private_lower : ∀ {n k : ℕ} (C : Circuit) (S : Finset (Fin n)) (o c : ℕ),
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      2 ≤ (support (n := n) C o).card → support (n := n) C o ⊆ S →
      (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S, x q = false) → val C x o = false) →
      c ≤ k → c + 1 ≤ (support (n := n) C o).card →
        c ≤ (privateWires (n := n) C S).card)
    : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
        (c : Fin m → ℕ),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ i : Fin m, 2 ≤ (support (n := n) C (o i)).card) →
      (∀ g ∈ C.gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      (∀ (i : Fin m) (p : Fin n), val C (single p) (o i) = true → p ∈ S i) →
      (∀ (i : Fin m) (x : Fin n → Bool),
        (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S i, x q = false) → val C x (o i) = false) →
      (∀ i : Fin m, c i ≤ k) →
      (∀ i : Fin m, c i + 1 ≤ (support (n := n) C (o i)).card) →
      ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hinter hcard hgate hsingle hzero hc hbelow
  have hpriv : ∀ i : Fin m, c i ≤ (privateWires (n := n) C (S i)).card := by
    intro i
    apply private_lower C (S i) (o i) (c i) hgate (hcard i)
    · intro p hp
      exact hsingle i p (Finset.mem_filter.mp hp).2
    · exact hzero i
    · exact hc i
    · exact hbelow i
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (fun i hi => hpriv i)
  exact hsum.trans (sum_private_le C S hinter)

def below (P : Finset ℕ) (b : ℕ) : Finset ℕ := P.filter (· < b)

theorem below_succ (P : Finset ℕ) (b : ℕ) :
    below P (b + 1) = if b ∈ P then insert b (below P b) else below P b := by
  ext w
  split_ifs with hb
  · simp only [below, mem_filter, mem_insert]
    constructor
    · rintro ⟨hw, hlt⟩
      by_cases he : w = b
      · exact Or.inl he
      · exact Or.inr ⟨hw, by omega⟩
    · rintro (rfl | ⟨hw, hlt⟩)
      · exact ⟨hb, by omega⟩
      · exact ⟨hw, by omega⟩
  · simp only [below, mem_filter]
    constructor
    · rintro ⟨hw, hlt⟩
      have hne : w ≠ b := fun he => hb (he ▸ hw)
      exact ⟨hw, by omega⟩
    · rintro ⟨hw, hlt⟩
      exact ⟨hw, by omega⟩

theorem frontier {X : Type*} (P : Finset ℕ) (deps : ℕ → Finset ℕ)
    (value : X → ℕ → Bool)
    (hsmall : ∀ w ∈ P, (deps w).card ≤ 2)
    (hprior : ∀ w ∈ P, ∀ v ∈ deps w, v < w)
    (hstep : ∀ w ∈ P, ∀ x y, (∀ v ∈ deps w, value x v = true → value y v = true) →
      value x w = true → value y w = true)
    (b : ℕ) (F : Finset ℕ) (hbound : ∀ w ∈ F, w ∈ P → w < b) :
    ∃ E : Finset ℕ, (∀ w ∈ E, w ∉ P) ∧ E.card ≤ F.card + (below P b).card ∧
      ∀ x y, (∀ v ∈ E, value x v = true → value y v = true) →
        ∀ w ∈ F, value x w = true → value y w = true := by
  induction b generalizing F with
  | zero =>
    refine ⟨F, ?_, by omega, ?_⟩
    · intro w hw hp
      have := hbound w hw hp
      omega
    · intro x y h
      exact h
  | succ b ih =>
    by_cases hb : b ∈ P ∧ b ∈ F
    · let G := (F.erase b) ∪ deps b
      have hGbound : ∀ w ∈ G, w ∈ P → w < b := by
        intro w hw hp
        rcases mem_union.mp hw with he | hd
        · have hlt := hbound w (mem_of_mem_erase he) hp
          have hne := ne_of_mem_erase he
          omega
        · exact hprior b hb.1 w hd
      obtain ⟨E, hE, hcard, himp⟩ := ih G hGbound
      have hGcard : G.card ≤ F.card + 1 := by
        have h₁ := card_union_le (F.erase b) (deps b)
        have h₂ := card_erase_add_one hb.2
        have h₃ := hsmall b hb.1
        change (F.erase b ∪ deps b).card ≤ _
        omega
      have hbelow : (below P (b + 1)).card = (below P b).card + 1 := by
        have hnot : b ∉ below P b := by simp [below]
        rw [below_succ, ite_eq_left hb.1, card_insert_of_notMem hnot]
      refine ⟨E, hE, by omega, ?_⟩
      intro x y hxy w hw hv
      by_cases hwb : w = b
      · subst w
        exact hstep b hb.1 x y (fun v hv' => himp x y hxy v (mem_union_right _ hv')) hv
      · exact himp x y hxy w (mem_union_left _ (mem_erase.mpr ⟨hwb, hw⟩)) hv
    · have hFbound : ∀ w ∈ F, w ∈ P → w < b := by
        intro w hw hp
        have hlt := hbound w hw hp
        by_contra! hn
        have heq : w = b := by omega
        subst w
        exact hb ⟨hp, hw⟩
      obtain ⟨E, hE, hcard, himp⟩ := ih F hFbound
      have hmono : below P b ⊆ below P (b + 1) := by
        intro w hw
        simp only [below, mem_filter] at hw ⊢
        exact ⟨hw.1, by omega⟩
      exact ⟨E, hE, hcard.trans (Nat.add_le_add_left (card_le_card hmono) _), himp⟩

def alive {n : ℕ} (V : Finset (Fin n) → ℕ → Bool) (w : ℕ) : Finset (Fin n) :=
  univ.filter (fun a => V {a} w = true)

theorem mem_alive {n : ℕ} (V : Finset (Fin n) → ℕ → Bool) (w : ℕ) (a : Fin n) :
    a ∈ alive V w ↔ V {a} w = true := by
  simp [alive]

theorem exit_bound {n k : ℕ} (V : Finset (Fin n) → ℕ → Bool)
    (hmono : ∀ {X Y}, X ⊆ Y → ∀ w, V X w = true → V Y w = true)
    (S : Finset (Fin n)) (E : Finset ℕ) (out : ℕ)
    (hfront : ∀ X Y, (∀ w ∈ E, V X w = true → V Y w = true) →
      V X out = true → V Y out = true)
    (hpromise : ∀ X, X.card ≤ k → (∀ a ∈ S, a ∉ X) → V X out = false)
    (hsmall : ∀ w ∈ E, alive V w ⊆ S → (alive V w).card ≤ 1)
    (hbudget : E.card ≤ k) : (alive V out).card ≤ E.card := by
  classical
  let bad := E.filter (fun w => ∃ a ∈ alive V w, a ∉ S)
  have hbad (w : ↥bad) : ∃ a ∈ alive V w.val, a ∉ S :=
    (mem_filter.mp w.property).2
  choose witness hwitness houtside using hbad
  let Y := bad.attach.image witness
  have hcard : Y.card ≤ E.card := by
    calc
      Y.card ≤ bad.attach.card := card_image_le
      _ = bad.card := card_attach
      _ ≤ E.card := card_filter_le _ _
  have hdisjoint : ∀ a ∈ S, a ∉ Y := by
    intro a ha hy
    obtain ⟨w, _, rfl⟩ := mem_image.mp hy
    exact houtside w ha
  have houtput : V Y out = false := hpromise Y (hcard.trans hbudget) hdisjoint
  have htest : ∀ w ∈ bad, V Y w = true := by
    intro w hw
    let b : ↥bad := ⟨w, hw⟩
    have hmem : witness b ∈ Y := mem_image.mpr ⟨b, mem_attach _ _, rfl⟩
    exact hmono (singleton_subset_iff.mpr hmem) w ((mem_alive V w _).mp (hwitness b))
  have hfind (a : ↥(alive V out)) : ∃ w ∈ E, a.val ∈ alive V w ∧ V Y w ≠ true := by
    by_contra! hn
    have h := hfront {a.val} Y (fun w hw hv => hn w hw ((mem_alive V w a.val).mpr hv))
      ((mem_alive V out a.val).mp a.property)
    simp [houtput] at h
  choose landing hlanding hsingle hfalse using hfind
  apply card_le_card_of_injective (f := fun a => ⟨landing a, hlanding a⟩)
  intro a b hab
  have heq : landing a = landing b := congrArg Subtype.val hab
  have hsubset : alive V (landing a) ⊆ S := by
    intro p hp
    by_contra hnot
    exact hfalse a (htest (landing a) (mem_filter.mpr ⟨hlanding a, p, hp, hnot⟩))
  have hle := hsmall (landing a) (hlanding a) hsubset
  rw [card_le_one] at hle
  exact Subtype.ext (hle _ (hsingle a) _ (heq ▸ hsingle b))

def operands (C : Circuit) (n w : ℕ) : Finset ℕ :=
  ((C.gates[w - n]?.map Gate.inputs).getD []).toFinset.filter (· < w)

theorem operands_at (C : Circuit) (n j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    operands C n (n + j) = g.inputs.toFinset.filter (· < n + j) := by
  simp [operands, hg]

theorem gate_at {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {w : ℕ}
    (hw : w ∈ privateWires C S) : ∃ j g, w = n + j ∧ C.gates[j]? = some g := by
  have hinterval : n ≤ w ∧ w < n + C.gates.length :=
    mem_Ico.mp (mem_filter.mp hw).1
  have hj : w - n < C.gates.length := by omega
  exact ⟨w - n, C.gates[w - n], by omega, List.getElem?_eq_getElem hj⟩

theorem private_lower {n k : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (out c : ℕ)
    (_hlarge : 2 ≤ (support (n := n) C out).card) (_hsub : support C out ⊆ S)
    (hpromise : ∀ x : Fin n → Bool, (univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val C x out = false)
    (hck : c ≤ k) (hc : c + 1 ≤ (support (n := n) C out).card) :
    c ≤ (privateWires C S).card := by
  classical
  let P := privateWires C S
  let V (X : Finset (Fin n)) : ℕ → Bool := val C (fun a => decide (a ∈ X))
  have halive (w : ℕ) : alive V w = support C w := by
    ext a
    have hfun : (fun q : Fin n => decide (q ∈ ({a} : Finset (Fin n)))) = single a := by
      funext q
      simp [Finset.mem_singleton, single]
    simp only [mem_alive, support, mem_filter, mem_univ, true_and, V, hfun]
  have hmono : ∀ {X Y}, X ⊆ Y → ∀ w, V X w = true → V Y w = true := by
    intro X Y hXY w hw
    apply val_mono C _ _ _ hC w hw
    intro a ha
    exact decide_eq_true (hXY (of_decide_eq_true ha))
  have hsmall : ∀ w ∈ P, (operands C n w).card ≤ 2 := by
    intro w hw
    obtain ⟨j, g, rfl, hg⟩ := gate_at hw
    have hlen := (hC g (List.mem_of_getElem? hg)).2
    rw [operands_at C n j g hg, ← hlen]
    exact (card_filter_le _ _).trans g.inputs.toFinset_card_le
  have hprior : ∀ w ∈ P, ∀ v ∈ operands C n w, v < w := by
    intro w _ v hv
    exact (mem_filter.mp hv).2
  have hstep : ∀ w ∈ P, ∀ X Y, (∀ v ∈ operands C n w, V X v = true → V Y v = true) →
      V X w = true → V Y w = true := by
    intro w hw X Y hXY
    obtain ⟨j, g, rfl, hg⟩ := gate_at hw
    apply val_gate_imp C _ _ j g hg hC
    intro v hv hlt
    apply hXY v
    rw [operands_at C n j g hg]
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hlt⟩
  let b := n + C.gates.length
  have hbound : ∀ w ∈ ({out} : Finset ℕ), w ∈ P → w < b := by
    intro w _ hw
    exact (mem_Ico.mp (mem_filter.mp hw).1).2
  obtain ⟨E, hexit, hcard, hforward⟩ :=
    frontier P (operands C n) V hsmall hprior hstep b {out} hbound
  have hE : E.card ≤ 1 + P.card := by
    simpa using hcard.trans (Nat.add_le_add_left (card_filter_le _ _) ({out} : Finset ℕ).card)
  by_contra! hnot
  have hbudget : E.card ≤ k := by change P.card < c at hnot; omega
  have hsafe : ∀ w ∈ E, alive V w ⊆ S → (alive V w).card ≤ 1 := by
    intro w hw hsub
    rw [halive] at hsub ⊢
    by_cases hinput : w < n
    · let a : Fin n := ⟨w, hinput⟩
      have heq : support C w = {a} := by
        ext q
        have hr : val C (single q) w = single q a := val_input C (single q) a
        simp only [support, mem_filter, mem_univ, true_and, hr, single, decide_eq_true_eq,
          mem_singleton]
        exact eq_comm
      rw [heq, card_singleton]
    by_cases hgate : w < n + C.gates.length
    · by_contra! hbig
      exact hexit w hw (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, hgate⟩, by omega, hsub⟩)
    · have heq : support (n := n) C w = ∅ := by
        ext q
        have hoob : n + C.gates.length ≤ w := by omega
        simp [support, val_oob C (single q) hoob]
      simp [heq]
  have htest : ∀ X : Finset (Fin n), X.card ≤ k → (∀ a ∈ S, a ∉ X) → V X out = false := by
    intro X hX hdis
    have heq : univ.filter (fun q : Fin n => decide (q ∈ X) = true) = X := by ext; simp
    apply hpromise _ (by rwa [heq])
    intro a ha
    exact decide_eq_false (hdis a ha)
  have hresult := exit_bound V hmono S E out
    (fun X Y hxy => hforward X Y hxy out (mem_singleton_self out)) htest hsafe hbudget
  rw [halive] at hresult
  change P.card < c at hnot
  omega

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 :
    ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m
    → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤
    (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b =
    a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op =
    PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide
    (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool),
    (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) →
    (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i +
    1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b =
    a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  exact PEqualNP.Outside.L_meta_782.assembly
    (fun C S out c hC => PEqualNP.Outside.L_meta_782.private_lower C hC S out c)
