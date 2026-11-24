import Mathlib
import PEqualNP.Defs

-- The wire evaluation identities follow L-meta-529.
namespace PEqualNP.Outside.L_meta_1534_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
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
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

def legal (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
def basis (gs : List Gate) := ∀ g ∈ gs, legal g
def atom (v : Fin n) (u : Fin n) := decide (u = v)
def supp (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => val gs (atom v) w = true
def sumOf (T : Finset (Fin n)) (x : Fin n → Bool) := decide (∃ v ∈ T, x v = true)

lemma mem_supp (gs : List Gate) (w : ℕ) (v : Fin n) :
    v ∈ supp gs w ↔ val gs (atom v) w = true := by simp [supp]

lemma sum_atom (T : Finset (Fin n)) (v : Fin n) :
    sumOf T (atom v) = decide (v ∈ T) := by simp [sumOf, atom]

lemma eval_up (g : Gate) (hg : legal g) (f h : ℕ → Bool)
    (hle : ∀ i, f i = true → h i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map h) = true := by
  obtain ⟨hand | hor, _⟩ := hg
  · simp only [hand, GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => hle i (hall i hi)
  · simp only [hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, hle i hv⟩

lemma mono (gs : List Gate) (hg : basis gs) (x y : Fin n → Bool)
    (hxy : ∀ v, x v = true → y v = true) : ∀ w, val gs x w = true → val gs y w = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    rw [val_nil, val_nil]
    split
    · exact hxy _
    · exact id
  | append_singleton gs g ih =>
    have hp := ih (fun f hf => hg f (by simp [hf]))
    intro w
    rw [val_snoc, val_snoc]
    by_cases h : w = n + gs.length
    · simpa [h] using eval_up g (hg _ (by simp)) _ _ hp
    · simpa [h] using hp w

lemma atom_le (gs : List Gate) (hg : basis gs) (v : Fin n) (x : Fin n → Bool)
    (hx : x v = true) (w : ℕ) :
    val gs (atom v) w = true → val gs x w = true := by
  apply mono gs hg
  intro u hu
  exact (of_decide_eq_true hu : u = v) ▸ hx

lemma primary (gs : List Gate) (x : Fin n → Bool) (v : Fin n) : val gs x v.val = x v := by
  induction gs using List.reverseRecOn with
  | nil => simp [val_nil, v.isLt]
  | append_singleton gs g ih =>
    rw [val_snoc, ite_eq_right (by have := v.isLt; omega), ih]

noncomputable def makeOr (T : Finset (Fin n)) : Gate := ⟨GateOp.or, T.toList.map Fin.val⟩

lemma makeOr_ok (T : Finset (Fin n)) (ht : T.card ≤ 1) : legal (makeOr T) := by
  constructor
  · exact Or.inr rfl
  · simpa [makeOr] using ht.trans (by decide : 1 ≤ 2)

lemma makeOr_value (T : Finset (Fin n)) (gs : List Gate) (x : Fin n → Bool) :
    (makeOr T).op.eval ((makeOr T).inputs.map fun w => val gs x w) = sumOf T x := by
  apply Bool.eq_iff_iff.mpr
  simp [makeOr, GateOp.eval, sumOf, List.any_eq_true, primary, Function.comp_def]

def normal (n : ℕ) (gs : List Gate) := ∀ k < gs.length, (supp (n := n) gs (n+k)).card ≤ 1 →
  ∀ x : Fin n → Bool, val gs x (n+k) = sumOf (supp gs (n+k)) x

lemma normalize (n : ℕ) (gs : List Gate) (hg : basis gs) :
    ∃ bs : List Gate, bs.length = gs.length ∧ basis bs ∧ normal n bs ∧
      (∀ v : Fin n, ∀ w, val bs (atom v) w = val gs (atom v) w) ∧
      (∀ x : Fin n → Bool, ∀ w, val bs x w = true → val gs x w = true) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    exact ⟨[], rfl, hg, by simp [normal], fun _ _ => rfl, fun _ _ => id⟩
  | append_singleton gs g ih =>
    obtain ⟨bs, hlen, hbs, hnormal, hatom, hdown⟩ := ih (fun f hf => hg f (by simp [hf]))
    let j := n + gs.length
    let T : Finset (Fin n) := supp (gs ++ [g]) j
    let g' := if T.card ≤ 1 then makeOr T else g
    have hleg : legal g' := by
      dsimp [g']
      split
      · exact makeOr_ok _ ‹_›
      · exact hg _ (by simp)
    have hbs' : basis (bs ++ [g']) := by
      intro f hf
      rcases List.mem_append.mp hf with h | h
      · exact hbs f h
      · simpa only [List.mem_singleton.mp h] using hleg
    have old (x : Fin n → Bool) : val (gs ++ [g]) x j =
        g.op.eval (g.inputs.map fun w => val gs x w) := by simp [val_snoc, j]
    have new (x : Fin n → Bool) : val (bs ++ [g']) x j =
        if T.card ≤ 1 then sumOf T x else g.op.eval (g.inputs.map fun w => val bs x w) := by
      rw [val_snoc, ite_eq_left (by simp [j, hlen])]
      by_cases ht : T.card ≤ 1 <;> simp [g', ht, makeOr_value]
    have same (v : Fin n) (w : ℕ) : val (bs ++ [g']) (atom v) w = val (gs ++ [g]) (atom v) w := by
      by_cases hw : w = j
      · subst w
        rw [new]
        split
        · rw [sum_atom]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          exact mem_supp _ _ _
        · rw [old]
          simp only [hatom]
      · rw [val_snoc, val_snoc, ite_eq_right (by simpa [hlen, j] using hw), ite_eq_right hw, hatom]
    have newSupp : supp (n := n) (bs ++ [g']) j = T := by
      ext v
      rw [mem_supp, mem_supp, same]
    refine ⟨bs ++ [g'], by simp [hlen], hbs', ?_, same, ?_⟩
    · intro k hk hc x
      by_cases he : k = gs.length
      · subst k
        change val (bs ++ [g']) x j = sumOf (supp (bs ++ [g']) j) x
        change (supp (n := n) (bs ++ [g']) j).card ≤ 1 at hc
        rw [newSupp] at hc ⊢
        rw [new, ite_eq_left hc]
      · have hk' : k < bs.length := by simp at hk; omega
        have hne : n+k ≠ n+bs.length := by omega
        have before (y : Fin n → Bool) : val (bs ++ [g']) y (n+k) = val bs y (n+k) := by
          rw [val_snoc, ite_eq_right hne]
        have sb : supp (n := n) (bs ++ [g']) (n+k) = supp bs (n+k) := by
          ext v
          rw [mem_supp, mem_supp, before]
        rw [sb] at hc ⊢
        rw [before]
        exact hnormal k hk' hc x
    · intro x w hv
      by_cases he : w = j
      · subst w
        rw [new] at hv
        split at hv
        · obtain ⟨v, hvT, hx⟩ := of_decide_eq_true hv
          exact atom_le _ hg v x hx j ((mem_supp _ _ _).mp hvT)
        · rw [old]
          exact eval_up g (hg _ (by simp)) _ _ (hdown x) hv
      · rw [val_snoc, ite_eq_right (by simpa [hlen, j] using he)] at hv
        rw [val_snoc, ite_eq_right he]
        exact hdown x w hv

end PEqualNP.Outside.L_meta_1534_aux

theorem PEqualNP.Outside.L_meta_1534 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (S : Fin m → Finset (Fin n)) (D : Set (Fin n → Bool)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ v : Fin n, (fun vk : Fin n => decide (vk = v)) ∈ D) → (∀ (w : Fin m) (x : Fin n → Bool), x ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (out w) false = decide (∃ v0 ∈ S w, x v0 = true)) → ∃ gates2 : List PEqualNP.CircuitLowerBounds.Gate, gates2.length ≤ gates.length ∧ (∀ g2 ∈ gates2, (g2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g2.inputs.length ≤ 2) ∧ (∀ ak : ℕ, ak < gates2.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) ∧ ∀ (w2 : Fin m) (x2 : Fin n → Bool), x2 ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn x2)).getD (out w2) false = decide (∃ v2 ∈ S w2, x2 v2 = true) := by
  intro n m gs out S D hg hD hout
  obtain ⟨bs, hlen, hbs, hnorm, hatom, hdown⟩ := PEqualNP.Outside.L_meta_1534_aux.normalize n gs hg
  refine ⟨bs, hlen.le, hbs, ?_, ?_⟩
  · intro k hk hsmall x
    change PEqualNP.Outside.L_meta_1534_aux.val bs x (n+k) = _
    rw [hnorm k hk hsmall x]
    apply Bool.eq_iff_iff.mpr
    simp only [PEqualNP.Outside.L_meta_1534_aux.sumOf, decide_eq_true_eq, PEqualNP.Outside.L_meta_1534_aux.mem_supp]
    rfl
  · intro w x hx
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro ht
      have ho := hdown x (out w) ht
      exact (hout w x hx).symm ▸ ho
    · intro ht
      obtain ⟨v, hv, hvx⟩ := of_decide_eq_true ht
      apply PEqualNP.Outside.L_meta_1534_aux.atom_le bs hbs v x hvx (out w)
      rw [hatom]
      have h := hout w _ (hD v)
      change PEqualNP.Outside.L_meta_1534_aux.val gs (PEqualNP.Outside.L_meta_1534_aux.atom v) (out w) = _ at h
      rw [h]
      exact decide_eq_true ⟨v, hv, by simp⟩
