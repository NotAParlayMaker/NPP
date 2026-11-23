import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

abbrev Bits (n : ℕ) := Fin n → Bool

def single {n : ℕ} (p : Fin n) : Bits n := fun q => decide (q = p)

def hits {n : ℕ} (f : Bits n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun p => f (single p) = true

def owned {n : ℕ} (S : Finset (Fin n)) (f : Bits n → Bool) : Prop :=
  hits f ⊆ S ∧ 2 ≤ (hits f).card

def upward {n : ℕ} (f : Bits n → Bool) : Prop :=
  ∀ p x, x p = true → f (single p) = true → f x = true

-- The representative set R has two jobs. Its inside points cover possible
-- singleton witnesses; its outside points can be turned on together.
def cert {n : ℕ} (S R : Finset (Fin n)) (f : Bits n → Bool) : Prop :=
  ∀ p ∉ R, ∀ x : Bits n, (∀ q ∈ R, q ∉ S → x q = true) →
    f (single p) = true → f x = true

theorem enlarge {n : ℕ} {S R T : Finset (Fin n)} {f : Bits n → Bool}
    (h : cert S R f) (sub : R ⊆ T) : cert S T f :=
  fun p hp x hx => h p (fun hR => hp (sub hR)) x (fun q hq => hx q (sub hq))

theorem one_rep {n : ℕ} (S : Finset (Fin n)) (f : Bits n → Bool)
    (mon : upward f) (no : ¬ owned S f) :
    ∃ R : Finset (Fin n), R.card ≤ 1 ∧ cert S R f := by
  classical
  by_cases sub : hits f ⊆ S
  · have small : ¬ 2 ≤ (hits f).card := fun h => no ⟨sub,h⟩
    exact ⟨hits f, by omega, fun p hp _ _ h => (hp (by simpa [hits] using h)).elim⟩
  · obtain ⟨q, hq, hqS⟩ := Finset.not_subset.mp sub
    exact ⟨{q}, by simp, fun _ _ x hx _ =>
      mon q x (hx q (by simp) hqS) (by simpa [hits] using hq)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

def wire {n : ℕ} (w : Bits n → List Bool) (j : ℕ) (x : Bits n) : Bool :=
  (w x).getD j false

def newGate {n : ℕ} (w : Bits n → List Bool) (g : Gate) (x : Bits n) : Bool :=
  g.op.eval (g.inputs.map fun j => wire w j x)

def ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem gate_mono {n : ℕ} {w : Bits n → List Bool} {g : Gate} (hg : ok g)
    (x y : Bits n) (h : ∀ j ∈ g.inputs, wire w j x = true → wire w j y = true) :
    newGate w g x = true → newGate w g y = true := by
  rcases hg.1 with hand | hor
  · simp only [newGate, hand, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx j hj => h j hj (hx j hj)
  · simp only [newGate, hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨j,hj,hy⟩
    exact ⟨j,hj,h j hj hy⟩

theorem snoc_wire {n l : ℕ} (w : Bits n → List Bool) (hl : ∀ x, (w x).length = l)
    (g : Gate) (j : ℕ) :
    wire (fun x => step (w x) g) j = if j = l then newGate w g else wire w j := by
  funext x
  have hw := hl x
  by_cases e : j = l
  · subst j
    simp [wire, step, newGate, ← hl x]
  · simp only [ite_eq_right e, wire, step]
    by_cases lt : j < (w x).length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp [hl x]; omega),
          List.getD_eq_default _ _ (by omega)]

def covered {n : ℕ} (S : Finset (Fin n)) (w : Bits n → List Bool) (cost : ℕ) : Prop :=
  ∀ W : Finset ℕ, ∃ R : Finset (Fin n), R.card ≤ cost + W.card ∧
    ∀ j ∈ W, cert S R (wire w j)

theorem advance {n l t : ℕ} (S : Finset (Fin n)) (w : Bits n → List Bool)
    (hl : ∀ x, (w x).length = l) (g : Gate) (hg : ok g) (mon : upward (newGate w g))
    (paid : covered S w t) :
    covered S (fun x => step (w x) g) (t + @ite _ (owned S (newGate w g)) (Classical.propDecidable _) 1 0) := by
  classical
  intro W
  by_cases hlW : l ∈ W
  · let V := W.erase l
    have hcard : V.card + 1 = W.card := Finset.card_erase_add_one hlW
    by_cases own : owned S (newGate w g)
    · obtain ⟨R, hr, hc⟩ := paid (V ∪ g.inputs.toFinset)
      have hle := Finset.card_union_le V g.inputs.toFinset
      have two := (List.toFinset_card_le g.inputs).trans hg.2.le
      refine ⟨R, by simp only [ite_eq_left own]; omega, ?_⟩
      intro j hj
      rw [snoc_wire w hl]
      split_ifs with e
      · intro p hp x hx
        apply gate_mono hg
        exact fun i hi => hc i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)) p hp x hx
      · exact hc j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hj⟩))
    · obtain ⟨T, ht, hT⟩ := one_rep S _ mon own
      obtain ⟨R, hr, hc⟩ := paid V
      have hu := Finset.card_union_le R T
      refine ⟨R ∪ T, by simp only [ite_eq_right own]; omega, ?_⟩
      intro j hj
      rw [snoc_wire w hl]
      split_ifs with e
      · exact enlarge hT Finset.subset_union_right
      · exact enlarge (hc j (Finset.mem_erase.mpr ⟨e,hj⟩)) Finset.subset_union_left
  · obtain ⟨R, hr, hc⟩ := paid W
    refine ⟨R, by omega, ?_⟩
    intro j hj
    have ne : j ≠ l := fun e => hlW (e ▸ hj)
    rw [snoc_wire w hl, ite_eq_right ne]
    exact hc j hj

noncomputable def charge {n : ℕ} (S : Finset (Fin n)) (f : Bits n → Bool) : ℕ :=
  @ite _ (owned S f) (Classical.propDecidable _) 1 0

theorem total_charge {n m : ℕ} (S : Fin m → Finset (Fin n))
    (overlap : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (f : Bits n → Bool) :
    ∑ i, charge (S i) f ≤ 1 := by
  classical
  let U := Finset.univ.filter (fun i => owned (S i) f)
  have hc : U.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    by_contra ne
    have small := overlap i j ne
    have sub : hits f ⊆ S i ∩ S j :=
      fun p hp => Finset.mem_inter.mpr ⟨hi'.1 hp, hj'.1 hp⟩
    have := Finset.card_le_card sub
    have := hi'.2
    omega
  simpa [U, charge, Finset.sum_boole] using hc

theorem drive {n m : ℕ} (S : Fin m → Finset (Fin n))
    (overlap : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hok : ∀ g ∈ gs, ok g) (w : Bits n → List Bool) (l : ℕ)
    (hl : ∀ x, (w x).length = l) (hm : ∀ j, upward (wire w j))
    (cost : Fin m → ℕ) (hcost : ∀ i, covered (S i) w (cost i)) :
    ∃ d : Fin m → ℕ, (∑ i, d i) ≤ (∑ i, cost i) + gs.length ∧
      ∀ i, covered (S i) (fun x => gs.foldl step (w x)) (d i) := by
  classical
  induction gs generalizing w l cost with
  | nil => exact ⟨cost, by simp, hcost⟩
  | cons g gs ih =>
    have hg := hok g List.mem_cons_self
    have mon : upward (newGate w g) :=
      fun p x hx => gate_mono hg _ _ (fun j _ => hm j p x hx)
    let w' := fun x => step (w x) g
    let c' := fun i => cost i + charge (S i) (newGate w g)
    have hl' (x) : (w' x).length = l + 1 := by simp [w', step, hl]
    have hm' (j) : upward (wire w' j) := by
      rw [show wire w' j = _ from snoc_wire w hl g j]
      split_ifs
      · exact mon
      · exact hm j
    have hc' (i) : covered (S i) w' (c' i) :=
      advance _ w hl g hg mon (hcost i)
    obtain ⟨d, hd, hall⟩ := ih (fun g' h => hok g' (List.mem_cons_of_mem _ h))
      w' (l+1) hl' hm' c' hc'
    refine ⟨d, ?_, hall⟩
    have bound := total_charge S overlap (newGate w g)
    simp only [c', Finset.sum_add_distrib] at hd
    simp only [List.length_cons]
    omega

theorem initial_up {n : ℕ} (j : ℕ) : upward (wire (fun x : Bits n => List.ofFn x) j) := by
  intro p x hx h
  by_cases hj : j < n
  · have e : (⟨j,hj⟩ : Fin n) = p := by simpa [wire, single, hj] using h
    simpa [wire, hj, e] using hx
  · simp [wire, hj] at h

theorem initial_covered {n : ℕ} (S : Finset (Fin n)) :
    covered S (fun x : Bits n => List.ofFn x) 0 := by
  classical
  intro W
  let R := Finset.univ.filter (fun p : Fin n => p.val ∈ W)
  have sub : R.image Fin.val ⊆ W := by
    rintro _ h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hp).2
  have bound := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at bound
  refine ⟨R, by simpa using bound, ?_⟩
  intro j hj p hp x _ h
  by_cases lt : j < n
  · have e : (⟨j,lt⟩ : Fin n) = p := by simpa [wire,single,lt] using h
    exact (hp (e ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)).elim
  · simp [wire, lt] at h

theorem output_bound {n : ℕ} (S : Finset (Fin n)) (f : Bits n → Bool) (c k t : ℕ)
    (R : Finset (Fin n)) (small : R.card ≤ t + 1) (hR : cert S R f)
    (ck : c ≤ k) (many : c + 1 ≤ (hits f).card)
    (promise : ∀ x : Bits n, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
       (∀ q ∈ S, x q = false) → f x = false) : c ≤ t := by
  classical
  by_contra! fail
  let x : Bits n := fun q => decide (q ∈ R \ S)
  have on : (Finset.univ.filter (fun q => x q = true)) = R \ S := by ext q; simp [x]
  have off := promise x (by rw [on]; have := Finset.card_le_card (Finset.sdiff_subset (s := R) (t := S)); omega)
    (by intro q hq; simp [x,hq])
  have sub : hits f ⊆ R := by
    intro p hp
    by_contra miss
    have tr := hR p miss x (fun q hq hs => by simp [x,hq,hs]) ((Finset.mem_filter.mp hp).2)
    simp [off] at tr
  have := Finset.card_le_card sub
  omega

end PEqualNP.Outside.L_meta_782

open PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c overlap _ gates _ promise ck many
  obtain ⟨d, hd, hall⟩ := drive S overlap C.gates gates
    (fun x : Bits n => List.ofFn x) n (by simp) initial_up (fun _ => 0)
    (fun i => initial_covered (S i))
  have point (i : Fin m) : c i ≤ d i := by
    obtain ⟨R, small, rep⟩ := hall i {o i}
    exact output_bound (S i) _ (c i) k (d i) R (by simpa using small)
      (rep (o i) (by simp)) (ck i) (many i) (promise i)
  exact (Finset.sum_le_sum (fun i _ => point i)).trans (by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hd)
