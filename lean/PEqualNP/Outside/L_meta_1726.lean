import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1726_aux

open CircuitLowerBounds MetaComplexity

def wireVal {N : ℕ} (C : Circuit) (x : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def single {N : ℕ} (p : Fin N) : Fin N → Bool := fun u => decide (u = p)

def active {N : ℕ} (x : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun p => x p = true

def Eval {N : ℕ} (D : Circuit) (x y : Fin N → Bool) : Bool :=
  circuitFun (N + N) D (Fin.append x y)

structure Problem {N : ℕ} (I : Fin N → Fin N → Prop) (D : Circuit)
    (S W : Finset (Fin N)) (a b : ℕ) : Prop where
  ignore : ∀ x x' y y', (∀ p ∈ S, x p = x' p) → (∀ l ∈ W, y l = y' l) →
    Eval D x y = Eval D x' y'
  accept : ∀ p ∈ S, ∀ l ∈ W, I p l → Eval D (single p) (single l) = true
  rejectPoint : ∀ p ∈ S, ∀ T ⊆ W, (∀ l ∈ T, ¬ I p l) → T.card ≤ a →
    Eval D (single p) (fun l => decide (l ∈ T)) = false
  rejectLine : ∀ l ∈ W, ∀ T ⊆ S, (∀ p ∈ T, ¬ I p l) → T.card ≤ b →
    Eval D (fun p => decide (p ∈ T)) (single l) = false

variable {N a b : ℕ} {I : Fin N → Fin N → Prop} {D : Circuit} {S W : Finset (Fin N)}

theorem Problem.pointNeg (P : Problem I D S W a b) {p : Fin N} (hp : p ∈ S)
    (y : Fin N → Bool) (hcard : (active y).card ≤ a)
    (hoff : ∀ l, I p l → y l = false) : Eval D (single p) y = false := by
  let T := (active y).filter (fun l => l ∈ W)
  have hT : T ⊆ W := fun l hl => (Finset.mem_filter.mp hl).2
  have hle : T.card ≤ a := (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  have ho : ∀ l ∈ T, ¬ I p l := by
    intro l hl hi
    have hyl : y l = true := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
    exact Bool.false_ne_true ((hoff l hi).symm.trans hyl)
  rw [P.ignore (single p) (single p) y (fun l => decide (l ∈ T))
    (fun _ _ => rfl) (fun l hl => by simp [T, active, hl])]
  exact P.rejectPoint p hp T hT ho hle

theorem Problem.lineNeg (P : Problem I D S W a b) {l : Fin N} (hl : l ∈ W)
    (x : Fin N → Bool) (hcard : (active x).card ≤ b)
    (hoff : ∀ p, I p l → x p = false) : Eval D x (single l) = false := by
  let T := (active x).filter (fun p => p ∈ S)
  have hT : T ⊆ S := fun p hp => (Finset.mem_filter.mp hp).2
  have hle : T.card ≤ b := (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  have ho : ∀ p ∈ T, ¬ I p l := by
    intro p hp hi
    have hxp : x p = true := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    exact Bool.false_ne_true ((hoff p hi).symm.trans hxp)
  rw [P.ignore x (fun p => decide (p ∈ T)) (single l) (single l)
    (fun p hp => by simp [T, active, hp]) (fun _ _ => rfl)]
  exact P.rejectLine l hl T hT ho hle

theorem Problem.noLine (P : Problem I D S W a b) {p : Fin N} (hp : p ∈ S) :
    Eval D (single p) (fun _ => false) = false :=
  P.pointNeg hp _ (by simp [active]) (fun _ _ => rfl)

theorem Problem.noPoint (P : Problem I D S W a b) {l : Fin N} (hl : l ∈ W) :
    Eval D (fun _ => false) (single l) = false :=
  P.lineNeg hl _ (by simp [active]) (fun _ _ => rfl)

theorem Problem.outsidePoint (P : Problem I D S W a b) {p : Fin N} (hp : p ∉ S)
    (y : Fin N → Bool) : Eval D (single p) y = Eval D (fun _ => false) y :=
  P.ignore _ _ _ _ (fun v hv => by
    have hne : v ≠ p := fun e => hp (e ▸ hv)
    simp [single, hne]) (fun _ _ => rfl)

theorem Problem.outsideLine (P : Problem I D S W a b) {l : Fin N} (hl : l ∉ W)
    (x : Fin N → Bool) : Eval D x (single l) = Eval D x (fun _ => false) :=
  P.ignore _ _ _ _ (fun _ _ => rfl) (fun v hv => by
    have hne : v ≠ l := fun e => hl (e ▸ hv)
    simp [single, hne])

theorem Problem.noNonedge (P : Problem I D S W a b) (ha : 1 ≤ a) {p l : Fin N}
    (hp : p ∈ S) (_hl : l ∈ W) (hn : ¬ I p l) : Eval D (single p) (single l) = false := by
  apply P.pointNeg hp
  · have e : active (single l) = {l} := by ext; simp [active, single]
    simpa [e] using ha
  · intro u hi
    have hne : u ≠ l := fun h => hn (h ▸ hi)
    simp [single, hne]

end PEqualNP.Outside.L_meta_1726_aux

namespace PEqualNP.Outside.L_meta_1726_aux.Geometry

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def pointsOn (l : Fin N) : Finset (Fin N) := Finset.univ.filter fun p => I p l

def linesThrough (p : Fin N) : Finset (Fin N) := Finset.univ.filter fun l => I p l

theorem mem_pointsOn {p l : Fin N} : p ∈ pointsOn I l ↔ I p l := by
  simp [pointsOn]

theorem mem_linesThrough {p l : Fin N} : l ∈ linesThrough I p ↔ I p l := by
  simp [linesThrough]

theorem lines_inter_card_le_one
    (hUnique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l l' : Fin N) (hne : l ≠ l') : ((pointsOn I l) ∩ (pointsOn I l')).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro p p' hp hp'
  by_contra hpne
  obtain ⟨j, _, hj⟩ := hUnique p p' hpne
  obtain ⟨hpl, hpl'⟩ := Finset.mem_inter.mp hp
  obtain ⟨hp'l, hp'l'⟩ := Finset.mem_inter.mp hp'
  exact hne ((hj l ⟨(mem_pointsOn I).mp hpl, (mem_pointsOn I).mp hp'l⟩).trans
    (hj l' ⟨(mem_pointsOn I).mp hpl', (mem_pointsOn I).mp hp'l'⟩).symm)

theorem points_inter_card_le_one
    (hUnique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p p' : Fin N) (hne : p ≠ p') : ((linesThrough I p) ∩ (linesThrough I p')).card ≤ 1 := by
  obtain ⟨j, _, hj⟩ := hUnique p p' hne
  apply Finset.card_le_one_iff.mpr
  intro l l' hl hl'
  obtain ⟨hpl, hp'l⟩ := Finset.mem_inter.mp hl
  obtain ⟨hpl', hp'l'⟩ := Finset.mem_inter.mp hl'
  exact (hj l ⟨(mem_linesThrough I).mp hpl, (mem_linesThrough I).mp hp'l⟩).trans
    (hj l' ⟨(mem_linesThrough I).mp hpl', (mem_linesThrough I).mp hp'l'⟩).symm

theorem linesThrough_card {q : ℕ} (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hLines : ∀ l : Fin N, (pointsOn I l).card = q + 1)
    (hUnique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (linesThrough I p).card = q + 1 := by
  let A := fun l : Fin N => (pointsOn I l).erase p
  have hA (l : Fin N) (hl : l ∈ linesThrough I p) : (A l).card = q := by
    have hpl : p ∈ pointsOn I l := (mem_pointsOn I).mpr ((mem_linesThrough I).mp hl)
    simp [A, Finset.card_erase_of_mem hpl, hLines l]
  have hdisj : ∀ l ∈ linesThrough I p, ∀ j ∈ linesThrough I p, l ≠ j → Disjoint (A l) (A j) := by
    intro l hl j hj hlne
    refine Finset.disjoint_left.mpr ?_
    intro p' hpl hpj
    obtain ⟨hpne, hp'l⟩ := Finset.mem_erase.mp hpl
    have hp'j := (Finset.mem_erase.mp hpj).2
    obtain ⟨l', _, huniq⟩ := hUnique p p' hpne.symm
    exact hlne ((huniq l ⟨(mem_linesThrough I).mp hl, (mem_pointsOn I).mp hp'l⟩).trans
      (huniq j ⟨(mem_linesThrough I).mp hj, (mem_pointsOn I).mp hp'j⟩).symm)
  have hcover : (linesThrough I p).biUnion A = (Finset.univ : Finset (Fin N)).erase p := by
    ext p'
    constructor
    · intro hp'
      obtain ⟨l, _, hpl⟩ := Finset.mem_biUnion.mp hp'
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hpl).1, Finset.mem_univ _⟩
    · intro hp'
      have hpne := (Finset.mem_erase.mp hp').1
      obtain ⟨l, ⟨hpl, hp'l⟩, _⟩ := hUnique p p' hpne.symm
      exact Finset.mem_biUnion.mpr ⟨l, (mem_linesThrough I).mpr hpl,
        Finset.mem_erase.mpr ⟨hpne, (mem_pointsOn I).mpr hp'l⟩⟩
  have hcount : (linesThrough I p).card * q = N - 1 := by
    calc
      _ = ∑ _l ∈ linesThrough I p, q := by simp
      _ = ∑ l ∈ linesThrough I p, (A l).card := Finset.sum_congr rfl fun l hl => (hA l hl).symm
      _ = ((linesThrough I p).biUnion A).card := (Finset.card_biUnion hdisj).symm
      _ = N - 1 := by rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ p)]; simp
  have hmul : (linesThrough I p).card * q = (q + 1) * q := by
    rw [hcount, hN]
    simp only [Nat.add_sub_cancel]
    ring
  exact (mul_right_cancel₀ (by omega : q ≠ 0)) hmul

def charge (k r : ℕ) : ℕ := min k (r - 1)

theorem charge_le (k r : ℕ) : charge k r ≤ k := min_le_left _ _

theorem charge_succ_le {k r : ℕ} (hr : 1 ≤ r) : charge k r + 1 ≤ r :=
  (Nat.add_le_add_right (min_le_right k (r - 1)) 1).trans (by omega)

theorem charge_zero_small {k r : ℕ} (hr : r ≤ 1) : charge k r = 0 := by
  simp [charge, show r - 1 = 0 by omega]

theorem charge_pay {q k r : ℕ} (hk : k ≤ q) (hr : r ≤ q + 1) :
    k * r ≤ q * charge k r + k := by
  by_cases h : r - 1 ≤ k
  · rw [charge, min_eq_right h]
    calc
      k * r ≤ k * (r - 1 + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = k * (r - 1) + k := by simp [Nat.mul_add]
      _ ≤ q * (r - 1) + k := Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) _
  · rw [charge, min_eq_left (by omega : k ≤ r - 1)]
    calc
      k * r ≤ k * (q + 1) := Nat.mul_le_mul_left _ hr
      _ = q * k + k := by simp [Nat.mul_add, Nat.mul_comm]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def ReferenceBound : Prop :=
  ∀ (n m k : ℕ) (U S : Fin m → Finset (Fin n)) (C : Circuit) (o c : Fin m → ℕ),
    (∀ i j : Fin m, i ≠ j → (U i ∩ U j).card ≤ 1) →
    (∀ i : Fin m, S i ⊆ U i) →
    (∀ i : Fin m, 2 ≤ (S i).card) →
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    ReadsBack n C →
    (∀ (i : Fin m) (p : Fin n),
      (C.wires (List.ofFn (fun a : Fin n => decide (a = p)))).getD (o i) false = true ↔ p ∈ S i) →
    (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun b : Fin n => x b = true)).card ≤ k →
      (∀ b ∈ U i, x b = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
    (∀ i : Fin m, c i ≤ k) →
    (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

theorem sum_charge_le (hRef : ReferenceBound) {n k : ℕ} {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (U S : ι → Finset (Fin n)) (C : Circuit) (o : ι → ℕ)
    (hPair : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → (U i ∩ U j).card ≤ 1)
    (hSub : ∀ i ∈ R, S i ⊆ U i)
    (hOps : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hRead : ReadsBack n C)
    (hPos : ∀ i ∈ R, ∀ p : Fin n,
      (C.wires (List.ofFn fun a : Fin n => decide (a = p))).getD (o i) false = true ↔ p ∈ S i)
    (hNeg : ∀ i ∈ R, ∀ x : Fin n → Bool, (Finset.univ.filter fun b => x b = true).card ≤ k →
      (∀ b ∈ U i, x b = false) → (C.wires (List.ofFn x)).getD (o i) false = false) :
    (∑ i ∈ R, charge k (S i).card) ≤ C.size := by
  let R' := R.filter (fun i => 2 ≤ (S i).card)
  let e : Fin R'.card ≃ R' := R'.equivFin.symm
  have he (r : Fin R'.card) : ((e r : R') : ι) ∈ R ∧ 2 ≤ (S (e r : ι)).card :=
    Finset.mem_filter.mp (e r).property
  have hbound := hRef n R'.card k (fun r => U (e r)) (fun r => S (e r)) C (fun r => o (e r))
    (fun r => charge k (S (e r)).card)
    (fun i j hij => hPair _ (he i).1 _ (he j).1 fun h => hij (e.injective (Subtype.ext h)))
    (fun r => hSub _ (he r).1) (fun r => (he r).2) hOps hRead
    (fun r => hPos _ (he r).1) (fun r => hNeg _ (he r).1)
    (fun r => charge_le k (S (e r)).card) (fun r => charge_succ_le (by have := (he r).2; omega))
  calc
    (∑ i ∈ R, charge k (S i).card) = ∑ i ∈ R', charge k (S i).card := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hn
      apply charge_zero_small
      by_contra hc
      exact hn (Finset.mem_filter.mpr ⟨hi, by omega⟩)
    _ = ∑ i : R', charge k (S (i : ι)).card := by
      rw [Finset.univ_eq_attach]
      exact (Finset.sum_attach R' (fun i : ι => charge k (S i).card)).symm
    _ = ∑ r : Fin R'.card, charge k (S (e r : ι)).card := (Equiv.sum_comp e _).symm
    _ ≤ C.size := hbound

theorem card_le_row_sum {P L : Type*} [DecidableEq P] [DecidableEq L]
    (S : Finset P) (W : Finset L) (E : Finset (P × L))
    (R : P → Finset L) (T : L → Finset P)
    (hCover : ∀ p l, (p, l) ∈ E → (p ∈ S ∧ l ∈ R p) ∨ (l ∈ W ∧ p ∈ T l)) :
    E.card ≤ (∑ p ∈ S, (R p).card) + ∑ l ∈ W, (T l).card := by
  let A := S.biUnion (fun p => ({p} : Finset P) ×ˢ R p)
  let B := W.biUnion (fun l => T l ×ˢ ({l} : Finset L))
  have hSub : E ⊆ A ∪ B := by
    rintro ⟨p, l⟩ hE
    rcases hCover p l hE with ⟨hp, hl⟩ | ⟨hl, hp⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_product.mpr ⟨by simp, hl⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨l, hl, Finset.mem_product.mpr ⟨hp, by simp⟩⟩)
  have hA : A.card ≤ ∑ p ∈ S, (R p).card := by
    simpa [A, Finset.card_product] using (Finset.card_biUnion_le (s := S) (t := fun p => ({p} : Finset P) ×ˢ R p))
  have hB : B.card ≤ ∑ l ∈ W, (T l).card := by
    simpa [B, Finset.card_product] using (Finset.card_biUnion_le (s := W) (t := fun l => T l ×ˢ ({l} : Finset L)))
  exact (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hA hB))

theorem sum_row_pay {ι α : Type*} {q k : ℕ} (hk : k ≤ q) (S : Finset ι) (R : ι → Finset α)
    (hCap : ∀ i ∈ S, (R i).card ≤ q + 1) :
    k * (∑ i ∈ S, (R i).card) ≤ q * (∑ i ∈ S, charge k (R i).card) + k * S.card := by
  rw [Finset.mul_sum, Finset.mul_sum]
  have h := Finset.sum_le_sum (s := S) (fun i hi => charge_pay hk (hCap i hi))
  simpa [Finset.sum_add_distrib, Nat.mul_comm] using h

theorem sigma_of_rows {P L : Type*} [DecidableEq P] [DecidableEq L] {q k s : ℕ}
    (hk : k ≤ q) (S : Finset P) (W : Finset L) (E : Finset (P × L))
    (R : P → Finset L) (T : L → Finset P)
    (hCover : ∀ p l, (p, l) ∈ E → (p ∈ S ∧ l ∈ R p) ∨ (l ∈ W ∧ p ∈ T l))
    (hR : ∀ p ∈ S, (R p).card ≤ q + 1) (hT : ∀ l ∈ W, (T l).card ≤ q + 1)
    (hSum : (∑ p ∈ S, charge k (R p).card) + (∑ l ∈ W, charge k (T l).card) ≤ s) :
    k * E.card ≤ q * s + k * (S.card + W.card) := by
  calc
    _ ≤ k * ((∑ p ∈ S, (R p).card) + ∑ l ∈ W, (T l).card) :=
      Nat.mul_le_mul_left _ (card_le_row_sum S W E R T hCover)
    _ ≤ q * ((∑ p ∈ S, charge k (R p).card) + ∑ l ∈ W, charge k (T l).card) + k * (S.card + W.card) := by
      rw [Nat.mul_add k, Nat.mul_add q, Nat.mul_add k]
      have h := Nat.add_le_add (sum_row_pay hk S R hR) (sum_row_pay hk W T hT)
      omega
    _ ≤ q * s + k * (S.card + W.card) := Nat.add_le_add_right (Nat.mul_le_mul_left _ hSum) _

theorem gateAt_mem (D : Circuit) {j : ℕ} (hj : j < D.gates.length) : gateAt D j ∈ D.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

end PEqualNP.Outside.L_meta_1726_aux.Geometry

namespace PEqualNP.Outside.L_meta_1726_aux.StarBins

variable {N : ℕ} (H : Finset ℕ) (A B : ℕ → Finset (Fin N))

def pointBin (p : Fin N) : Finset ℕ :=
  H.filter fun h => A h = {p} ∧ (B h).Nonempty

def lineBin (w : Fin N) : Finset ℕ :=
  H.filter fun h => B h = {w} ∧ 1 < (A h).card

def lineRow (p : Fin N) : Finset (Fin N) := (pointBin H A B p).biUnion B

def pointRow (w : Fin N) : Finset (Fin N) := (lineBin H A B w).biUnion A

theorem pointBin_mem {p : Fin N} {h : ℕ} :
    h ∈ pointBin H A B p ↔ h ∈ H ∧ A h = {p} ∧ (B h).Nonempty := by
  simp [pointBin]

theorem lineBin_mem {w : Fin N} {h : ℕ} :
    h ∈ lineBin H A B w ↔ h ∈ H ∧ B h = {w} ∧ 1 < (A h).card := by
  simp [lineBin]

theorem lineRow_mem {p w : Fin N} :
    w ∈ lineRow H A B p ↔ ∃ h ∈ pointBin H A B p, w ∈ B h := by
  simp [lineRow]

theorem pointRow_mem {p w : Fin N} :
    p ∈ pointRow H A B w ↔ ∃ h ∈ lineBin H A B w, p ∈ A h := by
  simp [pointRow]

theorem split (I : Fin N → Fin N → Prop)
    (noFour : ∀ ⦃p p' w w' : Fin N⦄,
      p ≠ p' → w ≠ w' → I p w → I p w' → I p' w → I p' w' → False)
    (legal : ∀ h ∈ H, ∀ p ∈ A h, ∀ w ∈ B h, I p w)
    {h : ℕ} (hh : h ∈ H) {p w : Fin N} (hp : p ∈ A h) (hw : w ∈ B h) :
    w ∈ lineRow H A B p ∨ p ∈ pointRow H A B w := by
  by_cases hA : (A h).card = 1
  · obtain ⟨p', hA'⟩ := Finset.card_eq_one.mp hA
    have e : p = p' := by simpa [hA'] using hp
    subst p'
    left
    exact (lineRow_mem H A B).2 ⟨h,
      (pointBin_mem H A B).2 ⟨hh, hA', ⟨w, hw⟩⟩, hw⟩
  · have ha : 1 < (A h).card := by
      have hpos := Finset.card_pos.mpr ⟨p, hp⟩
      omega
    have hb : (B h).card = 1 := by
      by_contra hne
      have hpos := Finset.card_pos.mpr ⟨w, hw⟩
      have htwo : 1 < (B h).card := by omega
      obtain ⟨p₁, hp₁, p₂, hp₂, hpp⟩ := Finset.one_lt_card.mp ha
      obtain ⟨w₁, hw₁, w₂, hw₂, hww⟩ := Finset.one_lt_card.mp htwo
      exact noFour hpp hww (legal h hh p₁ hp₁ w₁ hw₁) (legal h hh p₁ hp₁ w₂ hw₂)
        (legal h hh p₂ hp₂ w₁ hw₁) (legal h hh p₂ hp₂ w₂ hw₂)
    obtain ⟨w', hB⟩ := Finset.card_eq_one.mp hb
    have e : w = w' := by simpa [hB] using hw
    subst w'
    right
    exact (pointRow_mem H A B).2 ⟨h, (lineBin_mem H A B).2 ⟨hh, hB, ha⟩, hp⟩

theorem term_budget :
    (∑ p : Fin N, (pointBin H A B p).card) + (∑ w : Fin N, (lineBin H A B w).card) ≤ H.card := by
  let bins : Sum (Fin N) (Fin N) → Finset ℕ := Sum.elim (pointBin H A B) (lineBin H A B)
  have dh : (↑(Finset.univ : Finset (Sum (Fin N) (Fin N))) : Set (Sum (Fin N) (Fin N))).PairwiseDisjoint bins := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro h hx hy
    cases x with
    | inl p =>
      have hx' := (pointBin_mem H A B).1 hx
      cases y with
      | inl p' =>
        have hy' := (pointBin_mem H A B).1 hy
        have e : p = p' := Finset.singleton_injective (hx'.2.1.symm.trans hy'.2.1)
        exact hxy (congrArg Sum.inl e)
      | inr w =>
        have hy' := (lineBin_mem H A B).1 hy
        simpa [hx'.2.1] using hy'.2.2
    | inr w =>
      have hx' := (lineBin_mem H A B).1 hx
      cases y with
      | inl p =>
        have hy' := (pointBin_mem H A B).1 hy
        simpa [hy'.2.1] using hx'.2.2
      | inr w' =>
        have hy' := (lineBin_mem H A B).1 hy
        have e : w = w' := Finset.singleton_injective (hx'.2.1.symm.trans hy'.2.1)
        exact hxy (congrArg Sum.inr e)
  have sub : Finset.univ.biUnion bins ⊆ H := by
    intro h hh
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hh
    cases i with
    | inl p => exact ((pointBin_mem H A B).1 hi).1
    | inr w => exact ((lineBin_mem H A B).1 hi).1
  have hc := Finset.card_le_card sub
  rw [Finset.card_biUnion dh, Fintype.sum_sum_type] at hc
  simpa [bins] using hc

end PEqualNP.Outside.L_meta_1726_aux.StarBins

namespace PEqualNP.Outside.L_meta_1726_aux.Boundary

open CircuitLowerBounds MetaComplexity.NestedCover

abbrev pointDeg (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0

abbrev lineDeg (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

def pointGates (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => lineDeg N C (N + N + j) = 0

def lineGates (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => pointDeg N C (N + N + j) = 0

def mixedGates (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j =>
    0 < pointDeg N C (N + N + j) ∧ 0 < lineDeg N C (N + N + j)

def boundaryPort (N : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  pointDeg N C w = 0 ∧ 0 < lineDeg N C w ∧
    ∃ j < C.gates.length, w ∈ (gateAt C j).inputs ∧
      0 < pointDeg N C (N + N + j) ∧ 0 < lineDeg N C (N + N + j)

def boundary (N : ℕ) (C : Circuit) : Finset ℕ :=
  (mixedGates N C).biUnion fun j =>
    (gateAt C j).inputs.toFinset.filter fun w => pointDeg N C w = 0 ∧ 0 < lineDeg N C w

theorem mem_boundary (N : ℕ) (C : Circuit) (w : ℕ) :
    w ∈ boundary N C ↔ boundaryPort N C w := by
  simp only [boundary, Finset.mem_biUnion, mixedGates, Finset.mem_filter, Finset.mem_range,
    List.mem_toFinset, boundaryPort]
  aesop

theorem point_ncard (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ lineDeg N C (N + N + j) = 0} = (pointGates N C).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [pointGates]

theorem line_ncard (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ pointDeg N C (N + N + j) = 0} = (lineGates N C).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [lineGates]

theorem mixed_ncard (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧
        0 < pointDeg N C (N + N + j) ∧ 0 < lineDeg N C (N + N + j)} = (mixedGates N C).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [mixedGates]

theorem boundary_card_le (N : ℕ) (C : Circuit)
    (arity : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (boundary N C).card ≤ 2 * (mixedGates N C).card := by
  unfold boundary
  refine Finset.card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ j ∈ mixedGates N C, (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hj']
        exact List.getElem_mem _
      exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans (arity _ hmem).2.le)
    _ = _ := by simp [Nat.mul_comm]

theorem gate_budget (N : ℕ) (C : Circuit)
    (nonzero : ∀ j < C.gates.length,
      pointDeg N C (N + N + j) = 0 → 0 < lineDeg N C (N + N + j)) :
    (pointGates N C).card + (lineGates N C).card + (mixedGates N C).card ≤ C.size := by
  have dPL : Disjoint (pointGates N C) (lineGates N C) := by
    apply Finset.disjoint_left.mpr
    intro j hp hl
    have hp' : j < C.gates.length ∧ lineDeg N C (N + N + j) = 0 := by
      simpa [pointGates] using hp
    have hl' : pointDeg N C (N + N + j) = 0 := (Finset.mem_filter.mp hl).2
    exact (Nat.ne_of_gt (nonzero j hp'.1 hl')) hp'.2
  have dM : Disjoint (pointGates N C ∪ lineGates N C) (mixedGates N C) := by
    apply Finset.disjoint_left.mpr
    intro j ha hm
    have hp : 0 < pointDeg N C (N + N + j) ∧ 0 < lineDeg N C (N + N + j) :=
      (Finset.mem_filter.mp hm).2
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Nat.ne_of_gt hp.2) (Finset.mem_filter.mp ha).2
    · exact (Nat.ne_of_gt hp.1) (Finset.mem_filter.mp ha).2
  have sub : pointGates N C ∪ lineGates N C ∪ mixedGates N C ⊆ Finset.range C.gates.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact (Finset.mem_filter.mp hj).1
      · exact (Finset.mem_filter.mp hj).1
    · exact (Finset.mem_filter.mp hj).1
  have hb := Finset.card_le_card sub
  simpa only [Finset.card_union_of_disjoint dM, Finset.card_union_of_disjoint dPL, Finset.card_range,
     Circuit.size] using hb

end PEqualNP.Outside.L_meta_1726_aux.Boundary

namespace PEqualNP.Outside.L_meta_1726_aux.CircuitOps

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def Binary (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def deg (C : Circuit) (n : ℕ) (M : Finset ℕ) (w : ℕ) : ℕ :=
  (C.lineDegrees n M).getD w 0

private def run {α : Type} (step : Gate → List α → α) (gs : List Gate) (xs : List α) : List α :=
  gs.foldl (fun l g => l ++ [step g l]) xs

private theorem run_length {α : Type} (step : Gate → List α → α) (gs : List Gate)
    (xs : List α) : (run step gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run step gs (xs ++ [step g xs])).length = xs.length + (g :: gs).length
    rw [ih]
    simp
    omega

private theorem run_getD {α : Type} (step : Gate → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (d : α) (hi : i < xs.length) :
    (run step gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run step gs (xs ++ [step g xs])).getD i d = xs.getD i d
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private theorem run_append {α : Type} (step : Gate → List α → α) (gs hs : List Gate) (xs : List α) :
    run step (gs ++ hs) xs = run step hs (run step gs xs) := by
  simp [run, List.foldl_append]

private theorem run_gate {α : Type} (step : Gate → List α → α) (gs : List Gate)
    (xs : List α) (j : ℕ) (hj : j < gs.length) (d : α) :
    (run step gs xs).getD (xs.length + j) d = step gs[j] (run step (gs.take j) xs) := by
  let a := run step (gs.take j) xs
  have ha : a.length = xs.length + j := by
    simp [a, run_length, Nat.min_eq_left hj.le]
  have he : run step gs xs = run step (gs[j] :: gs.drop (j + 1)) a := by
    unfold a
    rw [← run_append, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  rw [he]
  change (run step (gs.drop (j + 1)) (a ++ [step gs[j] a])).getD (xs.length + j) d = _
  rw [run_getD _ _ _ _ _ (by simp [ha]), List.getD_append_right _ _ _ _ (by omega)]
  simp [ha, a]

private def valStep (g : Gate) (xs : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun w => xs.getD w false)

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) : val C x i = x i := by
  change (run valStep C.gates (List.ofFn x)).getD i false = x i
  have hi : (i : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

theorem val_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.size ≤ w) :
    val C x w = false := by
  change (run valStep C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

private theorem gateAt_eq (C : Circuit) {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

theorem val_gate {n : ℕ} (C : Circuit) (hR : ReadsBack n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (val C x)) := by
  change (run valStep C.gates (List.ofFn x)).getD (n + j) false = _
  have h := run_gate valStep C.gates (List.ofFn x) j hj false
  simp only [List.length_ofFn] at h
  rw [h, gateAt_eq _ hj]
  unfold valStep
  have hmap : C.gates[j].inputs.map (fun w => (run valStep (C.gates.take j) (List.ofFn x)).getD w false)
      = C.gates[j].inputs.map (val C x) := by
    apply List.map_congr_left
    intro w hw
    have hw' := hR j hj w (by rwa [gateAt_eq _ hj])
    have he := run_append valStep (C.gates.take j) (C.gates.drop j) (List.ofFn x)
    rw [List.take_append_drop] at he
    unfold val Circuit.wires
    change _ = (run valStep C.gates (List.ofFn x)).getD w false
    rw [he]
    exact (run_getD valStep (C.gates.drop j) _ _ _
      (by simpa [run_length, Nat.min_eq_left hj.le] using hw')).symm
  exact congrArg (C.gates[j].op.eval) hmap

theorem deg_input (C : Circuit) (n : ℕ) (M : Finset ℕ) (i : ℕ) (hi : i < n) :
    deg C n M i = if i ∈ M then 1 else 0 := by
  let xs := (List.range n).map fun w => if w ∈ M then 1 else 0
  change (run Gate.lineDegree C.gates xs).getD i 0 = _
  have hix : i < xs.length := by simpa [xs] using hi
  rw [run_getD _ _ _ _ _ hix, List.getD_eq_getElem _ _ hix]
  simp [xs]

theorem deg_oob (C : Circuit) (n : ℕ) (M : Finset ℕ) (i : ℕ) (hi : n + C.size ≤ i) :
    deg C n M i = 0 := by
  let xs := (List.range n).map fun w => if w ∈ M then 1 else 0
  change (run Gate.lineDegree C.gates xs).getD i 0 = 0
  exact List.getD_eq_default _ _ (by simpa [run_length, xs, Circuit.size] using hi)

private theorem deg_gate (C : Circuit) (n : ℕ) (M : Finset ℕ) (hR : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    deg C n M (n + j) =
      @ite ℕ ((gateAt C j).op = .and) (lineDegreeGateOpDecEq _ _)
        (((gateAt C j).inputs.map (deg C n M)).sum)
        (((gateAt C j).inputs.map (deg C n M)).foldr max 0) := by
  let xs := (List.range n).map fun w => if w ∈ M then 1 else 0
  have h : (run Gate.lineDegree C.gates xs).getD (n+j) 0 =
      Gate.lineDegree C.gates[j] (run Gate.lineDegree (C.gates.take j) xs) := by
    simpa [xs] using run_gate Gate.lineDegree C.gates xs j hj 0
  rw [show deg C n M (n+j) = (run Gate.lineDegree C.gates xs).getD (n+j) 0 from rfl, h, gateAt_eq _ hj]
  have hmap : C.gates[j].inputs.map (fun w => (run Gate.lineDegree (C.gates.take j) xs).getD w 0)
      = C.gates[j].inputs.map (deg C n M) := by
    apply List.map_congr_left
    intro w hw
    have hw' := hR j hj w (by rwa [gateAt_eq _ hj])
    have he := run_append Gate.lineDegree (C.gates.take j) (C.gates.drop j) xs
    rw [List.take_append_drop] at he
    change _ = (run Gate.lineDegree C.gates xs).getD w 0
    rw [he]
    exact (run_getD Gate.lineDegree (C.gates.drop j) _ _ _
      (by simpa [run_length, xs, Nat.min_eq_left hj.le] using hw')).symm
  simpa only [Gate.lineDegree] using congrArg (fun l : List ℕ =>
    @ite ℕ (C.gates[j].op = .and) (lineDegreeGateOpDecEq _ _) l.sum (l.foldr max 0)) hmap

theorem deg_read_le (C : Circuit) (n : ℕ) (M : Finset ℕ) (hB : Binary C) (hR : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
    deg C n M w ≤ deg C n M (n + j) := by
  have hg : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq _ hj]
    exact (hB _ (List.getElem_mem _)).2
  obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C j).inputs = [a, b] := by
    cases he : (gateAt C j).inputs with
    | nil => simp [he] at hg
    | cons a L =>
      cases L with
      | nil => simp [he] at hg
      | cons b L =>
        have hl : L = [] := by simpa [he] using hg
        exact ⟨a, b, by rw [hl]⟩
  rw [deg_gate C n M hR j hj, hab]
  rw [hab] at hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl <;> split <;> simp

theorem deg_pos_or (N : ℕ) (C : Circuit) (hB : Binary C) (hR : ReadsBack (N+N) C)
    (w : ℕ) (hw : w < N+N+C.gates.length) :
    0 < deg C (N+N) (Finset.range N) w ∨ 0 < deg C (N+N) (Finset.Ico N (N+N)) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hr : w < N+N
    · by_cases hp : w < N
      · left
        rw [deg_input C _ _ _ hr, ite_eq_left (Finset.mem_range.mpr hp)]
        decide
      · right
        rw [deg_input C _ _ _ hr, ite_eq_left (Finset.mem_Ico.mpr ⟨by omega, hr⟩)]
        decide
    · let j := w-(N+N)
      have hej : N+N+j = w := by unfold j; omega
      have hj : j < C.gates.length := by omega
      have hg := (hB C.gates[j] (List.getElem_mem _)).2
      rw [← gateAt_eq C hj] at hg
      obtain ⟨t, ht⟩ : ∃ t, t ∈ (gateAt C j).inputs := by
        cases hh : (gateAt C j).inputs with
        | nil => simp [hh] at hg
        | cons a l => exact ⟨a, by simp⟩
      have hlt : t < w := by rw [← hej]; exact hR j hj t ht
      rcases ih t hlt (hlt.trans hw) with he | he
      · left
        rw [← hej]
        exact he.trans_le (deg_read_le C _ _ hB hR j hj t ht)
      · right
        rw [← hej]
        exact he.trans_le (deg_read_le C _ _ hB hR j hj t ht)

private def push (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

private theorem size_push (C : Circuit) (g : Gate) : (push C g).size = C.size + 1 := by
  simp [push, Circuit.size]

private theorem push_ok {n : ℕ} (C : Circuit) (hB : Binary C) (hR : ReadsBack n C) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (hread : ∀ w ∈ g.inputs, w < n + C.size) : Binary (push C g) ∧ ReadsBack n (push C g) := by
  constructor
  · intro a ha
    simp only [push, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hB a ha
    · exact hg
  · intro j hj w hw
    simp only [push, List.length_append, List.length_singleton] at hj
    by_cases hlt : j < C.gates.length
    · have he : gateAt (push C g) j = gateAt C j := by
        unfold gateAt push
        exact List.getD_append _ _ _ _ hlt
      exact hR j hlt w (he ▸ hw)
    · have he : j = C.gates.length := by omega
      subst j
      have he : gateAt (push C g) C.gates.length = g := by simp [gateAt, push]
      exact hread w (he ▸ hw)

private theorem val_push_old {n : ℕ} (C : Circuit) (g : Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + C.size) : val (push C g) x w = val C x w := by
  change (run valStep (C.gates ++ [g]) (List.ofFn x)).getD w false = _
  rw [run_append, run_getD _ _ _ _ _ (by simpa [run_length, Circuit.size] using hw)]
  rfl

private theorem val_push_new {n : ℕ} (C : Circuit) (g : Gate) (x : Fin n → Bool) :
    val (push C g) x (n + C.size) = g.op.eval (g.inputs.map (val C x)) := by
  change (run valStep (C.gates ++ [g]) (List.ofFn x)).getD (n + C.size) false = _
  rw [run_append]
  have he : (run valStep C.gates (List.ofFn x)).length = n + C.size := by
    simp [run_length, Circuit.size]
  change ((run valStep C.gates (List.ofFn x)) ++ [valStep g (run valStep C.gates (List.ofFn x))]).getD (n + C.size) false = _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [he, Nat.sub_self, List.getD_cons_zero]
  rfl

theorem projectLines (N : ℕ) (C : Circuit) (hB : Binary C) (hR : ReadsBack (N+N) C) :
    ∃ L : Circuit, ∃ f : ℕ → ℕ, Binary L ∧ ReadsBack N L ∧
      L.size ≤ Set.ncard {j | j < C.gates.length ∧ deg C (N+N) (Finset.range N) (N+N+j) = 0} ∧
      (∀ w, deg C (N+N) (Finset.range N) w = 0 → ∀ y : Fin N → Bool,
        val L y (f w) = val C (Fin.append (fun _ : Fin N => false) y) w) := by
  let clean (w : ℕ) := deg C (N+N) (Finset.range N) w = 0
  let count (k : ℕ) := ((Finset.range k).filter fun j => clean (N+N+j)).card
  have hcount (k : ℕ) : count (k+1) = count k + (if clean (N+N+k) then 1 else 0) := by
    unfold count
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : clean (N+N+k)
    · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem]
      simp
    · rw [ite_eq_right h, ite_eq_right h, Nat.add_zero]
  have buildPrefix (k : ℕ) (hk : k ≤ C.gates.length) :
      ∃ L : Circuit, ∃ f : ℕ → ℕ, Binary L ∧ ReadsBack N L ∧ L.size ≤ count k ∧
        ∀ w < N+N+k, clean w → f w < N+L.size ∧ ∀ y : Fin N → Bool,
          val L y (f w) = val C (Fin.append (fun _ : Fin N => false) y) w := by
    induction k with
    | zero =>
      let L : Circuit := ⟨[], 0⟩
      refine ⟨L, (· - N), ?_, ?_, ?_, ?_⟩
      · simp [L, Binary]
      · simp [L, ReadsBack]
      · simp [L, Circuit.size]
      · intro w hw hclean
        have hn : N ≤ w := by
          by_contra! h
          change deg C (N+N) (Finset.range N) w = 0 at hclean
          rw [deg_input C (N+N) (Finset.range N) w (by omega),
            ite_eq_left (Finset.mem_range.mpr h)] at hclean
          omega
        have hi : w - N < N := by omega
        let i : Fin N := ⟨w - N, hi⟩
        refine ⟨by simpa [L, Circuit.size] using hi, fun y => ?_⟩
        have hwi : (Fin.natAdd N i).val = w := by
          simp [i]; omega
        calc
          val L y (w-N) = y i := val_input L y i
          _ = (Fin.append (fun _ : Fin N => false) y) (Fin.natAdd N i) :=
            (Fin.append_right (fun _ : Fin N => false) y i).symm
          _ = val C (Fin.append (fun _ : Fin N => false) y) w := by rw [← hwi, val_input]
    | succ k ih =>
      obtain ⟨L, f, hL, hLR, hs, himg⟩ := ih (by omega)
      let w₀ := N+N+k
      by_cases hc : clean w₀
      · have hcg : k < C.gates.length := by omega
        let g := gateAt C k
        let g' : Gate := ⟨g.op, g.inputs.map f⟩
        have hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
          unfold g
          rw [gateAt_eq _ hcg]
          exact hB _ (List.getElem_mem _)
        have hOld (r : ℕ) (hr : r ∈ g.inputs) :
            f r < N+L.size ∧ ∀ y : Fin N → Bool,
              val L y (f r) = val C (Fin.append (fun _ : Fin N => false) y) r := by
          have hdeg := deg_read_le C (N+N) (Finset.range N) hB hR k hcg r hr
          have hcz : deg C (N+N) (Finset.range N) (N+N+k) = 0 := hc
          have hrc : clean r := by unfold clean; omega
          exact himg r (hR k hcg r hr) hrc
        have hOK := push_ok L hL hLR g' (by simpa [g'] using hg) (by
          intro r hr
          obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
          exact (hOld r' hr').1)
        let f' := fun w => if w = w₀ then N+L.size else f w
        refine ⟨push L g', f', hOK.1, hOK.2, ?_, ?_⟩
        · rw [size_push, hcount, ite_eq_left hc]
          omega
        · intro w hw hwc
          by_cases he : w = w₀
          · subst w
            simp only [f', ite_eq_left rfl]
            refine ⟨by rw [size_push]; omega, fun y => ?_⟩
            rw [val_push_new, show w₀ = N+N+k from rfl, val_gate C hR _ k hcg]
            have hm : g'.inputs.map (val L y) = g.inputs.map (val C (Fin.append (fun _ : Fin N => false) y)) := by
              change (g.inputs.map f).map _ = _
              rw [List.map_map]
              exact List.map_congr_left (fun r hr => (hOld r hr).2 y)
            rw [show g'.op = g.op from rfl, hm]
          · have hh := himg w (by unfold w₀ at he; omega) hwc
            simp only [f', ite_eq_right he]
            refine ⟨by rw [size_push]; omega, fun y => ?_⟩
            rw [val_push_old _ _ _ _ hh.1, hh.2 y]
      · refine ⟨L, f, hL, hLR, ?_, ?_⟩
        · rw [hcount, ite_eq_right hc, Nat.add_zero]
          exact hs
        · intro w hw hwc
          have he : w ≠ w₀ := fun he => hc (he ▸ hwc)
          exact himg w (by unfold w₀ at he; omega) hwc
  obtain ⟨L, f, hL, hLR, hs, himg⟩ := buildPrefix C.gates.length le_rfl
  refine ⟨L, (fun w => if w < N+N+C.gates.length then f w else N+L.size), hL, hLR, ?_, ?_⟩
  · have hset : {j | j < C.gates.length ∧ deg C (N+N) (Finset.range N) (N+N+j) = 0} =
        ↑((Finset.range C.gates.length).filter fun j => clean (N+N+j)) := by
      ext j
      simp [clean]
    rw [hset, Set.ncard_coe_finset]
    exact hs
  · intro w hw y
    change val L y (if w < N+N+C.gates.length then f w else N+L.size) = _
    by_cases ht : w < N+N+C.gates.length
    · rw [ite_eq_left ht]
      exact (himg w ht hw).2 y
    · rw [ite_eq_right ht, val_oob L y _ le_rfl, val_oob C _ w (by unfold Circuit.size; omega)]

private theorem orChain (n : ℕ) (C : Circuit) (hB : Binary C) (hR : ReadsBack n C)
    (u : ℕ) (hu : u < n+C.size) (l : List ℕ) (hl : ∀ w ∈ l, w < n+C.size) :
    ∃ D : Circuit, ∃ o : ℕ, Binary D ∧ ReadsBack n D ∧ C.size ≤ D.size ∧
      D.size ≤ C.size + l.length ∧ o < n+D.size ∧
      (∀ (x : Fin n → Bool) w, w < n+C.size → val D x w = val C x w) ∧
      (∀ x : Fin n → Bool, val D x o = true ↔ ∃ w ∈ u :: l, val C x w = true) := by
  induction l generalizing C u with
  | nil => exact ⟨C, u, hB, hR, le_rfl, by simp, hu, fun _ _ _ => rfl, by simp⟩
  | cons v l ih =>
    let g : Gate := ⟨.or, [u,v]⟩
    have hv := hl v (by simp)
    have hOK := push_ok C hB hR g (by simp [g]) (by
      intro w hw
      simp [g] at hw
      rcases hw with rfl | rfl <;> assumption)
    obtain ⟨D, o, hD, hDR, hmin, hmax, ho, hp, he⟩ :=
      ih (push C g) hOK.1 hOK.2 (n+C.size) (by rw [size_push]; omega) (by
        intro w hw
        have h := hl w (List.mem_cons_of_mem _ hw)
        rw [size_push]
        omega)
    refine ⟨D, o, hD, hDR, ?_, ?_, ho, ?_, ?_⟩
    · rw [size_push] at hmin
      omega
    · rw [size_push] at hmax
      simp only [List.length_cons]
      omega
    · intro x w hw
      rw [hp x w (by rw [size_push]; omega), val_push_old _ _ _ _ hw]
    · intro x
      rw [he x]
      have hn : val (push C g) x (n+C.size) = (val C x u || val C x v) := by
        rw [val_push_new]
        simp [g, GateOp.eval]
      have hold : ∀ w ∈ l, val (push C g) x w = val C x w := by
        intro w hw
        exact val_push_old _ _ _ _ (hl _ (List.mem_cons_of_mem _ hw))
      constructor
      · rintro ⟨w, hw, ht⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · rw [hn, Bool.or_eq_true] at ht
          rcases ht with hu | hv
          · exact ⟨u, by simp, hu⟩
          · exact ⟨v, by simp, hv⟩
        · exact ⟨w, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw), (hold w hw) ▸ ht⟩
      · rintro ⟨w, hw, ht⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨n+C.size, by simp, by simp [hn, ht]⟩
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact ⟨n+C.size, by simp, by simp [hn, ht]⟩
          · exact ⟨w, List.mem_cons_of_mem _ hw, (hold w hw).symm ▸ ht⟩

private theorem addRow (n : ℕ) (C : Circuit) (hB : Binary C) (hR : ReadsBack n C)
    (l : List ℕ) (hl : ∀ w ∈ l, w < n+C.size) :
    ∃ D : Circuit, ∃ o : Option ℕ, Binary D ∧ ReadsBack n D ∧ C.size ≤ D.size ∧
      D.size ≤ C.size + l.length ∧ (∀ w ∈ o, w < n+D.size) ∧
      (∀ (x : Fin n → Bool) w, w < n+C.size → val D x w = val C x w) ∧
      (∀ x : Fin n → Bool, (o.elim false (val D x)) = true ↔ ∃ w ∈ l, val C x w = true) := by
  cases l with
  | nil =>
    refine ⟨C, none, hB, hR, le_rfl, by simp, by simp, fun _ _ _ => rfl, by simp⟩
  | cons u l =>
    obtain ⟨D, o, hD, hDR, hmin, hmax, ho, hp, he⟩ :=
      orChain n C hB hR u (hl u (by simp)) l (fun w hw => hl w (List.mem_cons_of_mem _ hw))
    refine ⟨D, some o, hD, hDR, hmin, ?_, ?_, hp, he⟩
    · simp only [List.length_cons]
      omega
    · intro w hw
      have hwo : o = w := by simpa using hw
      simpa [hwo] using ho

private theorem aggregateValid (n m : ℕ) (C : Circuit) (hB : Binary C) (hR : ReadsBack n C)
    (rows : Fin m → List ℕ) (hvalid : ∀ i w, w ∈ rows i → w < n+C.size) :
    ∃ D : Circuit, ∃ o : Fin m → Option ℕ, Binary D ∧ ReadsBack n D ∧ C.size ≤ D.size ∧
      D.size ≤ C.size + ∑ i, (rows i).length ∧ (∀ i w, w ∈ o i → w < n+D.size) ∧
      (∀ (x : Fin n → Bool) w, w < n+C.size → val D x w = val C x w) ∧
      (∀ i (x : Fin n → Bool), ((o i).elim false (val D x)) = true ↔ ∃ w ∈ rows i, val C x w = true) := by
  induction m with
  | zero =>
    refine ⟨C, Fin.elim0, hB, hR, le_rfl, by simp, ?_, fun _ _ _ => rfl, ?_⟩
    · intro i
      exact i.elim0
    · intro i
      exact i.elim0
  | succ m ih =>
    obtain ⟨D, o, hD, hDR, hmin, hmax, ho, hp, he⟩ :=
      ih (fun i => rows i.castSucc) (fun i w hw => hvalid i.castSucc w hw)
    obtain ⟨E, t, hE, hER, hmin', hmax', ht, hp', he'⟩ :=
      addRow n D hD hDR (rows (Fin.last m)) (by
        intro w hw
        have h := hvalid (Fin.last m) w hw
        omega)
    refine ⟨E, Fin.lastCases t o, hE, hER, hmin.trans hmin', ?_, ?_, ?_, ?_⟩
    · rw [Fin.sum_univ_castSucc]
      omega
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using ht
      · intro w hw
        have hh := ho j w (by simpa using hw)
        omega
    · intro x w hw
      rw [hp' x w (by omega), hp x w hw]
    · intro i x
      have hbase (w : ℕ) (hw : w ∈ rows (Fin.last m)) : val D x w = val C x w :=
        hp x w (hvalid _ _ hw)
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.lastCases_last, he']
        constructor <;> rintro ⟨w, hw, hh⟩ <;> exact ⟨w, hw, by simpa only [hbase w hw] using hh⟩
      · simp only [Fin.lastCases_castSucc, ← he j x]
        cases hoj : o j with
        | none => rfl
        | some w =>
          have hw : w < n + D.size := ho j w (by simp [hoj])
          simp [hp' x w hw]

theorem aggregate (n m : ℕ) (C : Circuit) (hB : Binary C) (hR : ReadsBack n C)
    (rows : Fin m → List ℕ) :
    ∃ D : Circuit, ∃ o : Fin m → ℕ, Binary D ∧ ReadsBack n D ∧
      D.size ≤ C.size + ∑ i, (rows i).length ∧
      (∀ i (x : Fin n → Bool), val D x (o i) = true ↔ ∃ w ∈ rows i, val C x w = true) := by
  let rows' (i : Fin m) := (rows i).filter fun w => decide (w < n+C.size)
  obtain ⟨D, o, hD, hDR, _, hmax, _, _, he⟩ := aggregateValid n m C hB hR rows' (by
    intro i w hw
    exact of_decide_eq_true (List.mem_filter.mp hw).2)
  refine ⟨D, (fun i => (o i).getD (n+D.size)), hD, hDR, ?_, ?_⟩
  · apply hmax.trans
    exact Nat.add_le_add_left (Finset.sum_le_sum fun i _ => List.length_filter_le ..) _
  · intro i x
    have ho : val D x ((o i).getD (n+D.size)) = (o i).elim false (val D x) := by
      cases h : o i with
      | none => simpa [h] using val_oob D x (n+D.size) le_rfl
      | some w => rfl
    rw [ho, he i x]
    constructor
    · rintro ⟨w, hw, h⟩
      exact ⟨w, (List.mem_filter.mp hw).1, h⟩
    · rintro ⟨w, hw, h⟩
      have hv : w < n + C.size := by
        by_contra! hbad
        simp [val_oob C x w hbad] at h
      exact ⟨w, List.mem_filter.mpr ⟨hw, decide_eq_true hv⟩, h⟩

end PEqualNP.Outside.L_meta_1726_aux.CircuitOps

namespace PEqualNP.Outside.L_meta_1726_aux

open CircuitLowerBounds MetaComplexity StarBins
open scoped BigOperators

theorem projectedBound {N q a b : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    {D X Y : Circuit} {S W : Finset (Fin N)} (P : Problem I D S W a b)
    (hRef : Geometry.ReferenceBound) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hLines : ∀ l, (Geometry.pointsOn I l).card = q + 1)
    (hUnique : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ha : 1 ≤ a)
    (hzero : Eval (N := N) D (fun _ => false) (fun _ => false) = false)
    (hX : CircuitOps.Binary X) (hXR : NestedCover.ReadsBack N X)
    (hY : CircuitOps.Binary Y) (hYR : NestedCover.ReadsBack N Y)
    (H : Finset ℕ) (ph lh : ℕ → ℕ) (T : Set ℕ)
    (hTrans : ∀ x y : Fin N → Bool, Eval D x y = true ↔
      Eval D x (fun _ => false) = true ∨ ∃ h ∈ H,
        wireVal Y y (lh h) = true ∧ (h ∈ T ∨ wireVal X x (ph h) = true))
    (hcost : X.size + Y.size + H.card ≤ 5 * D.size) :
    min (min a b) q * ((S ×ˢ W).filter fun pl => I pl.1 pl.2).card ≤
      5 * q * D.size + min (min a b) q * (S.card + W.card) := by
  classical
  have noLine (p : Fin N) : Eval D (single p) (fun _ => false) = false := by
    by_cases hp : p ∈ S
    · exact P.noLine hp
    · rw [P.outsidePoint hp, hzero]
  have noPoint (l : Fin N) : Eval D (fun _ => false) (single l) = false := by
    by_cases hl : l ∈ W
    · exact P.noPoint hl
    · rw [P.outsideLine hl, hzero]
  let A (h : ℕ) : Finset (Fin N) := Finset.univ.filter
    (fun p => wireVal X (single p) (ph h) = true)
  let B (h : ℕ) : Finset (Fin N) := Finset.univ.filter
    (fun l => wireVal Y (single l) (lh h) = true)
  have memA (h : ℕ) (p : Fin N) : p ∈ A h ↔ wireVal X (single p) (ph h) = true := by simp [A]
  have memB (h : ℕ) (l : Fin N) : l ∈ B h ↔ wireVal Y (single l) (lh h) = true := by simp [B]
  have legal (h : ℕ) (hh : h ∈ H) (p : Fin N) (hp : p ∈ A h)
      (l : Fin N) (hl : l ∈ B h) : I p l := by
    have hpw := (hTrans (single p) (single l)).2
      (Or.inr ⟨h, hh, (memB h l).mp hl, Or.inr ((memA h p).mp hp)⟩)
    have hpS : p ∈ S := by
      by_contra hn
      rw [P.outsidePoint hn, noPoint] at hpw
      contradiction
    have hlW : l ∈ W := by
      by_contra hn
      rw [P.outsideLine hn, noLine] at hpw
      contradiction
    by_contra hn
    rw [P.noNonedge ha hpS hlW hn] at hpw
    contradiction
  have noFour ⦃p p' l l' : Fin N⦄ (hp : p ≠ p') (hl : l ≠ l')
      (h₁ : I p l) (h₂ : I p l') (h₃ : I p' l) (h₄ : I p' l') : False := by
    obtain ⟨j, _, hu⟩ := hUnique p p' hp
    exact hl ((hu l ⟨h₁, h₃⟩).trans (hu l' ⟨h₂, h₄⟩).symm)
  have cover (p : Fin N) (hp : p ∈ S) (l : Fin N) (hl : l ∈ W) (hi : I p l) :
      l ∈ lineRow H A B p ∨ p ∈ pointRow H A B l := by
    have h := (hTrans (single p) (single l)).1 (P.accept p hp l hl hi)
    have hn : ¬ Eval D (single p) (fun _ => false) = true := by rw [noLine]; decide
    obtain ⟨j, hj, hB, hA⟩ := h.resolve_left hn
    have hAX : wireVal X (single p) (ph j) = true := by
      apply hA.resolve_left
      intro hT
      have hz := (hTrans (fun _ => false) (single l)).2 (Or.inr ⟨j, hj, hB, Or.inl hT⟩)
      rw [noPoint] at hz
      contradiction
    exact split H A B I noFour legal hj ((memA j p).2 hAX) ((memB j l).2 hB)
  let rowsY (p : Fin N) := (pointBin H A B p).toList.map lh
  let rowsX (l : Fin N) := (lineBin H A B l).toList.map ph
  obtain ⟨DY, oy, hDY, hDYR, hYSize, hYEval⟩ := CircuitOps.aggregate N N Y hY hYR rowsY
  obtain ⟨DX, ox, hDX, hDXR, hXSize, hXEval⟩ := CircuitOps.aggregate N N X hX hXR rowsX
  have evalY (p : Fin N) (y : Fin N → Bool) : wireVal DY y (oy p) = true ↔
      ∃ h ∈ pointBin H A B p, wireVal Y y (lh h) = true := by
    rw [show wireVal DY y (oy p) = CircuitOps.val DY y (oy p) from rfl, hYEval]
    simp only [rowsY, List.mem_map, Finset.mem_toList, CircuitOps.val, wireVal]
    aesop
  have evalX (l : Fin N) (x : Fin N → Bool) : wireVal DX x (ox l) = true ↔
      ∃ h ∈ lineBin H A B l, wireVal X x (ph h) = true := by
    rw [show wireVal DX x (ox l) = CircuitOps.val DX x (ox l) from rfl, hXEval]
    simp only [rowsX, List.mem_map, Finset.mem_toList, CircuitOps.val, wireVal]
    aesop
  let k := min (min a b) q
  have hkq : k ≤ q := min_le_right _ _
  have hka : k ≤ a := (min_le_left _ _).trans (min_le_left _ _)
  have hkb : k ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  have subY (p : Fin N) : lineRow H A B p ⊆ Geometry.linesThrough I p := by
    intro l hl
    obtain ⟨h, hh, hb⟩ := (lineRow_mem H A B).mp hl
    have hb₀ := (pointBin_mem H A B).mp hh
    exact (Geometry.mem_linesThrough I).mpr
      (legal h hb₀.1 p (by simp [hb₀.2.1]) l hb)
  have subX (l : Fin N) : pointRow H A B l ⊆ Geometry.pointsOn I l := by
    intro p hp
    obtain ⟨h, hh, ha₀⟩ := (pointRow_mem H A B).mp hp
    have hb₀ := (lineBin_mem H A B).mp hh
    exact (Geometry.mem_pointsOn I).mpr
      (legal h hb₀.1 p ha₀ l (by simp [hb₀.2.1]))
  have posY (p l : Fin N) : wireVal DY (single l) (oy p) = true ↔ l ∈ lineRow H A B p := by
    rw [evalY, lineRow_mem]
    simp only [memB]
  have posX (l p : Fin N) : wireVal DX (single p) (ox l) = true ↔ p ∈ pointRow H A B l := by
    rw [evalX, pointRow_mem]
    simp only [memA]
  have negY (p : Fin N) (hp : p ∈ S) (y : Fin N → Bool) (hy : (active y).card ≤ k)
      (hn : ∀ l ∈ Geometry.linesThrough I p, y l = false) : wireVal DY y (oy p) = false := by
    cases hv : wireVal DY y (oy p) with
    | false => rfl
    | true =>
      obtain ⟨h, hh, hYh⟩ := (evalY p y).mp hv
      have hb₀ := (pointBin_mem H A B).mp hh
      have hXh : wireVal X (single p) (ph h) = true :=
        (memA h p).mp (by simp [hb₀.2.1])
      have ht := (hTrans (single p) y).mpr (Or.inr ⟨h, hb₀.1, hYh, Or.inr hXh⟩)
      rw [P.pointNeg hp y (hy.trans hka) (fun l hl => hn l ((Geometry.mem_linesThrough I).mpr hl))] at ht
      contradiction
  have negX (l : Fin N) (hl : l ∈ W) (x : Fin N → Bool) (hx : (active x).card ≤ k)
      (hn : ∀ p ∈ Geometry.pointsOn I l, x p = false) : wireVal DX x (ox l) = false := by
    cases hv : wireVal DX x (ox l) with
    | false => rfl
    | true =>
      obtain ⟨h, hh, hXh⟩ := (evalX l x).mp hv
      have hb₀ := (lineBin_mem H A B).mp hh
      have hYh : wireVal Y (single l) (lh h) = true :=
        (memB h l).mp (by simp [hb₀.2.1])
      have ht := (hTrans x (single l)).mpr (Or.inr ⟨h, hb₀.1, hYh, Or.inr hXh⟩)
      rw [P.lineNeg hl x (hx.trans hkb) (fun p hp => hn p ((Geometry.mem_pointsOn I).mpr hp))] at ht
      contradiction
  have chargeY := Geometry.sum_charge_le hRef (k := k)
    S (Geometry.linesThrough I) (lineRow H A B) DY oy
    (fun p _ l _ h => Geometry.points_inter_card_le_one I hUnique p l h)
    (fun p _ => subY p) hDY hDYR (fun p _ => posY p) negY
  have chargeX := Geometry.sum_charge_le hRef (k := k)
    W (Geometry.pointsOn I) (pointRow H A B) DX ox
    (fun l _ j _ h => Geometry.lines_inter_card_le_one I hUnique l j h)
    (fun l _ => subX l) hDX hDXR (fun l _ => posX l) negX
  have cardY : DY.size ≤ Y.size + ∑ p, (pointBin H A B p).card := by
    simpa [rowsY] using hYSize
  have cardX : DX.size ≤ X.size + ∑ l, (lineBin H A B l).card := by
    simpa [rowsX] using hXSize
  have nterms := term_budget H A B
  have hsum : (∑ p ∈ S, Geometry.charge k (lineRow H A B p).card) +
      (∑ l ∈ W, Geometry.charge k (pointRow H A B l).card) ≤ 5 * D.size := by omega
  let E := (S ×ˢ W).filter (fun pl => I pl.1 pl.2)
  have hc (p l : Fin N) (he : (p, l) ∈ E) :
      (p ∈ S ∧ l ∈ lineRow H A B p) ∨ (l ∈ W ∧ p ∈ pointRow H A B l) := by
    have h := Finset.mem_filter.mp he
    obtain ⟨hp, hl⟩ := Finset.mem_product.mp h.1
    exact (cover p hp l hl h.2).imp (fun h' => ⟨hp, h'⟩) (fun h' => ⟨hl, h'⟩)
  have h := Geometry.sigma_of_rows hkq S W E (lineRow H A B) (pointRow H A B) hc
    (fun p _ => (Finset.card_le_card (subY p)).trans_eq (Geometry.linesThrough_card I hq hN hLines hUnique p))
    (fun l _ => (Finset.card_le_card (subX l)).trans_eq (hLines l)) hsum
  simpa only [k, E, Nat.mul_left_comm q 5, Nat.mul_assoc 5 q D.size] using h

end PEqualNP.Outside.L_meta_1726_aux

open PEqualNP.Outside.L_meta_1726_aux

theorem PEqualNP.Outside.L_meta_1726 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → (∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 3 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true)))) → ∀ (q122 N122 a122 b122 : ℕ) (I122 : Fin N122 → Fin N122 → Prop) [DecidableRel I122] (D122 : PEqualNP.CircuitLowerBounds.Circuit) (S122 W122 : Finset (Fin N122)), 2 ≤ q122 → N122 = q122 ^ 2 + q122 + 1 → (∀ l122d : Fin N122, (Finset.univ.filter (fun p122d => I122 p122d l122d)).card = q122 + 1) → (∀ pa122 pb122 : Fin N122, pa122 ≠ pb122 → ∃! lb122 : Fin N122, I122 pa122 lb122 ∧ I122 pb122 lb122) → (∀ g122 ∈ D122.gates, (g122.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g122.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g122.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N122 + N122) D122 → (∀ j122 < D122.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i122 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).inputs, (D122.lineDegrees (N122 + N122) (Finset.Ico N122 (N122 + N122))).getD i122 0 = 0) ∨ (∀ h122 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D122 j122).inputs, (D122.lineDegrees (N122 + N122) (Finset.range N122)).getD h122 0 = 0)) → 1 ≤ a122 → 1 ≤ b122 → (∀ x122 xa122 y122 ya122 : Fin N122 → Bool, (∀ p122 ∈ S122, x122 p122 = xa122 p122) → (∀ l122 ∈ W122, y122 l122 = ya122 l122) → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append x122 y122) = PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append xa122 ya122)) → (∀ p122a ∈ S122, ∀ l122a ∈ W122, I122 p122a l122a → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122a => decide (a122a = p122a)) (fun a122b => decide (a122b = l122a))) = true) → (∀ p122b ∈ S122, ∀ T122 ⊆ W122, (∀ l122b ∈ T122, ¬ I122 p122b l122b) → T122.card ≤ a122 → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122c => decide (a122c = p122b)) (fun a122d => decide (a122d ∈ T122))) = false) → (∀ l122c ∈ W122, ∀ X122 ⊆ S122, (∀ p122c ∈ X122, ¬ I122 p122c l122c) → X122.card ≤ b122 → PEqualNP.MetaComplexity.circuitFun (N122 + N122) D122 (Fin.append (fun a122e => decide (a122e ∈ X122)) (fun a122f => decide (a122f = l122c))) = false) → min (min a122 b122) q122 * ((S122 ×ˢ W122).filter (fun pl122 => I122 pl122.1 pl122.2)).card ≤ 5 * q122 * D122.size + min (min a122 b122) q122 * (S122.card + W122.card) := by
  classical
  intro hRef hNormal hTranspose q N a b I inst D S W hq hN hLines hUnique hOps hRead hKM
    ha hb hIgnore hAccept hRejectPoint hRejectLine
  let P : Problem I D S W a b := ⟨hIgnore, hAccept, hRejectPoint, hRejectLine⟩
  obtain ⟨hPure, _⟩ := hNormal N D hOps hRead hKM
  have hzero : Eval D (fun _ => false) (fun _ => false) = false :=
    (hPure D.output (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)).2.2
  let E := (S ×ˢ W).filter fun pl => I pl.1 pl.2
  by_cases hE : E.Nonempty
  · obtain ⟨⟨p, l⟩, he⟩ := hE
    have he' := Finset.mem_filter.mp he
    obtain ⟨hp, hl⟩ := Finset.mem_product.mp he'.1
    have hpw := P.accept p hp l hl he'.2
    have hpDep : 0 < Boundary.pointDeg N D D.output := by
      by_contra h
      have h' : Boundary.pointDeg N D D.output = 0 := Nat.eq_zero_of_not_pos h
      have eq := (hPure D.output (single p) (fun _ => false) (single l) (single l)).2.1 h'
      change Eval D (single p) (single l) = Eval D (fun _ => false) (single l) at eq
      rw [hpw, P.noPoint hl] at eq
      contradiction
    have hlDep : 0 < Boundary.lineDeg N D D.output := by
      by_contra h
      have h' : Boundary.lineDeg N D D.output = 0 := Nat.eq_zero_of_not_pos h
      have eq := (hPure D.output (single p) (single p) (single l) (fun _ => false)).1 h'
      change Eval D (single p) (single l) = Eval D (single p) (fun _ => false) at eq
      rw [hpw, P.noLine hp] at eq
      contradiction
    obtain ⟨X, ph, T, ⟨hX, hXR⟩, hXSize, _, hRepresentation⟩ :=
      hTranspose N D hOps hRead hKM hpDep hlDep
    obtain ⟨Y, lh, hY, hYR, hYSize, hProjection⟩ := CircuitOps.projectLines N D hOps hRead
    have hTrans : ∀ x y : Fin N → Bool, Eval D x y = true ↔
        Eval D x (fun _ => false) = true ∨ ∃ h ∈ Boundary.boundary N D,
          wireVal Y y (lh h) = true ∧ (h ∈ T ∨ wireVal X x (ph h) = true) := by
      intro x y
      constructor
      · intro h
        rcases (hRepresentation x y).mp h with hbase | ⟨j, hj, hEval, hTest⟩
        · exact Or.inl hbase
        · exact Or.inr ⟨j, (Boundary.mem_boundary N D j).mpr hj,
            (hProjection j hj.1 y).trans hEval, hTest⟩
      · intro h
        apply (hRepresentation x y).mpr
        rcases h with hbase | ⟨j, hj, hEval, hTest⟩
        · exact Or.inl hbase
        · have hpure := (Boundary.mem_boundary N D j).mp hj
          exact Or.inr ⟨j, hpure, (hProjection j hpure.1 y).symm.trans hEval, hTest⟩
    rw [Boundary.point_ncard, Boundary.mixed_ncard] at hXSize
    change Y.size ≤ Set.ncard {j : ℕ | j < D.gates.length ∧
      Boundary.pointDeg N D (N + N + j) = 0} at hYSize
    rw [Boundary.line_ncard] at hYSize
    have hports := Boundary.boundary_card_le N D hOps
    have hpartition := Boundary.gate_budget N D (fun j hj hp0 => by
      have hv := CircuitOps.deg_pos_or N D hOps hRead (N + N + j) (Nat.add_lt_add_left hj _)
      exact hv.resolve_left (by
        intro hpos
        change 0 < Boundary.pointDeg N D (N + N + j) at hpos
        exact (Nat.ne_of_gt hpos) hp0))
    have hcost : X.size + Y.size + (Boundary.boundary N D).card ≤ 5 * D.size := by omega
    exact projectedBound I P hRef hq hN hLines hUnique ha hzero hX hXR hY hYR
      (Boundary.boundary N D) ph lh T hTrans hcost
  · have hE' : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    change min (min a b) q * E.card ≤ _
    simp [hE']
