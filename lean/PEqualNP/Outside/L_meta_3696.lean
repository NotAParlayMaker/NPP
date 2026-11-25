import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3696

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def reads (n : ℕ) (g : Gate) : Finset ℕ := (g.inputs.filter (· < n)).toFinset

def reduce (n : ℕ) (g : Gate) (S : Finset ℕ) : Finset ℕ :=
  if n ∈ S then (S.erase n) ∪ reads n g else S

def support (n : ℕ) (gs : List Gate) (S : Finset ℕ) : Finset ℕ :=
  match gs with
  | [] => S
  | g :: tail => reduce n g (support (n + 1) tail S)

theorem reads_card (n : ℕ) (g : Gate) : (reads n g).card ≤ g.inputs.length := by
  exact le_trans (List.toFinset_card_le _) (List.length_filter_le _ _)

theorem reduce_card (n : ℕ) (g : Gate) (S : Finset ℕ) (h : g.inputs.length ≤ 2) :
    (reduce n g S).card ≤ S.card + 1 := by
  unfold reduce
  split
  · rename_i hn
    have hb := Finset.card_union_le (S.erase n) (reads n g)
    rw [Finset.card_erase_of_mem hn] at hb
    have hr := reads_card n g
    have hs : 0 < S.card := Finset.card_pos.mpr ⟨n, hn⟩
    omega
  · omega

theorem support_card (n : ℕ) (gs : List Gate) (S : Finset ℕ)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (support n gs S).card ≤ S.card + gs.length := by
  induction gs generalizing n with
  | nil => simp [support]
  | cons g gs ih =>
    have hh := reduce_card n g (support (n + 1) gs S) (h g (by simp))
    have ht := ih (n + 1) (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [support, List.length_cons]
    omega

theorem getD_step_old (w : List Bool) (g : Gate) (i : ℕ) (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · have hp : w.length < i := by omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_step_new (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [step, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
  rfl

theorem reduce_agree (n : ℕ) (g : Gate) (S : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i ∈ reduce n g S, x.getD i false = y.getD i false) :
    ∀ i ∈ S, (step x g).getD i false = (step y g).getD i false := by
  intro i hi
  by_cases hn : i = n
  · subst i
    rw [← hx, getD_step_new, hx, ← hy, getD_step_new]
    congr 1
    apply List.map_congr_left
    intro j hj
    by_cases hjn : j < n
    · apply h
      simp only [reduce, hi, ite_true, Finset.mem_union, reads, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq]
      exact Or.inr ⟨hj, by omega⟩
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  · rw [getD_step_old _ _ _ (by omega), getD_step_old _ _ _ (by omega)]
    apply h
    by_cases hsn : n ∈ S
    · simp [reduce, hsn, hn, hi]
    · simp [reduce, hsn, hi]

theorem support_agree (n : ℕ) (gs : List Gate) (S : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i ∈ support n gs S, x.getD i false = y.getD i false) :
    ∀ i ∈ S, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs generalizing n x y with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (n + 1) (step x g) (step y g) (by simp [step, hx]) (by simp [step, hy])
      (reduce_agree n g (support (n + 1) gs S) x y hx hy h)

theorem circuit_support (n : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i ∈ support n C.gates {C.output}, x.getD i false = y.getD i false) :
    C.eval x = C.eval y :=
  support_agree n C.gates {C.output} x y hx hy h C.output (by simp)


def single {n : ℕ} (a : Fin n) (i : Fin n) : Bool := decide (i = a)

def pair {n : ℕ} (a b : Fin n) (i : Fin n) : Bool := decide (i = a ∨ i = b)

theorem need_first {n : ℕ} (C : Circuit) (a b : Fin n)
    (hp : circuitFun n C (pair a b) = true)
    (hs : circuitFun n C (single b) = false) :
    a.val ∈ support n C.gates {C.output} := by
  by_contra hn
  have he : ∀ i ∈ support n C.gates {C.output},
      (List.ofFn (pair a b)).getD i false = (List.ofFn (single b)).getD i false := by
    intro i hi
    have hne : i ≠ a.val := by rintro rfl; exact hn hi
    by_cases hlt : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt),
          List.getD_eq_getElem _ _ (by simpa using hlt),
          List.getElem_ofFn, List.getElem_ofFn]
      have hd : (⟨i,hlt⟩ : Fin n) ≠ a := fun h => hne (congrArg Fin.val h)
      simp [pair, single, hd]
    · have hge := Nat.le_of_not_gt hlt
      rw [List.getD_eq_default _ _ (by simpa using hge),
          List.getD_eq_default _ _ (by simpa using hge)]
  have hh : circuitFun n C (pair a b) = circuitFun n C (single b) :=
    circuit_support n C _ _ (by simp) (by simp) he
  rw [hp, hs] at hh
  contradiction

theorem need_second {n : ℕ} (C : Circuit) (a b : Fin n)
    (hp : circuitFun n C (pair a b) = true)
    (hs : circuitFun n C (single a) = false) :
    b.val ∈ support n C.gates {C.output} := by
  apply need_first C b a _ hs
  have he : pair b a = pair a b := by funext i; simp [pair, or_comm]
  rwa [he]

theorem point_ne_line {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hh := congrArg Fin.val h
  change p.val = N + l.val at hh
  have hp := p.isLt
  omega

theorem lines_singleton {N : ℕ} (b : Fin (N+N)) :
    Fintype.card {l : Fin N // single b (Fin.natAdd N l) = true} ≤ 1 := by
  rw [Fintype.card_subtype]
  apply Finset.card_le_one.mpr
  intro l hl m hm
  have hl' : Fin.natAdd N l = b := by
    simpa [single] using (Finset.mem_filter.mp hl).2
  have hm' : Fin.natAdd N m = b := by
    simpa [single] using (Finset.mem_filter.mp hm).2
  apply Fin.ext
  have h := congrArg Fin.val (hl'.trans hm'.symm)
  change N + l.val = N + m.val at h
  omega

theorem singleton_false {N q : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) (hq : 1 ≤ q)
    (hs : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N+N) C x = false)
    (b : Fin (N+N)) :
    circuitFun (N+N) C (single b) = false := by
  apply hs _ ((lines_singleton b).trans hq)
  rintro ⟨p,l,_,hp,hl⟩
  have hp' : Fin.castAdd N p = b := by simpa [single] using hp
  have hl' : Fin.natAdd N l = b := by simpa [single] using hl
  exact point_ne_line p l (hp'.trans hl'.symm)


theorem endpoints_card {N q : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) (hq : 1 ≤ q)
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hs : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N+N) C x = false)
    (E : Finset (Fin N × Fin N))
    (hAccepted : ∀ e ∈ E, circuitFun (N+N) C (pair (Fin.castAdd N e.1) (Fin.natAdd N e.2)) = true) :
    (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size + 1 := by
  let A := (E.image Prod.fst).image Fin.val
  let B := (E.image Prod.snd).image (fun l => N + l.val)
  let S := support (N+N) C.gates {C.output}
  have ah : A.card = (E.image Prod.fst).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have bh : B.card = (E.image Prod.snd).card :=
    Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (by omega))
  have hdis : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro i ia ib
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ia
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp ib
    have h := p.isLt
    change p.val = i at hp
    change N + l.val = i at hl
    omega
  have hab : A ∪ B ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with ha | hb
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      exact need_first C _ _ (hAccepted e he) (singleton_false I C hq hs _)
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
      exact need_second C _ _ (hAccepted e he) (singleton_false I C hq hs _)
  calc (E.image Prod.fst).card + (E.image Prod.snd).card = (A ∪ B).card := by
         rw [Finset.card_union_of_disjoint hdis, ah, bh]
    _ ≤ S.card := Finset.card_le_card hab
    _ ≤ C.size + 1 := by
      have cc := support_card (N+N) C.gates {C.output} hFan
      simpa [S, Circuit.size, Nat.add_comm] using cc

theorem no_rectangle {N : ℕ} (I : Fin N → Fin N → Prop)
    (unique : ∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l)
    (E : Finset (Fin N × Fin N)) (contained : ∀ e ∈ E, I e.1 e.2)
    {p r l m : Fin N} (hpr : p ≠ r) (hlm : l ≠ m)
    (hpl : (p,l) ∈ E) (hpm : (p,m) ∈ E) (hrl : (r,l) ∈ E) (hrm : (r,m) ∈ E) : False := by
  obtain ⟨_, _, hu⟩ := unique p r hpr
  exact hlm ((hu l ⟨contained _ hpl, contained _ hrl⟩).trans
    (hu m ⟨contained _ hpm, contained _ hrm⟩).symm)

private theorem pnp3696_numeric_int (a b e : ℤ)
    (hb : 1 ≤ b) (hba : b ≤ a) (hsmax : a + b ≤ 4513)
    (heprod : e ≤ a * b) (hequad : e ^ 2 ≤ a * (e + b * (b - 1))) :
    e ≤ 24 * (a + b - 1) := by
  set s := a + b with hs
  set E := 24 * s - 23 with hE
  have hsmin : 2 ≤ s := by omega
  by_contra hc
  have heE : E ≤ e := by omega
  by_cases hsmall : s ≤ 95
  · have h1 := mul_nonneg (show 0 ≤ s - 2 by omega) (show 0 ≤ 95 - s by omega)
    have h2 : 4 * a * b ≤ s ^ 2 := by
      rw [hs]
      nlinarith only [sq_nonneg (a - b)]
    have h3 : s ^ 2 < 4 * E := by
      nlinarith only [h1, hsmall, hE]
    have h4 : 4 * E ≤ 4 * a * b := by linarith only [heE, heprod]
    exact (not_lt_of_ge (h4.trans h2)) h3
  · have hs96 : 96 ≤ s := by omega
    have hEa : a ≤ E := by omega
    have hmono := mul_nonneg (sub_nonneg.mpr heE) (show 0 ≤ e + E - a by omega)
    have hEbound : E ^ 2 ≤ a * (E + b * (b - 1)) := by
      nlinarith only [hmono, hequad]
    set d := a - b with hd
    have hd0 : 0 ≤ d := by omega
    have hsd : 0 ≤ s - d - 2 := by omega
    have hident :
        8 * a * (E + b * (b - 1)) =
          4 * s * E + s ^ 2 * (s - 2) - d * (s ^ 2 - 4 * E) -
            d ^ 2 * (s - d - 2) := by
      rw [hs, hd]
      ring
    have hmargin : 8 * E ^ 2 - 4 * s * E - s ^ 2 * (s - 2) =
        s * (s * (4514 - s) - 8740) + 4232 := by
      rw [hE]
      ring
    have hcoef : 0 ≤ s ^ 2 - 4 * E := by
      nlinarith only [hE, hs96, mul_nonneg (show 0 ≤ s - 96 by omega)
        (show 0 ≤ s by omega)]
    have h1 := mul_nonneg hd0 hcoef
    have h2 := mul_nonneg (sq_nonneg d) hsd
    by_cases hmid : s ≤ 4512
    · have h3 := mul_nonneg (show 0 ≤ s - 96 by omega)
          (show 0 ≤ 4512 - s by omega)
      have h4 : 9024 ≤ s * (4514 - s) := by
        nlinarith only [h3, hmid]
      have h5 := mul_nonneg (show 0 ≤ s by omega)
          (show 0 ≤ s * (4514 - s) - 8740 by omega)
      linarith only [hEbound, hident, hmargin, h1, h2, h5]
    · have hs4513 : s = 4513 := by omega
      have hd1 : 1 ≤ d := by omega
      have hEend : E = 108289 := by omega
      have h3 : 0 < (8 * E ^ 2 - 4 * s * E - s ^ 2 * (s - 2)) +
          d * (s ^ 2 - 4 * E) := by
        rw [hs4513, hEend]
        norm_num
        omega
      linarith only [hEbound, hident, h2, h3]

theorem numeric (a b e : ℕ)
    (hb : 1 ≤ b) (hba : b ≤ a) (hsmax : a + b ≤ 4513)
    (heprod : e ≤ a * b) (hequad : e ^ 2 ≤ a * (e + b * (b - 1))) :
    e ≤ 24 * (a + b - 1) := by
  have hb' : 1 ≤ (b : ℤ) := by exact_mod_cast hb
  have hba' : (b : ℤ) ≤ (a : ℤ) := by exact_mod_cast hba
  have hsmax' : (a : ℤ) + (b : ℤ) ≤ 4513 := by exact_mod_cast hsmax
  have heprod' : (e : ℤ) ≤ (a : ℤ) * (b : ℤ) := by exact_mod_cast heprod
  have hequad' : (↑(e ^ 2) : ℤ) ≤ ↑(a * (e + b * (b - 1))) := Int.ofNat_le.mpr hequad
  push_cast [Nat.cast_sub hb] at hequad'
  have h := pnp3696_numeric_int (a : ℤ) (b : ℤ) (e : ℤ) hb' hba' hsmax' heprod' hequad'
  have hab : 1 ≤ a + b := by omega
  apply Int.ofNat_le.mp
  push_cast [Nat.cast_sub hab]
  exact h

open Finset
open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem count (E : Finset (α × β))
    (hrect : ∀ {x x' : α} {y y' : β}, x ≠ x' → y ≠ y' →
      (x, y) ∈ E → (x, y') ∈ E → (x', y) ∈ E → (x', y') ∈ E → False) :
    E.card ≤ (E.image Prod.fst).card * (E.image Prod.snd).card ∧
    E.card ^ 2 ≤ (E.image Prod.fst).card *
      (E.card + (E.image Prod.snd).card * ((E.image Prod.snd).card - 1)) := by
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  change E.card ≤ A.card * B.card ∧ E.card ^ 2 ≤ A.card * (E.card + B.card * (B.card - 1))
  constructor
  · rw [← Finset.card_product]
    apply Finset.card_le_card
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  let N (x : α) : Finset β := (E.filter (fun p => p.1 = x)).image Prod.snd
  have hn (x : α) (y : β) : y ∈ N x ↔ (x, y) ∈ E := by
    simp only [N, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨u, v⟩, ⟨h, rfl⟩, rfl⟩
      exact h
    · intro h
      exact ⟨(x, y), ⟨h, rfl⟩, rfl⟩
  have hfib (x : α) : (N x).card = (E.filter (fun p => p.1 = x)).card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq hh
    have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
    have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    exact Prod.ext (hp'.trans hq'.symm) hh
  have hsum : ∑ x ∈ A, (N x).card = E.card := by
    simp_rw [hfib]
    exact (Finset.card_eq_sum_card_image Prod.fst E).symm
  have hdisj : (A : Set α).PairwiseDisjoint (fun x => (N x).offDiag) := by
    intro x _ x' _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    obtain ⟨py, py', hpy⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨qy, qy', _⟩ := Finset.mem_offDiag.mp hp'
    exact hrect hne hpy ((hn _ _).mp py) ((hn _ _).mp py') ((hn _ _).mp qy) ((hn _ _).mp qy')
  have hsub : A.biUnion (fun x => (N x).offDiag) ⊆ B.offDiag := by
    intro p hp
    obtain ⟨x, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr
      ⟨Finset.mem_image_of_mem Prod.snd ((hn _ _).mp h1),
       Finset.mem_image_of_mem Prod.snd ((hn _ _).mp h2), h3⟩
  have hpair : (∑ x ∈ A, (N x).offDiag.card) ≤ B.card * (B.card - 1) := by
    rw [← Finset.card_biUnion hdisj, Nat.mul_sub_one, ← Finset.offDiag_card]
    exact Finset.card_le_card hsub
  have hsum2 : (∑ x ∈ A, (N x).card ^ 2) = E.card + ∑ x ∈ A, (N x).offDiag.card := by
    rw [← hsum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.offDiag_card, pow_two]
    have h := Nat.le_mul_self (N x).card
    omega
  have hCS := sq_sum_le_card_mul_sum_sq (s := A) (f := fun x => (N x).card)
  rw [hsum, hsum2] at hCS
  exact hCS.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hpair _))

theorem countSwap (E : Finset (α × β))
    (hrect : ∀ {x x' : α} {y y' : β}, x ≠ x' → y ≠ y' →
      (x, y) ∈ E → (x, y') ∈ E → (x', y) ∈ E → (x', y') ∈ E → False) :
    E.card ^ 2 ≤ (E.image Prod.snd).card *
      (E.card + (E.image Prod.fst).card * ((E.image Prod.fst).card - 1)) := by
  let E' : Finset (β × α) := E.image Prod.swap
  have hmem (x : α) (y : β) : (y, x) ∈ E' ↔ (x, y) ∈ E := by
    change (y, x) ∈ E.image Prod.swap ↔ (x, y) ∈ E
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨u, v⟩, hm, hh⟩
      change (v, u) = (y, x) at hh
      cases hh
      exact hm
    · intro hm
      exact ⟨(x, y), hm, rfl⟩
  have hrect' : ∀ {x x' : β} {y y' : α}, x ≠ x' → y ≠ y' →
      (x, y) ∈ E' → (x, y') ∈ E' → (x', y) ∈ E' → (x', y') ∈ E' → False := by
    intro x x' y y' hx hy hxy hxy' hx'y hx'y'
    exact hrect hy hx ((hmem _ _).mp hxy) ((hmem _ _).mp hx'y)
      ((hmem _ _).mp hxy') ((hmem _ _).mp hx'y')
  have hcard : E'.card = E.card := by
    apply Finset.card_image_of_injOn
    intro p _ q _ h
    simpa using congrArg Prod.swap h
  have hfst : E'.image Prod.fst = E.image Prod.snd := by
    simp [E', Finset.image_image, Function.comp_def]
  have hsnd : E'.image Prod.snd = E.image Prod.fst := by
    simp [E', Finset.image_image, Function.comp_def]
  simpa only [hcard, hfst, hsnd] using (count E' hrect').2

end PEqualNP.Outside.L_meta_3696

theorem PEqualNP.Outside.L_meta_3696 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (1 : ℕ) ≤ x1 →     (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) →       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : Fin x2 × Fin x2 | x3 x8.1 x8.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x7 fun (x9 : Fin (x2 + x2)) => Decidable.decide (x9 = Fin.castAdd x2 x8.1 ∨ x9 = Fin.natAdd x2 x8.2)) = Bool.true};       have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x8 x9 = Bool.false;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x10 ∈ x9.gates, x10.inputs.length ≤ (2 : ℕ)) → x8 x9 → x9.size ≤ (4512 : ℕ) → (x7 x9).card ≤ (24 : ℕ) * x9.size := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
  open PEqualNP.Outside.L_meta_3696 in
  intro q N I instI hq unique
  dsimp only
  intro C hfan hsound hbudget
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
    I e.1 e.2 ∧ circuitFun (N+N) C (pair (Fin.castAdd N e.1) (Fin.natAdd N e.2)) = true
  change E.card ≤ 24 * C.size
  by_cases hEmpty : E = ∅
  · simp [hEmpty]
  have hmem : ∀ e ∈ E, I e.1 e.2 ∧
      circuitFun (N+N) C (pair (Fin.castAdd N e.1) (Fin.natAdd N e.2)) = true := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hrect : ∀ {p r l m : Fin N}, p ≠ r → l ≠ m →
      (p,l) ∈ E → (p,m) ∈ E → (r,l) ∈ E → (r,m) ∈ E → False := by
    intro p r l m
    exact no_rectangle I unique E (fun e he => (hmem e he).1)
  have limiting := endpoints_card I C hq hfan hsound E (fun e he => (hmem e he).2)
  have sum_limit : (E.image Prod.fst).card + (E.image Prod.snd).card ≤ 4513 := by omega
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have first_pos : 1 ≤ (E.image Prod.fst).card :=
    Finset.card_pos.mpr ⟨e.1, Finset.mem_image_of_mem _ he⟩
  have second_pos : 1 ≤ (E.image Prod.snd).card :=
    Finset.card_pos.mpr ⟨e.2, Finset.mem_image_of_mem _ he⟩
  have ⟨product_bound, square_bound⟩ := count E hrect
  have small : E.card ≤ 24 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
    by_cases hba : (E.image Prod.snd).card ≤ (E.image Prod.fst).card
    · exact numeric _ _ _ second_pos hba sum_limit product_bound square_bound
    · have hab : (E.image Prod.fst).card ≤ (E.image Prod.snd).card := by omega
      have hb := numeric _ _ _ first_pos hab
        (by rw [Nat.add_comm]; exact sum_limit) (by rw [Nat.mul_comm]; exact product_bound)
        (countSwap E hrect)
      rwa [Nat.add_comm] at hb
  exact small.trans (Nat.mul_le_mul_left _ (by omega))
