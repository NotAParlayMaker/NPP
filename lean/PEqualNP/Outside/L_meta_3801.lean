import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3801

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The plane of order 3 as the Singer difference set 0, 1, 3, 9 modulo 13: point p lies on
-- line l when p - l is in the set. A collineation renames the 26 input wires of a circuit;
-- translations and eighteen collineations that fix point 0 bring the free OR to one of
-- seven representatives.

def D : Finset (Fin 13) := {0, 1, 3, 9}

def P (p l : Fin 13) : List Bool :=
  (List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun u : Fin 13 => decide (u = l)

def N (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn fun u : Fin 13 => decide (∀ r ∈ Q, r - u ∉ D)

def good (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter fun u => u - k ∈ D).card ≤ 2

def ext (s : List ℕ) (x : List Bool) : List Bool := x ++ [s.any fun i => x.getD i false]

def fits (C : Circuit) (s : List ℕ) : Prop :=
  (∀ p l : Fin 13, p - l ∈ D → C.eval (ext s (P p l)) = true) ∧
    ∀ Q, good Q → C.eval (ext s (N Q)) = false

def Bnd (C : Circuit) : Prop :=
  ∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val

def canonList : List (List ℕ) := [[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]]

-- the wire map of a pair of maps on points and lines
def wmap (σ τ : Fin 13 → Fin 13) (i : ℕ) : ℕ :=
  if h : i < 13 then (σ ⟨i, h⟩).val
  else if h' : i < 26 then 13 + (τ ⟨i - 13, by omega⟩).val else i

theorem wmap_lt (σ τ : Fin 13 → Fin 13) (i : ℕ) (h : i < 26) : wmap σ τ i < 26 := by
  unfold wmap
  split_ifs with h1
  · have := (σ ⟨i, h1⟩).isLt; omega
  · have := (τ ⟨i - 13, by omega⟩).isLt; omega

theorem wmap_ge (σ τ : Fin 13 → Fin 13) (i : ℕ) (h : 26 ≤ i) : wmap σ τ i = i := by
  unfold wmap
  rw [dif_neg (by omega), dif_neg (by omega)]

def moveG (π : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map π⟩

def moveC (π : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (moveG π), π C.output⟩

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

def Rel (π : ℕ → ℕ) (w v : List Bool) : Prop :=
  w.length = v.length ∧ 26 ≤ w.length ∧ ∀ i, v.getD (π i) false = w.getD i false

theorem fold_rel (π : ℕ → ℕ) (hlt : ∀ i, i < 26 → π i < 26) (hge : ∀ i, 26 ≤ i → π i = i) :
    ∀ (gs : List Gate) (w v : List Bool), Rel π w v →
      Rel π (gs.foldl stepW w) ((gs.map (moveG π)).foldl stepW v) := by
  intro gs
  induction gs with
  | nil => exact fun _ _ h => h
  | cons g gs ih =>
    intro w v h
    obtain ⟨len, bound, reads⟩ := h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    apply ih
    have value : (moveG π g).op.eval ((moveG π g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [moveG, List.map_map, Function.comp_def, reads]
    unfold stepW
    rw [value]
    refine ⟨by simp [len], by simp; omega, ?_⟩
    intro i
    by_cases hi : i < w.length
    · have hw : π i < v.length := by
        by_cases h26 : i < 26
        · have := hlt i h26; omega
        · rw [hge i (by omega)]; omega
      rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hi]
      exact reads i
    · have hpi : π i = i := hge i (by omega)
      rw [hpi, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), len]

theorem eval_rel (π : ℕ → ℕ) (hlt : ∀ i, i < 26 → π i < 26) (hge : ∀ i, 26 ≤ i → π i = i)
    (C : Circuit) (w v : List Bool) (h : Rel π w v) : (moveC π C).eval v = C.eval w := by
  have := (fold_rel π hlt hge C.gates w v h).2.2 C.output
  exact this

-- reading one wire of the two kinds of input words
theorem getD_ofFn13 (F : Fin 13 → Bool) (i : ℕ) (h : i < 13) :
    (List.ofFn F).getD i false = F ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

theorem getD_two (F G : Fin 13 → Bool) (i : ℕ) :
    ((List.ofFn F) ++ List.ofFn G).getD i false =
      if h : i < 13 then F ⟨i, h⟩ else if h' : i < 26 then G ⟨i - 13, by omega⟩ else false := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ (by simpa using h1), getD_ofFn13 F i h1]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn,
      getD_ofFn13 G (i - 13) (by omega)]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem len_two (F G : Fin 13 → Bool) : ((List.ofFn F) ++ List.ofFn G).length = 26 := by simp

theorem P_len (p l : Fin 13) : (P p l).length = 26 := by simp [P]

theorem N_len (Q : Finset (Fin 13)) : (N Q).length = 26 := by simp [N]

-- a wire map that renames the input words of one kind into the other
theorem rel_ext (π : ℕ → ℕ) (hlt : ∀ i, i < 26 → π i < 26) (hge : ∀ i, 26 ≤ i → π i = i)
    (s : List ℕ) (x y : List Bool) (hx : x.length = 26) (hy : y.length = 26)
    (h : ∀ e, x.getD (π e) false = y.getD e false) :
    Rel π (ext s y) (ext (s.map π) x) := by
  have hany : (s.map π).any (fun i => x.getD i false) = s.any fun i => y.getD i false := by
    rw [List.any_map]
    congr 1
    funext e
    exact h e
  refine ⟨by simp [ext, hx, hy], by simp [ext, hy], ?_⟩
  intro i
  unfold ext
  rw [hany]
  rcases lt_trichotomy i 26 with hi | hi | hi
  · have hpi := hlt i hi
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    exact h i
  · subst hi
    rw [hge 26 le_rfl]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hx,
      hy]
  · rw [hge i (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

-- an incidence-preserving pair of bijections
def Auto (σ τ σi τi : Fin 13 → Fin 13) : Prop :=
  (∀ p, σi (σ p) = p) ∧ (∀ p, σ (σi p) = p) ∧ (∀ l, τi (τ l) = l) ∧ (∀ l, τ (τi l) = l) ∧
    ∀ p l, σ p - τ l ∈ D ↔ p - l ∈ D

theorem Auto.h1 {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) : ∀ p, σi (σ p) = p := A.1

theorem Auto.h2 {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) : ∀ p, σ (σi p) = p := A.2.1

theorem Auto.h3 {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) : ∀ l, τi (τ l) = l :=
  A.2.2.1

theorem Auto.h4 {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) : ∀ l, τ (τi l) = l :=
  A.2.2.2.1

theorem Auto.hinc {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) :
    ∀ p l, σ p - τ l ∈ D ↔ p - l ∈ D := A.2.2.2.2

theorem P_move {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) (p l : Fin 13) (e : ℕ) :
    (P p l).getD (wmap σ τ e) false = (P (σi p) (τi l)).getD e false := by
  unfold P
  rw [getD_two, getD_two]
  unfold wmap
  by_cases h1 : e < 13
  · rw [dif_pos h1, dif_pos (σ ⟨e, h1⟩).isLt, dif_pos h1]
    have : (⟨(σ ⟨e, h1⟩).val, (σ ⟨e, h1⟩).isLt⟩ : Fin 13) = σ ⟨e, h1⟩ := rfl
    rw [this]
    apply decide_eq_decide.2
    constructor
    · intro hq; rw [← hq, A.h1]
    · intro hq; rw [hq, A.h2]
  · rw [dif_neg h1]
    by_cases h2 : e < 26
    · rw [dif_pos h2, dif_neg (by omega), dif_pos (by have := (τ ⟨e - 13, by omega⟩).isLt; omega),
        dif_neg h1, dif_pos h2]
      have : (⟨13 + (τ ⟨e - 13, by omega⟩).val - 13, by have := (τ ⟨e - 13, by omega⟩).isLt; omega⟩ :
          Fin 13) = τ ⟨e - 13, by omega⟩ := by ext; simp
      rw [this]
      apply decide_eq_decide.2
      constructor
      · intro hq; rw [← hq, A.h3]
      · intro hq; rw [hq, A.h4]
    · rw [dif_neg h2, dif_neg h1, dif_neg h2, dif_neg h1, dif_neg h2]

theorem N_move {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) (Q : Finset (Fin 13))
    (e : ℕ) : (N Q).getD (wmap σ τ e) false = (N (Q.image σi)).getD e false := by
  unfold N
  rw [getD_two, getD_two]
  unfold wmap
  by_cases h1 : e < 13
  · rw [dif_pos h1, dif_pos (σ ⟨e, h1⟩).isLt, dif_pos h1]
    have : (⟨(σ ⟨e, h1⟩).val, (σ ⟨e, h1⟩).isLt⟩ : Fin 13) = σ ⟨e, h1⟩ := rfl
    rw [this]
    apply decide_eq_decide.2
    rw [Finset.mem_image]
    constructor
    · intro hq; exact ⟨_, hq, A.h1 _⟩
    · rintro ⟨q, hq, hq'⟩; rw [← hq', A.h2]; exact hq
  · rw [dif_neg h1]
    by_cases h2 : e < 26
    · rw [dif_pos h2, dif_neg (by omega), dif_pos (by have := (τ ⟨e - 13, by omega⟩).isLt; omega),
        dif_neg h1, dif_pos h2]
      have : (⟨13 + (τ ⟨e - 13, by omega⟩).val - 13, by have := (τ ⟨e - 13, by omega⟩).isLt; omega⟩ :
          Fin 13) = τ ⟨e - 13, by omega⟩ := by ext; simp
      rw [this]
      apply decide_eq_decide.2
      constructor
      · intro hq r hr
        obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.1 hr
        intro hD
        apply hq r0 hr0
        have := (A.hinc (σi r0) ⟨e - 13, by omega⟩).2 hD
        rwa [A.h2] at this
      · intro hq r hr hD
        apply hq (σi r) (Finset.mem_image_of_mem _ hr)
        have := (A.hinc (σi r) ⟨e - 13, by omega⟩).1
        rw [A.h2] at this
        exact this hD
    · rw [dif_neg h2, dif_neg h1, dif_neg h2, dif_neg h1, dif_neg h2]

theorem good_move {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) (Q : Finset (Fin 13))
    (hQ : good Q) : good (Q.image σi) := by
  have hinj : Function.Injective σi := by
    intro a b hab
    have := congrArg σ hab
    rwa [A.h2, A.h2] at this
  refine ⟨by rw [Finset.card_image_of_injective _ hinj]; exact hQ.1, ?_⟩
  intro k
  rw [Finset.filter_image]
  refine (Finset.card_image_le).trans ?_
  have e : (Q.filter fun a => σi a - k ∈ D) = Q.filter fun u => u - τ k ∈ D := by
    apply Finset.filter_congr
    intro u _
    have := A.hinc (σi u) k
    rw [A.h2] at this
    exact this.symm
  rw [e]
  exact hQ.2 (τ k)

theorem relabel {σ τ σi τi : Fin 13 → Fin 13} (A : Auto σ τ σi τi) (C : Circuit) (s : List ℕ)
    (hm : Monotone2 C) (hb : Bnd C) (hf : fits C s) :
    Monotone2 (moveC (wmap σ τ) C) ∧ Bnd (moveC (wmap σ τ) C) ∧
      (moveC (wmap σ τ) C).size = C.size ∧ fits (moveC (wmap σ τ) C) (s.map (wmap σ τ)) := by
  have hlt := wmap_lt σ τ
  have hge := wmap_ge σ τ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hm g0 hg0).1, by simpa [moveG] using (hm g0 hg0).2⟩
  · rintro ⟨iv, hiv⟩ w hw
    have hi : iv < C.gates.length := by simpa [moveC] using hiv
    have hget : (moveC (wmap σ τ) C).gates.get ⟨iv, hiv⟩ =
        moveG (wmap σ τ) (C.gates.get ⟨iv, hi⟩) := by
      simp [moveC]
    rw [hget] at hw
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
    have := hb ⟨iv, hi⟩ w0 hw0
    simp only [Fin.val_mk] at this ⊢
    by_cases h26 : w0 < 26
    · have := hlt w0 h26; omega
    · rw [hge w0 (by omega)]; exact this
  · simp [moveC, Circuit.size]
  · intro p l hpl
    rw [eval_rel _ hlt hge C (ext s (P (σi p) (τi l))) _
      (rel_ext _ hlt hge s _ _ (P_len _ _) (P_len _ _) (P_move A p l))]
    apply hf.1
    have := A.hinc (σi p) (τi l)
    rw [A.h2, A.h4] at this
    exact this.1 hpl
  · intro Q hQ
    rw [eval_rel _ hlt hge C (ext s (N (Q.image σi))) _
      (rel_ext _ hlt hge s _ _ (N_len _) (N_len _) (N_move A Q))]
    exact hf.2 _ (good_move A Q hQ)

theorem trans_auto (c : Fin 13) :
    Auto (fun p => p + c) (fun l => l + c) (fun p => p - c) (fun l => l - c) := by
  refine ⟨fun p => by simp, fun p => by simp, fun l => by simp, fun l => by simp, ?_⟩
  intro p l
  rw [add_sub_add_right_eq_sub]

def bS : Fin 18 → Fin 13 → Fin 13 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ![0, 9, 2, 1, 7, 4, 11, 5, 8, 3, 6, 10, 12],
    ![0, 10, 8, 6, 7, 5, 9, 4, 12, 11, 3, 1, 2],
    ![0, 5, 11, 7, 3, 1, 8, 9, 6, 4, 2, 12, 10],
    ![0, 7, 1, 5, 11, 6, 2, 10, 9, 4, 12, 8, 3],
    ![0, 3, 6, 9, 4, 7, 8, 5, 10, 1, 12, 2, 11],
    ![1, 2, 3, 10, 5, 8, 12, 6, 0, 4, 11, 7, 9],
    ![1, 2, 8, 10, 12, 7, 9, 11, 6, 4, 0, 3, 5],
    ![0, 7, 6, 4, 2, 12, 1, 8, 11, 5, 9, 3, 10],
    ![1, 4, 5, 2, 0, 3, 12, 9, 6, 10, 7, 11, 8],
    ![0, 1, 6, 3, 5, 4, 2, 7, 10, 9, 8, 12, 11],
    ![0, 3, 8, 1, 7, 5, 11, 4, 2, 9, 10, 6, 12],
    ![9, 3, 11, 0, 5, 10, 7, 12, 8, 1, 2, 6, 4],
    ![2, 4, 12, 1, 3, 11, 9, 5, 8, 10, 6, 7, 0],
    ![10, 1, 6, 4, 5, 12, 7, 9, 11, 2, 8, 3, 0],
    ![9, 0, 10, 3, 6, 7, 4, 2, 5, 1, 11, 8, 12],
    ![0, 8, 9, 12, 11, 10, 7, 6, 3, 2, 4, 5, 1],
    ![0, 6, 4, 11, 3, 9, 2, 1, 7, 10, 12, 8, 5]]

def bT : Fin 18 → Fin 13 → Fin 13 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ![0, 6, 1, 11, 4, 8, 2, 5, 7, 3, 10, 9, 12],
    ![10, 7, 5, 6, 4, 9, 8, 3, 11, 2, 0, 1, 12],
    ![4, 2, 11, 7, 0, 5, 8, 6, 3, 1, 12, 9, 10],
    ![4, 11, 5, 2, 10, 6, 1, 9, 8, 3, 12, 7, 0],
    ![0, 3, 6, 8, 4, 7, 5, 9, 1, 11, 12, 2, 10],
    ![1, 2, 7, 9, 5, 12, 3, 10, 4, 8, 11, 6, 0],
    ![1, 12, 7, 9, 11, 6, 8, 10, 3, 4, 0, 2, 5],
    ![4, 6, 3, 1, 12, 11, 5, 8, 2, 9, 0, 7, 10],
    ![1, 4, 2, 12, 0, 3, 9, 6, 10, 7, 11, 8, 5],
    ![0, 5, 3, 2, 4, 1, 6, 7, 9, 8, 12, 11, 10],
    ![0, 7, 5, 11, 4, 2, 8, 1, 6, 9, 10, 3, 12],
    ![0, 2, 10, 4, 9, 7, 11, 12, 5, 1, 6, 3, 8],
    ![1, 3, 11, 0, 2, 8, 9, 5, 7, 10, 6, 4, 12],
    ![1, 5, 3, 4, 9, 11, 6, 8, 2, 12, 7, 0, 10],
    ![0, 10, 7, 3, 6, 4, 1, 2, 5, 11, 8, 12, 9],
    ![12, 8, 9, 11, 10, 7, 6, 3, 2, 1, 4, 5, 0],
    ![10, 3, 8, 2, 0, 6, 1, 11, 7, 9, 12, 5, 4]]

def bSi : Fin 18 → Fin 13 → Fin 13 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ![0, 3, 2, 9, 5, 7, 10, 4, 8, 1, 11, 6, 12],
    ![0, 11, 12, 10, 7, 5, 3, 4, 2, 6, 1, 9, 8],
    ![0, 5, 10, 4, 9, 1, 8, 3, 6, 7, 12, 2, 11],
    ![0, 2, 6, 12, 9, 3, 5, 1, 11, 8, 7, 4, 10],
    ![0, 9, 11, 1, 4, 7, 2, 5, 6, 3, 8, 12, 10],
    ![8, 0, 1, 2, 9, 4, 7, 11, 5, 12, 3, 10, 6],
    ![10, 0, 1, 11, 9, 12, 8, 5, 2, 6, 3, 7, 4],
    ![0, 6, 4, 11, 3, 9, 2, 1, 7, 10, 12, 8, 5],
    ![4, 0, 3, 5, 1, 2, 8, 10, 12, 7, 9, 11, 6],
    ![0, 1, 6, 3, 5, 4, 2, 7, 10, 9, 8, 12, 11],
    ![0, 3, 8, 1, 7, 5, 11, 4, 2, 9, 10, 6, 12],
    ![3, 9, 10, 1, 12, 4, 11, 6, 8, 0, 5, 2, 7],
    ![12, 3, 0, 4, 1, 7, 10, 11, 8, 6, 9, 5, 2],
    ![12, 1, 9, 11, 3, 4, 2, 6, 10, 7, 0, 8, 5],
    ![1, 9, 7, 3, 6, 8, 4, 5, 11, 0, 2, 10, 12],
    ![0, 12, 9, 8, 10, 11, 7, 6, 1, 2, 5, 4, 3],
    ![0, 7, 6, 4, 2, 12, 1, 8, 11, 5, 9, 3, 10]]

def bTi : Fin 18 → Fin 13 → Fin 13 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ![0, 2, 6, 9, 4, 7, 1, 8, 5, 11, 10, 3, 12],
    ![10, 11, 9, 7, 4, 2, 3, 1, 6, 5, 0, 8, 12],
    ![4, 9, 1, 8, 0, 5, 7, 3, 6, 11, 12, 2, 10],
    ![12, 6, 3, 9, 0, 2, 5, 11, 8, 7, 4, 1, 10],
    ![0, 8, 11, 1, 4, 6, 2, 5, 3, 7, 12, 9, 10],
    ![12, 0, 1, 6, 8, 4, 11, 2, 9, 3, 7, 10, 5],
    ![10, 0, 11, 8, 9, 12, 5, 2, 6, 3, 7, 4, 1],
    ![10, 3, 8, 2, 0, 6, 1, 11, 7, 9, 12, 5, 4],
    ![4, 0, 2, 5, 1, 12, 7, 9, 11, 6, 8, 10, 3],
    ![0, 5, 3, 2, 4, 1, 6, 7, 9, 8, 12, 11, 10],
    ![0, 7, 5, 11, 4, 2, 8, 1, 6, 9, 10, 3, 12],
    ![0, 9, 1, 11, 3, 8, 10, 5, 12, 4, 2, 6, 7],
    ![3, 0, 4, 1, 11, 7, 10, 8, 5, 6, 9, 2, 12],
    ![11, 0, 8, 2, 3, 1, 6, 10, 7, 4, 12, 5, 9],
    ![0, 6, 7, 3, 5, 8, 4, 2, 10, 12, 1, 9, 11],
    ![12, 9, 8, 7, 10, 11, 6, 5, 1, 2, 4, 3, 0],
    ![4, 6, 3, 1, 12, 11, 5, 8, 2, 9, 0, 7, 10]]

def tPP : Fin 13 → Fin 18 := ![0, 0, 4, 1, 9, 3, 8, 17, 6, 5, 7, 2, 16]

def tLL : Fin 13 → Fin 18 := ![0, 0, 1, 13, 9, 10, 15, 11, 5, 12, 7, 14, 6]

def tPL : Fin 13 → Fin 18 := ![0, 0, 1, 8, 3, 10, 4, 11, 5, 3, 2, 2, 4]

theorem beta_auto (k : Fin 18) : Auto (bS k) (bT k) (bSi k) (bTi k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> revert k <;> decide +kernel

def sameReal (l1 l2 : List ℕ) : Bool :=
  (List.range 26).all fun e => l1.contains e == l2.contains e

theorem any_eq_of_sameReal (l1 l2 : List ℕ) (h : sameReal l1 l2 = true) (x : List Bool)
    (hx : x.length = 26) :
    l1.any (fun i => x.getD i false) = l2.any (fun i => x.getD i false) := by
  have key : ∀ e, e < 26 → (e ∈ l1 ↔ e ∈ l2) := by
    intro e he
    have h1 := List.all_eq_true.1 h e (List.mem_range.2 he)
    have h2 : l1.contains e = l2.contains e := by simpa using h1
    rw [← List.contains_iff_mem, ← List.contains_iff_mem, h2]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hv⟩
    have hlt : i < 26 := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by omega)] at hv
      cases hv
    exact ⟨i, (key i hlt).1 hi, hv⟩
  · rintro ⟨i, hi, hv⟩
    have hlt : i < 26 := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by omega)] at hv
      cases hv
    exact ⟨i, (key i hlt).2 hi, hv⟩

theorem fits_congr (C : Circuit) (s t : List ℕ)
    (h : ∀ x : List Bool, x.length = 26 →
      s.any (fun i => x.getD i false) = t.any (fun i => x.getD i false))
    (hf : fits C s) : fits C t := by
  refine ⟨fun p l hpl => ?_, fun Q hQ => ?_⟩
  · have e : ext t (P p l) = ext s (P p l) := by unfold ext; rw [h _ (P_len p l)]
    rw [e]; exact hf.1 p l hpl
  · have e : ext t (N Q) = ext s (N Q) := by unfold ext; rw [h _ (N_len Q)]
    rw [e]; exact hf.2 Q hQ

theorem getD_min (x : List Bool) (hx : x.length = 26) (e : ℕ) :
    x.getD (min e 26) false = x.getD e false := by
  by_cases h : e < 26
  · rw [min_eq_left h.le]
  · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

theorem norm_any (s : List ℕ) (hs : s.length ≤ 2) (x : List Bool) (hx : x.length = 26) :
    s.any (fun i => x.getD i false) =
      [min (s.getD 0 26) 26, min (s.getD 1 26) 26].any (fun i => x.getD i false) := by
  have h26 : x.getD 26 false = false := List.getD_eq_default _ _ (by omega)
  rcases s with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  all_goals simp only [List.getD_nil, List.getD_cons_zero, List.getD_cons_succ, List.any_cons,
    List.any_nil, getD_min x hx, h26, Bool.or_false, min_self]
  simp at hs

def single (x : ℕ) : Fin 13 × Fin 18 × ℕ :=
  if x < 13 then (-(Fin.ofNat 13 x), 0, 1) else (-Fin.ofNat 13 (x - 13), 0, 2)

def wit (a b : ℕ) : Fin 13 × Fin 18 × ℕ :=
  if 26 ≤ a ∧ 26 ≤ b then (0, 0, 0)
  else if 26 ≤ a then single b
  else if 26 ≤ b ∨ a = b then single a
  else if a < 13 ∧ b < 13 then (-Fin.ofNat 13 a, tPP (Fin.ofNat 13 b - Fin.ofNat 13 a), 3)
  else if 13 ≤ a ∧ 13 ≤ b then
    (-Fin.ofNat 13 (a - 13), tLL (Fin.ofNat 13 (b - 13) - Fin.ofNat 13 (a - 13)), 4)
  else if a < 13 then
    (-Fin.ofNat 13 a, tPL (Fin.ofNat 13 (b - 13) - Fin.ofNat 13 a),
      if 0 - (Fin.ofNat 13 (b - 13) - Fin.ofNat 13 a) ∈ D then 5 else 6)
  else
    (-Fin.ofNat 13 b, tPL (Fin.ofNat 13 (a - 13) - Fin.ofNat 13 b),
      if 0 - (Fin.ofNat 13 (a - 13) - Fin.ofNat 13 b) ∈ D then 5 else 6)

theorem wit_ok : ∀ a b : Fin 27,
    (wit a.val b.val).2.2 < 7 ∧
    sameReal (canonList.getD (wit a.val b.val).2.2 [])
      (([a.val, b.val].map (wmap (fun p => p + (wit a.val b.val).1)
          (fun l => l + (wit a.val b.val).1))).map
        (wmap (bS (wit a.val b.val).2.1) (bT (wit a.val b.val).2.1))) = true := by
  decide +kernel

theorem main (C : Circuit) (s : List ℕ) (hs : s.length ≤ 2) (hm : Monotone2 C) (hb : Bnd C)
    (hf : fits C s) :
    ∃ B t, t ∈ canonList ∧ B.size = C.size ∧ Monotone2 B ∧ Bnd B ∧ fits B t := by
  have haf : min (s.getD 0 26) 26 < 27 := by omega
  have hbf : min (s.getD 1 26) 26 < 27 := by omega
  have hf0 : fits C [min (s.getD 0 26) 26, min (s.getD 1 26) 26] :=
    fits_congr C s _ (fun x hx => norm_any s hs x hx) hf
  obtain ⟨hok, hsame⟩ := wit_ok ⟨_, haf⟩ ⟨_, hbf⟩
  obtain ⟨m1, b1, s1, f1⟩ := relabel (trans_auto (wit (min (s.getD 0 26) 26)
    (min (s.getD 1 26) 26)).1) C _ hm hb hf0
  obtain ⟨m2, b2, s2, f2⟩ := relabel (beta_auto (wit (min (s.getD 0 26) 26)
    (min (s.getD 1 26) 26)).2.1) _ _ m1 b1 f1
  refine ⟨_, canonList.getD (wit (min (s.getD 0 26) 26) (min (s.getD 1 26) 26)).2.2 [], ?_,
    s2.trans s1, m2, b2, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by simpa [canonList] using hok)]
    exact List.getElem_mem _
  · exact fits_congr _ _ _ (fun x hx => (any_eq_of_sameReal _ _ hsame x hx).symm) f2

end PEqualNP.Outside.L_meta_3801

theorem PEqualNP.Outside.L_meta_3801 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : List ℕ) =>   have x7 : List Bool → List Bool := fun (x7 : List Bool) => x7 ++ [x6.any fun (x8 : ℕ) => x7.getD x8 Bool.false];   (∀ (x8 x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 → x5.eval (x7 (x2 x8 x9)) = Bool.true) ∧ ∀ (x8 : Finset (Fin (13 : ℕ))), x4 x8 → x5.eval (x7 (x3 x8)) = Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List ℕ), x7.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin x6.gates.length), ∀ x11 ∈ (x6.gates.get x10).inputs, x11 < (27 : ℕ) + ↑x10) → x5 x6 x7 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), ∃ x13 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], x12.size = x6.size ∧ PEqualNP.MetaComplexity.Monotone2 x12 ∧ (∀ (x14 : Fin x12.gates.length), ∀ x15 ∈ (x12.gates.get x14).inputs, x15 < (27 : ℕ) + ↑x14) ∧ x5 x12 x13 := by
  intro x1 x2 x3 x4 x5 C s hs hm hb hf
  exact PEqualNP.Outside.L_meta_3801.main C s hs hm hb hf
