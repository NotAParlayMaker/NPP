import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4913

open PEqualNP.CircuitLowerBounds PEqualNP.SharedBlockCost PEqualNP.BicliqueBlockCost

def gfold {α : Type*} (d : α) (F : (ℕ → α) → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun acc g => acc ++ [F (fun i => acc.getD i d) g]) w

lemma gfold_append {α : Type*} (d : α) (F : (ℕ → α) → Gate → α) (gs₁ gs₂ : List Gate)
    (w : List α) : gfold d F (gs₁ ++ gs₂) w = gfold d F gs₂ (gfold d F gs₁ w) := by
  simp [gfold, List.foldl_append]

lemma gfold_ext {α : Type*} (d : α) (F : (ℕ → α) → Gate → α) (gs : List Gate) : ∀ w : List α,
    ∃ t : List α, gfold d F gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [gfold], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [F (fun i => w.getD i d) g])
    refine ⟨F (fun i => w.getD i d) g :: t, ?_, by simp [hl]⟩
    have hstep : gfold d F (g :: gs) w = gfold d F gs (w ++ [F (fun i => w.getD i d) g]) := rfl
    rw [hstep, ht]
    simp

lemma length_gfold {α : Type*} (d : α) (F : (ℕ → α) → Gate → α) (gs : List Gate) (w : List α) :
    (gfold d F gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := gfold_ext d F gs w
  rw [ht, List.length_append, hl]

lemma getD_gfold_lt {α : Type*} (d : α) (F : (ℕ → α) → Gate → α) (gs : List Gate) (w : List α)
    (i : ℕ) (h : i < w.length) : (gfold d F gs w).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := gfold_ext d F gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_gfold_big {α : Type*} (d : α) (F : (ℕ → α) → Gate → α) (gs : List Gate) (w : List α)
    (i : ℕ) (h : w.length + gs.length ≤ i) : (gfold d F gs w).getD i d = d := by
  rw [List.getD_eq_default]
  rw [length_gfold]; omega

lemma getD_gfold_take {α : Type*} (d : α) (F : (ℕ → α) → Gate → α) (gs : List Gate) (w : List α)
    (k i : ℕ) (hk : k ≤ gs.length) :
    (gfold d F (gs.take k) w).getD i d =
      if i < w.length + k then (gfold d F gs w).getD i d else d := by
  have hlen : (gfold d F (gs.take k) w).length = w.length + k := by
    rw [length_gfold, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, gfold_append]
    exact (getD_gfold_lt d F (gs.drop k) (gfold d F (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_gfold_gate {α : Type*} (d : α) (F : (ℕ → α) → Gate → α) (gs : List Gate)
    (w : List α) (k : ℕ) (hk : k < gs.length) :
    (gfold d F gs w).getD (w.length + k) d =
      F (fun i => if i < w.length + k then (gfold d F gs w).getD i d else d) gs[k] := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (gfold d F (gs.take k) w).length = w.length + k := by
    rw [length_gfold, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : gfold d F gs w =
      gfold d F (gs.drop (k + 1))
        (gfold d F (gs.take k) w ++
          [F (fun i => (gfold d F (gs.take k) w).getD i d) gs[k]]) := by
    conv_lhs => rw [hsplit, gfold_append]
    rfl
  rw [heq, getD_gfold_lt]
  · conv_lhs => rw [← hlen, List.getD_append_right _ _ _ _ (le_refl _)]
    simp only [Nat.sub_self, List.getD_cons_zero]
    congr 1
    funext i
    rw [getD_gfold_take d F gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

/-- Gate `j` (a default OR gate with no inputs if there is none). -/
def gt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨GateOp.or, []⟩

lemma gt_eq (C : Circuit) (j : ℕ) (h : j < C.gates.length) : gt C j = C.gates[j] := by
  simp [gt, List.getD_eq_getElem?_getD, h]

lemma gt_some (C : Circuit) (j : ℕ) (h : j < C.gates.length) : C.gates[j]? = some (gt C j) := by
  rw [gt_eq C j h]; simp [h]

def val (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (l : List Bool) :
    C.wires l = gfold false (fun r g => g.op.eval (g.inputs.map r)) C.gates l := rfl

lemma val_gate (C : Circuit) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (h : j < C.gates.length) :
    val C x (n + j) = (gt C j).op.eval ((gt C j).inputs.map
      fun i => if i < n + j then val C x i else false) := by
  have := getD_gfold_gate false (fun r g => g.op.eval (g.inputs.map r)) C.gates (List.ofFn x) j h
  simp only [List.length_ofFn] at this
  rw [val, wires_eq, this, gt_eq C j h]
  rfl

lemma val_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val C x i = x ⟨i, h⟩ := by
  rw [val, wires_eq, getD_gfold_lt _ _ _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_big (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + C.gates.length ≤ w) :
    val C x w = false := by
  rw [val, wires_eq, getD_gfold_big _ _ _ _ _ (by simpa using h)]

def sF {n : ℕ} (r : ℕ → Finset (Fin n)) (g : Gate) : Finset (Fin n) :=
  if isOrOp g.op then (g.inputs.map r).foldr (· ∪ ·) ∅ else ∅

def S (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  (gfold ∅ sF C.gates (List.ofFn fun i : Fin n => ({i} : Finset (Fin n)))).getD w ∅

def Srd (C : Circuit) (n : ℕ) (j i : ℕ) : Finset (Fin n) := if i < n + j then S C n i else ∅

lemma mem_foldr_union {n : ℕ} (ss : List (Finset (Fin n))) (u : Fin n) :
    u ∈ ss.foldr (· ∪ ·) ∅ ↔ ∃ A ∈ ss, u ∈ A := by
  induction ss with
  | nil => simp
  | cons A ss ih => simp [ih]

lemma S_gate (C : Circuit) (n : ℕ) (j : ℕ) (h : j < C.gates.length) (u : Fin n) :
    u ∈ S C n (n + j) ↔ isOrOp (gt C j).op = true ∧ ∃ i ∈ (gt C j).inputs, u ∈ Srd C n j i := by
  have := getD_gfold_gate (∅ : Finset (Fin n)) sF C.gates
    (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))) j h
  simp only [List.length_ofFn] at this
  rw [S, this, ← gt_eq C j h]
  show u ∈ sF (fun i => if i < n + j then S C n i else ∅) (gt C j) ↔ _
  unfold sF
  by_cases ho : isOrOp (gt C j).op = true
  · simp only [ho, ite_true, mem_foldr_union, List.mem_map, true_and]
    constructor
    · rintro ⟨A, ⟨i, hi, rfl⟩, hu⟩; exact ⟨i, hi, hu⟩
    · rintro ⟨i, hi, hu⟩; exact ⟨_, ⟨i, hi, rfl⟩, hu⟩
  · simp [ho]

lemma S_input (C : Circuit) (n : ℕ) (i : ℕ) (h : i < n) : S C n i = {⟨i, h⟩} := by
  rw [S, getD_gfold_lt _ _ _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma S_big (C : Circuit) (n : ℕ) (w : ℕ) (h : n + C.gates.length ≤ w) : S C n w = ∅ := by
  rw [S, getD_gfold_big _ _ _ _ _ (by simpa using h)]

lemma isOr_eq {o : GateOp} (h : isOrOp o = true) : o = GateOp.or := by
  cases o <;> simp_all [isOrOp]

/-- Lower bound: a wire is true as soon as a vertex of its singleton part is. -/
lemma lower (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    ∀ w, ∀ u ∈ S C n w, x u = true → val C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro u hu hx
    by_cases hw : w < n
    · rw [S_input C n w hw, Finset.mem_singleton] at hu
      subst hu; rw [val_input C x w hw]; exact hx
    · by_cases hb : n + C.gates.length ≤ w
      · rw [S_big C n w hb] at hu; simp at hu
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [S_gate C n j hj] at hu
        obtain ⟨ho, i, hi, hui⟩ := hu
        unfold Srd at hui
        split_ifs at hui with hlt
        · rw [val_gate C x j hj, isOr_eq ho]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          exact ⟨i, hi, by simp only [hlt, ite_true]; exact ih i hlt u hui hx⟩
        · simp at hui

inductive Rel (C : Circuit) (n : ℕ) : ℕ → Prop
  | out : Rel C n C.output
  | step (j i : ℕ) : j < C.gates.length → Rel C n (n + j) → i ∈ (gt C j).inputs → i < n + j →
      Rel C n i

def blk (C : Circuit) (n j : ℕ) : Block n :=
  (Srd C n j ((gt C j).inputs.getD 0 0), Srd C n j ((gt C j).inputs.getD 1 0))

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def Proper (C : Circuit) (n j : ℕ) : Prop :=
  j < C.gates.length ∧ isAndOp (gt C j).op = true ∧ (gt C j).inputs.length = 2 ∧
    (blk C n j).1.Nonempty ∧ (blk C n j).2.Nonempty

def edgeIn {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true

def single {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)

def pair {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma no_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : ¬ edgeIn G (single u) := by
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [single, decide_eq_true_eq] at ha hb
  subst ha; subst hb; exact G.irrefl hab

lemma pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) (h : edgeIn G (pair u v)) :
    G.Adj u v := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  simp only [pair, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (G.irrefl hab).elim
  · exact hab
  · exact hab.symm
  · exact (G.irrefl hab).elim

def Junk {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin n → Bool, val C x (n + j) = true → edgeIn G x

lemma shape (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) (j : ℕ)
    (hj : j < C.gates.length) :
    ((gt C j).op = GateOp.and ∨ (gt C j).op = GateOp.or) ∧ (gt C j).inputs.length ≤ 2 := by
  have hmem : gt C j ∈ C.gates := by rw [gt_eq C j hj]; exact List.getElem_mem hj
  obtain ⟨h1, h2⟩ := hM _ hmem
  refine ⟨?_, h2⟩
  simpa using h1

lemma isAnd_eq {o : GateOp} (h : isAndOp o = true) : o = GateOp.and := by
  cases o <;> simp_all [isAndOp]

lemma Srd_ne {C : Circuit} {n j i : ℕ} (h : (Srd C n j i).Nonempty) :
    i < n + j ∧ Srd C n j i = S C n i := by
  unfold Srd at h ⊢
  split_ifs at h ⊢ with hi
  · exact ⟨hi, rfl⟩
  · simp at h

lemma upper (C : Circuit) {n : ℕ} (G : SimpleGraph (Fin n))
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hJ : Junk G C) (x : Fin n → Bool) :
    ∀ w, Rel C n w → val C x w = true → (∃ u ∈ S C n w, x u = true) ∨
      ∃ j, Rel C n (n + j) ∧ Proper C n j ∧
        ∃ p ∈ (blk C n j).1, ∃ q ∈ (blk C n j).2, x p = true ∧ x q = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hR hv
    by_cases hw : w < n
    · left; exact ⟨⟨w, hw⟩, by rw [S_input C n w hw]; simp, by rw [← val_input C x w hw]; exact hv⟩
    · by_cases hb : n + C.gates.length ≤ w
      · rw [val_big C x w hb] at hv; exact absurd hv (by simp)
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨hop, hlen⟩ := shape C hM j hj
        rcases hop with hand | hor
        · rw [val_gate C x j hj, hand] at hv
          rcases hins : (gt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · exfalso
            obtain ⟨a, b, _, ha, _⟩ := hJ j (gt C j) (gt_some C j hj) hand (fun _ => false)
              (by rw [val_gate C (fun _ => false) j hj, hand, hins]; rfl)
            simp at ha
          · rw [hins] at hv
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              Bool.and_true, id_eq] at hv
            split_ifs at hv with hlt
            rcases ih a hlt (Rel.step j a hj hR (by rw [hins]; simp) hlt) hv with
              ⟨u, hu, _⟩ | hc
            · exfalso
              apply no_single G u
              apply hJ j (gt C j) (gt_some C j hj) hand (single u)
              rw [val_gate C (single u) j hj, hand, hins]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                Bool.and_true, id_eq, hlt, ite_true]
              exact lower C (single u) a u hu (by simp [single])
            · right; exact hc
          · rw [hins] at hv
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true] at hv
            obtain ⟨hva, hvb⟩ := hv
            split_ifs at hva with hla
            split_ifs at hvb with hlb
            rcases ih a hla (Rel.step j a hj hR (by rw [hins]; simp) hla) hva with
              ⟨p, hp, hxp⟩ | hc
            · rcases ih b hlb (Rel.step j b hj hR (by rw [hins]; simp) hlb) hvb with
                ⟨q, hq, hxq⟩ | hc
              · right
                have hblk : blk C n j = (S C n a, S C n b) := by
                  simp [blk, hins, Srd, hla, hlb]
                refine ⟨j, hR, ⟨hj, by rw [hand]; rfl, by rw [hins]; rfl, ?_, ?_⟩, ?_⟩
                · rw [hblk]; exact ⟨p, hp⟩
                · rw [hblk]; exact ⟨q, hq⟩
                · rw [hblk]; exact ⟨p, hp, q, hq, hxp, hxq⟩
              · right; exact hc
            · right; exact hc
          · rw [hins] at hlen; simp at hlen
        · rw [val_gate C x j hj, hor] at hv
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply,
            id_eq] at hv
          obtain ⟨i, hi, hvi⟩ := hv
          split_ifs at hvi with hlt
          rcases ih i hlt (Rel.step j i hj hR hi hlt) hvi with ⟨u, hu, hx⟩ | hc
          · left
            refine ⟨u, (S_gate C n j hj u).2 ⟨by rw [hor]; rfl, i, hi, ?_⟩, hx⟩
            simp [Srd, hlt, hu]
          · right; exact hc

lemma block_valid (C : Circuit) {n : ℕ} (G : SimpleGraph (Fin n)) (hJ : Junk G C) (j : ℕ)
    (hP : Proper C n j) : IsBlock G (blk C n j) := by
  obtain ⟨hj, hand, hlen, hA, hB⟩ := hP
  obtain ⟨a, b, hins⟩ := List.length_eq_two.1 hlen
  have hA' := hA; have hB' := hB
  simp only [blk, hins, List.getD_cons_zero, List.getD_cons_succ] at hA' hB'
  obtain ⟨hla, ea⟩ := Srd_ne hA'
  obtain ⟨hlb, eb⟩ := Srd_ne hB'
  have hblk : blk C n j = (S C n a, S C n b) := by
    simp only [blk, hins, List.getD_cons_zero, List.getD_cons_succ, ea, eb]
  have hadj : ∀ p ∈ S C n a, ∀ q ∈ S C n b, G.Adj p q := by
    intro p hp q hq
    apply pair_adj G p q
    apply hJ j (gt C j) (gt_some C j hj) (isAnd_eq hand) (pair p q)
    rw [val_gate C (pair p q) j hj, isAnd_eq hand, hins]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      Bool.and_true, id_eq, Bool.and_eq_true, hla, hlb, ite_true]
    exact ⟨lower C _ a p hp (by simp [pair]), lower C _ b q hq (by simp [pair])⟩
  rw [hblk]
  rw [hblk] at hA hB
  refine ⟨?_, hA, hB, hadj⟩
  rw [Finset.disjoint_left]
  intro r hra hrb
  exact G.irrefl (hadj r hra r hrb)

lemma S_out_empty (C : Circuit) {n : ℕ} (G : SimpleGraph (Fin n))
    (hE : ∀ x : Fin n → Bool, val C x C.output = true ↔ edgeIn G x) : S C n C.output = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u hu
  exact no_single G u ((hE (single u)).1 (lower C _ _ u hu (by simp [single])))

lemma cover (C : Circuit) {n : ℕ} (G : SimpleGraph (Fin n))
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hJ : Junk G C)
    (hE : ∀ x : Fin n → Bool, val C x C.output = true ↔ edgeIn G x) (u v : Fin n)
    (huv : G.Adj u v) : ∃ j, Rel C n (n + j) ∧ Proper C n j ∧ BlockCovers (blk C n j) u v := by
  have hv : val C (pair u v) C.output = true := (hE _).2 ⟨u, v, huv, by simp [pair], by simp [pair]⟩
  rcases upper C G hM hJ (pair u v) C.output Rel.out hv with ⟨w, hw, _⟩ | ⟨j, hR, hP, p, hp, q, hq, hxp, hxq⟩
  · rw [S_out_empty C G hE] at hw; simp at hw
  · refine ⟨j, hR, hP, ?_⟩
    have hb := block_valid C G hJ j hP
    have hpq : G.Adj p q := hb.2.2.2 p hp q hq
    simp only [pair, decide_eq_true_eq] at hxp hxq
    unfold BlockCovers
    rcases hxp with rfl | rfl <;> rcases hxq with rfl | rfl
    · exact (G.irrefl hpq).elim
    · left; exact ⟨hp, hq⟩
    · right; exact ⟨hp, hq⟩
    · exact (G.irrefl hpq).elim

def binB (C : Circuit) (n j : ℕ) : Bool :=
  decide (j < C.gates.length) && isOrOp (gt C j).op && decide ((gt C j).inputs.length = 2) &&
    decide (blk C n j).1.Nonempty && decide (blk C n j).2.Nonempty

lemma binB_iff (C : Circuit) (n j : ℕ) : binB C n j = true ↔ j < C.gates.length ∧
    isOrOp (gt C j).op = true ∧ (gt C j).inputs.length = 2 ∧ (blk C n j).1.Nonempty ∧
      (blk C n j).2.Nonempty := by
  simp [binB, Bool.and_eq_true, and_assoc]

def fl (C : Circuit) (n m : ℕ) : List ℕ := (List.range m).filter (binB C n)

def cntB (C : Circuit) (n m : ℕ) : ℕ := (fl C n m).length

lemma fl_add (C : Circuit) (n a b : ℕ) :
    fl C n (a + b) = fl C n a ++ ((List.range b).map (a + ·)).filter (binB C n) := by
  rw [fl, List.range_add, List.filter_append]; rfl

lemma cntB_mono (C : Circuit) (n : ℕ) {a b : ℕ} (h : a ≤ b) : cntB C n a ≤ cntB C n b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [cntB, cntB, fl_add, List.length_append]; omega

lemma fl_succ (C : Circuit) (n j : ℕ) (hb : binB C n j = true) : fl C n (j + 1) = fl C n j ++ [j] := by
  rw [fl, List.range_succ, List.filter_append]
  simp [hb, fl]

lemma cntB_succ (C : Circuit) (n j : ℕ) (hb : binB C n j = true) :
    cntB C n (j + 1) = cntB C n j + 1 := by
  rw [cntB, cntB, fl_succ C n j hb]; simp

lemma binB_lt {C : Circuit} {n j : ℕ} (hb : binB C n j = true) : j < C.gates.length :=
  ((binB_iff C n j).1 hb).1

lemma fl_split (C : Circuit) (n j : ℕ) (hb : binB C n j = true) :
    ∃ Y, fl C n C.gates.length = fl C n j ++ j :: Y := by
  have hj := binB_lt hb
  obtain ⟨c, hc⟩ : ∃ c, C.gates.length = (j + 1) + c := ⟨C.gates.length - (j + 1), by omega⟩
  rw [hc, fl_add, fl_succ C n j hb]
  exact ⟨((List.range c).map (fun x => j + 1 + x)).filter (binB C n), by simp⟩

lemma fl_get (C : Circuit) (n j : ℕ) (hb : binB C n j = true) :
    ∃ h : cntB C n j < (fl C n C.gates.length).length, (fl C n C.gates.length)[cntB C n j] = j := by
  obtain ⟨Y, hY⟩ := fl_split C n j hb
  have hlen : cntB C n j < (fl C n C.gates.length).length := by
    rw [hY, cntB]; simp
  refine ⟨hlen, ?_⟩
  simp only [hY, cntB]
  simp

lemma fl_nodup (C : Circuit) (n m : ℕ) : (fl C n m).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

lemma mem_fl (C : Circuit) (n m j : ℕ) : j ∈ fl C n m ↔ j < m ∧ binB C n j = true := by
  simp [fl]

def pick (C : Circuit) (n j : ℕ) : ℕ :=
  ((gt C j).inputs.filter (fun i => decide (i < n + j) && decide (S C n i).Nonempty)).headD 0

def rep (C : Circuit) (n : ℕ) (w : ℕ) : ℕ :=
  if w < n then w
  else if binB C n (w - n) then n + cntB C n (w - n)
  else if h : pick C n (w - n) < w then rep C n (pick C n (w - n)) else 0
termination_by w

def mkG (C : Circuit) (n j : ℕ) : Gate :=
  ⟨GateOp.or, [rep C n ((gt C j).inputs.getD 0 0), rep C n ((gt C j).inputs.getD 1 0)]⟩

def D (C : Circuit) (n : ℕ) : Circuit := ⟨(fl C n C.gates.length).map (mkG C n), 0⟩

lemma D_len (C : Circuit) (n : ℕ) : (D C n).gates.length = cntB C n C.gates.length := by
  simp [D, cntB]

lemma S_ne_lt {C : Circuit} {n w : ℕ} (h : (S C n w).Nonempty) : w < n + C.gates.length := by
  by_contra hc
  rw [S_big C n w (by omega)] at h; simp at h

/-- Shape of an OR gate with a nonempty singleton part that is not binary. -/
lemma pick_spec (C : Circuit) {n : ℕ} (hM : PEqualNP.MetaComplexity.Monotone2 C) (j : ℕ)
    (hj : j < C.gates.length) (hne : (S C n (n + j)).Nonempty) (hb : binB C n j = false) :
    pick C n j < n + j ∧ S C n (n + j) = S C n (pick C n j) := by
  obtain ⟨u0, hu0⟩ := hne
  have hor := ((S_gate C n j hj u0).1 hu0).1
  have hlen := (shape C hM j hj).2
  have hmem : ∀ u, u ∈ S C n (n + j) ↔ ∃ i ∈ (gt C j).inputs, u ∈ Srd C n j i := by
    intro u; rw [S_gate C n j hj u]; simp [hor]
  rcases hins : (gt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rw [hins] at hmem; simp at hmem; exact absurd hu0 (hmem u0)
  · rw [hins] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_left] at hmem
    obtain ⟨hla, ea⟩ := Srd_ne ⟨u0, (hmem u0).1 hu0⟩
    have hpick : pick C n j = a := by
      have hSa : (S C n a).Nonempty := by rw [← ea]; exact ⟨u0, (hmem u0).1 hu0⟩
      simp [pick, hins, hla, hSa]
    rw [hpick]
    refine ⟨hla, ?_⟩
    ext u; rw [hmem u, ea]
  · rw [hins] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
      at hmem
    have hnb : ¬ ((Srd C n j a).Nonempty ∧ (Srd C n j b).Nonempty) := by
      intro ⟨h1, h2⟩
      have : binB C n j = true := by
        rw [binB_iff]
        exact ⟨hj, hor, by rw [hins]; rfl, by simpa [blk, hins] using h1,
          by simpa [blk, hins] using h2⟩
      rw [hb] at this; exact absurd this (by simp)
    by_cases hA : (Srd C n j a).Nonempty
    · have hB : Srd C n j b = ∅ := Finset.not_nonempty_iff_eq_empty.1 (fun h => hnb ⟨hA, h⟩)
      obtain ⟨hla, ea⟩ := Srd_ne hA
      have hSa : (S C n a).Nonempty := by rw [← ea]; exact hA
      have hpick : pick C n j = a := by simp [pick, hins, hla, hSa]
      rw [hpick]
      refine ⟨hla, ?_⟩
      ext u; rw [hmem u, hB, ← ea]; simp
    · have hA' : Srd C n j a = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA
      have hB : (Srd C n j b).Nonempty := by
        rcases (hmem u0).1 hu0 with h | h
        · rw [hA'] at h; simp at h
        · exact ⟨u0, h⟩
      obtain ⟨hlb, eb⟩ := Srd_ne hB
      have hSb : (S C n b).Nonempty := by rw [← eb]; exact hB
      have hfa : ¬ (a < n + j ∧ (S C n a).Nonempty) := by
        rintro ⟨h1, h2⟩; apply hA; unfold Srd; rw [if_pos h1]; exact h2
      have hpick : pick C n j = b := by
        unfold pick; rw [hins]
        rw [List.filter_cons_of_neg (by simpa using hfa)]
        simp [hlb, hSb]
      rw [hpick]
      refine ⟨hlb, ?_⟩
      ext u; rw [hmem u, hA', ← eb]; simp
  · rw [hins] at hlen; simp at hlen

lemma rep_lt (C : Circuit) {n : ℕ} (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    ∀ w, (S C n w).Nonempty → rep C n w < n + cntB C n (w + 1 - n) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne
    by_cases hw : w < n
    · rw [rep, if_pos hw]; omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by have := S_ne_lt hne; omega
      have e1 : n + j - n = j := by omega
      have e2 : n + j + 1 - n = j + 1 := by omega
      rw [e2]
      cases hb : binB C n j
      · obtain ⟨hp, hS⟩ := pick_spec C hM j hj hne hb
        rw [rep, if_neg hw, e1, hb, dif_pos hp]
        have := ih _ hp (by rw [← hS]; exact hne)
        have hm := cntB_mono C n (show pick C n j + 1 - n ≤ j + 1 by omega)
        simp only [Bool.false_eq_true, ite_false]
        omega
      · rw [rep, if_neg hw, e1, if_pos hb, cntB_succ C n j hb]; omega

lemma rep_input (C : Circuit) {n w : ℕ} (hw : w < n) : rep C n w = w := by
  rw [rep, if_pos hw]

lemma rep_bin (C : Circuit) {n j : ℕ} (hb : binB C n j = true) : rep C n (n + j) = n + cntB C n j := by
  rw [rep, if_neg (by omega), show n + j - n = j by omega, if_pos hb]

lemma rep_lt' (C : Circuit) {n : ℕ} (hM : PEqualNP.MetaComplexity.Monotone2 C) (j a : ℕ)
    (ha : a < n + j) (hne : (S C n a).Nonempty) : rep C n a < n + cntB C n j := by
  have h1 := rep_lt C hM a hne
  have h2 := cntB_mono C n (show a + 1 - n ≤ j by omega)
  omega

lemma D_gate (C : Circuit) (n j : ℕ) (hb : binB C n j = true) :
    ∃ h : cntB C n j < (D C n).gates.length, gt (D C n) (cntB C n j) = mkG C n j := by
  obtain ⟨h, hg⟩ := fl_get C n j hb
  have h' : cntB C n j < (D C n).gates.length := by simpa [D] using h
  refine ⟨h', ?_⟩
  rw [gt_eq _ _ h']
  simp [D, hg]

lemma binB_inputs (C : Circuit) {n j : ℕ} (hb : binB C n j = true) :
    ∃ a b, (gt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ (S C n a).Nonempty ∧
      (S C n b).Nonempty := by
  obtain ⟨_, _, hlen, hA, hB⟩ := (binB_iff C n j).1 hb
  obtain ⟨a, b, hins⟩ := List.length_eq_two.1 hlen
  simp only [blk, hins, List.getD_cons_zero, List.getD_cons_succ] at hA hB
  obtain ⟨hla, ea⟩ := Srd_ne hA
  obtain ⟨hlb, eb⟩ := Srd_ne hB
  exact ⟨a, b, hins, hla, hlb, by rw [← ea]; exact hA, by rw [← eb]; exact hB⟩

lemma rep_correct (C : Circuit) {n : ℕ} (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (x : Fin n → Bool) :
    ∀ w, (S C n w).Nonempty → (val (D C n) x (rep C n w) = true ↔ ∃ u ∈ S C n w, x u = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne
    by_cases hw : w < n
    · rw [rep_input C hw, val_input _ x w hw, S_input C n w hw]; simp
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by have := S_ne_lt hne; omega
      cases hb : binB C n j
      · obtain ⟨hp, hS⟩ := pick_spec C hM j hj hne hb
        have hr : rep C n (n + j) = rep C n (pick C n j) := by
          rw [rep, if_neg hw, show n + j - n = j by omega, hb, dif_pos hp]
          simp
        rw [hr, hS]
        exact ih _ hp (by rw [← hS]; exact hne)
      · obtain ⟨a, b, hins, hla, hlb, hSa, hSb⟩ := binB_inputs C hb
        obtain ⟨hp, hg⟩ := D_gate C n j hb
        rw [rep_bin C hb, val_gate (D C n) x _ hp, hg]
        have ra := rep_lt' C hM j a hla hSa
        have rb := rep_lt' C hM j b hlb hSb
        simp only [mkG, hins, List.getD_cons_zero, List.getD_cons_succ, List.map_cons,
          List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq, ra, rb,
          ite_true, Bool.or_eq_true]
        rw [ih a (by omega) hSa, ih b (by omega) hSb]
        have hor := ((binB_iff C n j).1 hb).2.1
        have hmem : ∀ u, u ∈ S C n (n + j) ↔ u ∈ S C n a ∨ u ∈ S C n b := by
          intro u; rw [S_gate C n j hj u, hins]; simp [hor, Srd, hla, hlb]
        constructor
        · rintro (⟨u, hu, hx⟩ | ⟨u, hu, hx⟩)
          · exact ⟨u, (hmem u).2 (Or.inl hu), hx⟩
          · exact ⟨u, (hmem u).2 (Or.inr hu), hx⟩
        · rintro ⟨u, hu, hx⟩
          rcases (hmem u).1 hu with h | h
          · exact Or.inl ⟨u, h, hx⟩
          · exact Or.inr ⟨u, h, hx⟩

lemma D_isOr (C : Circuit) {n : ℕ} (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    IsOrCircuit n (D C n) := by
  intro p hp
  have hp' : p < (fl C n C.gates.length).length := by simpa [D] using hp
  set j := (fl C n C.gates.length)[p] with hjdef
  have hjm : j ∈ fl C n C.gates.length := List.getElem_mem hp'
  have hb : binB C n j = true := ((mem_fl C n _ j).1 hjm).2
  obtain ⟨h2, hg2⟩ := fl_get C n j hb
  have hcp : cntB C n j = p := by
    have := (List.Nodup.getElem_inj_iff (fl_nodup C n C.gates.length)).1 (hg2.trans hjdef)
    exact this
  have hgate : (D C n).gates[p] = mkG C n j := by simp [D, hjdef]
  rw [hgate]
  obtain ⟨a, b, hins, hla, hlb, hSa, hSb⟩ := binB_inputs C hb
  have ra := rep_lt' C hM j a hla hSa
  have rb := rep_lt' C hM j b hlb hSb
  rw [hcp] at ra rb
  refine ⟨rfl, by simp [mkG], ?_⟩
  intro i hi
  simp only [mkG, hins, List.getD_cons_zero, List.getD_cons_succ, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ra
  · exact rb

lemma D_computes (C : Circuit) {n : ℕ} (hM : PEqualNP.MetaComplexity.Monotone2 C) (w : ℕ)
    (hne : (S C n w).Nonempty) : ComputesOr n (D C n) (rep C n w) (S C n w) := by
  refine ⟨?_, fun x => rep_correct C hM x w hne⟩
  have h1 := rep_lt C hM w hne
  have h2 := S_ne_lt hne
  have h3 := cntB_mono C n (show w + 1 - n ≤ C.gates.length by omega)
  rw [D_len]; omega

lemma rel_inv {C : Circuit} {n w : ℕ} (h : Rel C n w) : w = C.output ∨
    ∃ c i, c < C.gates.length ∧ Rel C n (n + c) ∧ i ∈ (gt C c).inputs ∧ i < n + c ∧ w = i := by
  cases h with
  | out => left; rfl
  | step c i h1 h2 h3 h4 => right; exact ⟨c, _, h1, h2, h3, h4, rfl⟩

lemma S_and (C : Circuit) {n j : ℕ} (hj : j < C.gates.length) (h : isAndOp (gt C j).op = true) :
    S C n (n + j) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u hu
  have := ((S_gate C n j hj u).1 hu).1
  rw [isAnd_eq h] at this; simp [isOrOp] at this

lemma S_bin (C : Circuit) {n j : ℕ} (hb : binB C n j = true) : (S C n (n + j)).Nonempty := by
  obtain ⟨a, b, hins, hla, _, ⟨u, hu⟩, _⟩ := binB_inputs C hb
  refine ⟨u, (S_gate C n j (binB_lt hb) u).2 ⟨((binB_iff C n j).1 hb).2.1, a, by simp [hins], ?_⟩⟩
  simp [Srd, hla, hu]

lemma side_S (C : Circuit) {n j : ℕ} (hP : Proper C n j) :
    (∃ w, (blk C n j).1 = S C n w ∧ (S C n w).Nonempty) ∧
      (∃ w, (blk C n j).2 = S C n w ∧ (S C n w).Nonempty) := by
  obtain ⟨_, _, _, hA, hB⟩ := hP
  obtain ⟨_, ea⟩ := Srd_ne hA
  obtain ⟨_, eb⟩ := Srd_ne hB
  exact ⟨⟨_, ea, by rw [← ea]; exact hA⟩, ⟨_, eb, by rw [← eb]; exact hB⟩⟩

lemma main (C : Circuit) {n : ℕ} (G : SimpleGraph (Fin n))
    (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hE : ∀ x : Fin n → Bool, val C x C.output = true ↔ edgeIn G x) (hJ : Junk G C) :
    HasSharedBlockCost G C.size := by
  classical
  set L := C.gates.length with hL
  set H := (Finset.range L).filter (fun j => Rel C n (n + j) ∧ S C n (n + j) = ∅) with hH
  set P := H.filter (fun j => Proper C n j) with hPdef
  set E := H.filter (fun j => ¬ Proper C n j) with hEdef
  set U := (Finset.range L).filter (fun j => Rel C n (n + j) ∧ (S C n (n + j)).Nonempty ∧
    ∃ i ∈ (gt C j).inputs, Srd C n j i = ∅) with hUdef
  set B := (fl C n L).toFinset with hBdef
  set F := P.image (blk C n) with hFdef
  have memP : ∀ j ∈ P, Rel C n (n + j) ∧ Proper C n j := by
    intro j hj
    simp only [hPdef, hH, Finset.mem_filter] at hj
    exact ⟨hj.1.2.1, hj.2⟩
  refine ⟨F, ⟨?_, ?_⟩, cntB C n L, ⟨D C n, ⟨D_isOr C hM, ?_⟩, by rw [D_len]⟩, ?_⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    exact block_valid C G hJ j (memP j hj).2
  · intro u v huv
    obtain ⟨j, hR, hPr, hcov⟩ := cover C G hM hJ hE u v huv
    refine ⟨blk C n j, Finset.mem_image.2 ⟨j, ?_, rfl⟩, hcov⟩
    simp only [hPdef, hH, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨hPr.1, hR, S_and C hPr.1 hPr.2.1⟩, hPr⟩
  · intro s hs
    simp only [sides, Finset.mem_union, Finset.mem_image] at hs
    rcases hs with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨⟨w, ew, hne⟩, _⟩ := side_S C (memP j hj).2
      rw [ew]
      have hc := D_computes C hM w hne
      exact ⟨rep C n w, hc.1, hc⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨_, ⟨w, ew, hne⟩⟩ := side_S C (memP j hj).2
      rw [ew]
      have hc := D_computes C hM w hne
      exact ⟨rep C n w, hc.1, hc⟩
  · -- counting
    have hF : F.card ≤ P.card := Finset.card_image_le
    have hHc : P.card + E.card = H.card := Finset.card_filter_add_card_filter_not _
    have hBc : B.card = cntB C n L := List.toFinset_card_of_nodup (fl_nodup C n L)
    let piece : ℕ → Finset ℕ := fun c =>
      ((gt C c).inputs.toFinset.filter (fun i => Srd C n c i = ∅)).image (fun i => i - n)
    have hEU : Disjoint E U := by
      rw [Finset.disjoint_left]
      intro c hcE hcU
      simp only [hEdef, hH, hUdef, Finset.mem_filter] at hcE hcU
      rw [hcE.1.2.2] at hcU; exact Finset.not_nonempty_empty hcU.2.2.1
    have hsub : H.erase (C.output - n) ⊆ (E ∪ U).biUnion piece := by
      intro j hj
      rw [Finset.mem_erase] at hj
      obtain ⟨hjo, hjH⟩ := hj
      simp only [hH, Finset.mem_filter, Finset.mem_range] at hjH
      obtain ⟨hjL, hRj, hSj⟩ := hjH
      rcases rel_inv hRj with ho | ⟨c, i, hcL, hRc, hi, hic, rfl⟩
      · exact absurd (by omega : j = C.output - n) hjo
      · have hSrd : Srd C n c (n + j) = ∅ := by simp [Srd, hic, hSj]
        rw [Finset.mem_biUnion]
        refine ⟨c, ?_, ?_⟩
        · by_cases hSc : S C n (n + c) = ∅
          · apply Finset.mem_union_left
            simp only [hEdef, hH, Finset.mem_filter, Finset.mem_range]
            refine ⟨⟨hcL, hRc, hSc⟩, ?_⟩
            intro hPc
            obtain ⟨_, _, hlen, hA, hB⟩ := hPc
            obtain ⟨a, b, hins⟩ := List.length_eq_two.1 hlen
            simp only [blk, hins, List.getD_cons_zero, List.getD_cons_succ] at hA hB
            rw [hins] at hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with h | h
            · rw [← h, hSrd] at hA; exact Finset.not_nonempty_empty hA
            · rw [← h, hSrd] at hB; exact Finset.not_nonempty_empty hB
          · apply Finset.mem_union_right
            simp only [hUdef, Finset.mem_filter, Finset.mem_range]
            exact ⟨hcL, hRc, Finset.nonempty_iff_ne_empty.2 hSc, n + j, hi, hSrd⟩
        · simp only [piece, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
          exact ⟨n + j, ⟨hi, hSrd⟩, by omega⟩
    have hpiece2 : ∀ c ∈ E, (piece c).card ≤ 2 := by
      intro c hc
      have hcL : c < L := by
        simp only [hEdef, hH, Finset.mem_filter, Finset.mem_range] at hc; exact hc.1.1
      have hlen := (shape C hM c hcL).2
      calc (piece c).card ≤ _ := Finset.card_image_le
        _ ≤ (gt C c).inputs.toFinset.card := Finset.card_filter_le _ _
        _ ≤ (gt C c).inputs.length := List.toFinset_card_le _
        _ ≤ 2 := hlen
    have hpiece1 : ∀ c ∈ U, (piece c).card ≤ 1 := by
      intro c hc
      simp only [hUdef, Finset.mem_filter, Finset.mem_range] at hc
      obtain ⟨hcL, _, ⟨u, hu⟩, _⟩ := hc
      have hlen := (shape C hM c hcL).2
      obtain ⟨_, i0, hi0, hui0⟩ := (S_gate C n c hcL u).1 hu
      have hss : (gt C c).inputs.toFinset.filter (fun i => Srd C n c i = ∅) ⊂
          (gt C c).inputs.toFinset := by
        rw [Finset.filter_ssubset]
        refine ⟨i0, List.mem_toFinset.2 hi0, ?_⟩
        intro h; rw [h] at hui0; simp at hui0
      have h1 := Finset.card_lt_card hss
      have h2 := List.toFinset_card_le (gt C c).inputs
      calc (piece c).card ≤ _ := Finset.card_image_le
        _ ≤ 1 := by omega
    have hcount : H.card ≤ 1 + 2 * E.card + U.card := by
      have h1 := Finset.pred_card_le_card_erase (s := H) (a := C.output - n)
      have h2 := Finset.card_le_card hsub
      have h3 := Finset.card_biUnion_le (s := E ∪ U) (t := piece)
      rw [Finset.sum_union hEU] at h3
      have h4 : ∑ c ∈ E, (piece c).card ≤ ∑ _c ∈ E, 2 := Finset.sum_le_sum hpiece2
      have h5 : ∑ c ∈ U, (piece c).card ≤ ∑ _c ∈ U, 1 := Finset.sum_le_sum hpiece1
      simp only [Finset.sum_const, smul_eq_mul] at h4 h5
      omega
    have hsum : B.card + P.card + E.card + U.card ≤ L := by
      have hBP : Disjoint B P := by
        rw [Finset.disjoint_left]
        intro j hjB hjP
        have hb : binB C n j = true := ((mem_fl C n L j).1 (List.mem_toFinset.1 hjB)).2
        have h1 := ((binB_iff C n j).1 hb).2.1
        have h2 := (memP j hjP).2.2.1
        rw [isAnd_eq h2] at h1; simp [isOrOp] at h1
      have hBE : Disjoint B E := by
        rw [Finset.disjoint_left]
        intro j hjB hjE
        have hb : binB C n j = true := ((mem_fl C n L j).1 (List.mem_toFinset.1 hjB)).2
        simp only [hEdef, hH, Finset.mem_filter] at hjE
        have := S_bin C hb
        rw [hjE.1.2.2] at this; exact Finset.not_nonempty_empty this
      have hBU : Disjoint B U := by
        rw [Finset.disjoint_left]
        intro j hjB hjU
        have hb : binB C n j = true := ((mem_fl C n L j).1 (List.mem_toFinset.1 hjB)).2
        simp only [hUdef, Finset.mem_filter] at hjU
        obtain ⟨_, _, _, i, hi, hie⟩ := hjU
        obtain ⟨a, b, hins, hla, hlb, hSa, hSb⟩ := binB_inputs C hb
        rw [hins] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · simp only [Srd, hla, ite_true] at hie; rw [hie] at hSa
          exact Finset.not_nonempty_empty hSa
        · simp only [Srd, hlb, ite_true] at hie; rw [hie] at hSb
          exact Finset.not_nonempty_empty hSb
      have hPE : Disjoint P E := by
        rw [Finset.disjoint_left]
        intro j hjP hjE
        simp only [hEdef, Finset.mem_filter] at hjE
        exact hjE.2 (memP j hjP).2
      have hPU : Disjoint P U := by
        rw [Finset.disjoint_left]
        intro j hjP hjU
        simp only [hPdef, hH, hUdef, Finset.mem_filter] at hjP hjU
        rw [hjP.1.2.2] at hjU; exact Finset.not_nonempty_empty hjU.2.2.1
      have hsubL : B ∪ P ∪ E ∪ U ⊆ Finset.range L := by
        intro j hj
        simp only [Finset.mem_union] at hj
        rw [Finset.mem_range]
        rcases hj with ((hj | hj) | hj) | hj
        · exact ((mem_fl C n L j).1 (List.mem_toFinset.1 hj)).1
        · exact (memP j hj).2.1
        · simp only [hEdef, hH, Finset.mem_filter, Finset.mem_range] at hj; exact hj.1.1
        · simp only [hUdef, Finset.mem_filter, Finset.mem_range] at hj; exact hj.1
      have hc := Finset.card_le_card hsubL
      rw [Finset.card_range, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
        Finset.card_union_of_disjoint] at hc
      · exact hc
      · exact hBP
      · exact Finset.disjoint_union_left.2 ⟨hBE, hPE⟩
      · exact Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hBU, hPU⟩, hEU⟩
    show cntB C n L + F.card + (F.card - 1) ≤ L
    omega

end PEqualNP.Outside.L_meta_4913

theorem PEqualNP.Outside.L_meta_4913 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 : Fin x1 → Bool), x3.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 → x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x10 : Fin x1 → Bool), (x3.wires (List.ofFn x10)).getD (x1 + x6) Bool.false = Bool.true → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x10 x12 = Bool.true ∧ x10 x13 = Bool.true) → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x3.size := by
  intro n G C hM hE hJ
  exact PEqualNP.Outside.L_meta_4913.main C G hM hE hJ
