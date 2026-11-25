import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6179_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (862 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

abbrev BE : BinaryTree ℕ := BinaryTree.nil
abbrev BN (v : ℕ) (l r : BinaryTree ℕ) : BinaryTree ℕ := BinaryTree.node v l r
abbrev BL (v : ℕ) : BinaryTree ℕ := BinaryTree.node v BinaryTree.nil BinaryTree.nil

def InTree (x : ℕ) : BinaryTree ℕ → Prop
  | BinaryTree.nil => False
  | BinaryTree.node v l r => x = v ∨ InTree x l ∨ InTree x r

def treeMem (x : ℕ) : BinaryTree ℕ → Bool
  | BinaryTree.nil => false
  | BinaryTree.node v l r =>
    if x == v then true
    else if x < v then treeMem x l
    else treeMem x r

theorem treeMem_imp {x : ℕ} : ∀ t : BinaryTree ℕ, treeMem x t = true → InTree x t
  | BinaryTree.nil, h => by simp [treeMem] at h
  | BinaryTree.node v l r, h => by
    unfold treeMem at h
    by_cases h1 : x == v
    · exact Or.inl (beq_iff_eq.mp h1)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : x < v
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inl (treeMem_imp l h))
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inr (treeMem_imp r h))

def checkTree (f : ℕ → Bool) : BinaryTree ℕ → Bool
  | BinaryTree.nil => true
  | BinaryTree.node v l r => f v && checkTree f l && checkTree f r

theorem checkTree_node {f : ℕ → Bool} {v : ℕ} {l r : BinaryTree ℕ}
    (hv : f v = true) (hl : checkTree f l = true) (hr : checkTree f r = true) :
    checkTree f (BN v l r) = true := by
  simp [checkTree, hv, hl, hr]

theorem checkTree_sound {f : ℕ → Bool} : ∀ t : BinaryTree ℕ, checkTree f t = true → ∀ x, InTree x t → f x = true
  | BinaryTree.nil, _, _, hx => hx.elim
  | BinaryTree.node v l r, h, x, hx => by
    simp only [checkTree, Bool.and_eq_true] at h
    rcases hx with rfl | hl | hr
    · exact h.1.1
    · exact checkTree_sound l h.1.2 x hl
    · exact checkTree_sound r h.2 x hr

def freeM (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = 65535 ∨ v ∈ S

def combM : Fin 2 → ℕ → ℕ → ℕ
  | 0, a, b => a &&& b
  | 1, a, b => a ||| b

def CanM (f : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => freeM S f
  | k+1, S => ∃ (o : Fin 2) (a b : ℕ), freeM S a ∧ freeM S b ∧ CanM f k (insert (combM o a b) S)

theorem freeMMono {v : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hv : freeM S v) : freeM T v :=
  hv.imp_right (Or.imp_right (fun e => h e))

theorem freeMSub {S T : Finset ℕ} (h : ∀ x ∈ S, freeM T x) {v : ℕ} (hv : freeM S v) : freeM T v := by
  rcases hv with rfl | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact h v hv

theorem monoCM_free {f k : ℕ} {S T : Finset ℕ} (h : ∀ x ∈ S, freeM T x) (hc : CanM f k S) : CanM f k T := by
  induction k generalizing S T with
  | zero => exact freeMSub h hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    refine ⟨o, a, b, freeMSub h ha, freeMSub h hb, ih ?_ hh⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
    · exact freeMMono (Finset.subset_insert _ _) (h x hx)

theorem monoCM {f k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hc : CanM f k S) : CanM f k T :=
  monoCM_free (fun x hx => Or.inr (Or.inr (h hx))) hc

theorem stepUpM {f k : ℕ} {S : Finset ℕ} (hc : CanM f k S) : CanM f (k+1) S :=
  ⟨0, 0, 0, Or.inl rfl, Or.inl rfl, monoCM (Finset.subset_insert _ _) hc⟩

theorem smallM {f k : ℕ} {S : Finset ℕ} (hc : CanM f k S) :
    ∃ T ⊆ S, T.card ≤ k+1 ∧ CanM f k T := by
  induction k generalizing S with
  | zero =>
    rcases hc with h | h | h
    · exact ⟨∅, by simp, by simp, Or.inl h⟩
    · exact ⟨∅, by simp, by simp, Or.inr (Or.inl h)⟩
    · exact ⟨{f}, by simpa, by simp, Or.inr (Or.inr (by simp))⟩
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    let v := combM o a b
    obtain ⟨T, hT, hn, hc'⟩ := ih hh
    change T ⊆ insert v S at hT
    by_cases hv : v ∈ T
    · let U := T.erase v ∪ ({a, b} ∩ S)
      have hu : T.erase v ⊆ S := by
        intro x hx
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
      have hU : U ⊆ S := Finset.union_subset hu Finset.inter_subset_right
      have liftWire : ∀ w ∈ ({a, b} : Finset ℕ), freeM S w → freeM U w := by
        intro w hw he
        exact he.imp_right (Or.imp_right (fun h => Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw, h⟩)))
      have hcard := Finset.card_union_le (T.erase v) ({a, b} ∩ S)
      have hpair := Finset.card_le_card (Finset.inter_subset_left : ({a, b} ∩ S) ⊆ {a, b})
      have htwo : ({a, b} : Finset ℕ).card ≤ 2 := by
        calc
          _ ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ = _ := by simp
      rw [Finset.card_erase_of_mem hv] at hcard
      refine ⟨U, hU, by dsimp [U]; omega, o, a, b, liftWire a (by simp) ha, liftWire b (by simp) hb, monoCM ?_ hc'⟩
      intro x hx
      by_cases e : x = v
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e, hx⟩)))
    · refine ⟨T, ?_, by omega, stepUpM hc'⟩
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun e => hv (e ▸ hx))

theorem agreeM {f k a b : ℕ} {S : Finset ℕ} (hb16 : b < 16) (hc : CanM f k S)
    (hs : ∀ v ∈ S, v.testBit a = true → v.testBit b = true) :
    f.testBit a = true → f.testBit b = true := by
  have h65535 : ∀ i < 16, (65535 : ℕ).testBit i = true := by
    intro i hi
    exact (show ∀ j : Fin 16, (65535 : ℕ).testBit j.val = true by decide) ⟨i, hi⟩
  induction k generalizing S with
  | zero =>
    rcases hc with rfl | rfl | h
    · simp
    · intro _; exact h65535 b hb16
    · exact hs _ h
  | succ k ih =>
    have w {v} (hv : freeM S v) : v.testBit a = true → v.testBit b = true := by
      rcases hv with rfl | rfl | h
      · simp
      · intro _; exact h65535 b hb16
      · exact hs _ h
    obtain ⟨o, x, y, hx, hy, hh⟩ := hc
    have hg : (combM o x y).testBit a = true → (combM o x y).testBit b = true := by
      fin_cases o
      · intro h
        simp only [combM, Nat.testBit_land, Bool.and_eq_true] at h ⊢
        exact ⟨w hx h.1, w hy h.2⟩
      · intro h
        simp only [combM, Nat.testBit_lor, Bool.or_eq_true] at h ⊢
        exact h.imp (w hx) (w hy)
    apply ih hh
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact hg
    · exact hs _ h

def gtM : GateOp → List ℕ → ℕ
  | GateOp.and, [] => 65535
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | _, _ => 0

def tstepM (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gtM g.op (g.inputs.map fun i => T.getD i 0)]

def tabsM (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl tstepM T0

def GOkM (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem gtM_testBit (p : Fin 16) (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (l : List ℕ) (hl : l.length ≤ 2) :
    (gtM op l).testBit p.val = op.eval (l.map fun t => t.testBit p.val) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have h6 : (65535 : ℕ).testBit p.val = true :=
    (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) p
  match l, hl with
  | [], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval, h6]
  | [a], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval]
  | [a, b], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval]

theorem gtM_bit_false (p : ℕ) (hp : 16 ≤ p) (op : GateOp) (l : List ℕ)
    (hl : ∀ x ∈ l, x.testBit p = false) : (gtM op l).testBit p = false := by
  have h6 : (65535 : ℕ).testBit p = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by decide) hp))
  cases op <;> cases l with
  | nil => simp [gtM, h6]
  | cons a t =>
    cases t with
    | nil => simp [gtM, hl a (by simp)]
    | cons b t' => simp [gtM, hl a (by simp), hl b (by simp)]

theorem getD_map_testBitM (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

theorem wires_tabsM (p : Fin 16) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOkM g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p.val)
        = (tabsM T0 gs).map fun t => t.testBit p.val := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p.val) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p.val).getD i false)]
        = (tstepM T0 g).map fun t => t.testBit p.val := by
      simp only [tstepM, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gtM_testBit p g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBitM T0 p.val i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

theorem tabsM_bit_false (p : ℕ) (hp : 16 ≤ p) :
    ∀ (gs : List Gate) (T0 : List ℕ),
      (∀ t ∈ T0, t.testBit p = false) →
      ∀ t ∈ tabsM T0 gs, t.testBit p = false := by
  intro gs
  induction gs with
  | nil => intro T0 hT0; exact hT0
  | cons g gs ih =>
    intro T0 hT0
    apply ih (tstepM T0 g)
    intro t ht
    simp only [tstepM, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hT0 t ht
    · apply gtM_bit_false p hp g.op
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [List.getD_eq_getElem?_getD]
      cases h : T0[i]? with
      | none => simp
      | some v => exact hT0 v (List.mem_of_getElem? h)

theorem getWireM (T : List ℕ) (i : ℕ) : freeM T.toFinset (T.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T[i]? with
  | none => exact Or.inl rfl
  | some t => exact Or.inr (Or.inr (List.mem_toFinset.mpr (List.mem_of_getElem? h)))

theorem gateChoiceM (T : List ℕ) (g : Gate) (hg : GOkM g) :
    ∃ (o : Fin 2) (a b : ℕ), freeM T.toFinset a ∧ freeM T.toFinset b ∧
      gtM g.op (g.inputs.map fun i => T.getD i 0) = combM o a b := by
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  generalize g.inputs = ins at hl ⊢
  have z : freeM T.toFinset 0 := Or.inl rfl
  have u : freeM T.toFinset 65535 := Or.inr (Or.inl rfl)
  match ins, hl with
  | [], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨1, 65535, 0, u, z, by simp [gtM, combM]⟩
    · exact ⟨1, 0, 0, z, z, rfl⟩
  | [i], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨1, _, 0, getWireM T i, z, by simp [gtM, combM]⟩
    · exact ⟨1, _, 0, getWireM T i, z, by simp [gtM, combM]⟩
  | [i, j], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨0, _, _, getWireM T i, getWireM T j, rfl⟩
    · exact ⟨1, _, _, getWireM T i, getWireM T j, rfl⟩

theorem fromTabsM (f : ℕ) (gs : List Gate) (T : List ℕ) (ok : ∀ g ∈ gs, GOkM g)
    (h : freeM (tabsM T gs).toFinset f) : CanM f gs.length T.toFinset := by
  induction gs generalizing T with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨o, a, b, ha, hb, e⟩ := gateChoiceM T g (ok g (by simp))
    have hh := ih (tstepM T g) (fun g' hg' => ok _ (by simp [hg'])) h
    refine ⟨o, a, b, ha, hb, ?_⟩
    rw [← e]
    simpa [tstepM] using hh

def cuts : ℕ → List ℕ → List (List ℕ)
  | _, [] => [[]]
  | k, x :: xs => if (x :: xs).length ≤ k then [x :: xs] else
      match k with
      | 0 => [[]]
      | j+1 => (cuts j xs).map (x :: ·) ++ cuts (j+1) xs
termination_by _ l => l.length

theorem cutsSpec (k : ℕ) (l : List ℕ) (T : Finset ℕ) (h : T ⊆ l.toFinset) (n : T.card ≤ k) :
    ∃ U ∈ cuts k l, T ⊆ U.toFinset := by
  induction l generalizing k T with
  | nil => exact ⟨[], by simp [cuts], h⟩
  | cons x xs ih =>
    cases k with
    | zero =>
      have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[], by simp [cuts], by simp [he]⟩
    | succ j =>
      rw [cuts]
      split
      · exact ⟨_, by simp, h⟩
      ·
        by_cases hx : x ∈ T
        · have hs : T.erase x ⊆ xs.toFinset := by
            intro y hy
            have hh := h (Finset.mem_of_mem_erase hy)
            simpa [Finset.ne_of_mem_erase hy] using hh
          obtain ⟨U, hU, sub⟩ := ih j (T.erase x) hs (by rw [Finset.card_erase_of_mem hx]; omega)
          refine ⟨x::U, List.mem_append_left _ (List.mem_map.mpr ⟨U, hU, rfl⟩), ?_⟩
          intro y hy
          by_cases e : y = x
          · simp [e]
          · simpa [e] using sub (Finset.mem_erase.mpr ⟨e, hy⟩)
        · have hs : T ⊆ xs.toFinset := by
            intro y hy
            have e : y ≠ x := fun he => hx (he ▸ hy)
            simpa [e] using h hy
          obtain ⟨U, hU, sub⟩ := ih (j+1) T hs n
          exact ⟨U, List.mem_append_right _ hU, sub⟩

theorem cuts_mem_sub : ∀ (l : List ℕ) (k : ℕ) (U : List ℕ), U ∈ cuts k l → ∀ y ∈ U, y ∈ l
  | [], k, U, hU, y, hy => by simp [cuts] at hU; subst hU; simp at hy
  | z :: zs, k, U, hU, y, hy => by
    unfold cuts at hU
    split at hU
    · simp at hU; subst hU; exact hy
    · cases k with
      | zero => simp at hU; subst hU; simp at hy
      | succ j =>
        simp only [List.mem_append, List.mem_map] at hU
        rcases hU with ⟨V, hV, rfl⟩ | hU
        · rcases List.mem_cons.mp hy with rfl | hy
          · simp
          · exact List.mem_cons_of_mem _ (cuts_mem_sub zs j V hV y hy)
        · exact List.mem_cons_of_mem _ (cuts_mem_sub zs (j + 1) U hU y hy)

def sepFold (p0Mask a : ℕ) (U : List ℕ) : ℕ :=
  U.foldl (fun acc v => if v.testBit a then acc &&& v else acc) p0Mask

theorem sepFold_bit_true (a b : ℕ) : ∀ (U : List ℕ) (acc : ℕ),
    (U.foldl (fun acc v => if v.testBit a then acc &&& v else acc) acc).testBit b = true →
    acc.testBit b = true ∧ ∀ v ∈ U, v.testBit a = true → v.testBit b = true
  | [], acc, h => ⟨h, by simp⟩
  | v :: vs, acc, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨hstep, hvs⟩ := sepFold_bit_true a b vs _ h
    by_cases hva : v.testBit a = true
    · simp only [hva, ↓reduceIte, Nat.testBit_land, Bool.and_eq_true] at hstep
      refine ⟨hstep.1, fun w hw hwa => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hstep.2
      · exact hvs w hw hwa
    · simp only [hva, ↓reduceIte] at hstep
      refine ⟨hstep, fun w hw hwa => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact absurd hwa hva
      · exact hvs w hw hwa

def sepOk (p1List : List ℕ) (p0Mask : ℕ) (U : List ℕ) : Bool :=
  p1List.all fun a => sepFold p0Mask a U == 0

theorem coveredM {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {U : List ℕ}
    (hc : CanM f k U.toFinset)
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false) :
    sepOk p1List p0Mask U = true := by
  rw [sepOk, List.all_eq_true]
  intro a ha
  rw [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.zero_testBit]
  cases htb : (sepFold p0Mask a U).testBit b with
  | false => rfl
  | true =>
    obtain ⟨hb0, hall⟩ := sepFold_bit_true a b U p0Mask htb
    have hfa := hp1 a ha
    have ⟨hb16, hfb⟩ := hp0 b hb0
    have hfb' := agreeM hb16 hc (fun v hv => hall v (List.mem_toFinset.mp hv)) hfa
    exact absurd (hfb'.symm.trans hfb) (by decide)

def insOne (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insOne x ys

def sortU : List ℕ → List ℕ
  | [] => []
  | x :: xs => insOne x (sortU xs)

theorem mem_insOne (x z : ℕ) : ∀ l : List ℕ, z ∈ insOne x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insOne]
  | y :: ys => by
    unfold insOne
    by_cases h1 : x == y
    · simp only [h1, ↓reduceIte]
      have hxy := beq_iff_eq.mp h1; subst hxy; simp
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : x < y
      · simp only [h2, ↓reduceIte]; simp
      · simp only [h2, ↓reduceIte]; simp [mem_insOne x z ys]; tauto

theorem mem_sortU (z : ℕ) : ∀ l : List ℕ, z ∈ sortU l ↔ z ∈ l
  | [] => by simp [sortU]
  | x :: xs => by simp [sortU, mem_insOne, mem_sortU z xs]

def pack : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 65536 * pack xs

def unpack (n : ℕ) : List ℕ :=
  if n = 0 then []
  else (n &&& 65535) :: unpack (n >>> 16)
termination_by n
decreasing_by
  have h1 : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
  omega

theorem unpack_lt : ∀ (n x : ℕ), x ∈ unpack n → x < 65536 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro x hx
    unfold unpack at hx
    by_cases h0 : n = 0
    · simp [h0] at hx
    · simp only [h0, ↓reduceIte, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      · have hlt : n >>> 16 < n := by
          have h1 : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
          omega
        exact ih (n >>> 16) hlt x hx

theorem unpack_pack : ∀ l : List ℕ, (∀ x ∈ l, 0 < x ∧ x < 65536) → unpack (pack l) = l
  | [], _ => by unfold unpack; simp [pack]
  | x :: xs, hl => by
    have hx := hl x (by simp)
    have hne : x + 65536 * pack xs ≠ 0 := by omega
    rw [pack, unpack]
    simp only [hne, ↓reduceIte]
    have hlo : (x + 65536 * pack xs) &&& 65535 = x := by
      rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have hhi : (x + 65536 * pack xs) >>> 16 = pack xs := by
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [hlo, hhi, unpack_pack xs (fun y hy => hl y (by simp [hy]))]

def normList (U : List ℕ) : List ℕ :=
  sortU (U.filter (fun x => decide (0 < x) && decide (x < 65535)))

def packSet (U : List ℕ) : ℕ := pack (normList U)

theorem normList_bounds (U : List ℕ) : ∀ x ∈ normList U, 0 < x ∧ x < 65536 := by
  intro x hx
  rw [normList, mem_sortU, List.mem_filter] at hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  omega

theorem unpack_packSet (U : List ℕ) : unpack (packSet U) = normList U :=
  unpack_pack (normList U) (normList_bounds U)

theorem freeM_packSet {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) :
    ∀ x ∈ U.toFinset, freeM (unpack (packSet U)).toFinset x := by
  intro x hx
  have hxm := List.mem_toFinset.mp hx
  have hlt := hU x hxm
  by_cases h0 : x = 0
  · exact Or.inl h0
  · by_cases h1 : x = 65535
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_)
      rw [unpack_packSet, List.mem_toFinset, normList, mem_sortU, List.mem_filter]
      exact ⟨hxm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩

def opPairsM : List ℕ → List ℕ
  | [] => []
  | a :: t => t.flatMap (fun b => [a &&& b, a ||| b]) ++ opPairsM t

theorem mem_opPairsM : ∀ (w : List ℕ) (a b : ℕ), a ∈ w → b ∈ w →
    a &&& b ∈ w ++ opPairsM w ∧ a ||| b ∈ w ++ opPairsM w
  | [], _, _, ha, _ => by simp at ha
  | x :: t, a, b, ha, hb => by
    simp only [List.mem_cons] at ha hb
    simp only [opPairsM, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false]
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact ⟨Or.inl (Or.inl (Nat.and_self _)), Or.inl (Or.inl (Nat.or_self _))⟩
    · exact ⟨Or.inr (Or.inl ⟨b, hb, Or.inl rfl⟩), Or.inr (Or.inl ⟨b, hb, Or.inr rfl⟩)⟩
    · exact ⟨Or.inr (Or.inl ⟨a, ha, Or.inl (Nat.land_comm _ _)⟩),
             Or.inr (Or.inl ⟨a, ha, Or.inr (Nat.lor_comm _ _)⟩)⟩
    · have ih := mem_opPairsM t a b ha hb
      simp only [List.mem_append] at ih
      refine ⟨?_, ?_⟩
      · rcases ih.1 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
      · rcases ih.2 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

def valsNew (S : List ℕ) : List ℕ :=
  ((opPairsM S).filter (fun v => decide (0 < v) && decide (v < 65535) && !S.contains v)).eraseDups

theorem and_65535_of_lt {x : ℕ} (hx : x < 65536) : x &&& 65535 = x := by
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hx

theorem or_65535_of_lt {x : ℕ} (hx : x < 65536) : x ||| 65535 = 65535 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor]
  by_cases hi : i < 16
  · have h6 : (65535 : ℕ).testBit i = true :=
      (show ∀ j : Fin 16, (65535 : ℕ).testBit j.val = true by decide) ⟨i, hi⟩
    simp [h6]
  · have h2 : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have hx0 : x.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx h2)
    have h60 : (65535 : ℕ).testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) h2)
    simp [hx0, h60]

theorem combM_lt {o : Fin 2} {a b : ℕ} (ha : a < 65536) (hb : b < 65536) : combM o a b < 65536 := by
  fin_cases o
  · exact Nat.and_lt_two_pow (n := 16) a hb
  · exact Nat.or_lt_two_pow (n := 16) ha hb

theorem combM_case {S : List ℕ} (hS : ∀ x ∈ S, x < 65536) {o : Fin 2} {a b : ℕ}
    (ha : freeM S.toFinset a) (hb : freeM S.toFinset b) :
    freeM S.toFinset (combM o a b) ∨ combM o a b ∈ valsNew S := by
  have free_lt {w : ℕ} (hw : freeM S.toFinset w) : w < 65536 := by
    rcases hw with rfl | rfl | h
    · decide
    · decide
    · exact hS w (List.mem_toFinset.mp h)
  have hlt : combM o a b < 65536 := combM_lt (free_lt ha) (free_lt hb)
  rcases ha with rfl | rfl | ha'
  · left; fin_cases o
    · simp only [combM, Nat.zero_and]; exact Or.inl rfl
    · simp only [combM, Nat.zero_or]; exact hb
  · left; fin_cases o
    · simp only [combM, Nat.land_comm 65535, and_65535_of_lt (free_lt hb)]; exact hb
    · simp only [combM, Nat.lor_comm 65535, or_65535_of_lt (free_lt hb)]; exact Or.inr (Or.inl rfl)
  · rcases hb with rfl | rfl | hb'
    · left; fin_cases o
      · simp only [combM, Nat.and_zero]; exact Or.inl rfl
      · simp only [combM, Nat.or_zero]; exact Or.inr (Or.inr ha')
    · left; fin_cases o
      · simp only [combM, and_65535_of_lt (hS _ (List.mem_toFinset.mp ha'))]; exact Or.inr (Or.inr ha')
      · simp only [combM, or_65535_of_lt (hS _ (List.mem_toFinset.mp ha'))]; exact Or.inr (Or.inl rfl)
    · have haL := List.mem_toFinset.mp ha'
      have hbL := List.mem_toFinset.mp hb'
      have hpair := mem_opPairsM S a b haL hbL
      have hmem : combM o a b ∈ S ∨ combM o a b ∈ opPairsM S := by
        fin_cases o
        · exact List.mem_append.mp hpair.1
        · exact List.mem_append.mp hpair.2
      by_cases h0 : combM o a b = 0
      · exact Or.inl (Or.inl h0)
      · by_cases h1 : combM o a b = 65535
        · exact Or.inl (Or.inr (Or.inl h1))
        · by_cases hin : combM o a b ∈ S
          · exact Or.inl (Or.inr (Or.inr (List.mem_toFinset.mpr hin)))
          · right
            rcases hmem with h | hop
            · exact absurd h hin
            · simp only [valsNew, List.mem_eraseDups, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
              refine ⟨hop, ⟨by omega, by omega⟩, ?_⟩
              cases hc : S.contains (combM o a b) with
              | false => rfl
              | true => exact absurd (List.contains_iff_mem.mp hc) hin

theorem can1M_case {f : ℕ} {S : List ℕ} (hS : ∀ x ∈ S, x < 65536) (hc : CanM f 1 S.toFinset) :
    freeM S.toFinset f ∨ f ∈ valsNew S := by
  obtain ⟨o, a, b, ha, hb, h0⟩ := hc
  rcases h0 with rfl | rfl | hm
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · rcases Finset.mem_insert.mp hm with rfl | hf
    · exact combM_case hS ha hb
    · exact Or.inl (Or.inr (Or.inr hf))

def permWGo : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | idx :: rest, k, w => (((w >>> idx) &&& 1) <<< k) ||| permWGo rest (k + 1) w

def permW (p : List ℕ) (w : ℕ) : ℕ := permWGo p 0 w

theorem permWGo_testBit : ∀ (p : List ℕ) (k w i : ℕ),
    (permWGo p k w).testBit i =
      if k ≤ i ∧ i - k < p.length then w.testBit (p.getD (i - k) 0) else false
  | [], k, w, i => by simp [permWGo]
  | idx :: rest, k, w, i => by
    simp only [permWGo, Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_land, Nat.testBit_shiftRight,
      permWGo_testBit rest (k + 1) w i]
    by_cases hlt : i < k
    · have h1 : ¬ k ≤ i := by omega
      have h2 : ¬ k + 1 ≤ i := by omega
      simp [h1, h2]
    · by_cases heq : i = k
      · subst heq
        have h2 : ¬ i + 1 ≤ i := by omega
        simp [h2]
      · have hgt : k + 1 ≤ i := by omega
        have hge : k ≤ i := by omega
        have h1f : (1 : ℕ).testBit (i - k) = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega)))
        have hlen : i - k < (idx :: rest).length ↔ i - (k + 1) < rest.length := by simp; omega
        have hget : (idx :: rest).getD (i - k) 0 = rest.getD (i - (k + 1)) 0 := by
          cases hd : i - k with
          | zero => omega
          | succ m =>
            have hm : i - (k + 1) = m := by omega
            simp [hm]
        simp only [hge, hgt, h1f, Bool.and_false, Bool.false_or, decide_true, Bool.true_and, true_and, ↓reduceIte, hlen, hget]

theorem permW_testBit (p : List ℕ) (hp : p.length = 16) (w i : ℕ) :
    (permW p w).testBit i = if i < 16 then w.testBit (p.getD i 0) else false := by
  simp [permW, permWGo_testBit, hp]

theorem permW_zero (p : List ℕ) (hp : p.length = 16) : permW p 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; simp [permW_testBit p hp]

theorem permW_all (p : List ℕ) (hp : p.length = 16) (hb : ∀ x ∈ p, x < 16) : permW p 65535 = 65535 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [permW_testBit p hp]
  by_cases hi : i < 16
  · simp only [hi, ↓reduceIte]
    have hgi : p.getD i 0 < 16 := by
      rw [List.getD_eq_getElem?_getD]
      cases hg : p[i]? with
      | none => decide
      | some v => exact hb v (List.mem_of_getElem? hg)
    have h6 : ∀ j < 16, (65535 : ℕ).testBit j = true := fun j hj =>
      (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) ⟨j, hj⟩
    rw [h6 _ hgi, h6 _ hi]
  · simp only [hi, ↓reduceIte]
    symm
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by decide) (by omega)))

theorem permWGo_lt : ∀ (p : List ℕ) (k w : ℕ), permWGo p k w < 2 ^ (k + p.length)
  | [], k, _ => by simp [permWGo]
  | idx :: rest, k, w => by
    have h1 : (((w >>> idx) &&& 1) <<< k) < 2 ^ (k + 1) := by
      rw [Nat.shiftLeft_eq]
      have hb : (w >>> idx) &&& 1 < 2 := by
        rw [show (1 : ℕ) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      have hmul : ((w >>> idx) &&& 1) * 2 ^ k < 2 * 2 ^ k := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      have hpow : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      omega
    have h1' : (((w >>> idx) &&& 1) <<< k) < 2 ^ (k + (idx :: rest).length) :=
      lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by simp))
    have h2 : permWGo rest (k + 1) w < 2 ^ (k + (idx :: rest).length) := by
      have := permWGo_lt rest (k + 1) w
      have heq : k + 1 + rest.length = k + (idx :: rest).length := by simp; omega
      rwa [heq] at this
    exact Nat.or_lt_two_pow h1' h2

theorem permW_lt (p : List ℕ) (hp : p.length = 16) (w : ℕ) : permW p w < 65536 := by
  have h := permWGo_lt p 0 w
  simp [hp] at h
  exact h

theorem permW_comb (p : List ℕ) (hp : p.length = 16) (o : Fin 2) (a b : ℕ) :
    permW p (combM o a b) = combM o (permW p a) (permW p b) := by
  apply Nat.eq_of_testBit_eq; intro i
  fin_cases o <;> simp only [combM, Nat.testBit_land, Nat.testBit_lor, permW_testBit p hp] <;> split <;> simp

theorem canM_perm (p : List ℕ) (hp : p.length = 16) (hb : ∀ x ∈ p, x < 16) {f k : ℕ} {S : Finset ℕ}
    (hc : CanM f k S) : CanM (permW p f) k (S.image (permW p)) := by
  have hfree {T : Finset ℕ} {v : ℕ} (hv : freeM T v) : freeM (T.image (permW p)) (permW p v) := by
    rcases hv with rfl | rfl | h
    · exact Or.inl (permW_zero p hp)
    · exact Or.inr (Or.inl (permW_all p hp hb))
    · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ h))
  induction k generalizing S with
  | zero => exact hfree hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb', hh⟩ := hc
    refine ⟨o, permW p a, permW p b, hfree ha, hfree hb', ?_⟩
    have h' := ih hh
    rw [Finset.image_insert, permW_comb p hp] at h'
    exact h'

def treeHit (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (U : List ℕ) : Bool :=
  treeMem (packSet U) nextTree || auts.any (fun p => treeMem (packSet (U.map (permW p))) nextTree)

theorem treeHit_sound {auts : List (List ℕ)} {f k : ℕ} {nextTree : BinaryTree ℕ} {U : List ℕ}
    (hU : ∀ x ∈ U, x < 65536)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hh : treeHit auts nextTree U = true)
    (hc : CanM f k U.toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  simp only [treeHit, Bool.or_eq_true, List.any_eq_true] at hh
  rcases hh with h0 | ⟨p, hp, hm⟩
  · exact ⟨packSet U, treeMem_imp nextTree h0, monoCM_free (freeM_packSet hU) hc⟩
  · obtain ⟨hlen, hbd, hfix⟩ := haut p hp
    have hcp : CanM f k (U.map (permW p)).toFinset := by
      have h1 := canM_perm p hlen hbd hc
      have heq : (U.map (permW p)).toFinset = U.toFinset.image (permW p) := by
        ext y; simp
      rw [hfix, ← heq] at h1
      exact h1
    have hUp : ∀ y ∈ U.map (permW p), y < 65536 := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      exact permW_lt p hlen x
    exact ⟨packSet (U.map (permW p)), treeMem_imp nextTree hm, monoCM_free (freeM_packSet hUp) hcp⟩

def checkCuts (p1List : List ℕ) (p0Mask k : ℕ) (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (l : List ℕ) : Bool :=
  (cuts (k + 1) l).all fun U => !sepOk p1List p0Mask U || treeHit auts nextTree U

def verifyNode (p1List : List ℕ) (p0Mask k : ℕ) (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (packedS : ℕ) : Bool :=
  let S := unpack packedS
  checkCuts p1List p0Mask k auts nextTree S &&
  (valsNew S).all fun v => checkCuts p1List p0Mask k auts nextTree (v :: S)

theorem checkCuts_sound {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {auts : List (List ℕ)} {nextTree : BinaryTree ℕ} {l : List ℕ}
    (hl : ∀ x ∈ l, x < 65536)
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hchk : checkCuts p1List p0Mask k auts nextTree l = true)
    (hc : CanM f k l.toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  obtain ⟨T, hT, hn, ht⟩ := smallM hc
  obtain ⟨U, hU, hu⟩ := cutsSpec (k + 1) l T hT hn
  have hcU := monoCM hu ht
  have htest := List.all_eq_true.mp hchk U hU
  have hcov := coveredM hcU hp1 hp0
  simp only [hcov, Bool.not_true, Bool.false_or] at htest
  have hU_lt : ∀ x ∈ U, x < 65536 := fun x hx => hl x (cuts_mem_sub l (k + 1) U hU x hx)
  exact treeHit_sound hU_lt haut htest hcU

theorem advanceNode {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {auts : List (List ℕ)} {nextTree : BinaryTree ℕ} {packedS : ℕ}
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hv : verifyNode p1List p0Mask k auts nextTree packedS = true)
    (hc : CanM f (k + 1) (unpack packedS).toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  simp only [verifyNode, Bool.and_eq_true] at hv
  obtain ⟨o, a, b, ha, hb, hh⟩ := hc
  have hS_lt : ∀ x ∈ unpack packedS, x < 65536 := unpack_lt packedS
  rcases combM_case hS_lt ha hb with hfree | hnew
  · have hh' : CanM f k (unpack packedS).toFinset := by
      refine monoCM_free (fun x hx => ?_) hh
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hfree
      · exact Or.inr (Or.inr hx)
    exact checkCuts_sound hS_lt hp1 hp0 haut hv.1 hh'
  · have hv_lt : combM o a b < 65536 := by
      simp only [valsNew, List.mem_eraseDups, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hnew
      omega
    have hvl : ∀ x ∈ combM o a b :: unpack packedS, x < 65536 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv_lt
      · exact hS_lt x hx
    have hchk := List.all_eq_true.mp hv.2 (combM o a b) hnew
    exact checkCuts_sound hvl hp1 hp0 haut hchk (by simpa using hh)

abbrev targetNat : ℕ := 862
abbrev p0Mask : ℕ := 64673
def p1List : List ℕ := [1, 2, 3, 4, 6, 8, 9]
def inputs : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
def auts : List (List ℕ) := [[0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]]

def row1 : BinaryTree ℕ := BE
def row2 : BinaryTree ℕ := BL 87154063184159
def row3 : BinaryTree ℕ := BN 5711728684836126735 (BN 4921346915873787648 (BN 4919095150419840768 (BL 4919095116060102408) (BE)) (BL 5711728650477305864)) (BN 12297728886551220511 (BN 9869725737445101855 (BL 9838200540053508383) (BE)) (BL 12320246884688072991))
def row4_c0 : BinaryTree ℕ := BN 374323848837620588019720 (BN 322377817526114870886408 (BN 322377761231119528755440 (BL 322377758979319715070200) (BL 322377817526054741868559)) (BN 322525391478644417757199 (BL 322377819777854555029519) (BE))) (BN 644756310592946725388528 (BN 644756310592946724470799 (BL 644755517959412308184832) (BL 644756310592946725388303)) (BN 644756310592947010801951 (BL 644756310592946725392657) (BE)))
def row4_c1 : BinaryTree ℕ := BN 805943960308127434211568 (BN 646822345965838551617823 (BN 646822345928308841971952 (BL 646821553295667777965824) (BL 646822345929202194251791)) (BN 805943167675486370205440 (BL 677817033958026568143135) (BE))) (BN 807419699834917550620687 (BN 807418907200489781137152 (BL 805943960309020786491407) (BL 807418907201383134334720)) (BN 1173661356674346988404751 (BL 1133377794089254904795423) (BE)))
def row4 : BinaryTree ℕ := BN 646821553294774424768256 row4_c0 row4_c1
def row5_c0 : BinaryTree ℕ := BN 42254697624988045029201150192 (BN 21127352649387523528738144264 (BN 21127348812468696846840102920 (BL 21127348812464756197166678031) (BL 21127348960038708786842566671)) (BN 42254697624988044969071607823 (BL 42254697624929498234045333744) (BL 42254697624988045029201149967))) (BN 42254749571019375299915743247 (BN 42254697624988063733819313920 (BL 42254697624988045029235822336) (BL 42254749571019356534933028879)) (BN 42390097316726336701612425231 (BL 42390097316726336641482883087) (BL 42390097316726336701612425456)))
def row5_c1 : BinaryTree ℕ := BN 52818343382753439468359778319 (BN 42390419694485315900852342528 (BN 42390149262757648207344304143 (BL 42390097316784883436638699535) (BL 42390149265217195318824730639)) (BN 52818291436722127962627899632 (BL 44421417137473229169827577871) (BL 52818291436780674697654173711))) (BN 74277047113433409440671924239 (BN 52915005502349845031630667791 (BL 52915005502291298236474851343) (BL 74277047112640775906255638272)) (BN 74937122676185680033014087695 (BL 74277049178676111268372221696) (BL 76917018724978692666247086095)))
def row5 : BinaryTree ℕ := BN 42390097316726336701647097600 row5_c0 row5_c1
def row6 : BinaryTree ℕ := BN 2778098545097789662878198990372879 (BN 2769203863547379596268667265876208 (BN 2769203863547379592325745318297615 (BL 1384601931773690262137481051701256) (BL 2769203863547379596266394992246799)) (BN 2769203863551217744859522427518991 (BL 2769203863551216515093076905033743) (BL 2778077417748977198136222240735247))) (BN 4867820694973717628083981791526927 (BN 4867820559574025831245574353977584 (BL 3461499547597021374218132356333583) (BL 4867820559574025889792309380251663)) (BN 4911079136306812929805143698833423 (BL 4889449847940419995406279449247759) (BL 5040833739156366679807837462331407)))
def row7 : BinaryTree ℕ := BL 319017488192243356876506020212600995855

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit : checkCuts p1List p0Mask 7 auts row7 inputs = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk2 : checkTree (verifyNode p1List p0Mask 1 auts row1) row2 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk3 : checkTree (verifyNode p1List p0Mask 2 auts row2) row3 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4L : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_c0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4R : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_c1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk4V : (verifyNode p1List p0Mask 3 auts row3) 646821553294774424768256 = true := by decide +kernel
theorem chk4 : checkTree (verifyNode p1List p0Mask 3 auts row3) row4 = true := checkTree_node chk4V chk4L chk4R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5L : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5R : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5V : (verifyNode p1List p0Mask 4 auts row4) 42390097316726336701647097600 = true := by decide +kernel
theorem chk5 : checkTree (verifyNode p1List p0Mask 4 auts row4) row5 = true := checkTree_node chk5V chk5L chk5R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6 : checkTree (verifyNode p1List p0Mask 5 auts row5) row6 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk7 : checkTree (verifyNode p1List p0Mask 6 auts row6) row7 = true := by decide +kernel

theorem hp1_proof : ∀ a ∈ p1List, targetNat.testBit a = true := by decide +kernel
theorem hp0_fin : ∀ b : Fin 16, p0Mask.testBit b.val = true → targetNat.testBit b.val = false := by decide +kernel
theorem hp0_proof : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ targetNat.testBit b = false := by
  intro b hb
  by_cases h16 : b < 16
  · exact ⟨h16, hp0_fin ⟨b, h16⟩ hb⟩
  · have hf : p0Mask.testBit b = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : p0Mask < 2 ^ 16) (Nat.pow_le_pow_right (by decide) (by omega)))
    exact absurd hb (by simp [hf])
theorem haut_proof : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p targetNat = targetNat := by decide +kernel
theorem inputs_lt : ∀ t ∈ inputs, t < 65536 := by decide
theorem targetNat_lt : targetNat < 2 ^ 16 := by decide

theorem excluded (hc : CanM targetNat 7 inputs.toFinset) : False := by
  obtain ⟨x7, hx7, c7⟩ := checkCuts_sound inputs_lt hp1_proof hp0_proof haut_proof chkInit hc
  obtain ⟨x6, hx6, c6⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row7 chk7 x7 hx7) c7
  obtain ⟨x5, hx5, c5⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row6 chk6 x6 hx6) c6
  obtain ⟨x4, hx4, c4⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row5 chk5 x5 hx5) c5
  obtain ⟨x3, hx3, c3⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row4 chk4 x4 hx4) c4
  obtain ⟨x2, hx2, c2⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row3 chk3 x3 hx3) c3
  obtain ⟨x1, hx1, c1⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row2 chk2 x2 hx2) c2
  exact hx1

theorem oneEach_map (p : Fin 16) :
    oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4) =
    inputs.map (fun t => t.testBit p.val) := by
  revert p; decide

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (862 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  rintro ⟨C, hC, hs, hrep⟩
  have hok : ∀ g ∈ C.gates, GOkM g := hC
  let out := (tabsM inputs C.gates).getD C.output 0
  have obs (p : Fin 16) : out.testBit p.val = targetNat.testBit p.val := by
    have hval := hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
    unfold Circuit.eval Circuit.wires at hval
    rw [oneEach_map p, wires_tabsM p C.gates inputs hok, getD_map_testBitM] at hval
    dsimp only at hval
    have he : 4 * (p.val / 4) + p.val % 4 = p.val := Nat.div_add_mod p.val 4
    rw [he] at hval
    exact hval
  have hout_eq : out = targetNat := by
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p < 16
    · exact obs ⟨p, hp⟩
    · have h2 : 2 ^ 16 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
      have hT : targetNat.testBit p = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le targetNat_lt h2)
      have hI : ∀ v ∈ inputs, v.testBit p = false := fun v hv => Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (inputs_lt v hv) h2)
      have hall := tabsM_bit_false p (by omega) C.gates inputs hI
      have hout_f : out.testBit p = false := by
        dsimp [out]
        rw [List.getD_eq_getElem?_getD]
        cases hget : (tabsM inputs C.gates)[C.output]? with
        | none => simp
        | some v => exact hall v (List.mem_of_getElem? hget)
      rw [hout_f, hT]
  have hc := fromTabsM out C.gates inputs hok (getWireM _ C.output)
  rw [hout_eq] at hc
  have pad {k j : ℕ} (hj : k ≤ j) (ha : CanM targetNat k inputs.toFinset) : CanM targetNat j inputs.toFinset := by
    induction hj with
    | refl => exact ha
    | step _ ih => exact stepUpM ih
  change C.gates.length ≤ _ at hs
  exact excluded (pad hs hc)

end PEqualNP.Outside.L_meta_6179_aux

theorem PEqualNP.Outside.L_meta_6179 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (862 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (862 : ℕ).testBit (4 * u.val + v.val)) 7 :=
  ⟨PEqualNP.Outside.L_meta_6179_aux.upper, PEqualNP.Outside.L_meta_6179_aux.lower⟩
