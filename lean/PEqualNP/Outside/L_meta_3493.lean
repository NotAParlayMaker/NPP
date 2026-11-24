import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_3493

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldLen (gs : List Gate) (base : List Bool) :
    (gs.foldl step base).length = base.length + gs.length := by
  induction gs generalizing base with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

def bit (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD w false

theorem bit_prefix (n : ℕ) (gs more : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs.length) : bit n (gs ++ more) x w = bit n gs x w := by
  induction more generalizing gs with
  | nil => simp
  | cons g more ih =>
      have hlen : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
        simpa [List.length_ofFn] using foldLen gs (List.ofFn x)
      rw [show gs ++ g :: more = (gs ++ [g]) ++ more by simp]
      have hw' : w < n + (gs ++ [g]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [ih (gs ++ [g]) hw']
      unfold bit
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step]
      exact List.getD_append _ _ _ _ (by rw [hlen]; exact hw)

theorem bit_input (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    bit n gs x w = x ⟨w, hw⟩ := by
  have h := bit_prefix n [] gs x w (by simpa using hw)
  simp only [List.nil_append] at h
  rw [h]
  unfold bit
  simp [List.length_ofFn, hw, List.getElem_ofFn]

theorem bit_or_new (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (a b : ℕ)
    (_ha : a < n + gs.length) (_hb : b < n + gs.length) :
    bit n (gs ++ [⟨GateOp.or, [a, b]⟩]) x (n + gs.length) =
      (bit n gs x a || bit n gs x b) := by
  unfold bit
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step]
  have hlen : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    simpa [List.length_ofFn] using foldLen gs (List.ofFn x)
  rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
  have hsub : n + gs.length - (gs.foldl step (List.ofFn x)).length = 0 := by
    rw [hlen]; exact Nat.sub_self _
  simp only [hsub, List.getD_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, Bool.or_false, id_eq]

theorem bit_and_new (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (a b : ℕ)
    (_ha : a < n + gs.length) (_hb : b < n + gs.length) :
    bit n (gs ++ [⟨GateOp.and, [a, b]⟩]) x (n + gs.length) =
      (bit n gs x a && bit n gs x b) := by
  unfold bit
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step]
  have hlen : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    simpa [List.length_ofFn] using foldLen gs (List.ofFn x)
  rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
  have hsub : n + gs.length - (gs.foldl step (List.ofFn x)).length = 0 := by
    rw [hlen]; exact Nat.sub_self _
  simp only [hsub, List.getD_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, Bool.and_true, id_eq]

def orAcc (n : ℕ) : List ℕ → List Gate → ℕ → List Gate × ℕ × List ℕ
  | [], gs, root => (gs, root, [])
  | w :: rest, gs, root =>
      let r := orAcc n rest (gs ++ [⟨GateOp.or, [root, w]⟩]) (n + gs.length)
      (r.1, r.2.1, (n + gs.length) :: r.2.2)

theorem orAcc_nil (n : ℕ) (gs : List Gate) (root : ℕ) : orAcc n [] gs root = (gs, root, []) := rfl

theorem orAcc_cons (n : ℕ) (w : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ) :
    orAcc n (w :: rest) gs root =
      let r := orAcc n rest (gs ++ [⟨GateOp.or, [root, w]⟩]) (n + gs.length)
      (r.1, r.2.1, (n + gs.length) :: r.2.2) := rfl

theorem orAcc_len (n : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ) :
    (orAcc n rest gs root).1.length = gs.length + rest.length := by
  induction rest generalizing gs root with
  | nil => simp [orAcc_nil]
  | cons w rest ih =>
      rw [orAcc_cons]
      simp only [ih, List.length_append, List.length_cons, List.length_nil]
      omega

theorem orAcc_prefix (n : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ) :
    ∃ extra, (orAcc n rest gs root).1 = gs ++ extra := by
  induction rest generalizing gs root with
  | nil => exact ⟨[], by simp [orAcc_nil]⟩
  | cons w rest ih =>
      rw [orAcc_cons]
      obtain ⟨extra, hextra⟩ := ih (gs ++ [⟨GateOp.or, [root, w]⟩]) (n + gs.length)
      refine ⟨⟨GateOp.or, [root, w]⟩ :: extra, ?_⟩
      rw [hextra]
      simp [List.append_assoc]

def addedOrs (n start root : ℕ) : List ℕ → List Gate
  | [] => []
  | w :: rest => ⟨GateOp.or, [root, w]⟩ :: addedOrs n (start + 1) (n + start) rest

theorem orAcc_added (n : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ) :
    (orAcc n rest gs root).1 = gs ++ addedOrs n gs.length root rest := by
  induction rest generalizing gs root with
  | nil => simp [orAcc_nil, addedOrs]
  | cons w rest ih =>
      rw [orAcc_cons, addedOrs]
      dsimp only
      simp only [ih (gs ++ [⟨GateOp.or, [root, w]⟩]) (n + gs.length),
        List.append_assoc, List.cons_append, List.nil_append, List.length_append,
        List.length_singleton]

theorem added_at (n start root : ℕ) (rest : List ℕ) (k : ℕ)
    (hk : k < (addedOrs n start root rest).length) :
    ((addedOrs n start root rest)[k]'hk).op = GateOp.or ∧
      ∀ i ∈ ((addedOrs n start root rest)[k]'hk).inputs,
        i = root ∨ i ∈ rest ∨ ∃ j, j < k ∧ i = n + start + j := by
  induction rest generalizing start root k with
  | nil => simp [addedOrs] at hk
  | cons w rest ih =>
      simp only [addedOrs, List.length_cons] at hk
      cases k with
      | zero =>
          simp [addedOrs, List.mem_cons]
      | succ k =>
          have hk' : k < (addedOrs n (start + 1) (n + start) rest).length := by
            simp [addedOrs, List.length_cons] at hk
            omega
          obtain ⟨hop, hin⟩ := ih (start + 1) (n + start) k hk'
          refine ⟨hop, ?_⟩
          intro i hi
          rcases hin i hi with h | h | ⟨j, hj, hij⟩
          · exact Or.inr (Or.inr ⟨0, by omega, h⟩)
          · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
          · exact Or.inr (Or.inr ⟨j + 1, by omega, by
              simp only [hij, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩)

theorem get_append_skip (gs extra : List Gate) (k : ℕ) (hk : k < extra.length) :
    ((gs ++ extra)[gs.length + k]'(by simp [List.length_append]; omega)) = extra[k] := by
  have hnot : ¬ gs.length + k < gs.length := by omega
  simp [List.getElem_append, hnot, Nat.add_sub_cancel_left]

theorem orAcc_root_mem (n : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ) :
    let r := orAcc n rest gs root
    r.2.1 = root ∨ r.2.1 ∈ r.2.2 := by
  induction rest generalizing gs root with
  | nil => simp [orAcc_nil]
  | cons w rest ih =>
      rw [orAcc_cons]
      rcases ih (gs ++ [⟨GateOp.or, [root, w]⟩]) (n + gs.length) with h | h
      · simp [h]
      · simp [h]

theorem any_eq {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have htail := ih (fun b hb => h b (by simp [hb]))
      simp only [List.any_cons, h a (by simp), htail]

theorem orAcc_bit (n : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ) (x : Fin n → Bool)
    (hroot : root < n + gs.length) (hrest : ∀ w ∈ rest, w < n + gs.length) :
    bit n (orAcc n rest gs root).1 x (orAcc n rest gs root).2.1 =
      (bit n gs x root || rest.any (fun w => bit n gs x w)) := by
  induction rest generalizing gs root with
  | nil => simp [orAcc_nil, Bool.or_false]
  | cons w rest ih =>
      rw [orAcc_cons]
      have hw : w < n + gs.length := hrest w (by simp)
      let gate : Gate := ⟨GateOp.or, [root, w]⟩
      have hgrow : n + gs.length < n + (gs ++ [gate]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      have htail : ∀ u ∈ rest, u < n + (gs ++ [gate]).length := by
        intro u hu
        simp only [List.length_append, List.length_singleton]
        exact Nat.lt_of_lt_of_le (hrest u (by simp [hu])) (Nat.le_succ _)
      rw [ih (gs ++ [gate]) (n + gs.length) hgrow htail]
      rw [bit_or_new n gs x root w hroot hw]
      have hstab : ∀ u ∈ rest, bit n (gs ++ [gate]) x u = bit n gs x u := by
        intro u hu
        exact bit_prefix n gs [gate] x u (hrest u (by simp [hu]))
      have hany : rest.any (fun u => bit n (gs ++ [gate]) x u) =
          rest.any (fun u => bit n gs x u) :=
        any_eq rest _ _ hstab
      simp only [List.any_cons, hany, Bool.or_assoc]

theorem and_any {α : Type} (p : Bool) (f : α → Bool) (l : List α) :
    (p && l.any f) = l.any (fun a => p && f a) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.any_cons, Bool.and_or_distrib_left, ih]

def pointWire {N : ℕ} (p : Fin N) : ℕ := p.val

def lineWire (N : ℕ) {M : ℕ} (l : Fin M) : ℕ := N + l.val

def edgeOn {N M : ℕ} (x : Fin (N + M) → Bool) (p : Fin N) (l : Fin M) : Bool :=
  x (Fin.castAdd M p) && x (Fin.natAdd N l)

theorem point_bit {N M : ℕ} (gs : List Gate) (x : Fin (N + M) → Bool) (p : Fin N) :
    bit (N + M) gs x (pointWire p) = x (Fin.castAdd M p) := by
  have hw : pointWire p < N + M := by simp [pointWire]; omega
  rw [bit_input (N + M) gs x (pointWire p) hw]
  apply congrArg
  apply Fin.ext
  simp [pointWire, Fin.val_castAdd]

theorem line_bit {N M : ℕ} (gs : List Gate) (x : Fin (N + M) → Bool) (l : Fin M) :
    bit (N + M) gs x (lineWire N l) = x (Fin.natAdd N l) := by
  have hw : lineWire N l < N + M := by simp [lineWire]
  rw [bit_input (N + M) gs x (lineWire N l) hw]
  apply congrArg
  apply Fin.ext
  simp [lineWire, Fin.val_natAdd]

theorem any_map {α β : Type} (l : List α) (f : α → β) (p : β → Bool) :
    (l.map f).any p = l.any (fun a => p (f a)) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.any_cons, ih]

theorem orAcc_lines {N M : ℕ} (ls : List (Fin M)) (gs : List Gate) (x : Fin (N + M) → Bool)
    (hne : ls ≠ []) :
    bit (N + M) (orAcc (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne))).1 x
      (orAcc (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne))).2.1 =
      ls.any (fun l => x (Fin.natAdd N l)) := by
  have hs : ls.head hne :: ls.tail = ls := List.cons_head_tail hne
  have hhead : lineWire N (ls.head hne) < N + M + gs.length := by
    simp [lineWire]; omega
  have htail : ∀ w ∈ ls.tail.map (lineWire N), w < N + M + gs.length := by
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨l, _, rfl⟩ := hw
    simp only [lineWire]
    omega
  rw [orAcc_bit (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne)) x hhead htail]
  rw [line_bit gs x (ls.head hne), any_map, any_eq _ _ _ (fun l _ => line_bit gs x l)]
  rw [← List.any_cons (l := ls.tail) (a := ls.head hne) (f := fun l => x (Fin.natAdd N l))]
  rw [hs]

theorem orAcc_points {N M : ℕ} (ps : List (Fin N)) (gs : List Gate) (x : Fin (N + M) → Bool)
    (hne : ps ≠ []) :
    bit (N + M) (orAcc (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))).1 x
      (orAcc (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))).2.1 =
      ps.any (fun p => x (Fin.castAdd M p)) := by
  have hs : ps.head hne :: ps.tail = ps := List.cons_head_tail hne
  have hhead : pointWire (ps.head hne) < N + M + gs.length := by simp [pointWire]; omega
  have htail : ∀ w ∈ ps.tail.map pointWire, w < N + M + gs.length := by
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨p, _, rfl⟩ := hw
    simp only [pointWire]
    omega
  rw [orAcc_bit (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne)) x hhead htail]
  rw [point_bit gs x (ps.head hne), any_map, any_eq _ _ _ (fun p _ => point_bit gs x p)]
  rw [← List.any_cons (l := ps.tail) (a := ps.head hne) (f := fun p => x (Fin.castAdd M p))]
  rw [hs]

theorem orAcc_root_lt (n : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ)
    (hroot : root < n + gs.length) :
    (orAcc n rest gs root).2.1 < n + (orAcc n rest gs root).1.length := by
  induction rest generalizing gs root with
  | nil => simpa [orAcc_nil] using hroot
  | cons w rest ih =>
      rw [orAcc_cons]
      exact ih _ _ (by simp [List.length_append])

def addAnd (gs : List Gate) (left right : ℕ) : List Gate :=
  gs ++ [⟨GateOp.and, [left, right]⟩]

theorem point_star_bit {N M : ℕ} (ls : List (Fin M)) (gs : List Gate) (x : Fin (N + M) → Bool)
    (p : Fin N) (hne : ls ≠ []) :
    let folded := orAcc (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne))
    bit (N + M) (addAnd folded.1 folded.2.1 (pointWire p)) x (N + M + folded.1.length) =
      ls.any (fun l => edgeOn x p l) := by
  intro folded
  have hroot : folded.2.1 < N + M + folded.1.length := orAcc_root_lt (N + M)
      (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne)) (by simp [lineWire]; omega)
  have hp : pointWire p < N + M + folded.1.length := by simp [pointWire]; omega
  rw [show addAnd folded.1 folded.2.1 (pointWire p) =
      folded.1 ++ [⟨GateOp.and, [folded.2.1, pointWire p]⟩] from rfl]
  rw [bit_and_new (N + M) folded.1 x folded.2.1 (pointWire p) hroot hp]
  rw [orAcc_lines ls gs x hne, point_bit folded.1 x p, Bool.and_comm, and_any]
  rfl

def Good (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ j, (hj : j < gs.length) → ∀ i ∈ (gs[j]'hj).inputs, i < n + j

theorem good_nil (n : ℕ) : Good n [] := by
  refine ⟨?_, ?_⟩
  · intro g hg; simp at hg
  · intro j hj; simp at hj

theorem good_append_or (n : ℕ) (gs : List Gate) (a b : ℕ) (h : Good n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    Good n (gs ++ [⟨GateOp.or, [a, b]⟩]) := by
  let gate : Gate := ⟨GateOp.or, [a, b]⟩
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.1 g hg
    · exact ⟨Or.inr rfl, by simp⟩
  · intro j hj i hi
    simp only [List.getElem_append, List.length_singleton] at hi
    split at hi
    · exact h.2 j (by assumption) i hi
    · have hj0 : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst hj0
      simp only [Nat.sub_self, List.getElem_singleton, List.mem_cons, List.mem_singleton] at hi
      rcases hi with rfl | hi
      · exact ha
      · rcases hi with rfl | hi
        · exact hb
        · simp at hi

theorem good_append_and (n : ℕ) (gs : List Gate) (a b : ℕ) (h : Good n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    Good n (gs ++ [⟨GateOp.and, [a, b]⟩]) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.1 g hg
    · exact ⟨Or.inl rfl, by simp⟩
  · intro j hj i hi
    simp only [List.getElem_append] at hi
    split at hi
    · exact h.2 j (by assumption) i hi
    · have hj0 : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst hj0
      simp only [Nat.sub_self, List.getElem_singleton, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact ha
      · rcases hi with rfl | hi
        · exact hb
        · simp at hi

theorem good_orAcc (n : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ)
    (h : Good n gs) (hroot : root < n + gs.length) (hrest : ∀ w ∈ rest, w < n + gs.length) :
    Good n (orAcc n rest gs root).1 := by
  induction rest generalizing gs root with
  | nil => simpa [orAcc_nil] using h
  | cons w rest ih =>
      rw [orAcc_cons]
      exact ih _ _ (good_append_or n gs root w h hroot (hrest w (by simp)))
        (by simp [List.length_append])
        (by intro u hu; simp [List.length_append];
            exact Nat.lt_succ_of_lt (hrest u (by simp [hu])))

theorem ao2 {N M : ℕ} (C : Circuit) (h : Good (N + M) C.gates) : IsAO2 (N + M) C := by
  unfold IsAO2
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact (h.1 g hg).1
  · intro j hj i hi
    have hgate : gateAt C j = C.gates[j] := by
      simp [gateAt, List.getD_eq_getElem, hj]
    simpa [hgate] using h.2 j hj i (by simpa [hgate] using hi)
  · intro g hg
    exact (h.1 g hg).2

theorem line_star_bit {N M : ℕ} (ps : List (Fin N)) (gs : List Gate) (x : Fin (N + M) → Bool)
    (l : Fin M) (hne : ps ≠ []) :
    let folded := orAcc (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))
    bit (N + M) (addAnd folded.1 (lineWire N l) folded.2.1) x (N + M + folded.1.length) =
      ps.any (fun p => edgeOn x p l) := by
  intro folded
  have hroot : folded.2.1 < N + M + folded.1.length :=
    orAcc_root_lt (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))
      (by simp [pointWire]; omega)
  have hl : lineWire N l < N + M + folded.1.length := by
    have := l.isLt
    simp only [lineWire]
    omega
  rw [show addAnd folded.1 (lineWire N l) folded.2.1 =
      folded.1 ++ [⟨GateOp.and, [lineWire N l, folded.2.1]⟩] from rfl]
  rw [bit_and_new (N + M) folded.1 x (lineWire N l) folded.2.1 hl hroot]
  rw [line_bit folded.1 x l, orAcc_points ps gs x hne, and_any]
  apply any_eq
  intro p _
  simp [edgeOn, Bool.and_comm]

noncomputable def pointOwners {N M : ℕ} (cover : Finset (Fin (N + M)))
    (I : Fin N → Fin M → Prop) [DecidableRel I] : Finset (Fin N) :=
  Finset.univ.filter fun p => Fin.castAdd M p ∈ cover ∧ ∃ l, I p l

noncomputable def lineOwners {N M : ℕ} (cover : Finset (Fin (N + M)))
    (I : Fin N → Fin M → Prop) [DecidableRel I] : Finset (Fin M) :=
  Finset.univ.filter fun l => Fin.natAdd N l ∈ cover ∧ ∃ p, I p l ∧ Fin.castAdd M p ∉ cover

theorem owners_le {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] :
    (pointOwners cover I).card + (lineOwners cover I).card ≤ cover.card := by
  let eP : Fin N ↪ Fin (N + M) := ⟨Fin.castAdd M, @Fin.castAdd_injective N M⟩
  let eL : Fin M ↪ Fin (N + M) := ⟨Fin.natAdd N, @Fin.natAdd_injective M N⟩
  have hP : (pointOwners cover I).map eP ⊆ cover := by
    intro w hw
    simp only [Finset.mem_map, pointOwners, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    exact hp.1
  have hL : (lineOwners cover I).map eL ⊆ cover := by
    intro w hw
    simp only [Finset.mem_map, lineOwners, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨l, hl, rfl⟩ := hw
    exact hl.1
  have hdis : Disjoint ((pointOwners cover I).map eP) ((lineOwners cover I).map eL) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hwP hwL
    simp only [Finset.mem_map] at hwP hwL
    obtain ⟨p, _, hp⟩ := hwP
    obtain ⟨l, _, hl⟩ := hwL
    have heq : Fin.natAdd N l = Fin.castAdd M p := hl.trans hp.symm
    have hval := congrArg Fin.val heq
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
    have := p.isLt
    omega
  have hsub : (pointOwners cover I).map eP ∪ (lineOwners cover I).map eL ⊆ cover :=
    Finset.union_subset hP hL
  have hcard := Finset.card_le_card hsub
  simpa [Finset.card_union_of_disjoint hdis, Finset.card_map] using hcard

inductive Star (N M : ℕ) where
  | pt (p : Fin N) (ls : List (Fin M)) (hne : ls ≠ [])
  | ln (l : Fin M) (ps : List (Fin N)) (hne : ps ≠ [])

def starBit {N M : ℕ} (x : Fin (N + M) → Bool) : Star N M → Bool
  | Star.pt p ls _ => ls.any (fun l => edgeOn x p l)
  | Star.ln l ps _ => ps.any (fun p => edgeOn x p l)

def oneStar {N M : ℕ} (gs : List Gate) : Star N M → List Gate × ℕ
  | Star.pt p ls hne =>
      let folded := orAcc (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne))
      (addAnd folded.1 folded.2.1 (pointWire p), N + M + folded.1.length)
  | Star.ln l ps hne =>
      let folded := orAcc (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))
      (addAnd folded.1 (lineWire N l) folded.2.1, N + M + folded.1.length)

theorem oneStar_bit {N M : ℕ} (gs : List Gate) (s : Star N M) (x : Fin (N + M) → Bool) :
    bit (N + M) (oneStar gs s).1 x (oneStar gs s).2 = starBit x s := by
  cases s with
  | pt p ls hne =>
      simpa [oneStar, starBit] using point_star_bit ls gs x p hne
  | ln l ps hne =>
      simpa [oneStar, starBit] using line_star_bit ps gs x l hne

theorem oneStar_form {N M : ℕ} (gs : List Gate) (s : Star N M) :
    match s with
    | Star.pt p ls hne =>
        (oneStar gs s).1 = gs ++ addedOrs (N + M) gs.length (lineWire N (ls.head hne))
          (ls.tail.map (lineWire N)) ++ [⟨GateOp.and,
            [(orAcc (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne))).2.1,
              pointWire p]⟩]
    | Star.ln l ps hne =>
        (oneStar gs s).1 = gs ++ addedOrs (N + M) gs.length (pointWire (ps.head hne))
          (ps.tail.map pointWire) ++ [⟨GateOp.and,
            [lineWire N l,
              (orAcc (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))).2.1]⟩] := by
  cases s with
  | pt p ls hne =>
      simp [oneStar, addAnd, orAcc_added, List.append_assoc]
  | ln l ps hne =>
      simp [oneStar, addAnd, orAcc_added, List.append_assoc]

def foldStars {N M : ℕ} (gs : List Gate) : List (Star N M) → List Gate × List ℕ
  | [] => (gs, [])
  | s :: rest =>
      let built := oneStar gs s
      let later := foldStars built.1 rest
      (later.1, built.2 :: later.2)

theorem foldStars_len {N M : ℕ} (gs : List Gate) (stars : List (Star N M)) :
    (foldStars gs stars).2.length = stars.length := by
  induction stars generalizing gs with
  | nil => simp [foldStars]
  | cons s stars ih => simp [foldStars, ih]

theorem oneStar_grow {N M : ℕ} (gs : List Gate) (s : Star N M) :
    (oneStar gs s).2 < N + M + (oneStar gs s).1.length ∧ ∃ extra, (oneStar gs s).1 = gs ++ extra := by
  cases s with
  | pt p ls hne =>
      have hlen := orAcc_len (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne))
      obtain ⟨extra, hpre⟩ := orAcc_prefix (N + M) (ls.tail.map (lineWire N)) gs
        (lineWire N (ls.head hne))
      simp only [oneStar, addAnd]
      constructor
      · rw [List.length_append, List.length_singleton, hlen]
        omega
      · refine ⟨extra ++ [⟨GateOp.and, [(orAcc (N + M) (ls.tail.map (lineWire N)) gs
            (lineWire N (ls.head hne))).2.1, pointWire p]⟩], ?_⟩
        rw [hpre]
        simp [List.append_assoc]
  | ln l ps hne =>
      have hlen := orAcc_len (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))
      obtain ⟨extra, hpre⟩ := orAcc_prefix (N + M) (ps.tail.map pointWire) gs
        (pointWire (ps.head hne))
      simp only [oneStar, addAnd]
      constructor
      · rw [List.length_append, List.length_singleton, hlen]
        omega
      · refine ⟨extra ++ [⟨GateOp.and, [lineWire N l, (orAcc (N + M) (ps.tail.map pointWire) gs
            (pointWire (ps.head hne))).2.1]⟩], ?_⟩
        rw [hpre]
        simp [List.append_assoc]

theorem foldStars_prefix {N M : ℕ} (gs : List Gate) (stars : List (Star N M)) :
    ∃ extra, (foldStars gs stars).1 = gs ++ extra := by
  induction stars generalizing gs with
  | nil => exact ⟨[], by simp [foldStars]⟩
  | cons s stars ih =>
      obtain ⟨_, extra1, h1⟩ := oneStar_grow gs s
      obtain ⟨extra2, h2⟩ := ih (oneStar gs s).1
      refine ⟨extra1 ++ extra2, ?_⟩
      simp only [foldStars]
      rw [h2, h1]
      simp [List.append_assoc]

theorem foldStars_bit {N M : ℕ} (gs : List Gate) (stars : List (Star N M))
    (x : Fin (N + M) → Bool) :
    ∀ pair ∈ (foldStars gs stars).2.zip stars,
      bit (N + M) (foldStars gs stars).1 x pair.1 = starBit x pair.2 := by
  induction stars generalizing gs with
  | nil =>
      intro pair hp
      simp only [foldStars] at hp
      cases hp
  | cons s stars ih =>
      intro pair hp
      unfold foldStars at hp
      dsimp only at hp
      rw [List.zip_cons_cons] at hp
      simp only [List.mem_cons] at hp
      obtain ⟨hwire, _⟩ := oneStar_grow gs s
      obtain ⟨extra, hextra⟩ := foldStars_prefix (oneStar gs s).1 stars
      rcases hp with rfl | hp
      · unfold foldStars
        dsimp only
        rw [hextra]
        exact (bit_prefix (N + M) (oneStar gs s).1 extra x (oneStar gs s).2 hwire).trans
          (oneStar_bit gs s x)
      · exact ih (oneStar gs s).1 pair hp

def starDeg {N M : ℕ} : Star N M → ℕ
  | Star.pt _ ls _ => ls.length
  | Star.ln _ ps _ => ps.length

theorem oneStar_count {N M : ℕ} (gs : List Gate) (s : Star N M) :
    (oneStar gs s).1.length = gs.length + starDeg s := by
  cases s with
  | pt p ls hne =>
      have hs : ls.head hne :: ls.tail = ls := List.cons_head_tail hne
      simp only [oneStar, addAnd, starDeg, orAcc_len, List.length_append, List.length_singleton,
        List.length_map]
      have : ls.tail.length + 1 = ls.length := by
        rw [← hs]
        simp only [List.tail_cons, List.length_cons]
      omega
  | ln l ps hne =>
      have hs : ps.head hne :: ps.tail = ps := List.cons_head_tail hne
      simp only [oneStar, addAnd, starDeg, orAcc_len, List.length_append, List.length_singleton,
        List.length_map]
      have : ps.tail.length + 1 = ps.length := by
        rw [← hs]
        simp only [List.tail_cons, List.length_cons]
      omega

theorem foldStars_count {N M : ℕ} (gs : List Gate) (stars : List (Star N M)) :
    (foldStars gs stars).1.length = gs.length + (stars.map starDeg).sum := by
  induction stars generalizing gs with
  | nil => simp [foldStars]
  | cons s stars ih =>
      simp only [foldStars, List.map_cons, List.sum_cons, ih, oneStar_count]
      omega

theorem ands_lt {N M : ℕ} (gs : List Gate) (stars : List (Star N M)) :
    ∀ w ∈ (foldStars gs stars).2, w < N + M + (foldStars gs stars).1.length := by
  induction stars generalizing gs with
  | nil => intro w hw; simp [foldStars] at hw
  | cons s stars ih =>
      intro w hw
      unfold foldStars at hw
      dsimp only at hw
      simp only [List.mem_cons] at hw
      obtain ⟨hwire, _⟩ := oneStar_grow gs s
      obtain ⟨extra, hextra⟩ := foldStars_prefix (oneStar gs s).1 stars
      rcases hw with rfl | hw
      · unfold foldStars
        dsimp only
        rw [hextra, List.length_append]
        omega
      · exact ih (oneStar gs s).1 w hw

theorem zip_any {N M : ℕ} (ws : List ℕ) (ss : List (Star N M)) (gs : List Gate)
    (x : Fin (N + M) → Bool) (hlen : ws.length = ss.length)
    (h : ∀ p ∈ ws.zip ss, bit (N + M) gs x p.1 = starBit x p.2) :
    ws.any (fun w => bit (N + M) gs x w) = ss.any (starBit x) := by
  induction ws generalizing ss with
  | nil =>
      cases ss with
      | nil => simp
      | cons s ss => simp at hlen
  | cons w ws ih =>
      cases ss with
      | nil => simp at hlen
      | cons s ss =>
          have hw : bit (N + M) gs x w = starBit x s := by
            have hp := h (w, s) (by simp [List.zip_cons_cons, List.mem_cons])
            simpa using hp
          have ht := ih ss (by simp at hlen; omega)
            (fun p hp => h p (by simp [List.zip_cons_cons, List.mem_cons, hp]))
          simp [List.any_cons, hw, ht]

def finishGates {N M : ℕ} (stars : List (Star N M)) : List Gate × ℕ :=
  let packed := foldStars [] stars
  if h : packed.2 = [] then ([], N + M) else
    let w := packed.2.head h
    let r := orAcc (N + M) packed.2.tail packed.1 w
    (r.1, r.2.1)

theorem finish_bit {N M : ℕ} (stars : List (Star N M)) (x : Fin (N + M) → Bool) :
    bit (N + M) (finishGates stars).1 x (finishGates stars).2 = stars.any (starBit x) := by
  by_cases hstars : stars = []
  · subst hstars
    simp [finishGates, foldStars, bit, List.length_ofFn, List.getD_eq_default]
  · have hlen := foldStars_len ([] : List Gate) stars
    have hne : (foldStars [] stars).2 ≠ [] := by
      intro h
      have : stars.length = 0 := by simpa [h] using hlen.symm
      exact hstars (List.eq_nil_of_length_eq_zero this)
    have hs := List.cons_head_tail hne
    have hlt := ands_lt ([] : List Gate) stars
    simp only [finishGates, hne, dite_false]
    have hhead : (foldStars [] stars).2.head hne < N + M + (foldStars [] stars).1.length :=
      hlt _ (List.head_mem hne)
    have htail : ∀ u ∈ (foldStars [] stars).2.tail, u < N + M + (foldStars [] stars).1.length := by
      intro u hu
      exact hlt u (by rw [← hs]; exact List.mem_cons_of_mem _ hu)
    rw [orAcc_bit (N + M) (foldStars [] stars).2.tail (foldStars [] stars).1
      ((foldStars [] stars).2.head hne) x hhead htail]
    have hzip := foldStars_bit ([] : List Gate) stars x
    have hany := zip_any (foldStars [] stars).2 stars (foldStars [] stars).1 x hlen hzip
    have hform : ((foldStars [] stars).2.head hne :: (foldStars [] stars).2.tail).any
        (fun w => bit (N + M) (foldStars [] stars).1 x w) =
        (bit (N + M) (foldStars [] stars).1 x ((foldStars [] stars).2.head hne) ||
          (foldStars [] stars).2.tail.any (fun w => bit (N + M) (foldStars [] stars).1 x w)) :=
      List.any_cons
    have hlist : ((foldStars [] stars).2.head hne :: (foldStars [] stars).2.tail).any
        (fun w => bit (N + M) (foldStars [] stars).1 x w) =
        (foldStars [] stars).2.any (fun w => bit (N + M) (foldStars [] stars).1 x w) := by
      rw [hs]
    exact (hform.symm.trans hlist).trans hany

theorem good_oneStar {N M : ℕ} (gs : List Gate) (s : Star N M) (h : Good (N + M) gs) :
    Good (N + M) (oneStar gs s).1 := by
  cases s with
  | pt p ls hne =>
      have hroot : lineWire N (ls.head hne) < N + M + gs.length := by
        have := (ls.head hne).isLt
        simp only [lineWire]
        omega
      have hrest : ∀ w ∈ ls.tail.map (lineWire N), w < N + M + gs.length := by
        intro w hw
        simp only [List.mem_map] at hw
        obtain ⟨l, _, rfl⟩ := hw
        have := l.isLt
        simp only [lineWire]
        omega
      have hg := good_orAcc (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne)) h hroot hrest
      have hroot2 := orAcc_root_lt (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne)) hroot
      have hp : pointWire p < N + M + (orAcc (N + M) (ls.tail.map (lineWire N)) gs
          (lineWire N (ls.head hne))).1.length := by
        simp only [pointWire]
        omega
      simpa [oneStar, addAnd] using good_append_and (N + M)
        (orAcc (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne))).1
        (orAcc (N + M) (ls.tail.map (lineWire N)) gs (lineWire N (ls.head hne))).2.1
        (pointWire p) hg hroot2 hp
  | ln l ps hne =>
      have hroot : pointWire (ps.head hne) < N + M + gs.length := by
        simp only [pointWire]
        omega
      have hrest : ∀ w ∈ ps.tail.map pointWire, w < N + M + gs.length := by
        intro w hw
        simp only [List.mem_map] at hw
        obtain ⟨p, _, rfl⟩ := hw
        simp only [pointWire]
        omega
      have hg := good_orAcc (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne)) h hroot hrest
      have hroot2 := orAcc_root_lt (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne)) hroot
      have hl : lineWire N l < N + M + (orAcc (N + M) (ps.tail.map pointWire) gs
          (pointWire (ps.head hne))).1.length := by
        have := l.isLt
        simp only [lineWire]
        omega
      simpa [oneStar, addAnd] using good_append_and (N + M)
        (orAcc (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))).1
        (lineWire N l)
        (orAcc (N + M) (ps.tail.map pointWire) gs (pointWire (ps.head hne))).2.1
        hg hl hroot2

theorem good_fold {N M : ℕ} (gs : List Gate) (stars : List (Star N M)) (h : Good (N + M) gs) :
    Good (N + M) (foldStars gs stars).1 := by
  induction stars generalizing gs with
  | nil => simpa [foldStars] using h
  | cons s stars ih =>
      unfold foldStars
      dsimp only
      exact ih _ (good_oneStar gs s h)

theorem good_finish {N M : ℕ} (stars : List (Star N M)) : Good (N + M) (finishGates stars).1 := by
  have hfold := good_fold ([] : List Gate) stars (good_nil _)
  by_cases hstars : stars = []
  · subst hstars
    simpa [finishGates, foldStars] using good_nil (N + M)
  · have hlen := foldStars_len ([] : List Gate) stars
    have hne : (foldStars [] stars).2 ≠ [] := by
      intro h
      have : stars.length = 0 := by simpa [h] using hlen.symm
      exact hstars (List.eq_nil_of_length_eq_zero this)
    have hs := List.cons_head_tail hne
    have hlt := ands_lt ([] : List Gate) stars
    simp only [finishGates, hne, dite_false]
    exact good_orAcc (N + M) (foldStars [] stars).2.tail (foldStars [] stars).1
      ((foldStars [] stars).2.head hne) hfold (hlt _ (List.head_mem hne))
      (by intro u hu; exact hlt u (by rw [← hs]; exact List.mem_cons_of_mem _ hu))



def isOr (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

def grow (n : ℕ) (pts lns : Finset ℕ) (j : ℕ) (g : Gate) : Finset ℕ × Finset ℕ :=
  if isOr g && g.inputs.all (fun i => decide (i ∈ pts)) then (insert (n + j) pts, lns)
  else if isOr g && g.inputs.all (fun i => decide (i ∈ lns)) then (pts, insert (n + j) lns)
  else (pts, lns)

def foldClass (n : ℕ) : Finset ℕ → Finset ℕ → ℕ → List Gate → Finset ℕ × Finset ℕ
  | pts, lns, _, [] => (pts, lns)
  | pts, lns, j, g :: gs =>
      let next := grow n pts lns j g
      foldClass n next.1 next.2 (j + 1) gs

def classes (N M : ℕ) (gs : List Gate) : Finset ℕ × Finset ℕ :=
  foldClass (N + M) (Finset.range N) (Finset.Ico N (N + M)) 0 gs

def PointOk (N n : ℕ) (gs : List Gate) (pts : Finset ℕ) : Prop :=
  ∀ w ∈ pts, w < N ∨ ∃ k, ∃ (hk : k < gs.length), w = n + k ∧
    (gs[k]'hk).op = GateOp.or ∧ ∀ i ∈ (gs[k]'hk).inputs, i ∈ pts

def LineOk (N n : ℕ) (gs : List Gate) (lns : Finset ℕ) : Prop :=
  ∀ w ∈ lns, (N ≤ w ∧ w < n) ∨ ∃ k, ∃ (hk : k < gs.length), w = n + k ∧
    (gs[k]'hk).op = GateOp.or ∧ ∀ i ∈ (gs[k]'hk).inputs, i ∈ lns

theorem get_left (done : List Gate) (g : Gate) (k : ℕ) (hk : k < done.length) :
    ((done ++ [g])[k]'(by simp [List.length_append]; omega)) = done[k] := by
  simp [List.getElem_append, hk]

theorem get_last (done : List Gate) (g : Gate) :
    ((done ++ [g])[done.length]'(by simp [List.length_append])) = g := by
  simp [List.getElem_append_right, Nat.sub_self]

theorem all_mem (l : List ℕ) (s : Finset ℕ) :
    l.all (fun i => decide (i ∈ s)) = true ↔ ∀ i ∈ l, i ∈ s := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.all_cons, ih]

theorem isOr_iff (g : Gate) : isOr g = true ↔ g.op = GateOp.or := by
  unfold isOr
  cases g.op <;> simp

theorem grow_sup (n : ℕ) (pts lns : Finset ℕ) (j : ℕ) (g : Gate) :
    pts ⊆ (grow n pts lns j g).1 ∧ lns ⊆ (grow n pts lns j g).2 := by
  unfold grow
  split
  · simp
  · split <;> simp

theorem point_old (N n : ℕ) (done : List Gate) (g : Gate) (pts lns : Finset ℕ)
    (hpts : PointOk N n done pts) :
    PointOk N n (done ++ [g]) (grow n pts lns done.length g).1 := by
  intro w hw
  have hsub := (grow_sup n pts lns done.length g).1
  by_cases hold : w ∈ pts
  · rcases hpts w hold with h | ⟨k, hk, hwk, hop, hin⟩
    · exact Or.inl h
    · refine Or.inr ⟨k, by simp [List.length_append]; omega, hwk, ?_, ?_⟩
      · simpa [get_left done g k hk] using hop
      · intro i hi
        exact hsub (hin i (by simpa [get_left done g k hk] using hi))
  · have hgrow : w ∈ (grow n pts lns done.length g).1 := hw
    unfold grow at hgrow
    split at hgrow
    · rename_i hflag
      simp only [Finset.mem_insert] at hgrow
      rcases hgrow with rfl | hgrow
      · have hor : isOr g = true := by
          cases h : isOr g
          · simp [h] at hflag
          · rfl
        have hall : ∀ i ∈ g.inputs, i ∈ pts := by
          simp [hor] at hflag
          exact hflag
        refine Or.inr ⟨done.length, by simp [List.length_append], rfl, ?_, ?_⟩
        · simpa [get_last done g, isOr_iff] using hor
        · intro i hi
          exact hsub (hall i (by simpa [get_last done g] using hi))
      · exact absurd hgrow hold
    · split at hgrow
      · simp at hgrow
        exact absurd hgrow hold
      · simp at hgrow
        exact absurd hgrow hold

theorem line_old (N n : ℕ) (done : List Gate) (g : Gate) (pts lns : Finset ℕ)
    (hlns : LineOk N n done lns) :
    LineOk N n (done ++ [g]) (grow n pts lns done.length g).2 := by
  intro w hw
  have hsub := (grow_sup n pts lns done.length g).2
  by_cases hold : w ∈ lns
  · rcases hlns w hold with h | ⟨k, hk, hwk, hop, hin⟩
    · exact Or.inl h
    · refine Or.inr ⟨k, by simp [List.length_append]; omega, hwk, ?_, ?_⟩
      · simpa [get_left done g k hk] using hop
      · intro i hi
        exact hsub (hin i (by simpa [get_left done g k hk] using hi))
  · have hgrow : w ∈ (grow n pts lns done.length g).2 := hw
    unfold grow at hgrow
    split at hgrow
    · simp at hgrow
      exact absurd hgrow hold
    · split at hgrow
      · rename_i hflag
        simp only [Finset.mem_insert] at hgrow
        rcases hgrow with rfl | hgrow
        · have hor : isOr g = true := by
            cases h : isOr g
            · simp [h] at hflag
            · rfl
          have hall : ∀ i ∈ g.inputs, i ∈ lns := by
            simp [hor] at hflag
            exact hflag
          refine Or.inr ⟨done.length, by simp [List.length_append], rfl, ?_, ?_⟩
          · simpa [get_last done g, isOr_iff] using hor
          · intro i hi
            exact hsub (hall i (by simpa [get_last done g] using hi))
        · exact absurd hgrow hold
      · simp at hgrow
        exact absurd hgrow hold

theorem closed_aux (N n : ℕ) (done rest : List Gate) (pts lns : Finset ℕ)
    (hpts : PointOk N n done pts) (hlns : LineOk N n done lns) :
    let full := done ++ rest
    let S := foldClass n pts lns done.length rest
    PointOk N n full S.1 ∧ LineOk N n full S.2 := by
  induction rest generalizing done pts lns with
  | nil =>
      simp [foldClass]
      exact ⟨hpts, hlns⟩
  | cons g rest ih =>
      simp [foldClass]
      simpa [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] using
        ih (done ++ [g]) (grow n pts lns done.length g).1 (grow n pts lns done.length g).2
          (point_old N n done g pts lns hpts) (line_old N n done g pts lns hlns)

theorem classes_closed (N M : ℕ) (gs : List Gate) :
    PointOk N (N + M) gs (classes N M gs).1 ∧ LineOk N (N + M) gs (classes N M gs).2 := by
  simpa [classes] using closed_aux N (N + M) [] gs (Finset.range N) (Finset.Ico N (N + M))
    (by intro w hw; simp [Finset.mem_range] at hw; exact Or.inl hw)
    (by intro w hw; simp [Finset.mem_Ico] at hw; exact Or.inl hw)

theorem fold_append (n : ℕ) (pts lns : Finset ℕ) (j : ℕ) (gs extra : List Gate) :
    foldClass n pts lns j (gs ++ extra) =
      foldClass n (foldClass n pts lns j gs).1 (foldClass n pts lns j gs).2 (j + gs.length) extra := by
  induction gs generalizing pts lns j with
  | nil => simp [foldClass]
  | cons g gs ih =>
      simp [foldClass, ih]
      rw [show j + 1 + gs.length = j + (gs.length + 1) by omega]

theorem base_kept (N M : ℕ) (gs : List Gate) :
    Finset.range N ⊆ (classes N M gs).1 ∧ Finset.Ico N (N + M) ⊆ (classes N M gs).2 := by
  have h := fold_append (N + M) (Finset.range N) (Finset.Ico N (N + M)) 0 [] gs
  simp [classes, foldClass] at h
  -- grow from the initial sets along gs only enlarges them
  have hsub : ∀ (pts lns : Finset ℕ) (j : ℕ) (rest : List Gate),
      pts ⊆ (foldClass (N + M) pts lns j rest).1 ∧ lns ⊆ (foldClass (N + M) pts lns j rest).2 := by
    intro pts lns j rest
    induction rest generalizing pts lns j with
    | nil => simp [foldClass]
    | cons g rest ih =>
        simp [foldClass]
        have hs := grow_sup (N + M) pts lns j g
        have ht := ih (grow (N + M) pts lns j g).1 (grow (N + M) pts lns j g).2 (j + 1)
        exact ⟨fun x hx => ht.1 (hs.1 hx), fun x hx => ht.2 (hs.2 hx)⟩
  simpa [classes, foldClass] using hsub (Finset.range N) (Finset.Ico N (N + M)) 0 gs

theorem orAcc_wire_idx (n : ℕ) (rest : List ℕ) (gs : List Gate) (root : ℕ) :
    ∀ w ∈ (orAcc n rest gs root).2.2, ∃ i, i < rest.length ∧ w = n + gs.length + i := by
  induction rest generalizing gs root with
  | nil => intro w hw; simp [orAcc_nil] at hw
  | cons w rest ih =>
      intro u hu
      rw [orAcc_cons] at hu
      dsimp only at hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨i, hi, h⟩ := ih (gs ++ [⟨GateOp.or, [root, w]⟩]) (n + gs.length) u hu
        refine ⟨i + 1, by
          have : (w :: rest).length = rest.length + 1 := by simp
          omega, ?_⟩
        simp only [List.length_append, List.length_singleton] at h
        omega

theorem fold_sup (n : ℕ) (pts lns : Finset ℕ) (j : ℕ) (rest : List Gate) :
    pts ⊆ (foldClass n pts lns j rest).1 ∧ lns ⊆ (foldClass n pts lns j rest).2 := by
  induction rest generalizing pts lns j with
  | nil => simp [foldClass]
  | cons g rest ih =>
      simp [foldClass]
      have hs := grow_sup n pts lns j g
      have ht := ih (grow n pts lns j g).1 (grow n pts lns j g).2 (j + 1)
      exact ⟨fun x hx => ht.1 (hs.1 hx), fun x hx => ht.2 (hs.2 hx)⟩

theorem chain_out (n : ℕ) (pts lns : Finset ℕ) (j root : ℕ) (leaves : List ℕ)
    (hroot : root ∈ lns) (hleaves : ∀ a ∈ leaves, a ∈ lns) (hp0 : root ∉ pts)
    (hp1 : ∀ a ∈ leaves, a ∉ pts) (hp2 : ∀ i, i < leaves.length → n + j + i ∉ pts) :
    ∀ i, i < (addedOrs n j root leaves).length →
      n + j + i ∈ (foldClass n pts lns j (addedOrs n j root leaves)).2 := by
  induction leaves generalizing pts lns j root with
  | nil =>
      intro i hi
      simp [addedOrs, List.length_nil] at hi
  | cons a as ih =>
      intro i hi
      have ha : a ∈ lns := hleaves a (by simp)
      have hskip : (isOr (⟨GateOp.or, [root, a]⟩ : Gate) &&
          (⟨GateOp.or, [root, a]⟩ : Gate).inputs.all (fun t => decide (t ∈ pts))) = false := by
        simp [isOr, List.all_cons, hp0]
      have htake : (isOr (⟨GateOp.or, [root, a]⟩ : Gate) &&
          (⟨GateOp.or, [root, a]⟩ : Gate).inputs.all (fun t => decide (t ∈ lns))) = true := by
        simp [isOr, List.all_cons, hroot, ha]
      have hgrow : grow n pts lns j (⟨GateOp.or, [root, a]⟩ : Gate) =
          (pts, insert (n + j) lns) := by
        unfold grow
        split
        · rename_i h
          simp [isOr, List.all_cons, hp0] at h
        · rfl
      cases i with
      | zero =>
          rw [addedOrs, foldClass, hgrow]
          exact (fold_sup n pts (insert (n + j) lns) (j + 1)
            (addedOrs n (j + 1) (n + j) as)).2 (Finset.mem_insert_self (n + j) lns)
      | succ i =>
          have hlen : i < (addedOrs n (j + 1) (n + j) as).length := by
            simp [addedOrs, List.length_cons] at hi
            omega
          have hmem := ih pts (insert (n + j) lns) (j + 1) (n + j)
            (Finset.mem_insert_self (n + j) lns)
            (fun b hb => Finset.mem_insert_of_mem (hleaves b (List.mem_cons_of_mem a hb)))
            (by simpa using hp2 0 (by simp [List.length_cons]))
            (fun b hb => hp1 b (List.mem_cons_of_mem a hb))
            (fun k hk => by
              have hlt : k + 1 < (a :: as).length := by
                have : (a :: as).length = as.length + 1 := by simp
                omega
              have hne := hp2 (k + 1) hlt
              have heq : n + (j + 1) + k = n + j + (k + 1) := by omega
              rw [heq]
              exact hne)
            i hlen
          simpa [addedOrs, foldClass, hgrow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmem

theorem chain_in (n : ℕ) (pts lns : Finset ℕ) (j root : ℕ) (leaves : List ℕ)
    (hroot : root ∈ pts) (hleaves : ∀ a ∈ leaves, a ∈ pts) :
    ∀ i, i < (addedOrs n j root leaves).length →
      n + j + i ∈ (foldClass n pts lns j (addedOrs n j root leaves)).1 := by
  induction leaves generalizing pts lns j root with
  | nil =>
      intro i hi
      simp [addedOrs, List.length_nil] at hi
  | cons a as ih =>
      intro i hi
      have ha : a ∈ pts := hleaves a (by simp)
      have htake : (isOr (⟨GateOp.or, [root, a]⟩ : Gate) &&
          (⟨GateOp.or, [root, a]⟩ : Gate).inputs.all (fun t => decide (t ∈ pts))) = true := by
        simp [isOr, List.all_cons, hroot, ha]
      have hgrow : grow n pts lns j (⟨GateOp.or, [root, a]⟩ : Gate) =
          (insert (n + j) pts, lns) := by
        unfold grow
        split
        · rfl
        · rfl
      cases i with
      | zero =>
          rw [addedOrs, foldClass, hgrow]
          exact (fold_sup n (insert (n + j) pts) lns (j + 1)
            (addedOrs n (j + 1) (n + j) as)).1 (Finset.mem_insert_self (n + j) pts)
      | succ i =>
          have hlen : i < (addedOrs n (j + 1) (n + j) as).length := by
            simp [addedOrs, List.length_cons] at hi
            omega
          have hmem := ih (insert (n + j) pts) lns (j + 1) (n + j)
            (Finset.mem_insert_self (n + j) pts)
            (fun b hb => Finset.mem_insert_of_mem (hleaves b (List.mem_cons_of_mem a hb)))
            i hlen
          simpa [addedOrs, foldClass, hgrow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmem

theorem added_len (n start root : ℕ) (leaves : List ℕ) :
    (addedOrs n start root leaves).length = leaves.length := by
  induction leaves generalizing start root with
  | nil => simp [addedOrs]
  | cons _ rest ih => simp [addedOrs, ih]

theorem not_point (N M : ℕ) (gs : List Gate) (pts : Finset ℕ) (w : ℕ)
    (h : PointOk N (N + M) gs pts) (hw : N ≤ w ∧ w < N + M) : w ∉ pts := by
  intro hw'
  rcases h w hw' with hlt | ⟨k, _, hwk, _, _⟩
  · omega
  · omega

theorem not_fresh (N M : ℕ) (gs : List Gate) (pts : Finset ℕ) (k : ℕ)
    (h : PointOk N (N + M) gs pts) (hk : gs.length ≤ k) : N + M + k ∉ pts := by
  intro hw
  rcases h _ hw with hlt | ⟨j, hj, hwj, _, _⟩
  · omega
  · omega

theorem not_line (N M : ℕ) (gs : List Gate) (lns : Finset ℕ) (w : ℕ)
    (h : LineOk N (N + M) gs lns) (hw : w < N) : w ∉ lns := by
  intro hw'
  rcases h w hw' with hmid | ⟨k, _, hwk, _, _⟩
  · omega
  · omega

theorem classes_grow {N M : ℕ} (gs extra : List Gate) :
    (classes N M gs).1 ⊆ (classes N M (gs ++ extra)).1 ∧
      (classes N M gs).2 ⊆ (classes N M (gs ++ extra)).2 := by
  have happ := fold_append (N + M) (Finset.range N) (Finset.Ico N (N + M)) 0 gs extra
  have hsup := fold_sup (N + M) (classes N M gs).1 (classes N M gs).2 gs.length extra
  constructor
  · intro w hw
    have := hsup.1 hw
    simpa [classes, happ, Nat.zero_add] using this
  · intro w hw
    have := hsup.2 hw
    simpa [classes, happ, Nat.zero_add] using this

theorem finish_count {N M : ℕ} (stars : List (Star N M)) :
    (finishGates stars).1.length = (stars.map starDeg).sum + stars.length - 1 := by
  by_cases hstars : stars = []
  · subst hstars
    simp [finishGates, foldStars]
  · have hlen := foldStars_len ([] : List Gate) stars
    have hne : (foldStars [] stars).2 ≠ [] := by
      intro h
      have : stars.length = 0 := by simpa [h] using hlen.symm
      exact hstars (List.eq_nil_of_length_eq_zero this)
    simp only [finishGates, hne, dite_false]
    have hacc := orAcc_len (N + M) (foldStars [] stars).2.tail (foldStars [] stars).1
      ((foldStars [] stars).2.head hne)
    have hfold := foldStars_count ([] : List Gate) stars
    have hplus : (foldStars [] stars).2.tail.length + 1 = stars.length := by
      have hs := List.cons_head_tail hne
      have hlen2 : (foldStars [] stars).2.length =
          ((foldStars [] stars).2.head hne :: (foldStars [] stars).2.tail).length :=
        congrArg List.length hs.symm
      simp only [List.length_cons] at hlen2
      rw [hlen] at hlen2
      exact hlen2.symm
    rw [hacc, hfold]
    simp only [List.length_nil, Nat.zero_add]
    have hone : 1 ≤ stars.length := by omega
    have htail : (foldStars [] stars).2.tail.length = stars.length - 1 := by omega
    rw [htail]
    exact (Nat.add_sub_assoc hone ((stars.map starDeg).sum)).symm

theorem bit_fun {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    bit n gs x out = circuitFun n ⟨gs, out⟩ x := by
  unfold bit circuitFun Circuit.eval Circuit.wires
  rfl

noncomputable def linesOf {N M : ℕ} (I : Fin N → Fin M → Prop) [DecidableRel I] (p : Fin N) :
    List (Fin M) :=
  (Finset.univ.filter (fun l : Fin M => I p l)).toList

noncomputable def ownedPts {N M : ℕ} (cover : Finset (Fin (N + M)))
    (I : Fin N → Fin M → Prop) [DecidableRel I] (l : Fin M) : List (Fin N) :=
  (Finset.univ.filter (fun p : Fin N => I p l ∧ Fin.castAdd M p ∉ cover)).toList

theorem lines_mem {N M : ℕ} (I : Fin N → Fin M → Prop) [DecidableRel I] (p : Fin N) (l : Fin M) :
    l ∈ linesOf I p ↔ I p l := by
  simp [linesOf, Finset.mem_toList, Finset.mem_filter]

theorem owned_mem {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] (l : Fin M) (p : Fin N) :
    p ∈ ownedPts cover I l ↔ I p l ∧ Fin.castAdd M p ∉ cover := by
  simp [ownedPts, Finset.mem_toList, Finset.mem_filter]

theorem lines_ne {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] (p : Fin N) (hp : p ∈ pointOwners cover I) : linesOf I p ≠ [] := by
  simp only [pointOwners, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨l, hl⟩ := hp.2
  intro h
  have : l ∈ linesOf I p := (lines_mem I p l).2 hl
  simp [h] at this

theorem owned_ne {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] (l : Fin M) (hl : l ∈ lineOwners cover I) : ownedPts cover I l ≠ [] := by
  simp only [lineOwners, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨p, hp, hnot⟩ := hl.2
  intro h
  have : p ∈ ownedPts cover I l := (owned_mem cover I l p).2 ⟨hp, hnot⟩
  simp [h] at this

noncomputable def pointStars {N M : ℕ} (cover : Finset (Fin (N + M)))
    (I : Fin N → Fin M → Prop) [DecidableRel I] : List (Star N M) :=
  (pointOwners cover I).toList.attach.map fun p =>
    Star.pt p.1 (linesOf I p.1) (lines_ne cover I p.1 (Finset.mem_toList.mp p.2))

noncomputable def lineStars {N M : ℕ} (cover : Finset (Fin (N + M)))
    (I : Fin N → Fin M → Prop) [DecidableRel I] : List (Star N M) :=
  (lineOwners cover I).toList.attach.map fun l =>
    Star.ln l.1 (ownedPts cover I l.1) (owned_ne cover I l.1 (Finset.mem_toList.mp l.2))

noncomputable def allStars {N M : ℕ} (cover : Finset (Fin (N + M)))
    (I : Fin N → Fin M → Prop) [DecidableRel I] : List (Star N M) :=
  pointStars cover I ++ lineStars cover I

theorem point_len {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] : (pointStars cover I).length = (pointOwners cover I).card := by
  simp [pointStars, List.length_map, List.length_attach, Finset.length_toList]

theorem line_len {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] : (lineStars cover I).length = (lineOwners cover I).card := by
  simp [lineStars, List.length_map, List.length_attach, Finset.length_toList]

theorem stars_len {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] :
    (allStars cover I).length = (pointOwners cover I).card + (lineOwners cover I).card := by
  simp [allStars, point_len, line_len]

theorem stars_le {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] : (allStars cover I).length ≤ cover.card := by
  rw [stars_len]
  exact owners_le cover I

theorem pmap_val {α : Type} {P : α → Prop} (l : List α) (H : ∀ x, x ∈ l → P x) :
    ((l.pmap Subtype.mk H).map fun p => p.1) = l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.pmap, List.map_cons]
      exact congrArg (fun t => a :: t) (ih fun x hx => H x (List.mem_cons_of_mem a hx))

theorem sum_val {α : Type} (l : List α) (f : α → ℕ) :
    (l.attach.map fun p => f p.1).sum = (l.map f).sum := by
  have hvals : (l.attach.map fun p => p.1) = l := by
    simpa [List.attach, List.attachWith] using pmap_val l (fun x hx => hx)
  have hmap : (l.attach.map fun p => f p.1) = (l.attach.map fun p => p.1).map f := by
    simp [List.map_map]
  simp [hmap, hvals, List.map_map]

theorem sum_toList {α : Type} (s : Finset α) (f : α → ℕ) :
    (s.toList.map f).sum = ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hperm : List.Perm ((insert a s).toList.map f) ((a :: s.toList).map f) :=
        List.Perm.map f (Finset.toList_insert ha)
      rw [Finset.sum_insert ha, List.Perm.sum_eq hperm]
      simp [ih]

theorem point_deg {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] :
    ((pointStars cover I).map starDeg).sum =
      ∑ p ∈ pointOwners cover I, (Finset.univ.filter (fun l : Fin M => I p l)).card := by
  classical
  have hmap : ((pointStars cover I).map starDeg) =
      ((pointOwners cover I).toList.attach.map fun p => (linesOf I p.1).length) := by
    simp [pointStars, starDeg]
  rw [hmap]
  have hs := sum_val ((pointOwners cover I).toList) (fun p => (linesOf I p).length)
  rw [hs, sum_toList]
  refine Finset.sum_congr rfl ?_
  intro p _
  simp [linesOf, Finset.length_toList]

theorem line_deg {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] :
    ((lineStars cover I).map starDeg).sum =
      ∑ l ∈ lineOwners cover I,
        (Finset.univ.filter (fun p : Fin N => I p l ∧ Fin.castAdd M p ∉ cover)).card := by
  classical
  have hmap : ((lineStars cover I).map starDeg) =
      ((lineOwners cover I).toList.attach.map fun l => (ownedPts cover I l.1).length) := by
    simp [lineStars, starDeg]
  rw [hmap]
  have hs := sum_val ((lineOwners cover I).toList) (fun l => (ownedPts cover I l).length)
  rw [hs, sum_toList]
  refine Finset.sum_congr rfl ?_
  intro l _
  simp [ownedPts, Finset.length_toList]

theorem incid_card_sum {N M : ℕ} (I : Fin N → Fin M → Prop) [DecidableRel I] :
    (PEqualNP.ReadTwo.incid I).card =
      ∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => I p l)).card := by
  classical
  let fiber (p : Fin N) : Finset (Fin N × Fin M) :=
    (Finset.univ.filter (fun l : Fin M => I p l)).map
      ⟨fun l => (p, l), fun a b h => by simpa using congrArg Prod.snd h⟩
  have hunion : PEqualNP.ReadTwo.incid I = Finset.univ.biUnion fiber := by
    ext e
    constructor
    · intro he
      have hI : I e.1 e.2 := by
        simpa [PEqualNP.ReadTwo.incid] using he
      refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_univ _, ?_⟩
      refine Finset.mem_map.mpr ⟨e.2, ?_, ?_⟩
      · simpa using hI
      · cases e
        rfl
    · intro he
      obtain ⟨p, _, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨l, hl, heq⟩ := Finset.mem_map.mp he
      have hI : I p l := by simpa using hl
      have hpair : fiber p = (Finset.univ.filter (fun l : Fin M => I p l)).map
          ⟨fun l => (p, l), fun a b h => by simpa using congrArg Prod.snd h⟩ := rfl
      rw [← heq]
      simpa [PEqualNP.ReadTwo.incid, hI]
  have hdis : ∀ p ∈ (Finset.univ : Finset (Fin N)), ∀ q ∈ (Finset.univ : Finset (Fin N)),
      p ≠ q → Disjoint (fiber p) (fiber q) := by
    intro p _ q _ hpq
    refine Finset.disjoint_left.mpr ?_
    intro w hwP hwQ
    obtain ⟨l1, _, rfl⟩ := Finset.mem_map.mp hwP
    obtain ⟨l2, _, h⟩ := Finset.mem_map.mp hwQ
    cases h
    exact hpq rfl
  rw [hunion, Finset.card_biUnion hdis]
  simp [fiber, Finset.card_map]

theorem edge_bits {N M : ℕ} (x : Fin (N + M) → Bool) (p : Fin N) (l : Fin M) :
    edgeOn x p l = true ↔
      x (Fin.castAdd M p) = true ∧ x (Fin.natAdd N l) = true := by
  simp [edgeOn]

theorem point_owner_iff {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] (p : Fin N) :
    p ∈ pointOwners cover I ↔ Fin.castAdd M p ∈ cover ∧ ∃ l, I p l := by
  simp [pointOwners, Finset.mem_filter]

theorem line_owner_iff {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] (l : Fin M) :
    l ∈ lineOwners cover I ↔
      Fin.natAdd N l ∈ cover ∧ ∃ p, I p l ∧ Fin.castAdd M p ∉ cover := by
  simp [lineOwners, Finset.mem_filter]

theorem point_hit {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] (x : Fin (N + M) → Bool) :
    (pointStars cover I).any (starBit x) = true ↔
      ∃ p l, p ∈ pointOwners cover I ∧ I p l ∧ edgeOn x p l = true := by
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨s, hs, hb⟩ := h
    simp only [pointStars, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    simp only [starBit, List.any_eq_true] at hb
    obtain ⟨l, hl, he⟩ := hb
    exact ⟨p.1, l, Finset.mem_toList.mp p.2, (lines_mem I p.1 l).1 hl, he⟩
  · rintro ⟨p, l, hp, hI, he⟩
    rw [List.any_eq_true]
    have hne := lines_ne cover I p hp
    refine ⟨Star.pt p (linesOf I p) hne, ?_, ?_⟩
    · simp only [pointStars, List.mem_map]
      exact ⟨⟨p, Finset.mem_toList.mpr hp⟩, by simp, rfl⟩
    · simp only [starBit, List.any_eq_true]
      exact ⟨l, (lines_mem I p l).2 hI, he⟩

theorem line_hit {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I] (x : Fin (N + M) → Bool) :
    (lineStars cover I).any (starBit x) = true ↔
      ∃ l p, l ∈ lineOwners cover I ∧ I p l ∧ Fin.castAdd M p ∉ cover ∧ edgeOn x p l = true := by
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨s, hs, hb⟩ := h
    simp only [lineStars, List.mem_map] at hs
    obtain ⟨l, hl, rfl⟩ := hs
    simp only [starBit, List.any_eq_true] at hb
    obtain ⟨p, hp, he⟩ := hb
    exact ⟨l.1, p, Finset.mem_toList.mp l.2, ((owned_mem cover I l.1 p).1 hp).1,
      ((owned_mem cover I l.1 p).1 hp).2, he⟩
  · rintro ⟨l, p, hl, hI, hnot, he⟩
    rw [List.any_eq_true]
    have hne := owned_ne cover I l hl
    refine ⟨Star.ln l (ownedPts cover I l) hne, ?_, ?_⟩
    · simp only [lineStars, List.mem_map]
      exact ⟨⟨l, Finset.mem_toList.mpr hl⟩, by simp, rfl⟩
    · simp only [starBit, List.any_eq_true]
      exact ⟨p, (owned_mem cover I l p).2 ⟨hI, hnot⟩, he⟩

theorem stars_hit {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I]
    (hcover : ∀ p l, I p l → Fin.castAdd M p ∈ cover ∨ Fin.natAdd N l ∈ cover)
    (x : Fin (N + M) → Bool) :
    (allStars cover I).any (starBit x) = true ↔
      ∃ p l, I p l ∧ x (Fin.castAdd M p) = true ∧ x (Fin.natAdd N l) = true := by
  rw [allStars, List.any_append, Bool.or_eq_true, point_hit, line_hit]
  constructor
  · rintro (⟨p, l, _, hI, he⟩ | ⟨l, p, _, hI, _, he⟩)
    · exact ⟨p, l, hI, (edge_bits x p l).1 he⟩
    · exact ⟨p, l, hI, (edge_bits x p l).1 he⟩
  · rintro ⟨p, l, hI, hx⟩
    have he : edgeOn x p l = true := (edge_bits x p l).2 hx
    by_cases hc : Fin.castAdd M p ∈ cover
    · exact Or.inl ⟨p, l, (point_owner_iff cover I p).2 ⟨hc, l, hI⟩, hI, he⟩
    · have hl : Fin.natAdd N l ∈ cover := by
        rcases hcover p l hI with h | h
        · exact absurd h hc
        · exact h
      exact Or.inr ⟨l, p, (line_owner_iff cover I l).2 ⟨hl, p, hI, hc⟩, hI, hc, he⟩

theorem rowCard {N M : ℕ} (Q : Fin N → Fin M → Prop) [DecidableRel Q] :
    (Finset.univ.filter (fun e : Fin N × Fin M => Q e.1 e.2)).card =
      ∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => Q p l)).card := by
  classical
  let fiber (p : Fin N) : Finset (Fin N × Fin M) :=
    (Finset.univ.filter (fun l : Fin M => Q p l)).map
      ⟨fun l => (p, l), fun a b h => by simpa using congrArg Prod.snd h⟩
  have hunion : Finset.univ.filter (fun e : Fin N × Fin M => Q e.1 e.2) = Finset.univ.biUnion fiber := by
    ext e
    constructor
    · intro he
      have hQ : Q e.1 e.2 := by simpa using he
      refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_univ _, ?_⟩
      refine Finset.mem_map.mpr ⟨e.2, ?_, ?_⟩
      · simpa using hQ
      · cases e
        rfl
    · intro he
      obtain ⟨p, _, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨l, hl, heq⟩ := Finset.mem_map.mp he
      have hQ : Q p l := by simpa using hl
      rw [← heq]
      simpa [hQ]
  have hdis : ∀ p ∈ (Finset.univ : Finset (Fin N)), ∀ q ∈ (Finset.univ : Finset (Fin N)),
      p ≠ q → Disjoint (fiber p) (fiber q) := by
    intro p _ q _ hpq
    refine Finset.disjoint_left.mpr ?_
    intro w hwP hwQ
    obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hwP
    obtain ⟨_, _, h⟩ := Finset.mem_map.mp hwQ
    cases h
    exact hpq rfl
  rw [hunion, Finset.card_biUnion hdis]
  simp [fiber, Finset.card_map]

theorem colCard {N M : ℕ} (Q : Fin N → Fin M → Prop) [DecidableRel Q] :
    (Finset.univ.filter (fun e : Fin N × Fin M => Q e.1 e.2)).card =
      ∑ l : Fin M, (Finset.univ.filter (fun p : Fin N => Q p l)).card := by
  classical
  let fiber (l : Fin M) : Finset (Fin N × Fin M) :=
    (Finset.univ.filter (fun p : Fin N => Q p l)).map
      ⟨fun p => (p, l), fun a b h => by simpa using congrArg Prod.fst h⟩
  have hunion : Finset.univ.filter (fun e : Fin N × Fin M => Q e.1 e.2) = Finset.univ.biUnion fiber := by
    ext e
    constructor
    · intro he
      have hQ : Q e.1 e.2 := by simpa using he
      refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_univ _, ?_⟩
      refine Finset.mem_map.mpr ⟨e.1, ?_, ?_⟩
      · simpa using hQ
      · cases e
        rfl
    · intro he
      obtain ⟨l, _, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨p, hp, heq⟩ := Finset.mem_map.mp he
      have hQ : Q p l := by simpa using hp
      rw [← heq]
      simpa [hQ]
  have hdis : ∀ l ∈ (Finset.univ : Finset (Fin M)), ∀ k ∈ (Finset.univ : Finset (Fin M)),
      l ≠ k → Disjoint (fiber l) (fiber k) := by
    intro l _ k _ hlk
    refine Finset.disjoint_left.mpr ?_
    intro w hwL hwK
    obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hwL
    obtain ⟨_, _, h⟩ := Finset.mem_map.mp hwK
    cases h
    exact hlk rfl
  rw [hunion, Finset.card_biUnion hdis]
  simp [fiber, Finset.card_map]

theorem deg_card {N M : ℕ} (cover : Finset (Fin (N + M))) (I : Fin N → Fin M → Prop)
    [DecidableRel I]
    (hcover : ∀ (p : Fin N) (l : Fin M), I p l → Fin.castAdd M p ∈ cover ∨ Fin.natAdd N l ∈ cover) :
    ((allStars cover I).map starDeg).sum = (PEqualNP.ReadTwo.incid I).card := by
  classical
  rw [allStars, List.map_append, List.sum_append, point_deg, line_deg, incid_card_sum]
  let Qin := fun p l => I p l ∧ Fin.castAdd M p ∈ cover
  let Qout := fun p l => I p l ∧ Fin.castAdd M p ∉ cover
  have hQin : DecidableRel Qin := inferInstance
  have hQout : DecidableRel Qout := inferInstance
  have hsplit : ∀ p : Fin N,
      (Finset.univ.filter (fun l : Fin M => I p l)).card =
        (Finset.univ.filter (fun l : Fin M => Qin p l)).card +
        (Finset.univ.filter (fun l : Fin M => Qout p l)).card := by
    intro p
    let A := Finset.univ.filter (fun l : Fin M => Qin p l)
    let B := Finset.univ.filter (fun l : Fin M => Qout p l)
    have hdis : Disjoint A B := by
      refine Finset.disjoint_left.mpr ?_
      intro l hA hB
      simp only [A, B, Qin, Qout, Finset.mem_filter, Finset.mem_univ, true_and] at hA hB
      exact hB.2 hA.2
    have hun : A ∪ B = Finset.univ.filter (fun l : Fin M => I p l) := by
      ext l
      simp only [Finset.mem_union, A, B, Qin, Qout, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨hI, _⟩ | ⟨hI, _⟩) <;> exact hI
      · intro hI
        by_cases hc : Fin.castAdd M p ∈ cover
        · exact Or.inl ⟨hI, hc⟩
        · exact Or.inr ⟨hI, hc⟩
    have hcard := Finset.card_union_of_disjoint hdis
    rw [hun] at hcard
    exact hcard
  have hsum : (∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => I p l)).card) =
      (∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => Qin p l)).card) +
      (∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => Qout p l)).card) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => hsplit p
  have hpt : (∑ p ∈ pointOwners cover I, (Finset.univ.filter (fun l : Fin M => I p l)).card) =
      ∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => Qin p l)).card := by
    let s := Finset.univ.filter (fun p : Fin N => Fin.castAdd M p ∈ cover)
    have hsub : pointOwners cover I ⊆ s := by
      intro p hp
      have hp' := (point_owner_iff cover I p).1 hp
      simpa [s] using hp'.1
    have hzero : ∀ p ∈ s, p ∉ pointOwners cover I →
        (Finset.univ.filter (fun l : Fin M => I p l)).card = 0 := by
      intro p hs hp
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [Finset.card_eq_zero]
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hI
        exact False.elim (hp ((point_owner_iff cover I p).2 ⟨hs, l, hI⟩))
      · intro hempty
        exact False.elim (Finset.notMem_empty l hempty)
    have hown := Finset.sum_subset hsub hzero
    have hsift : (∑ p ∈ s, (Finset.univ.filter (fun l : Fin M => I p l)).card) =
        ∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => Qin p l)).card := by
      rw [show s = Finset.univ.filter (fun p : Fin N => Fin.castAdd M p ∈ cover) from rfl,
        Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro p _
      by_cases hc : Fin.castAdd M p ∈ cover
      · simp only [hc, ite_true]
        apply congrArg Finset.card
        ext l
        simp [Qin, hc]
      · simp [Qin, hc]
    exact hown.trans hsift
  have hout : (∑ l ∈ lineOwners cover I,
      (Finset.univ.filter (fun p : Fin N => I p l ∧ Fin.castAdd M p ∉ cover)).card) =
      ∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => Qout p l)).card := by
    have hrows := rowCard Qout
    have hcols := colCard Qout
    have hzero : ∀ l ∈ (Finset.univ : Finset (Fin M)), l ∉ lineOwners cover I →
        (Finset.univ.filter (fun p : Fin N => Qout p l)).card = 0 := by
      intro l _ hl
      rw [Finset.card_eq_zero]
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Qout]
      constructor
      · intro hp
        have hline : Fin.natAdd N l ∈ cover := by
          rcases hcover p l hp.1 with h | h
          · exact absurd h hp.2
          · exact h
        exact False.elim (hl ((line_owner_iff cover I l).2 ⟨hline, p, hp.1, hp.2⟩))
      · intro hempty
        exact False.elim (Finset.notMem_empty p hempty)
    have hsubsum := Finset.sum_subset (Finset.subset_univ (lineOwners cover I)) hzero
    exact hsubsum.trans (hcols.symm.trans hrows)
  rw [hpt, hsum]
  refine congrArg (fun n => (∑ p : Fin N, (Finset.univ.filter (fun l : Fin M => Qin p l)).card) + n) ?_
  convert hout

theorem in_ico {N M : ℕ} (l : Fin M) : lineWire N l ∈ Finset.Ico N (N + M) := by
  have := l.isLt
  simp [lineWire, Finset.mem_Ico]

theorem in_range {N : ℕ} (p : Fin N) : pointWire p ∈ Finset.range N := by
  simp [pointWire, Finset.mem_range, p.isLt]

theorem wire_line {N M : ℕ} (gs : List Gate) (root : ℕ) (leaves : List ℕ)
    (hroot : root ∈ Finset.Ico N (N + M)) (hleaves : ∀ a ∈ leaves, a ∈ Finset.Ico N (N + M)) :
    (orAcc (N + M) leaves gs root).2.1 ∈
      (classes N M (gs ++ addedOrs (N + M) gs.length root leaves)).2 := by
  rcases orAcc_root_mem (N + M) leaves gs root with h | h
  · rw [h]
    exact (base_kept N M (gs ++ addedOrs (N + M) gs.length root leaves)).2 hroot
  · obtain ⟨i, hi, hw⟩ := orAcc_wire_idx (N + M) leaves gs root _ h
    have hcl := classes_closed N M gs
    have hmem := chain_out (N + M) (classes N M gs).1 (classes N M gs).2 gs.length root leaves
      ((base_kept N M gs).2 hroot)
      (fun a ha => (base_kept N M gs).2 (hleaves a ha))
      (not_point N M gs (classes N M gs).1 root hcl.1 (by simpa [Finset.mem_Ico] using hroot))
      (fun a ha => not_point N M gs (classes N M gs).1 a hcl.1 (by simpa [Finset.mem_Ico] using hleaves a ha))
      (fun j hj => by
        have hnf := not_fresh N M gs (classes N M gs).1 (gs.length + j) hcl.1 (by omega)
        simpa [Nat.add_assoc] using hnf)
      i (by rw [added_len]; exact hi)
    have happ := fold_append (N + M) (Finset.range N) (Finset.Ico N (N + M)) 0 gs
      (addedOrs (N + M) gs.length root leaves)
    simpa [classes, happ, hw] using hmem

theorem wire_point {N M : ℕ} (gs : List Gate) (root : ℕ) (leaves : List ℕ)
    (hroot : root ∈ Finset.range N) (hleaves : ∀ a ∈ leaves, a ∈ Finset.range N) :
    (orAcc (N + M) leaves gs root).2.1 ∈
      (classes N M (gs ++ addedOrs (N + M) gs.length root leaves)).1 := by
  rcases orAcc_root_mem (N + M) leaves gs root with h | h
  · rw [h]
    exact (base_kept N M (gs ++ addedOrs (N + M) gs.length root leaves)).1 hroot
  · obtain ⟨i, hi, hw⟩ := orAcc_wire_idx (N + M) leaves gs root _ h
    have hmem := chain_in (N + M) (classes N M gs).1 (classes N M gs).2 gs.length root leaves
      ((base_kept N M gs).1 hroot)
      (fun a ha => (base_kept N M gs).1 (hleaves a ha))
      i (by rw [added_len]; exact hi)
    have happ := fold_append (N + M) (Finset.range N) (Finset.Ico N (N + M)) 0 gs
      (addedOrs (N + M) gs.length root leaves)
    simpa [classes, happ, hw] using hmem

def AndSplit (N M : ℕ) (gs : List Gate) : Prop :=
  ∀ k, (hk : k < gs.length) → (gs[k]'hk).op = GateOp.and →
    ∃ a b, (gs[k]'hk).inputs = [a, b] ∧ a ∈ (classes N M gs).2 ∧ b ∈ (classes N M gs).1

theorem split_nil (N M : ℕ) : AndSplit N M [] := by
  intro k hk
  simp at hk

theorem split_prefix {N M : ℕ} {gs extra : List Gate} (h : AndSplit N M gs) (k : ℕ)
    (hk : k < (gs ++ extra).length) (hk0 : k < gs.length)
    (hop : ((gs ++ extra)[k]'hk).op = GateOp.and) :
    ∃ a b, ((gs ++ extra)[k]'hk).inputs = [a, b] ∧
      a ∈ (classes N M (gs ++ extra)).2 ∧ b ∈ (classes N M (gs ++ extra)).1 := by
  have hget : ((gs ++ extra)[k]'hk) = gs[k] := by
    simp [List.getElem_append, hk0]
  rw [hget] at hop ⊢
  obtain ⟨a, b, hin, ha, hb⟩ := h k hk0 hop
  have hsub := classes_grow (N := N) (M := M) gs extra
  exact ⟨a, b, hin, hsub.2 ha, hsub.1 hb⟩

theorem split_block {N M : ℕ} (gs ors : List Gate) (gate : Gate) (a b : ℕ)
    (h : AndSplit N M gs) (hgate : gate = ⟨GateOp.and, [a, b]⟩)
    (hors : ∀ j, (hj : j < ors.length) → (ors[j]'hj).op = GateOp.or)
    (ha : a ∈ (classes N M (gs ++ ors ++ [gate])).2)
    (hb : b ∈ (classes N M (gs ++ ors ++ [gate])).1) :
    AndSplit N M (gs ++ ors ++ [gate]) := by
  intro k hk hop
  by_cases hk0 : k < gs.length
  · have hassoc : gs ++ ors ++ [gate] = gs ++ (ors ++ [gate]) := List.append_assoc _ _ _
    have hk' : k < (gs ++ (ors ++ [gate])).length := by
      simpa [hassoc, List.length_append] using hk
    have hop' : ((gs ++ (ors ++ [gate]))[k]'hk').op = GateOp.and := by
      simpa [hassoc] using hop
    obtain ⟨a', b', hin, ha', hb'⟩ := split_prefix h k hk' hk0 hop'
    refine ⟨a', b', ?_, ?_, ?_⟩
    · simpa [hassoc] using hin
    · simpa [hassoc] using ha'
    · simpa [hassoc] using hb'
  · by_cases hk1 : k < (gs ++ ors).length
    · have hj : k - gs.length < ors.length := by simp [List.length_append] at hk1; omega
      have hop' : (ors[k - gs.length]'hj).op = GateOp.or := hors _ hj
      have hget : ((gs ++ ors ++ [gate])[k]'hk) = ors[k - gs.length] := by
        simp [List.getElem_append, hk0, hj]
      rw [hget, hop'] at hop
      cases hop
    · have hlen : k = (gs ++ ors).length := by
        have hfull : (gs ++ ors ++ [gate]).length = (gs ++ ors).length + 1 := by
          simp [List.length_append, List.length_singleton]
          exact (Nat.add_assoc gs.length ors.length 1).symm
        have hsuml : (gs ++ ors).length = gs.length + ors.length := by
          simp [List.length_append]
        simp only [hfull, hsuml] at hk
        omega
      subst hlen
      rw [get_last (gs ++ ors) gate]
      refine ⟨a, b, ?_, ha, hb⟩
      simp [hgate]

theorem split_ors {N M : ℕ} (gs ors : List Gate) (h : AndSplit N M gs)
    (hors : ∀ j, (hj : j < ors.length) → (ors[j]'hj).op = GateOp.or) :
    AndSplit N M (gs ++ ors) := by
  intro k hk hop
  by_cases hk0 : k < gs.length
  · exact split_prefix h k hk hk0 hop
  · have hj : k - gs.length < ors.length := by simp [List.length_append] at hk; omega
    have hop' : (ors[k - gs.length]'hj).op = GateOp.or := hors _ hj
    have hget : ((gs ++ ors)[k]'hk) = ors[k - gs.length] := by
      simp [List.getElem_append, hk0]
    rw [hget, hop'] at hop
    cases hop

theorem leaves_line {N M : ℕ} (ls : List (Fin M)) :
    ∀ a ∈ ls.map (lineWire N), a ∈ Finset.Ico N (N + M) := by
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨l, _, rfl⟩ := ha
  exact in_ico l

theorem leaves_point {N : ℕ} (ps : List (Fin N)) :
    ∀ a ∈ ps.map pointWire, a ∈ Finset.range N := by
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨p, _, rfl⟩ := ha
  exact in_range p

theorem split_one {N M : ℕ} (gs : List Gate) (s : Star N M) (h : AndSplit N M gs) :
    AndSplit N M (oneStar gs s).1 := by
  cases s with
  | pt p ls hne =>
      let root := lineWire N (ls.head hne)
      let leaves := ls.tail.map (lineWire N)
      let ors := addedOrs (N + M) gs.length root leaves
      let a := (orAcc (N + M) leaves gs root).2.1
      let gate : Gate := ⟨GateOp.and, [a, pointWire p]⟩
      have ha0 := wire_line gs root leaves (in_ico (ls.head hne)) (leaves_line ls.tail)
      have ha := (classes_grow (N := N) (M := M) (gs ++ ors) [gate]).2 ha0
      have hb := (base_kept N M (gs ++ ors ++ [gate])).1 (in_range p)
      have hors : ∀ j, (hj : j < ors.length) → (ors[j]'hj).op = GateOp.or := by
        intro j hj
        exact (added_at (N + M) gs.length root leaves j hj).1
      have htail : ls.tail.map (lineWire N) = (ls.map (lineWire N)).tail := by
        cases ls with
        | nil => exact (hne rfl).elim
        | cons _ _ => simp
      have hform : (oneStar gs (Star.pt p ls hne)).1 = gs ++ ors ++ [gate] := by
        simp only [oneStar, addAnd, orAcc_added, List.append_assoc]
        rfl
      rw [hform]
      exact split_block gs ors gate a (pointWire p) h rfl hors ha hb
  | ln l ps hne =>
      let root := pointWire (ps.head hne)
      let leaves := ps.tail.map pointWire
      let ors := addedOrs (N + M) gs.length root leaves
      let b := (orAcc (N + M) leaves gs root).2.1
      let gate : Gate := ⟨GateOp.and, [lineWire N l, b]⟩
      have hb0 := wire_point (N := N) (M := M) gs root leaves (in_range (ps.head hne))
        (leaves_point (N := N) ps.tail)
      have hb := (classes_grow (N := N) (M := M) (gs ++ ors) [gate]).1 hb0
      have ha := (base_kept N M (gs ++ ors ++ [gate])).2 (in_ico l)
      have hors : ∀ j, (hj : j < ors.length) → (ors[j]'hj).op = GateOp.or := by
        intro j hj
        exact (added_at (N + M) gs.length root leaves j hj).1
      have htail : ps.tail.map pointWire = (ps.map pointWire).tail := by
        cases ps with
        | nil => exact (hne rfl).elim
        | cons _ _ => simp
      have hform : (oneStar gs (Star.ln l ps hne)).1 = gs ++ ors ++ [gate] := by
        simp only [oneStar, addAnd, orAcc_added, List.append_assoc]
        rfl
      rw [hform]
      exact split_block gs ors gate (lineWire N l) b h rfl hors ha hb

theorem split_from {N M : ℕ} (gs : List Gate) (h : AndSplit N M gs) (stars : List (Star N M)) :
    AndSplit N M (foldStars gs stars).1 := by
  induction stars generalizing gs with
  | nil => simpa [foldStars] using h
  | cons s rest ih =>
      unfold foldStars
      dsimp only
      exact ih _ (split_one gs s h)

theorem split_finish {N M : ℕ} (stars : List (Star N M)) :
    AndSplit N M (finishGates stars).1 := by
  have hfold : AndSplit N M (foldStars ([] : List Gate) stars).1 :=
    split_from [] (split_nil N M) stars
  by_cases hstars : stars = []
  · subst hstars
    simpa [finishGates, foldStars] using split_nil N M
  · have hlen := foldStars_len ([] : List Gate) stars
    have hne : (foldStars [] stars).2 ≠ [] := by
      intro h
      have : stars.length = 0 := by simpa [h] using hlen.symm
      exact hstars (List.eq_nil_of_length_eq_zero this)
    simp only [finishGates, hne, dite_false]
    have hors : ∀ j, (hj : j < (addedOrs (N + M) (foldStars [] stars).1.length
        ((foldStars [] stars).2.head hne) (foldStars [] stars).2.tail).length) →
        ((addedOrs (N + M) (foldStars [] stars).1.length ((foldStars [] stars).2.head hne)
          (foldStars [] stars).2.tail)[j]'hj).op = GateOp.or := by
      intro j hj
      exact (added_at (N + M) (foldStars [] stars).1.length ((foldStars [] stars).2.head hne)
        (foldStars [] stars).2.tail j hj).1
    have hlist := orAcc_added (N + M) (foldStars [] stars).2.tail (foldStars [] stars).1
      ((foldStars [] stars).2.head hne)
    rw [hlist]
    exact split_ors _ _ hfold hors

end PEqualNP.Outside.L_meta_3493

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3493

theorem PEqualNP.Outside.L_meta_3493 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : Finset (Fin (x1 + x2))), (∀ (x6 : Fin x1) (x7 : Fin x2), x3 x6 x7 → Fin.castAdd x2 x6 ∈ x5 ∨ Fin.natAdd x1 x7 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x7.size ≤ (PEqualNP.ReadTwo.incid x3).card + x5.card - (1 : ℕ) ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x1 + x2 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).inputs = [x13, x14] ∧ x13 ∈ x9 ∧ x14 ∈ x8 := by
  intro x1 x2 x3 _ x5 hcover
  let stars := allStars x5 x3
  let C : Circuit := ⟨(finishGates stars).1, (finishGates stars).2⟩
  let x8 := (classes x1 x2 C.gates).1
  let x9 := (classes x1 x2 C.gates).2
  refine ⟨C, x8, x9, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ao2 C (good_finish stars)
  · intro x
    rw [← bit_fun, finish_bit]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff]
    exact (stars_hit x5 x3 hcover x)
  · rw [show C.size = (finishGates stars).1.length from rfl, finish_count, deg_card x5 x3 hcover]
    exact Nat.sub_le_sub_right (Nat.add_le_add_left (stars_le x5 x3) (PEqualNP.ReadTwo.incid x3).card) 1
  · intro w hw
    rcases (classes_closed x1 x2 C.gates).1 w hw with h | ⟨k, hk, hwk, hop, hin⟩
    · exact Or.inl h
    · refine Or.inr ⟨k, hk, hwk, ?_, ?_⟩
      · have hgate : gateAt C k = C.gates[k] := by
          simp [gateAt, hk]
        simpa [hgate] using hop
      · intro i hi
        have hgate : gateAt C k = C.gates[k] := by
          simp [gateAt, hk]
        exact hin i (by simpa [hgate] using hi)
  · intro w hw
    rcases (classes_closed x1 x2 C.gates).2 w hw with h | ⟨k, hk, hwk, hop, hin⟩
    · exact Or.inl h
    · refine Or.inr ⟨k, hk, hwk, ?_, ?_⟩
      · have hgate : gateAt C k = C.gates[k] := by
          simp [gateAt, hk]
        simpa [hgate] using hop
      · intro i hi
        have hgate : gateAt C k = C.gates[k] := by
          simp [gateAt, hk]
        exact hin i (by simpa [hgate] using hi)
  · intro k hk hop
    have hsp := split_finish (N := x1) (M := x2) stars k hk
    have hgate : gateAt C k = C.gates[k] := by
      simp [gateAt, hk]
    rw [hgate] at hop
    obtain ⟨a, b, hin, ha, hb⟩ := hsp hop
    exact ⟨a, b, by simpa [hgate] using hin, ha, hb⟩
