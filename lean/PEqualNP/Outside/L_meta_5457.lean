import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5457

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 8

private def ones : Word := BitVec.allOnes 8
private def inputs : List Word := [133, 30, 46, 200, 240]
private def target : Word := 188

private def candidatesWith (a : Word) (bs : List Word) : List Word :=
  (~~~a) :: bs.flatMap (fun b => [a &&& b, a ||| b])

private def candidates : List Word → List Word
  | [] => []
  | a :: bs => candidatesWith a bs ++ candidates bs

private def present (bs : List Word) (v : Word) : Bool :=
  v == 0 || v == ones || bs.contains v

private def insertWire (bs : List Word) (v : Word) : List Word :=
  if present bs v then bs else v :: bs

private def two (bs : List Word) : Bool :=
  let low := bs.filter (fun v => v &&& target == v)
  let high := bs.filter (fun v => v ||| target == v)
  bs.contains target || (candidates bs).any (fun v =>
    v == target || (~~~v) == target ||
    low.any (fun a => (v ||| a) == target) ||
    high.any (fun a => (v &&& a) == target))

private def inOrder (v : Word) : List Word → List Word
  | [] => [v]
  | a :: rest =>
    if v.toNat ≤ a.toNat then v :: a :: rest else a :: inOrder v rest

private def collapse {A : Type} [BEq A] : List A → List A
  | [] => []
  | a :: rest =>
    match rest with
    | [] => [a]
    | b :: _ => if a == b then collapse rest else a :: collapse rest

private def bankKey (bs : List Word) : ℕ :=
  (bs.filter fun v => !(inputs.contains v)).foldl (fun key v => key * 256 + v.toNat) 1

private def byBits : Nat → List (ℕ × List Word) → List (ℕ × List Word)
  | 0, items => items
  | _+1, [] => []
  | _+1, [a] => [a]
  | k+1, a :: b :: rest =>
    let items := a :: b :: rest
    byBits k (items.filter fun p => !(p.1.testBit k)) ++
      byBits k (items.filter fun p => p.1.testBit k)

private def compact (banks : List (List Word)) : List (List Word) :=
  let keyed := banks.map fun bs => (bankKey bs, bs)
  (collapse (byBits 25 keyed)).map Prod.snd

private def extensions (bs : List Word) : List (List Word) :=
  bs :: ((candidates bs).filter (fun v => !(present bs v))).map (fun v => inOrder v bs)

private def advance (banks : List (List Word)) : List (List Word) :=
  compact (banks.flatMap extensions)

private def explore : Nat → List (List Word) → Bool
  | 0, banks => banks.any two
  | k+1, banks => explore k (advance banks)

private def initialBank : List Word := [30, 46, 133, 200, 240]

private theorem present_iff (bs : List Word) (v : Word) :
    present bs v = true ↔ v = 0 ∨ v = ones ∨ v ∈ bs := by
  simp [present, or_assoc]

private theorem mem_inOrder (bs : List Word) (v u : Word) :
    u ∈ inOrder v bs ↔ u = v ∨ u ∈ bs := by
  induction bs with
  | nil => simp [inOrder]
  | cons a rest ih =>
    rw [inOrder]
    split
    · simp only [List.mem_cons]
    · simp only [List.mem_cons, ih]
      tauto

private theorem inOrder_present {bs : List Word} {v u : Word}
    (h : present (v :: bs) u = true) : present (inOrder v bs) u = true := by
  rw [present_iff] at h ⊢
  simpa only [mem_inOrder, List.mem_cons] using h

private theorem mem_collapse {A : Type} [BEq A] [LawfulBEq A] (xs : List A) (u : A) :
    u ∈ collapse xs ↔ u ∈ xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      rw [collapse]
      by_cases h : a = b
      · subst b
        simp only [beq_self_eq_true, ite_true, ih, List.mem_cons]
        tauto
      · have hn : (a == b) = false := Bool.eq_false_iff.mpr (h ∘ beq_iff_eq.mp)
        simp only [hn, Bool.false_eq_true, ite_false, List.mem_cons, ih]

private theorem mem_byBits (k : Nat) (xs : List (ℕ × List Word)) (p : ℕ × List Word) :
    p ∈ byBits k xs ↔ p ∈ xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b rest =>
        rw [byBits, List.mem_append, ih, ih]
        simp only [List.mem_filter]
        cases p.1.testBit k <;> simp

private theorem mem_compact {banks : List (List Word)} {bs : List Word} :
    bs ∈ compact banks ↔ bs ∈ banks := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    rw [mem_collapse, mem_byBits] at hp
    obtain ⟨b, hb, hp⟩ := List.mem_map.mp hp
    rw [← hp]
    exact hb
  · intro h
    apply List.mem_map.mpr
    refine ⟨(bankKey bs, bs), ?_, rfl⟩
    rw [mem_collapse, mem_byBits]
    exact List.mem_map.mpr ⟨bs, h, rfl⟩

private theorem old_in_advance {banks : List (List Word)} {bs : List Word}
    (h : bs ∈ banks) : bs ∈ advance banks :=
  mem_compact.mpr (List.mem_flatMap.mpr ⟨bs, h, by simp [extensions]⟩)

private theorem new_in_advance {banks : List (List Word)} {bs : List Word} {v : Word}
    (h : bs ∈ banks) (cv : v ∈ candidates bs) (fresh : present bs v = false) :
    inOrder v bs ∈ advance banks := by
  apply mem_compact.mpr
  apply List.mem_flatMap.mpr
  refine ⟨bs, h, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨v, ?_, rfl⟩)⟩
  simp [cv, fresh]

private theorem present_cons {bs : List Word} {u : Word} (v : Word)
    (h : present bs u = true) : present (v :: bs) u = true := by
  apply (present_iff _ _).2
  rcases (present_iff _ _).1 h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

private theorem retains {bs : List Word} {u : Word} (v : Word)
    (h : present bs u = true) : present (insertWire bs v) u = true := by
  unfold insertWire
  split
  · exact h
  · exact present_cons v h

private theorem inserted (bs : List Word) (v : Word) :
    present (insertWire bs v) v = true := by
  unfold insertWire
  split
  · assumption
  · exact (present_iff _ _).2 (Or.inr (Or.inr (by simp)))

private theorem not_candidate {bs : List Word} {a : Word} (ha : a ∈ bs) :
    ~~~a ∈ candidates bs := by
  induction bs with
  | nil => simp at ha
  | cons b bs ih =>
    rw [candidates, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inl (by simp [candidatesWith])
    · exact Or.inr (ih ha)

private theorem pair_with {bs : List Word} (a : Word) {b : Word} (hb : b ∈ bs) :
    (a &&& b) ∈ candidatesWith a bs ∧ (a ||| b) ∈ candidatesWith a bs := by
  constructor <;> apply List.mem_cons_of_mem <;>
    exact List.mem_flatMap.mpr ⟨b, hb, by simp⟩

private theorem pair_candidate {bs : List Word} {a b : Word} (ha : a ∈ bs)
    (hb : b ∈ bs) (hne : a ≠ b) :
    (a &&& b) ∈ candidates bs ∧ (a ||| b) ∈ candidates bs := by
  induction bs with
  | nil => simp at ha
  | cons c bs ih =>
    have ha' : a = c ∨ a ∈ bs := List.mem_cons.mp ha
    have hb' : b = c ∨ b ∈ bs := List.mem_cons.mp hb
    rcases ha' with ea | haTail <;> rcases hb' with eb | hbTail
    · exact (hne (ea.trans eb.symm)).elim
    · subst c
      obtain ⟨h₁, h₂⟩ := pair_with (bs := bs) a hbTail
      exact ⟨List.mem_append_left _ h₁, List.mem_append_left _ h₂⟩
    · subst c
      obtain ⟨h₁, h₂⟩ := pair_with (bs := bs) b haTail
      rw [BitVec.and_comm, BitVec.or_comm]
      exact ⟨List.mem_append_left _ h₁, List.mem_append_left _ h₂⟩
    · obtain ⟨h₁, h₂⟩ := ih haTail hbTail
      exact ⟨List.mem_append_right _ h₁, List.mem_append_right _ h₂⟩

private def choice (bs : List Word) (v : Word) : Prop :=
  present bs v = true ∨ v ∈ candidates bs

private theorem choice_not {bs : List Word} {a : Word} (h : present bs a = true) :
    choice bs (~~~a) := by
  rcases (present_iff _ _).1 h with rfl | rfl | h
  · exact Or.inl ((present_iff _ _).2 (Or.inr (Or.inl (by decide +kernel))))
  · exact Or.inl ((present_iff _ _).2 (Or.inl (by decide +kernel)))
  · exact Or.inr (not_candidate h)

private theorem choice_both {bs : List Word} {a b : Word}
    (ha : present bs a = true) (hb : present bs b = true) :
    choice bs (a &&& b) ∧ choice bs (a ||| b) := by
  have zero : choice bs 0 := Or.inl ((present_iff _ _).2 (Or.inl rfl))
  have full : choice bs ones := Or.inl ((present_iff _ _).2 (Or.inr (Or.inl rfl)))
  have ca : choice bs a := Or.inl ha
  have cb : choice bs b := Or.inl hb
  rcases (present_iff _ _).1 ha with rfl | rfl | ha'
  · simpa using And.intro zero cb
  · simpa only [ones, BitVec.allOnes_and, BitVec.allOnes_or] using And.intro cb full
  · rcases (present_iff _ _).1 hb with rfl | rfl | hb'
    · simpa using And.intro zero ca
    · simpa only [ones, BitVec.and_allOnes, BitVec.or_allOnes] using And.intro ca full
    · by_cases he : a = b
      · subst b
        simpa using And.intro ca ca
      · obtain ⟨h₁, h₂⟩ := pair_candidate ha' hb' he
        exact ⟨Or.inr h₁, Or.inr h₂⟩

private theorem two_present {bs : List Word} (h : present bs target = true) :
    two bs = true := by
  rcases (present_iff _ _).1 h with he | he | hm
  · exact ((by decide : target ≠ 0) he).elim
  · exact ((by decide : target ≠ ones) he).elim
  · simp [two, hm]

private theorem two_witness {bs : List Word} {v : Word} (hv : v ∈ candidates bs)
    (h : v = target ∨ ~~~v = target ∨
      (∃ a ∈ bs, v ||| a = target) ∨ (∃ a ∈ bs, v &&& a = target)) :
    two bs = true := by
  apply Bool.or_eq_true_iff.mpr
  right
  apply List.any_eq_true.mpr
  refine ⟨v, hv, ?_⟩
  rcases h with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩
  · simp [h]
  · simp [h]
  · have low : a &&& target = a := by
      rw [← h]
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
      cases a.getLsbD i <;> cases v.getLsbD i <;> rfl
    have mem : a ∈ bs.filter (fun val => val &&& target == val) := by simp [ha, low]
    have hit : (bs.filter (fun val => val &&& target == val)).any
        (fun val => (v ||| val) == target) = true :=
      List.any_eq_true.mpr ⟨a, mem, beq_iff_eq.mpr h⟩
    simp [hit]
  · have high : a ||| target = a := by
      rw [← h]
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
      cases a.getLsbD i <;> cases v.getLsbD i <;> rfl
    have mem : a ∈ bs.filter (fun val => val ||| target == val) := by simp [ha, high]
    have hit : (bs.filter (fun val => val ||| target == val)).any
        (fun val => (v &&& val) == target) = true :=
      List.any_eq_true.mpr ⟨a, mem, beq_iff_eq.mpr h⟩
    simp [hit]

private theorem two_choice {bs : List Word} (h : choice bs target) : two bs = true := by
  rcases h with h | h
  · exact two_present h
  · exact two_witness h (Or.inl rfl)

private theorem two_steps {bs : List Word} {v : Word} (hv : choice bs v)
    (h : choice (insertWire bs v) target) : two bs = true := by
  unfold insertWire at h
  split at h
  · exact two_choice h
  next hp =>
    have hv' : v ∈ candidates bs := hv.resolve_left hp
    rcases h with h | h
    · rcases (present_iff _ _).1 h with h | h | h
      · exact ((by decide : target ≠ 0) h).elim
      · exact ((by decide : target ≠ ones) h).elim
      · rcases List.mem_cons.mp h with h | h
        · exact two_witness hv' (Or.inl h.symm)
        · exact two_present ((present_iff _ _).2 (Or.inr (Or.inr h)))
    · rw [candidates, List.mem_append] at h
      rcases h with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact two_witness hv' (Or.inr (Or.inl h.symm))
        · obtain ⟨a, ha, h⟩ := List.mem_flatMap.mp h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h
          · exact two_witness hv' (Or.inr (Or.inr (Or.inr ⟨a, ha, h.symm⟩)))
          · exact two_witness hv' (Or.inr (Or.inr (Or.inl ⟨a, ha, h.symm⟩)))
      · exact two_choice (Or.inr h)

private theorem choice_of_insert {bs : List Word} {v u : Word} (hv : choice bs v)
    (h : present (insertWire bs v) u = true) : choice bs u := by
  unfold insertWire at h
  split at h
  · exact Or.inl h
  · rcases (present_iff _ _).1 h with h | h | h
    · exact Or.inl ((present_iff _ _).2 (Or.inl h))
    · exact Or.inl ((present_iff _ _).2 (Or.inr (Or.inl h)))
    · rcases List.mem_cons.mp h with rfl | h
      · exact hv
      · exact Or.inl ((present_iff _ _).2 (Or.inr (Or.inr h)))

private def wordOp (op : GateOp) (vs : List Word) : Word :=
  match op with
  | .and => vs.foldr (· &&& ·) ones
  | .or  => vs.foldr (· ||| ·) 0
  | .not => ~~~(vs.headD 0)
  | _ => 0

private def allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private def reads (bank wires : List Word) : Prop :=
  ∀ v ∈ wires, present bank v = true

private theorem read_wire {bank wires : List Word} (h : reads bank wires) (i : ℕ) :
    present bank (wires.getD i 0) = true := by
  cases hi : wires[i]? with
  | none =>
    rw [List.getD_eq_getElem?_getD, hi]
    exact (present_iff _ _).2 (Or.inl rfl)
  | some v =>
    rw [List.getD_eq_getElem?_getD, hi]
    exact h v (List.mem_of_getElem? hi)

private theorem choice_op {bank : List Word} (g : Gate) (vs : List Word)
    (ha : allowed g) (hlen : vs.length ≤ 2) (hv : reads bank vs) :
    choice bank (wordOp g.op vs) := by
  rcases vs with _ | ⟨a, vs⟩
  · rcases ha.1 with h | h | h <;> simp [h, wordOp, choice, present, ones]
  have hA : present bank a = true := hv a (by simp)
  rcases vs with _ | ⟨b, vs⟩
  · rcases ha.1 with h | h | h
    · exact Or.inl (by simpa only [h, wordOp, List.foldr_cons, List.foldr_nil, ones,
        BitVec.and_allOnes] using hA)
    · exact Or.inl (by simpa [h, wordOp] using hA)
    · simpa [h, wordOp] using choice_not hA
  · have hB : present bank b = true := hv b (by simp)
    have none : vs = [] := List.length_eq_zero_iff.mp (by
      simp only [List.length_cons] at hlen
      omega)
    subst vs
    rcases ha.1 with h | h | h
    · simpa only [h, wordOp, List.foldr_cons, List.foldr_nil, ones, BitVec.and_allOnes]
        using (choice_both hA hB).1
    · simpa [h, wordOp] using (choice_both hA hB).2
    · simpa [h, wordOp] using choice_not hA

private def value (wires : List Word) (g : Gate) : Word :=
  wordOp g.op (g.inputs.map fun i => wires.getD i 0)

private def appendGate (wires : List Word) (g : Gate) : List Word :=
  wires ++ [value wires g]

private theorem gate_choice {bank wires : List Word} (h : reads bank wires)
    (g : Gate) (ha : allowed g) : choice bank (value wires g) := by
  unfold value
  apply choice_op g _ ha (by simpa using ha.2)
  intro v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  exact read_wire h i

private theorem next_reads {bank wires : List Word} (h : reads bank wires) (g : Gate) :
    reads (insertWire bank (value wires g)) (appendGate wires g) := by
  intro v hv
  simp only [appendGate, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | rfl
  · exact retains _ (h v hv)
  · exact inserted _ _

private theorem final_two {bank wires : List Word} (h : reads bank wires)
    (gs : List Gate) (hk : gs.length ≤ 2) (hg : ∀ g ∈ gs, allowed g) (out : ℕ)
    (ans : (gs.foldl appendGate wires).getD out 0 = target) : two bank = true := by
  cases gs with
  | nil =>
    have ht := read_wire h out
    change wires.getD out 0 = target at ans
    rw [ans] at ht
    exact two_present ht
  | cons first rest =>
    have fc := gate_choice h first (hg _ (by simp))
    have fnext := next_reads h first
    apply two_steps fc
    cases rest with
    | nil =>
      have ht := read_wire fnext out
      change (appendGate wires first).getD out 0 = target at ans
      rw [ans] at ht
      exact Or.inl ht
    | cons second tail =>
      have empty : tail = [] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons] at hk
        omega)
      subst tail
      have sc := gate_choice fnext second (hg _ (by simp))
      have ht := read_wire (next_reads fnext second) out
      change (appendGate (appendGate wires first) second).getD out 0 = target at ans
      rw [ans] at ht
      exact choice_of_insert sc ht

private theorem search_complete (depth : ℕ) (banks : List (List Word)) (bank wires : List Word)
    (hb : bank ∈ banks) (h : reads bank wires) (gs : List Gate) (hk : gs.length ≤ depth + 2)
    (hg : ∀ g ∈ gs, allowed g) (out : ℕ)
    (ans : (gs.foldl appendGate wires).getD out 0 = target) :
    explore depth banks = true := by
  induction depth generalizing banks bank wires gs with
  | zero => exact List.any_eq_true.mpr ⟨bank, hb, final_two h gs hk hg out ans⟩
  | succ depth ih =>
    change explore depth (advance banks) = true
    cases gs with
    | nil =>
      exact ih _ bank wires (old_in_advance hb) h [] (by simp) hg ans
    | cons first rest =>
      have hc := gate_choice h first (hg _ (by simp))
      have hrest : ∀ g ∈ rest, allowed g :=
        fun g hm => hg g (List.mem_cons_of_mem _ hm)
      change (rest.foldl appendGate (appendGate wires first)).getD out 0 = target at ans
      have bound : rest.length ≤ depth + 2 := by simp at hk; omega
      by_cases hp : present bank (value wires first) = true
      · have hnext : reads bank (appendGate wires first) := by
          simpa only [insertWire, hp, ite_true] using next_reads h first
        exact ih _ bank _ (old_in_advance hb) hnext rest bound hrest ans
      · have present_false : present bank (value wires first) = false :=
          Bool.eq_false_iff.mpr hp
        have good := hc.resolve_left hp
        have hnext : reads (value wires first :: bank) (appendGate wires first) := by
          simpa only [insertWire, present_false, Bool.false_eq_true, ite_false]
            using next_reads h first
        have after : reads (inOrder (value wires first) bank) (appendGate wires first) :=
          fun u hu => inOrder_present (hnext u hu)
        exact ih _ _ _ (new_in_advance hb good present_false) after rest bound hrest ans

private def bit (j : Fin 8) (v : Word) : Bool := v.getLsbD j.val

private theorem read_bits (j : Fin 8) (w : List Word) (i : ℕ) :
    (w.map (bit j)).getD i false = bit j (w.getD i 0) := by
  simpa [bit] using (List.getD_map (l := w) (d := (0 : Word)) (n := i) (bit j))

private def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem bit_op (j : Fin 8) (op : GateOp) (vs : List Word)
    (h : op = .and ∨ op = .or ∨ op = .not) :
    bit j (wordOp op vs) = op.eval (vs.map (bit j)) := by
  rcases h with rfl | rfl | rfl
  · induction vs with
    | nil =>
      change (BitVec.allOnes 8).getLsbD j.val = true
      simp only [BitVec.getLsbD_allOnes, decide_eq_true_eq.mpr j.isLt]
    | cons a rest ih =>
      simp only [wordOp, List.foldr_cons, List.map_cons, GateOp.eval, List.all_cons] at ih ⊢
      simp only [bit, BitVec.getLsbD_and] at ih ⊢
      rw [ih]
      rfl
  · induction vs with
    | nil => simp [bit, wordOp, GateOp.eval]
    | cons a rest ih =>
      simp only [wordOp, List.foldr_cons, List.map_cons, GateOp.eval, List.any_cons] at ih ⊢
      simp only [bit, BitVec.getLsbD_or] at ih ⊢
      rw [ih]
      rfl
  · have hs : (vs.map (bit j)).headD false = bit j (vs.headD 0) := by
      simpa [bit] using (List.headD_map (l := vs) (a := (0 : Word)) (f := bit j))
    rw [wordOp, GateOp.eval, hs]
    simp only [bit, BitVec.getLsbD_not, decide_eq_true_eq.mpr j.isLt, Bool.true_and]

private theorem map_step (j : Fin 8) (w : List Word) (g : Gate) (h : allowed g) :
    (appendGate w g).map (bit j) = boolStep (w.map (bit j)) g := by
  simp only [appendGate, boolStep, List.map_append, List.map_cons, List.map_nil, value,
    bit_op j _ _ h.1, List.map_map, Function.comp_def, read_bits]

private theorem map_fold (j : Fin 8) (gs : List Gate) (w : List Word)
    (h : ∀ g ∈ gs, allowed g) :
    (gs.foldl appendGate w).map (bit j) = gs.foldl boolStep (w.map (bit j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    have hg : allowed g := h g (by simp)
    have hr : ∀ g ∈ rest, allowed g := fun g hm => h g (List.mem_cons_of_mem _ hm)
    simpa only [List.foldl_cons, map_step j w g hg] using ih (appendGate w g) hr

-- Each lane records one of the input words with indices 1, 6, 7, 14, 18, 20, 24, 25.
private def sample (j : Fin 8) (i : Fin 5) : Bool :=
  bit j (inputs.getD i.val 0)

private def edge (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
    (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4)

private theorem row_checks :
    ∀ j : Fin 8, inputs.map (bit j) = List.ofFn (sample j) ∧
      bit j target = edge (sample j) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1800000 in
private theorem lowerBound (exhausted : explore 3 [initialBank] = false)
    (t : ℕ) (hf : HasCircuitSize 5 edge t) : 6 ≤ t := by
  obtain ⟨C, fan, ht, computes⟩ := hf
  by_contra! small
  change C.gates.length ≤ t at ht
  have size : C.gates.length ≤ 3 + 2 := by omega
  have good : ∀ g ∈ C.gates, allowed g := by
    intro g hg
    simpa only [allowed, Set.mem_insert_iff, Set.mem_singleton_iff] using fan g hg
  have ans : (C.gates.foldl appendGate inputs).getD C.output 0 = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let j : Fin 8 := ⟨i, hi⟩
    change bit j ((C.gates.foldl appendGate inputs).getD C.output 0) = bit j target
    rw [← read_bits, map_fold j C.gates inputs good, (row_checks j).1]
    change C.eval (List.ofFn (sample j)) = bit j target
    exact (computes (sample j)).trans (row_checks j).2.symm
  have initial : reads initialBank inputs := by
    intro v h
    apply (present_iff _ _).2
    right
    right
    simp only [inputs, initialBank, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have found := search_complete 3 [initialBank] initialBank inputs (by simp) initial
    C.gates size good C.output ans
  have impossible : false = true := exhausted.symm.trans found
  cases impossible

-- Each batch checks all ways to finish from its banks with at most three further gates.
private def banks00 : List (List Word) :=
  [[30, 46, 133, 200, 240],
   [4, 30, 46, 133, 200, 240],
   [8, 30, 46, 133, 200, 240],
   [14, 30, 46, 133, 200, 240],
   [15, 30, 46, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects00 : banks00.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks01 : List (List Word) :=
  [[16, 30, 46, 133, 200, 240],
   [30, 32, 46, 133, 200, 240],
   [30, 46, 55, 133, 200, 240],
   [30, 46, 62, 133, 200, 240],
   [30, 46, 122, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects01 : banks01.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks02 : List (List Word) :=
  [[30, 46, 128, 133, 200, 240],
   [30, 46, 133, 159, 200, 240],
   [30, 46, 133, 175, 200, 240],
   [30, 46, 133, 192, 200, 240],
   [30, 46, 133, 200, 205, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects02 : banks02.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks03 : List (List Word) :=
  [[30, 46, 133, 200, 209, 240],
   [30, 46, 133, 200, 222, 240],
   [30, 46, 133, 200, 225, 240],
   [30, 46, 133, 200, 238, 240],
   [30, 46, 133, 200, 240, 245]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects03 : banks03.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks04 : List (List Word) :=
  [[30, 46, 133, 200, 240, 248],
   [30, 46, 133, 200, 240, 254],
   [1, 30, 46, 133, 200, 240, 254],
   [4, 8, 30, 46, 133, 200, 240],
   [4, 14, 30, 46, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects04 : banks04.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks05 : List (List Word) :=
  [[4, 15, 30, 46, 133, 200, 240],
   [4, 16, 30, 46, 133, 200, 240],
   [4, 30, 32, 46, 133, 200, 240],
   [4, 30, 46, 55, 133, 200, 240],
   [4, 30, 46, 62, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects05 : banks05.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks06 : List (List Word) :=
  [[4, 30, 46, 122, 133, 200, 240],
   [4, 30, 46, 128, 133, 200, 240],
   [4, 30, 46, 133, 159, 200, 240],
   [4, 30, 46, 133, 175, 200, 240],
   [4, 30, 46, 133, 192, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects06 : banks06.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks07 : List (List Word) :=
  [[4, 30, 46, 133, 200, 204, 240],
   [4, 30, 46, 133, 200, 205, 240],
   [4, 30, 46, 133, 200, 209, 240],
   [4, 30, 46, 133, 200, 222, 240],
   [4, 30, 46, 133, 200, 225, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects07 : banks07.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks08 : List (List Word) :=
  [[4, 30, 46, 133, 200, 238, 240],
   [4, 30, 46, 133, 200, 240, 244],
   [4, 30, 46, 133, 200, 240, 245],
   [4, 30, 46, 133, 200, 240, 248],
   [4, 30, 46, 133, 200, 240, 251]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects08 : banks08.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks09 : List (List Word) :=
  [[4, 30, 46, 133, 200, 240, 254],
   [5, 15, 30, 46, 133, 200, 240],
   [5, 30, 46, 55, 133, 200, 240],
   [7, 30, 46, 133, 200, 240, 248],
   [8, 14, 30, 46, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects09 : banks09.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks10 : List (List Word) :=
  [[8, 15, 30, 46, 133, 200, 240],
   [8, 16, 30, 46, 133, 200, 240],
   [8, 30, 32, 46, 133, 200, 240],
   [8, 30, 46, 55, 133, 200, 240],
   [8, 30, 46, 62, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects10 : banks10.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks11 : List (List Word) :=
  [[8, 30, 46, 122, 133, 200, 240],
   [8, 30, 46, 128, 133, 200, 240],
   [8, 30, 46, 133, 141, 200, 240],
   [8, 30, 46, 133, 159, 200, 240],
   [8, 30, 46, 133, 175, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects11 : banks11.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks12 : List (List Word) :=
  [[8, 30, 46, 133, 192, 200, 240],
   [8, 30, 46, 133, 200, 205, 240],
   [8, 30, 46, 133, 200, 209, 240],
   [8, 30, 46, 133, 200, 222, 240],
   [8, 30, 46, 133, 200, 225, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects12 : banks12.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks13 : List (List Word) :=
  [[8, 30, 46, 133, 200, 238, 240],
   [8, 30, 46, 133, 200, 240, 245],
   [8, 30, 46, 133, 200, 240, 247],
   [8, 30, 46, 133, 200, 240, 248],
   [8, 30, 46, 133, 200, 240, 254]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects13 : banks13.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks14 : List (List Word) :=
  [[10, 30, 46, 133, 200, 240, 245],
   [12, 30, 46, 133, 200, 205, 240],
   [14, 15, 30, 46, 133, 200, 240],
   [14, 16, 30, 46, 133, 200, 240],
   [14, 30, 32, 46, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects14 : banks14.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks15 : List (List Word) :=
  [[14, 30, 46, 55, 133, 200, 240],
   [14, 30, 46, 62, 133, 200, 240],
   [14, 30, 46, 122, 133, 200, 240],
   [14, 30, 46, 128, 133, 200, 240],
   [14, 30, 46, 133, 143, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects15 : banks15.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks16 : List (List Word) :=
  [[14, 30, 46, 133, 159, 200, 240],
   [14, 30, 46, 133, 175, 200, 240],
   [14, 30, 46, 133, 192, 200, 240],
   [14, 30, 46, 133, 200, 205, 240],
   [14, 30, 46, 133, 200, 206, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects16 : banks16.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks17 : List (List Word) :=
  [[14, 30, 46, 133, 200, 209, 240],
   [14, 30, 46, 133, 200, 222, 240],
   [14, 30, 46, 133, 200, 225, 240],
   [14, 30, 46, 133, 200, 238, 240],
   [14, 30, 46, 133, 200, 240, 241]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects17 : banks17.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks18 : List (List Word) :=
  [[14, 30, 46, 133, 200, 240, 245],
   [14, 30, 46, 133, 200, 240, 248],
   [14, 30, 46, 133, 200, 240, 254],
   [15, 16, 30, 46, 133, 200, 240],
   [15, 30, 31, 46, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects18 : banks18.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks19 : List (List Word) :=
  [[15, 30, 32, 46, 133, 200, 240],
   [15, 30, 46, 47, 133, 200, 240],
   [15, 30, 46, 55, 133, 200, 240],
   [15, 30, 46, 62, 133, 200, 240],
   [15, 30, 46, 122, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects19 : banks19.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks20 : List (List Word) :=
  [[15, 30, 46, 128, 133, 200, 240],
   [15, 30, 46, 133, 143, 200, 240],
   [15, 30, 46, 133, 159, 200, 240],
   [15, 30, 46, 133, 175, 200, 240],
   [15, 30, 46, 133, 192, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects20 : banks20.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks21 : List (List Word) :=
  [[15, 30, 46, 133, 200, 205, 240],
   [15, 30, 46, 133, 200, 207, 240],
   [15, 30, 46, 133, 200, 209, 240],
   [15, 30, 46, 133, 200, 222, 240],
   [15, 30, 46, 133, 200, 225, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects21 : banks21.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks22 : List (List Word) :=
  [[15, 30, 46, 133, 200, 238, 240],
   [15, 30, 46, 133, 200, 240, 245],
   [15, 30, 46, 133, 200, 240, 248],
   [15, 30, 46, 133, 200, 240, 254],
   [16, 30, 32, 46, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects22 : banks22.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks23 : List (List Word) :=
  [[16, 30, 46, 55, 133, 200, 240],
   [16, 30, 46, 62, 133, 200, 240],
   [16, 30, 46, 122, 133, 200, 240],
   [16, 30, 46, 128, 133, 200, 240],
   [16, 30, 46, 133, 149, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects23 : banks23.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks24 : List (List Word) :=
  [[16, 30, 46, 133, 159, 200, 240],
   [16, 30, 46, 133, 175, 200, 240],
   [16, 30, 46, 133, 192, 200, 240],
   [16, 30, 46, 133, 200, 205, 240],
   [16, 30, 46, 133, 200, 209, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects24 : banks24.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks25 : List (List Word) :=
  [[16, 30, 46, 133, 200, 216, 240],
   [16, 30, 46, 133, 200, 222, 240],
   [16, 30, 46, 133, 200, 225, 240],
   [16, 30, 46, 133, 200, 238, 240],
   [16, 30, 46, 133, 200, 239, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects25 : banks25.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks26 : List (List Word) :=
  [[16, 30, 46, 133, 200, 240, 245],
   [16, 30, 46, 133, 200, 240, 248],
   [16, 30, 46, 133, 200, 240, 254],
   [17, 30, 46, 133, 200, 238, 240],
   [20, 30, 46, 133, 200, 240, 245]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects26 : banks26.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks27 : List (List Word) :=
  [[22, 30, 46, 55, 133, 200, 240],
   [24, 30, 46, 133, 200, 240, 248],
   [26, 30, 46, 122, 133, 200, 240],
   [30, 32, 46, 55, 133, 200, 240],
   [30, 32, 46, 62, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects27 : banks27.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks28 : List (List Word) :=
  [[30, 32, 46, 122, 133, 200, 240],
   [30, 32, 46, 128, 133, 200, 240],
   [30, 32, 46, 133, 159, 200, 240],
   [30, 32, 46, 133, 165, 200, 240],
   [30, 32, 46, 133, 175, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects28 : banks28.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks29 : List (List Word) :=
  [[30, 32, 46, 133, 192, 200, 240],
   [30, 32, 46, 133, 200, 205, 240],
   [30, 32, 46, 133, 200, 209, 240],
   [30, 32, 46, 133, 200, 222, 240],
   [30, 32, 46, 133, 200, 223, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects29 : banks29.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks30 : List (List Word) :=
  [[30, 32, 46, 133, 200, 225, 240],
   [30, 32, 46, 133, 200, 232, 240],
   [30, 32, 46, 133, 200, 238, 240],
   [30, 32, 46, 133, 200, 240, 245],
   [30, 32, 46, 133, 200, 240, 248]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects30 : banks30.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks31 : List (List Word) :=
  [[30, 32, 46, 133, 200, 240, 254],
   [30, 33, 46, 133, 200, 222, 240],
   [30, 36, 46, 133, 200, 240, 245],
   [30, 38, 46, 55, 133, 200, 240],
   [30, 40, 46, 133, 200, 240, 248]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects31 : banks31.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks32 : List (List Word) :=
  [[30, 42, 46, 122, 133, 200, 240],
   [30, 46, 48, 55, 133, 200, 240],
   [30, 46, 48, 62, 133, 200, 240],
   [30, 46, 50, 133, 200, 205, 240],
   [30, 46, 55, 62, 133, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects32 : banks32.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks33 : List (List Word) :=
  [[30, 46, 55, 63, 133, 200, 240],
   [30, 46, 55, 122, 133, 200, 240],
   [30, 46, 55, 128, 133, 200, 240],
   [30, 46, 55, 133, 159, 200, 240],
   [30, 46, 55, 133, 175, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects33 : banks33.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks34 : List (List Word) :=
  [[30, 46, 55, 133, 183, 200, 240],
   [30, 46, 55, 133, 192, 200, 240],
   [30, 46, 55, 133, 200, 205, 240],
   [30, 46, 55, 133, 200, 209, 240],
   [30, 46, 55, 133, 200, 222, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects34 : banks34.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks35 : List (List Word) :=
  [[30, 46, 55, 133, 200, 225, 240],
   [30, 46, 55, 133, 200, 238, 240],
   [30, 46, 55, 133, 200, 240, 245],
   [30, 46, 55, 133, 200, 240, 247],
   [30, 46, 55, 133, 200, 240, 248]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects35 : banks35.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks36 : List (List Word) :=
  [[30, 46, 55, 133, 200, 240, 254],
   [30, 46, 62, 122, 133, 200, 240],
   [30, 46, 62, 128, 133, 200, 240],
   [30, 46, 62, 133, 159, 200, 240],
   [30, 46, 62, 133, 175, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects36 : banks36.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks37 : List (List Word) :=
  [[30, 46, 62, 133, 191, 200, 240],
   [30, 46, 62, 133, 192, 200, 240],
   [30, 46, 62, 133, 193, 200, 240],
   [30, 46, 62, 133, 200, 205, 240],
   [30, 46, 62, 133, 200, 209, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects37 : banks37.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks38 : List (List Word) :=
  [[30, 46, 62, 133, 200, 222, 240],
   [30, 46, 62, 133, 200, 225, 240],
   [30, 46, 62, 133, 200, 238, 240],
   [30, 46, 62, 133, 200, 240, 245],
   [30, 46, 62, 133, 200, 240, 248]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects38 : banks38.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks39 : List (List Word) :=
  [[30, 46, 62, 133, 200, 240, 254],
   [30, 46, 63, 133, 192, 200, 240],
   [30, 46, 72, 122, 133, 200, 240],
   [30, 46, 80, 133, 175, 200, 240],
   [30, 46, 96, 133, 159, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects39 : banks39.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks40 : List (List Word) :=
  [[30, 46, 112, 122, 133, 200, 240],
   [30, 46, 122, 126, 133, 200, 240],
   [30, 46, 122, 128, 133, 200, 240],
   [30, 46, 122, 133, 159, 200, 240],
   [30, 46, 122, 133, 175, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects40 : banks40.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks41 : List (List Word) :=
  [[30, 46, 122, 133, 192, 200, 240],
   [30, 46, 122, 133, 200, 205, 240],
   [30, 46, 122, 133, 200, 209, 240],
   [30, 46, 122, 133, 200, 222, 240],
   [30, 46, 122, 133, 200, 225, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects41 : banks41.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks42 : List (List Word) :=
  [[30, 46, 122, 133, 200, 238, 240],
   [30, 46, 122, 133, 200, 240, 245],
   [30, 46, 122, 133, 200, 240, 248],
   [30, 46, 122, 133, 200, 240, 250],
   [30, 46, 122, 133, 200, 240, 254]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects42 : banks42.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks43 : List (List Word) :=
  [[30, 46, 127, 128, 133, 200, 240],
   [30, 46, 128, 133, 158, 200, 240],
   [30, 46, 128, 133, 159, 200, 240],
   [30, 46, 128, 133, 174, 200, 240],
   [30, 46, 128, 133, 175, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects43 : banks43.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks44 : List (List Word) :=
  [[30, 46, 128, 133, 192, 200, 240],
   [30, 46, 128, 133, 200, 205, 240],
   [30, 46, 128, 133, 200, 209, 240],
   [30, 46, 128, 133, 200, 222, 240],
   [30, 46, 128, 133, 200, 225, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects44 : banks44.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks45 : List (List Word) :=
  [[30, 46, 128, 133, 200, 238, 240],
   [30, 46, 128, 133, 200, 240, 245],
   [30, 46, 128, 133, 200, 240, 248],
   [30, 46, 128, 133, 200, 240, 254],
   [30, 46, 129, 133, 200, 209, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects45 : banks45.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks46 : List (List Word) :=
  [[30, 46, 129, 133, 200, 225, 240],
   [30, 46, 132, 133, 200, 222, 240],
   [30, 46, 132, 133, 200, 238, 240],
   [30, 46, 132, 133, 200, 240, 254],
   [30, 46, 133, 136, 159, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects46 : banks46.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks47 : List (List Word) :=
  [[30, 46, 133, 136, 175, 200, 240],
   [30, 46, 133, 144, 159, 200, 240],
   [30, 46, 133, 159, 175, 200, 240],
   [30, 46, 133, 159, 191, 200, 240],
   [30, 46, 133, 159, 192, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects47 : banks47.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks48 : List (List Word) :=
  [[30, 46, 133, 159, 200, 205, 240],
   [30, 46, 133, 159, 200, 209, 240],
   [30, 46, 133, 159, 200, 222, 240],
   [30, 46, 133, 159, 200, 223, 240],
   [30, 46, 133, 159, 200, 225, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects48 : banks48.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks49 : List (List Word) :=
  [[30, 46, 133, 159, 200, 238, 240],
   [30, 46, 133, 159, 200, 240, 245],
   [30, 46, 133, 159, 200, 240, 248],
   [30, 46, 133, 159, 200, 240, 254],
   [30, 46, 133, 160, 175, 200, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects49 : banks49.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks50 : List (List Word) :=
  [[30, 46, 133, 175, 191, 200, 240],
   [30, 46, 133, 175, 192, 200, 240],
   [30, 46, 133, 175, 200, 205, 240],
   [30, 46, 133, 175, 200, 209, 240],
   [30, 46, 133, 175, 200, 222, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects50 : banks50.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks51 : List (List Word) :=
  [[30, 46, 133, 175, 200, 225, 240],
   [30, 46, 133, 175, 200, 238, 240],
   [30, 46, 133, 175, 200, 239, 240],
   [30, 46, 133, 175, 200, 240, 245],
   [30, 46, 133, 175, 200, 240, 248]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects51 : banks51.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks52 : List (List Word) :=
  [[30, 46, 133, 175, 200, 240, 254],
   [30, 46, 133, 192, 197, 200, 240],
   [30, 46, 133, 192, 200, 205, 240],
   [30, 46, 133, 192, 200, 209, 240],
   [30, 46, 133, 192, 200, 222, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects52 : banks52.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks53 : List (List Word) :=
  [[30, 46, 133, 192, 200, 225, 240],
   [30, 46, 133, 192, 200, 238, 240],
   [30, 46, 133, 192, 200, 240, 245],
   [30, 46, 133, 192, 200, 240, 248],
   [30, 46, 133, 192, 200, 240, 254]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects53 : banks53.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks54 : List (List Word) :=
  [[30, 46, 133, 200, 205, 209, 240],
   [30, 46, 133, 200, 205, 222, 240],
   [30, 46, 133, 200, 205, 223, 240],
   [30, 46, 133, 200, 205, 225, 240],
   [30, 46, 133, 200, 205, 238, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects54 : banks54.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks55 : List (List Word) :=
  [[30, 46, 133, 200, 205, 239, 240],
   [30, 46, 133, 200, 205, 240, 245],
   [30, 46, 133, 200, 205, 240, 248],
   [30, 46, 133, 200, 205, 240, 253],
   [30, 46, 133, 200, 205, 240, 254]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects55 : banks55.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks56 : List (List Word) :=
  [[30, 46, 133, 200, 208, 209, 240],
   [30, 46, 133, 200, 208, 222, 240],
   [30, 46, 133, 200, 209, 213, 240],
   [30, 46, 133, 200, 209, 217, 240],
   [30, 46, 133, 200, 209, 222, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects56 : banks56.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks57 : List (List Word) :=
  [[30, 46, 133, 200, 209, 223, 240],
   [30, 46, 133, 200, 209, 225, 240],
   [30, 46, 133, 200, 209, 238, 240],
   [30, 46, 133, 200, 209, 240, 241],
   [30, 46, 133, 200, 209, 240, 245]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects57 : banks57.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks58 : List (List Word) :=
  [[30, 46, 133, 200, 209, 240, 248],
   [30, 46, 133, 200, 209, 240, 254],
   [30, 46, 133, 200, 222, 223, 240],
   [30, 46, 133, 200, 222, 225, 240],
   [30, 46, 133, 200, 222, 238, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects58 : banks58.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks59 : List (List Word) :=
  [[30, 46, 133, 200, 222, 240, 245],
   [30, 46, 133, 200, 222, 240, 248],
   [30, 46, 133, 200, 222, 240, 254],
   [30, 46, 133, 200, 224, 225, 240],
   [30, 46, 133, 200, 224, 238, 240]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects59 : banks59.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks60 : List (List Word) :=
  [[30, 46, 133, 200, 225, 229, 240],
   [30, 46, 133, 200, 225, 233, 240],
   [30, 46, 133, 200, 225, 238, 240],
   [30, 46, 133, 200, 225, 239, 240],
   [30, 46, 133, 200, 225, 240, 241]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects60 : banks60.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks61 : List (List Word) :=
  [[30, 46, 133, 200, 225, 240, 245],
   [30, 46, 133, 200, 225, 240, 248],
   [30, 46, 133, 200, 225, 240, 254],
   [30, 46, 133, 200, 238, 239, 240],
   [30, 46, 133, 200, 238, 240, 245]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects61 : banks61.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks62 : List (List Word) :=
  [[30, 46, 133, 200, 238, 240, 248],
   [30, 46, 133, 200, 238, 240, 254],
   [30, 46, 133, 200, 240, 245, 248],
   [30, 46, 133, 200, 240, 245, 253],
   [30, 46, 133, 200, 240, 245, 254]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects62 : banks62.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def banks63 : List (List Word) :=
  [[30, 46, 133, 200, 240, 248, 253],
   [30, 46, 133, 200, 240, 248, 254]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
private theorem rejects63 : banks63.any (fun b => (extensions b).any two) = false := by
  decide +kernel

private def checkedBanks : List (List Word) :=
  banks00 ++ banks01 ++ banks02 ++ banks03 ++ banks04 ++ banks05 ++ banks06 ++
    banks07 ++ banks08 ++ banks09 ++ banks10 ++ banks11 ++ banks12 ++ banks13 ++
    banks14 ++ banks15 ++ banks16 ++ banks17 ++ banks18 ++ banks19 ++ banks20 ++
    banks21 ++ banks22 ++ banks23 ++ banks24 ++ banks25 ++ banks26 ++ banks27 ++
    banks28 ++ banks29 ++ banks30 ++ banks31 ++ banks32 ++ banks33 ++ banks34 ++
    banks35 ++ banks36 ++ banks37 ++ banks38 ++ banks39 ++ banks40 ++ banks41 ++
    banks42 ++ banks43 ++ banks44 ++ banks45 ++ banks46 ++ banks47 ++ banks48 ++
    banks49 ++ banks50 ++ banks51 ++ banks52 ++ banks53 ++ banks54 ++ banks55 ++
    banks56 ++ banks57 ++ banks58 ++ banks59 ++ banks60 ++ banks61 ++ banks62 ++
    banks63

set_option maxRecDepth 30000 in
private theorem rejected : checkedBanks.any (fun b => (extensions b).any two) = false := by
  simp only [checkedBanks, List.any_append,
    rejects00, rejects01, rejects02, rejects03, rejects04, rejects05, rejects06,
    rejects07, rejects08, rejects09, rejects10, rejects11, rejects12, rejects13,
    rejects14, rejects15, rejects16, rejects17, rejects18, rejects19, rejects20,
    rejects21, rejects22, rejects23, rejects24, rejects25, rejects26, rejects27,
    rejects28, rejects29, rejects30, rejects31, rejects32, rejects33, rejects34,
    rejects35, rejects36, rejects37, rejects38, rejects39, rejects40, rejects41,
    rejects42, rejects43, rejects44, rejects45, rejects46, rejects47, rejects48,
    rejects49, rejects50, rejects51, rejects52, rejects53, rejects54, rejects55,
    rejects56, rejects57, rejects58, rejects59, rejects60, rejects61, rejects62,
    rejects63, Bool.false_or]

-- The kernel checks that the batches cover exactly the second frontier.
set_option maxRecDepth 42000 in
set_option maxHeartbeats 10000000 in
private theorem coverage : advance (advance [initialBank]) = checkedBanks := by
  decide +kernel

private theorem exhausted : explore 3 [initialBank] = false := by
  apply Bool.eq_false_iff.mpr
  intro ok
  change (advance (advance (advance [initialBank]))).any two = true at ok
  obtain ⟨b, hb, hresult⟩ := List.any_eq_true.mp ok
  change b ∈ compact ((advance (advance [initialBank])).flatMap extensions) at hb
  obtain ⟨earlier, hearlier, hstep⟩ := List.mem_flatMap.mp (mem_compact.mp hb)
  rw [coverage] at hearlier
  have found : checkedBanks.any (fun p => (extensions p).any two) = true :=
    List.any_eq_true.mpr ⟨earlier, hearlier, List.any_eq_true.mpr ⟨b, hstep, hresult⟩⟩
  exact Bool.noConfusion (rejected.symm.trans found)


end PEqualNP.Outside.L_meta_5457

theorem PEqualNP.Outside.L_meta_5457 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4)) t → 6 ≤ t := by
  exact PEqualNP.Outside.L_meta_5457.lowerBound PEqualNP.Outside.L_meta_5457.exhausted
