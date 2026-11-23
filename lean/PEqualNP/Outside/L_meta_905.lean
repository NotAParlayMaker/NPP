import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_905
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

abbrev V := Fin 10
def edges : Finset (Sym2 V) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}
def related (v w : V) : Bool := decide (s(v, w) ∈ edges)
def Good (I : Finset V) : Prop :=
  (∀ v ∈ I, ∀ w ∈ I, related v w = false) ∧
  (∀ u : V, u ∉ I → ∃ v ∈ I, related u v = true)
def rows : Fin 15 → Finset V := ![{1, 4, 5}, {0, 2, 6}, {3, 5, 6}, {2, 4, 5, 6}, {1, 3, 7}, {0, 3, 6, 7}, {4, 6, 7}, {2, 4, 8}, {0, 7, 8}, {1, 4, 7, 8}, {0, 3, 9}, {2, 5, 9}, {1, 3, 5, 9}, {1, 8, 9}, {0, 2, 8, 9}]
def through : V → Fin 5 → Fin 15 := ![![1, 5, 8, 10, 14],
    ![0, 4, 9, 12, 13],
    ![1, 3, 7, 11, 14],
    ![2, 4, 5, 10, 12],
    ![0, 3, 6, 7, 9],
    ![0, 2, 3, 11, 12],
    ![1, 2, 3, 5, 6],
    ![4, 5, 6, 8, 9],
    ![7, 8, 9, 13, 14],
    ![10, 11, 12, 13, 14]]
theorem rowsGood : ∀ i, Good (rows i) := by
  unfold Good
  decide +kernel
theorem rowContains : ∀ v i, v ∈ rows (through v i) := by decide +kernel
private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩
private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]
private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]
def Separates (C : AndCountCircuit 10) : Prop :=
  ∀ I, Good I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true
theorem bare_out_empty (C : AndCountCircuit 10) (h : Separates C) (v : V) : v ∉ C.outVars := by
  intro hv
  have he := (h _ (rowsGood (through v 0))).1
  have ht : C.eval (rows (through v 0)) = true :=
    decide_eq_true (Or.inl ⟨v, hv, rowContains v 0⟩)
  simp [he] at ht
theorem jointlyPresent : ∀ a b : V, related a b = false → ∃ i, a ∈ rows i ∧ b ∈ rows i := by
  decide +kernel
theorem noSquare : ∀ a b c d : V, related a c = true → related a d = true →
    related b c = true → related b d = true → a = b ∨ c = d := by decide +kernel
theorem isolatedEdge : ∀ a b : V, related a b = true → ∃ i, a ∉ rows i ∧
    ∀ x ∈ insert a (rows i), ∀ y ∈ insert a (rows i), related x y = true →
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by decide +kernel
theorem starCenter (L R : Finset V) (h : ∀ a ∈ L, ∀ b ∈ R, related a b = true) :
    ∃ t : V, ∀ a ∈ L, ∀ b ∈ R, a = t ∨ b = t := by
  rcases L.eq_empty_or_nonempty with he | ⟨a, ha⟩
  · exact ⟨0, by simp [he]⟩
  rcases R.eq_empty_or_nonempty with he | ⟨b, hb⟩
  · exact ⟨0, by simp [he]⟩
  by_cases hl : ∀ x ∈ L, x = a
  · exact ⟨a, fun x hx _ _ => Or.inl (hl x hx)⟩
  push Not at hl
  obtain ⟨x, hx, hn⟩ := hl
  exact ⟨b, fun _ _ y hy => Or.inr ((noSquare x a y b
    (h x hx y hy) (h x hx b hb) (h a ha y hy) (h a ha b hb)).resolve_left hn)⟩
theorem firstTrue (C : AndCountCircuit 10) (h : Separates C) (U : Finset V) (hu : C.eval U = true) :
    ∃ i, (∃ a ∈ C.leftVars i, a ∈ U) ∧ (∃ b ∈ C.rightVars i, b ∈ U) := by
  by_contra hn
  have hz (d : ℕ) (i : Fin C.size) : C.gateValFuel U d i = false := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      apply Bool.eq_false_iff.mpr
      simp only [gateValFuel, sideTrue, ih, Bool.false_eq_true,
        and_false, exists_false, or_false]
      exact fun ht => hn ⟨i, by simpa only [Bool.and_eq_true, decide_eq_true_eq] using ht⟩
  rw [eval, decide_eq_true_eq] at hu
  rcases hu with ⟨v, hv, _⟩ | ⟨i, _, ht⟩
  · exact bare_out_empty C h v hv
  · simp [gateVal, hz] at ht
def bare (C : AndCountCircuit 10) (v : V) :=
  Finset.univ.filter fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i
lemma degreeThree : ∀ v : V, (Finset.univ.filter (fun w : V => related v w)).card = 3 := by
  decide +kernel
lemma safeImpossible (C : AndCountCircuit 10) (h : Separates C)
    (small : C.size ≤ 6) (readTwo : ∀ v, (bare C v).card ≤ 2)
    (safe : ∀ i j, C.gateVal (rows j) i = false) : False := by
  classical
  have rect (i : Fin C.size) (a : V) (ha : a ∈ C.leftVars i) (b : V) (hb : b ∈ C.rightVars i) :
      related a b = true := by
    by_contra! hn
    obtain ⟨j, hja, hjb⟩ := jointlyPresent a b (Bool.eq_false_iff.mpr hn)
    have ht : C.gateVal (rows j) i = true := by
      rw [gateVal_unfold, Bool.and_eq_true]
      exact ⟨decide_eq_true (Or.inl ⟨a, ha, hja⟩), decide_eq_true (Or.inl ⟨b, hb, hjb⟩)⟩
    simp [safe] at ht
  choose center hc using fun i => starCenter _ _ (rect i)
  let T := Finset.univ.image center
  obtain ⟨v,hv⟩ : ∃ v : V, v ∉ T := by
    by_contra! hh
    have eq : T = Finset.univ := Finset.eq_univ_of_forall hh
    have card : T.card ≤ C.size := Finset.card_image_le.trans_eq (by simp)
    rw [eq] at card
    simp [V] at card
    omega
  have sub : Finset.univ.filter (fun w : V => related v w) ⊆ (bare C v).image center := by
    intro w hw
    have edge : related v w = true := (Finset.mem_filter.mp hw).2
    obtain ⟨j,missing,isolated⟩ := isolatedEdge v w edge
    have hp := (h _ (rowsGood j)).2 v missing
    obtain ⟨i, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := firstTrue C h _ hp
    have neq : v ≠ center i := fun e => hv (e ▸ Finset.mem_image_of_mem center (Finset.mem_univ i))
    have cen := hc i x hx y hy
    rcases isolated x hx' y hy' (rect i x hx y hy) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl hx⟩,
        (cen.resolve_left neq).symm⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hy⟩,
        (cen.resolve_right neq).symm⟩
  have bound := (Finset.card_le_card sub).trans (Finset.card_image_le.trans (readTwo v))
  rw [degreeThree] at bound
  omega
def portVars (C : AndCountCircuit 10) (i : Fin C.size) : Bool → Finset V
  | false => C.leftVars i
  | true => C.rightVars i
def references (C : AndCountCircuit 10) (i : Fin C.size) : Bool → Finset (Fin C.size)
  | false => C.leftGates i
  | true => C.rightGates i
def meets (B U : Finset V) : Prop := ∃ v ∈ B, v ∈ U
def seed (C : AndCountCircuit 10) (p : Fin C.size) (U : Finset V) : Prop :=
  ∀ b, meets (portVars C p b) U
def firesAt (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V) (b : Bool) : Prop :=
  meets (portVars C i b) U ∨ ∃ j ∈ references C i b, j < i ∧ C.gateVal U j = true
lemma gate_iff (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V) :
    C.gateVal U i = true ↔ ∀ b, firesAt C i U b := by
  rw [gateVal_unfold, Bool.and_eq_true]
  simp only [sideTrue, decide_eq_true_eq]
  exact ⟨fun h b => by cases b with | false => exact h.1 | true => exact h.2,
    fun h => ⟨h false, h true⟩⟩
def residualRaw (C : AndCountCircuit 10) (p i : Fin C.size) (U : Finset V) (b : Bool) : Prop :=
  meets (portVars C i b) U ∨ p ∈ references C i b ∧ seed C p U
def residualOut (C : AndCountCircuit 10) (p i : Fin C.size) : Prop := i < p ∨ i ∈ C.outGates
lemma positiveClosure (C : AndCountCircuit 10) (correct : Separates C) (p : Fin C.size)
    (outside : p ∉ C.outGates) (U : Finset V) (hu : C.eval U = true)
    (active : Fin C.size → Prop)
    (closed : ∀ i, i ≠ p → (∀ b, residualRaw C p i U b ∨
      ∃ j ∈ references C i b, j ≠ p ∧ active j) → active i) :
    ∃ i, i ≠ p ∧ residualOut C p i ∧ active i := by
  by_contra h
  have off (i : Fin C.size) (hi : i < p) : ¬ active i :=
    fun a => h ⟨i, ne_of_lt hi, Or.inl hi, a⟩
  have sim (i : Fin C.size) :
      C.gateVal U i = true → (i = p → seed C p U) ∧ (i ≠ p → active i) := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h i ih =>
      intro val
      have sides := (gate_iff C i U).mp val
      constructor
      · rintro rfl b
        rcases sides b with hv | ⟨j, _, hj, valj⟩
        · exact hv
        · exact (off j hj ((ih j hj valj).2 (ne_of_lt hj))).elim
      · intro ne
        apply closed i ne
        intro b
        rcases sides b with hv | ⟨j, hj, ltj, valj⟩
        · exact Or.inl (Or.inl hv)
        · by_cases e : j = p
          · exact Or.inl (Or.inr ⟨e ▸ hj, (ih j ltj valj).1 e⟩)
          · exact Or.inr ⟨j, hj, e, (ih j ltj valj).2 e⟩
  rcases (decide_eq_true_eq.mp hu : (∃ v ∈ C.outVars, v ∈ U) ∨
      ∃ i ∈ C.outGates, C.gateVal U i = true) with ⟨v, hv, _⟩ | ⟨i, hi, val⟩
  · exact bare_out_empty C correct v hv
  · have ne : i ≠ p := fun e => outside (e ▸ hi)
    exact h ⟨i, ne, Or.inr hi, (sim i val).2 ne⟩
def early (C : AndCountCircuit 10) (p : Fin C.size) : Prop :=
  ∀ j, j < p → ∀ r, C.gateVal (rows r) j = false
lemma seed_eq (C : AndCountCircuit 10) (p : Fin C.size) (r : Fin 15) (ep : early C p) :
    seed C p (rows r) ↔ C.gateVal (rows r) p = true := by
  rw [gate_iff]
  constructor
  · intro h b
    exact Or.inl (h b)
  · intro h b
    rcases h b with v | ⟨j, _, e, ht⟩
    · exact v
    · simp [ep j e r] at ht
lemma refs_earlier (C : AndCountCircuit 10) (wf : C.WellFormed) (i j : Fin C.size) (b : Bool)
    (mem : j ∈ references C i b) : j < i := by
  cases b with
  | false => exact (wf i).1 j mem
  | true => exact (wf i).2 j mem
def chosenSide (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V) : Bool :=
  decide ((C.leftVars i ∩ U).Nonempty ∨
    ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true)
lemma choice_false (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V)
    (z : C.gateVal U i = false) : ¬ firesAt C i U (chosenSide C i U) := by
  have bv : chosenSide C i U = true ↔ firesAt C i U false := by
    simp [chosenSide, firesAt, meets, portVars, references, Finset.Nonempty]
  cases v : chosenSide C i U with
  | false => exact fun f => by have := bv.mpr f; simp [v] at this
  | true =>
    intro f
    have g := (gate_iff C i U).mpr (fun b => by
      cases b with | false => exact bv.mp v | true => exact f)
    simp [z] at g
def selected (C : AndCountCircuit 10) (p i : Fin C.size) (r : Fin 15) (b : Bool) : Prop :=
  i ≠ p ∧ C.gateVal (rows r) i = false ∧ b = chosenSide C i (rows r)
lemma selected_raw (C : AndCountCircuit 10) (wf : C.WellFormed) (p : Fin C.size)
    (ep : early C p) (r : Fin 15) (i : Fin C.size) (b : Bool) (sel : selected C p i r b) :
    ¬ residualRaw C p i (rows r) b := by
  obtain ⟨_, hz, rfl⟩ := sel
  intro h
  apply choice_false C i _ hz
  rcases h with hv | ⟨mem, hot⟩
  · exact Or.inl hv
  · exact Or.inr ⟨p, mem, refs_earlier C wf i p _ mem, (seed_eq C p r ep).mp hot⟩
lemma selected_ref (C : AndCountCircuit 10) (wf : C.WellFormed) (p : Fin C.size)
    (r : Fin 15) (i j : Fin C.size) (b : Bool) (sel : selected C p i r b)
    (mem : j ∈ references C i b) (ne : j ≠ p) : ∃ b', selected C p j r b' := by
  obtain ⟨_, hz, rfl⟩ := sel
  refine ⟨_, ne, Bool.eq_false_iff.mpr ?_, rfl⟩
  intro ht
  exact choice_false C i _ hz (Or.inr ⟨j, mem, refs_earlier C wf i j _ mem, ht⟩)
lemma selected_out (C : AndCountCircuit 10) (correct : Separates C) (p : Fin C.size)
    (ep : early C p) (r : Fin 15) (i : Fin C.size) (ne : i ≠ p) (out : residualOut C p i) :
    ∃ b, selected C p i r b := by
  refine ⟨_, ne, ?_, rfl⟩
  rcases out with hi | hi
  · exact ep i hi r
  · apply Bool.eq_false_iff.mpr
    intro ht
    have con : C.eval (rows r) = true := decide_eq_true (Or.inr ⟨i,hi,ht⟩)
    simp [(correct _ (rowsGood r)).1] at con
abbrev Slot := Fin 5 × Bool
abbrev Feature := Option V
def present (A B U : Finset V) : Feature → Prop
  | some v => v ∈ U
  | none => meets A U ∧ meets B U
def point (U : Finset V) : Prop := ∃ r : Fin 15, ∃ v : V, v ∉ rows r ∧ U = insert v (rows r)
def layout (A B : Finset V) (pos : Feature → Slot → Prop) : Prop :=
  ∃ (out : Fin 5 → Prop) (ref : Slot → Fin 5 → Prop) (cut : Fin 15 → Slot → Prop),
    (∀ r k b d, cut r (k,b) → cut r (k,d) → b = d) ∧
    (∀ r s z, cut r s → pos z s → ¬ present A B (rows r) z) ∧
    (∀ r s j, cut r s → ref s j → ∃ b, cut r (j,b)) ∧
    (∀ r k, out k → ∃ b, cut r (k,b)) ∧
    ∀ U, point U → ∀ a : Fin 5 → Prop,
      (∀ k, (∀ b, (∃ z, pos z (k,b) ∧ present A B U z) ∨
        ∃ j, ref (k,b) j ∧ a j) → a k) → ∃ k, out k ∧ a k
def capacity (A B : Finset V) (pos : Feature → Slot → Prop) : Prop :=
  ∀ v : V, ∃ S : Finset (Fin 5), (∀ k, k ∈ S ↔ ∃ b, pos (some v) (k,b)) ∧
    S.card ≤ 2 ∧ (v ∈ A ∨ v ∈ B → S.card ≤ 1)
abbrev otherGate (C : AndCountCircuit 10) (p : Fin C.size) := {i : Fin C.size // i ≠ p}
def number (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6)
    (i : otherGate C p) : Fin 5 :=
  ⟨if i.val < p then i.val.val else i.val.val - 1, by
    have hn : i.val.val ≠ p.val := fun h => i.property (Fin.ext h)
    have hi := i.val.isLt
    have hp := p.isLt
    split <;> simp_all only [Fin.lt_def] <;> omega⟩
lemma number_inj (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6) :
    Function.Injective (number C p small) := by
  intro i j h
  have hi : i.val.val ≠ p.val := fun h => i.property (Fin.ext h)
  have hj : j.val.val ≠ p.val := fun h => j.property (Fin.ext h)
  apply Subtype.ext
  apply Fin.ext
  have eq := congrArg Fin.val h
  simp only [number, Fin.lt_def] at eq
  split at eq <;> split at eq <;> omega
def marking (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6)
    (z : Feature) (s : Slot) : Prop :=
  ∃ i : otherGate C p, number C p small i = s.1 ∧ match z with
    | some v => v ∈ portVars C i.val s.2
    | none => p ∈ references C i.val s.2
lemma seed_present (C : AndCountCircuit 10) (p : Fin C.size) (U : Finset V) :
    seed C p U ↔ present (C.leftVars p) (C.rightVars p) U none :=
  ⟨fun h => ⟨h false,h true⟩, fun h b => by cases b with | false => exact h.1 | true => exact h.2⟩
lemma marking_raw (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6)
    (i : otherGate C p) (b : Bool) (U : Finset V) :
    residualRaw C p i.val U b ↔ ∃ z, marking C p small z (number C p small i,b) ∧
      present (C.leftVars p) (C.rightVars p) U z := by
  constructor
  · rintro (⟨v, hv, hu⟩ | ⟨hp, hs⟩)
    · exact ⟨some v, ⟨i, rfl, hv⟩, hu⟩
    · exact ⟨none, ⟨i, rfl, hp⟩, (seed_present C p U).mp hs⟩
  · rintro ⟨z, ⟨j, eq, mem⟩, hz⟩
    obtain rfl := number_inj C p small eq
    cases z with
    | none => exact Or.inr ⟨mem,(seed_present C p U).mpr hz⟩
    | some v => exact Or.inl ⟨v,mem,hz⟩
lemma get_layout (C : AndCountCircuit 10) (wf : C.WellFormed) (correct : Separates C)
    (p : Fin C.size) (small : C.size ≤ 6) (ep : early C p) (outside : p ∉ C.outGates) :
    layout (C.leftVars p) (C.rightVars p) (marking C p small) := by
  let f := number C p small
  let O (k : Fin 5) := ∃ i : otherGate C p, f i = k ∧ residualOut C p i.val
  let R (s : Slot) (k : Fin 5) := ∃ i j : otherGate C p,
    f i = s.1 ∧ f j = k ∧ j.val ∈ references C i.val s.2
  let M (r : Fin 15) (s : Slot) := ∃ i : otherGate C p, f i = s.1 ∧ selected C p i.val r s.2
  have inj : Function.Injective f := number_inj C p small
  refine ⟨O,R,M,?_,?_,?_,?_,?_⟩
  · rintro r k b d ⟨i, ei, hb⟩ ⟨j, ej, hd⟩
    obtain rfl := inj (ei.trans ej.symm)
    exact hb.2.2.trans hd.2.2.symm
  · rintro r ⟨k,b⟩ z ⟨i,ei,sel⟩ pos hz
    change f i = k at ei
    subst k
    exact selected_raw C wf p ep r i.val b sel ((marking_raw C p small i b _).mpr ⟨z,pos,hz⟩)
  · rintro r ⟨k,b⟩ j ⟨i,ei,sel⟩ ⟨x,y,ex,ey,ref⟩
    obtain rfl := inj (ei.trans ex.symm)
    obtain ⟨d,hd⟩ := selected_ref C wf p r i.val y.val b sel ref y.property
    exact ⟨d,y,ey,hd⟩
  · rintro r k ⟨i,ei,out⟩
    obtain ⟨b,hb⟩ := selected_out C correct p ep r i.val i.property out
    exact ⟨b,i,ei,hb⟩
  · rintro U ⟨r,v,miss,rfl⟩ a closed
    let active (i : Fin C.size) := ∃ e : i ≠ p, a (f ⟨i,e⟩)
    have cl (i : Fin C.size) (ne : i ≠ p) (hs : ∀ b, residualRaw C p i (insert v (rows r)) b ∨
        ∃ j ∈ references C i b, j ≠ p ∧ active j) : active i := by
      let x : otherGate C p := ⟨i,ne⟩
      refine ⟨ne,closed (f x) ?_⟩
      intro b
      rcases hs b with raw | ⟨j,ref,ne',_,act⟩
      · exact Or.inl ((marking_raw C p small x b _).mp raw)
      · let y : otherGate C p := ⟨j,ne'⟩
        exact Or.inr ⟨f y,⟨x,y,rfl,rfl,ref⟩,act⟩
    obtain ⟨i,ne,out,_,act⟩ := positiveClosure C correct p outside _ ((correct _ (rowsGood r)).2 v miss) active cl
    exact ⟨f ⟨i,ne⟩,⟨⟨i,ne⟩,rfl,out⟩,act⟩
lemma get_capacity (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6)
    (bound : ∀ v, (bare C v).card ≤ 2) :
    capacity (C.leftVars p) (C.rightVars p) (marking C p small) := by
  classical
  intro v
  let T := Finset.univ.filter (fun i : otherGate C p => i.val ∈ bare C v)
  let f := number C p small
  have eq : T.image Subtype.val = (bare C v).erase p := by
    ext i
    simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨j,h,rfl⟩
      exact ⟨j.property,h⟩
    · rintro ⟨ne,mem⟩
      exact ⟨⟨i,ne⟩,mem,rfl⟩
  have count : T.card = ((bare C v).erase p).card := by
    rw [← eq, Finset.card_image_of_injective _ Subtype.val_injective]
  refine ⟨T.image f,?_,(Finset.card_image_le.trans count.le).trans
    ((Finset.card_le_card (Finset.erase_subset _ _)).trans (bound v)),?_⟩
  · intro k
    constructor
    · rintro h
      obtain ⟨i,mem,e⟩ := Finset.mem_image.mp h
      rcases (Finset.mem_filter.mp (Finset.mem_filter.mp mem).2).2 with hl | hr
      · exact ⟨false,i,e,hl⟩
      · exact ⟨true,i,e,hr⟩
    · rintro ⟨b,i,e,mem⟩
      refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,e⟩
      cases b with
      | false => exact Or.inl mem
      | true => exact Or.inr mem
  · intro hp
    have own : p ∈ bare C v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
    have total := Finset.card_erase_add_one own
    have le := (Finset.card_image_le : (T.image f).card ≤ T.card).trans count.le
    have bound' := bound v
    omega
def edgePairs : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def graph : SimpleGraph V := SimpleGraph.fromRel fun a b : V => (a.val,b.val) ∈ edgePairs
lemma graph_iff (v w : V) : graph.Adj v w ↔ related v w = true := by
  change (v ≠ w ∧ ((v.val,w.val) ∈ edgePairs ∨ (w.val,v.val) ∈ edgePairs)) ↔ _
  revert v w
  decide +kernel
lemma related_symm : ∀ v w : V, related v w = related w v := by decide +kernel
lemma reduce_problem (noLayout : ∀ A B pos, (∃ r, present A B (rows r) none) →
    capacity A B pos → layout A B pos → False)
    (C : AndCountCircuit 10) (wf : C.WellFormed) (small : C.size ≤ 6)
    (bound : ∀ v, (bare C v).card ≤ 2)
    (spec : ∀ I : Finset V, (∀ a ∈ I, ∀ c ∈ I, ¬ graph.Adj a c) →
      (∀ w : V, w ∉ I → ∃ a ∈ I, graph.Adj a w) →
      C.eval I = false ∧ ∀ w : V, w ∉ I → C.eval (insert w I) = true) : False := by
  classical
  have correct : Separates C := by
    intro I hI
    refine spec I (fun a ha c hc h => ?_) (fun w hw => ?_)
    · have eq := (graph_iff a c).mp h
      simp [hI.1 a ha c hc] at eq
    · obtain ⟨a,ha,adj⟩ := hI.2 w hw
      exact ⟨a,ha,(graph_iff a w).mpr ((related_symm a w).trans adj)⟩
  let S := Finset.univ.filter fun i : Fin C.size => ∃ r : Fin 15, C.gateVal (rows r) i = true
  have ne : S.Nonempty := by
    by_contra hn
    exact safeImpossible C correct small bound fun i r => Bool.eq_false_iff.mpr
      (fun h => hn ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,r,h⟩⟩)
  let p := S.min' ne
  obtain ⟨r,hr⟩ := (Finset.mem_filter.mp (S.min'_mem ne)).2
  have ep : early C p := by
    intro i hi t
    apply Bool.eq_false_iff.mpr
    intro ht
    exact (not_le_of_gt hi) (S.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,ht⟩))
  have out : p ∉ C.outGates := by
    intro hp
    have ht : C.eval (rows r) = true := decide_eq_true (Or.inr ⟨p,hp,hr⟩)
    simp [(correct _ (rowsGood r)).1] at ht
  exact noLayout _ _ _ ⟨r,(seed_present C p _).mp ((seed_eq C p r ep).mpr hr)⟩
    (get_capacity C p small bound) (get_layout C wf correct p small ep out)
def stable (A B : Finset V) (r : Fin 15) (v : V) : Prop :=
  v ∉ rows r ∧ (present A B (insert v (rows r)) none → present A B (rows r) none)
def conflict (A B : Finset V) (v w : V) : Prop :=
  (∃ r, stable A B r v ∧ stable A B r w) ∧
  (∃ r, stable A B r v ∧ w ∈ rows r) ∧ (∃ r, stable A B r w ∧ v ∈ rows r)
def coverCuts (A B : Finset V) (pos : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) : Prop :=
  (∀ r k b d, M r (k,b) → M r (k,d) → b = d) ∧
  (∀ r s z, M r s → pos z s → ¬ present A B (rows r) z) ∧
  ∀ r U, point U → ∃ s z, M r s ∧ pos z s ∧ present A B U z
lemma cuts_of_layout {A B : Finset V} {pos : Feature → Slot → Prop} (h : layout A B pos) :
    ∃ M, coverCuts A B pos M := by
  classical
  obtain ⟨O,R,M,unique,avoid,closed,root,positive⟩ := h
  refine ⟨M,unique,avoid,?_⟩
  intro r U hu
  by_contra nf
  let a (k : Fin 5) := ¬ ∃ b, M r (k,b)
  have hh (k) (inputs : ∀ b, (∃ z, pos z (k,b) ∧ present A B U z) ∨ ∃ j, R (k,b) j ∧ a j) :
      a k := by
    rintro ⟨b,mem⟩
    rcases inputs b with ⟨z,pz,hz⟩ | ⟨j,ref,absent⟩
    · exact nf ⟨_,z,mem,pz,hz⟩
    · exact absent (closed r _ j mem ref)
  obtain ⟨k,out,off⟩ := positive U hu a hh
  exact off (root r k out)
lemma stable_cut {A B : Finset V} {pos : Feature → Slot → Prop} {M : Fin 15 → Slot → Prop}
    (h : coverCuts A B pos M) {r : Fin 15} {v : V} (st : stable A B r v) :
    ∃ s, M r s ∧ pos (some v) s := by
  obtain ⟨s,z,mem,pz,hz⟩ := h.2.2 r _ ⟨r,v,st.1,rfl⟩
  cases z with
  | none => exact (h.2.1 r s none mem pz (st.2 hz)).elim
  | some w =>
    rcases Finset.mem_insert.mp hz with e | hin
    · exact ⟨s,mem,e ▸ pz⟩
    · exact (h.2.1 r s (some w) mem pz hin).elim
lemma conflict_distinct {A B : Finset V} {pos : Feature → Slot → Prop} {M : Fin 15 → Slot → Prop}
    (h : coverCuts A B pos M) {v w : V} (hc : conflict A B v w) (k : Fin 5)
    (onlyV : ∀ s, pos (some v) s → s.1 = k)
    (onlyW : ∀ s, pos (some w) s → s.1 = k) : False := by
  obtain ⟨⟨r,sv,sw⟩,⟨j,sj,wj⟩,⟨l,sl,vl⟩⟩ := hc
  obtain ⟨⟨k₁,b⟩,mb,pb⟩ := stable_cut h sv
  obtain ⟨⟨k₂,d⟩,md,pd⟩ := stable_cut h sw
  have eqk₁ : k₁ = k := onlyV _ pb
  subst k₁
  have eqk₂ : k₂ = k := onlyW _ pd
  subst k₂
  have eqd := h.1 r k b d mb md
  subst d
  obtain ⟨⟨k₃,c⟩,mc,pc⟩ := stable_cut h sj
  have eqk₃ : k₃ = k := onlyV _ pc
  subst k₃
  obtain ⟨⟨k₄,e⟩,me,pe⟩ := stable_cut h sl
  have eqk₄ : k₄ = k := onlyW _ pe
  subst k₄
  have nc : ¬pos (some w) (k,c) := fun hh => h.2.1 j _ (some w) mc hh wj
  have ne : ¬pos (some v) (k,e) := fun hh => h.2.1 l _ (some v) me hh vl
  have bd : b ≠ c := fun eq => nc (eq ▸ pd)
  have be : b ≠ e := fun eq => ne (eq ▸ pb)
  have ce : c ≠ e := fun eq => nc (eq ▸ pe)
  cases b <;> cases c <;> cases e <;> simp_all
lemma six_conflict {A B : Finset V} {pos : Feature → Slot → Prop}
    (cap : capacity A B pos) (h : layout A B pos) (xs : Fin 6 → V)
    (use : ∀ i, xs i ∈ A ∨ xs i ∈ B) (cl : ∀ i j, i ≠ j → conflict A B (xs i) (xs j)) : False := by
  classical
  obtain ⟨M,hM⟩ := cuts_of_layout h
  choose S hs using cap
  have single (i : Fin 6) : ∃ k : Fin 5, ∀ s, pos (some (xs i)) s → s.1 = k := by
    let j : Fin 6 := if i = 0 then 1 else 0
    have different : i ≠ j := by by_cases hi : i = 0 <;> simp [j,hi]
    obtain ⟨r,sv,_⟩ := (cl i j different).1
    obtain ⟨s,_,ps⟩ := stable_cut hM sv
    have mem : s.1 ∈ S (xs i) := ((hs (xs i)).1 s.1).mpr ⟨s.2,ps⟩
    have one := (hs (xs i)).2.2 (use i)
    obtain ⟨k,eq⟩ := Finset.card_eq_one.mp (le_antisymm one (Finset.card_pos.mpr ⟨_,mem⟩))
    refine ⟨k,fun t ht => ?_⟩
    have ht' := ((hs (xs i)).1 t.1).mpr ⟨t.2,ht⟩
    simpa [eq] using ht'
  choose f hf using single
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    exact conflict_distinct hM (cl i j ne) (f i) (hf i) (fun s ht => (hf j s ht).trans eq.symm)
  have bad := Fintype.card_le_of_injective f inj
  simp at bad
def flipSide (e b : Bool) : Bool := if e then !b else b
lemma flip_twice (e b : Bool) : flipSide e (flipSide e b) = b := by cases e <;> cases b <;> rfl
def relabel (pos : Feature → Slot → Prop) (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool)
    (z : Feature) (s : Slot) : Prop := pos z (π s.1,flipSide (sw s.1) s.2)
lemma cap_relabel {A B : Finset V} {pos : Feature → Slot → Prop}
    (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) (h : capacity A B pos) :
    capacity A B (relabel pos π sw) := by
  intro v
  obtain ⟨S,he,le,one⟩ := h v
  refine ⟨S.map π.symm.toEmbedding,?_,by simpa using le,fun hv => by simpa using one hv⟩
  intro k
  simp only [Finset.mem_map_equiv,Equiv.symm_symm]
  rw [he]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨flipSide (sw k) b,by simpa only [relabel,flip_twice] using hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨flipSide (sw k) b,hb⟩
def apartRows (A B : Finset V) (r s : Fin 15) : Prop :=
  ∃ U, point U ∧ ∀ z, present A B U z → present A B (rows r) z ∨ present A B (rows s) z
def rooted (A B : Finset V) (P : Feature → Slot → Prop) (O : Fin 5 → Prop)
    (R : Slot → Fin 5 → Prop) (M : Fin 15 → Slot → Prop) : Prop :=
    (∀ r k b d, M r (k,b) → M r (k,d) → b = d) ∧
    (∀ r s z, M r s → P z s → ¬ present A B (rows r) z) ∧
    (∀ r s j, M r s → R s j → ∃ b, M r (j,b)) ∧
    (∀ r k, O k → ∃ b, M r (k,b)) ∧
    ∀ U, point U → ∀ a : Fin 5 → Prop,
      (∀ k, (∀ b, (∃ z, P z (k,b) ∧ present A B U z) ∨
        ∃ j, R (k,b) j ∧ a j) → a k) → ∃ k, O k ∧ a k
lemma apart_cut {A B P O R M} (h : rooted A B P O R M) {r s : Fin 15}
    (apt : apartRows A B r s) : ∃ k b, M r (k,b) ∧ M s (k,!b) := by
  classical
  obtain ⟨_,avoid,refs,out,pos⟩ := h
  obtain ⟨U,hU,sub⟩ := apt
  by_contra noCross
  let a (k : Fin 5) := ¬((∃ b, M r (k,b)) ∧ (∃ b, M s (k,b)))
  have step (k : Fin 5) (both : ∀ b, (∃ z, P z (k,b) ∧ present A B U z) ∨
      ∃ j, R (k,b) j ∧ a j) : a k := by
    rintro ⟨⟨b,hr⟩,⟨d,hs⟩⟩
    have e : d = b := by
      by_contra ne
      have ee : d = !b := by cases d <;> cases b <;> simp_all
      exact noCross ⟨k,b,hr,ee ▸ hs⟩
    subst d
    rcases both b with ⟨z,pz,pr⟩ | ⟨j,rd,act⟩
    · rcases sub z pr with hit | hit
      · exact avoid r _ z hr pz hit
      · exact avoid s _ z hs pz hit
    · exact act ⟨refs r _ j hr rd,refs s _ j hs rd⟩
  obtain ⟨k,hk,act⟩ := pos U hU a step
  exact act ⟨out r k hk,out s k hk⟩
lemma row_gap : ∀ r s : Fin 15, r ≠ s → ∃ v ∈ rows s, v ∉ rows r := by decide +kernel
lemma hot_apart {A B : Finset V} {r s : Fin 15} (ne : r ≠ s) (hr : present A B (rows r) none) :
    apartRows A B r s := by
  obtain ⟨v,hs,hn⟩ := row_gap r s ne
  refine ⟨insert v (rows r),⟨r,v,hn,rfl⟩,?_⟩
  rintro ( _ | w ) hz
  · exact Or.inl hr
  · rcases Finset.mem_insert.mp hz with eq | mem
    · exact Or.inr (eq ▸ hs)
    · exact Or.inl mem
lemma idle_capacity {A B P O R M} (h : rooted A B P O R M) (T : Finset (Fin 15))
    (hot : ∀ r ∈ T, present A B (rows r) none) (S : Finset (Fin 5))
    (idle : ∀ k, k ∈ S ↔ ∀ b, ¬P none (k,b)) : T.card ≤ 2 ^ S.card := by
  classical
  let code (r : ↥T) (k : ↥S) := decide (M r.val (k.val,true))
  have inj : Function.Injective code := by
    intro r s eq
    by_contra ne
    have diff : r.val ≠ s.val := fun e => ne (Subtype.ext e)
    obtain ⟨k,b,mr,ms⟩ := apart_cut h (hot_apart diff (hot _ r.property))
    have hn (c : Bool) : ¬ P none (k,c) := by
      intro mem
      by_cases same : c = b
      · exact h.2.1 r.val _ none mr (same ▸ mem) (hot _ r.property)
      · have other : c = !b := by cases c <;> cases b <;> simp_all
        exact h.2.1 s.val _ none ms (other ▸ mem) (hot _ s.property)
    let i : ↥S := ⟨k,(idle k).mpr hn⟩
    have he := congrFun eq i
    change decide (M r.val (k,true)) = decide (M s.val (k,true)) at he
    have link := decide_eq_decide.mp he
    cases b with
    | false =>
      have both := h.1 r.val k false true mr (link.mpr ms)
      contradiction
    | true =>
      have both := h.1 s.val k true false (link.mp mr) ms
      contradiction
  have hc := Fintype.card_le_of_injective code inj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_bool] using hc
def vectorBits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => vectorBits f n ||| (if f n then 2^n else 0)
lemma vectorBits_bit (f : ℕ → Bool) (n i : ℕ) :
    (vectorBits f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [vectorBits]
  | succ n ih =>
    rw [vectorBits,Nat.testBit_or,ih]
    by_cases e : i = n
    · subst i
      cases hf : f n <;> simp [hf,Nat.testBit_two_pow]
    · by_cases lt : i < n
      · have le : i < n+1 := by omega
        cases hf : f n <;> simp [hf,lt,le,Nat.testBit_two_pow,e,Ne.symm e]
      · have ge : ¬i < n+1 := by omega
        cases hf : f n <;> simp [hf,lt,ge,Nat.testBit_two_pow,e,Ne.symm e]
lemma vectorBits_lt (f : ℕ → Bool) (n : ℕ) : vectorBits f n < 2^n := by
  by_contra! he
  obtain ⟨i,hi,ht⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow he
  simp [vectorBits_bit, Nat.not_lt_of_ge hi] at ht
def slotNum (s : Slot) : ℕ := 2*s.1.val+s.2.toNat
def readSlot (i : ℕ) : Slot := (⟨(i/2) % 5,by omega⟩,decide (i % 2=1))
lemma flipSlotNum : ∀ s : Slot, readSlot (slotNum s) = s := by decide +kernel
lemma slotNum_lt : ∀ s : Slot, slotNum s < 10 := by decide +kernel
lemma readSlotNum : ∀ i : Fin 10, slotNum (readSlot i.val) = i.val := by decide +kernel
noncomputable def word (P : Slot → Prop) : Fin 1024 :=
  ⟨vectorBits (fun i => @decide (P (readSlot i)) (Classical.propDecidable _)) 10,
    vectorBits_lt _ 10⟩
lemma word_spec (P : Slot → Prop) (s : Slot) : (word P).val.testBit (slotNum s) = true ↔ P s := by
  simp [word,vectorBits_bit,slotNum_lt,flipSlotNum]
def fsCode (m : ℕ) : Finset V := Finset.univ.filter fun v => m.testBit v.val
def fsWord (S : Finset V) : Fin 1024 :=
  ⟨vectorBits (fun i => decide (⟨i % 10,by omega⟩ ∈ S)) 10, vectorBits_lt _ 10⟩
lemma fsRound (S : Finset V) : fsCode (fsWord S).val = S := by
  ext v
  simp [fsCode,fsWord,vectorBits_bit,V,v.isLt,Nat.mod_eq_of_lt v.isLt]
def overlaps (x y : ℕ) : Bool := (x &&& y) != 0
lemma overlaps_bit {x y i : ℕ} (a : x.testBit i = true) (b : y.testBit i = true) : overlaps x y = true := by
  apply bne_iff_ne.mpr
  intro eq
  have h := congrArg (fun n : ℕ => n.testBit i) eq
  simp [Nat.testBit_and,a,b] at h
def featureNum : Feature → ℕ
  | none => 10
  | some v => v.val
def atFeature (i : ℕ) : Feature := if i < 10 then some ⟨i % 10,by omega⟩ else none
lemma feature_inv : ∀ z : Feature, atFeature (featureNum z) = z := by decide +kernel
def allWords : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def column (k : ℕ) : ℕ :=
  if k < 5 then if k < 2 then if k < 1 then 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa else 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc else if k < 3 then 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 else if k < 4 then 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 else 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 else if k < 7 then if k < 6 then 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 else 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 else if k < 8 then 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000 else if k < 9 then 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def included (x y : ℕ) : Prop := ∀ i, x.testBit i = true → y.testBit i = true
set_option maxRecDepth 10000 in
lemma column_ok : ∀ m : Fin 1024, ∀ i : Fin 10,
    (column i.val).testBit m.val = m.val.testBit i.val := by
  decide +kernel
set_option maxRecDepth 10000 in
lemma allWords_bit : ∀ m : Fin 1024, allWords.testBit m.val = true := by decide +kernel
lemma singleton_sub {D u : ℕ} (h : D.testBit u = true) : included (2^u) D := by
  intro i hi
  simp only [Nat.testBit_two_pow,decide_eq_true_eq] at hi
  simpa [hi] using h
def signedColumn (up : Bool) (i : ℕ) := if up then column i else allWords ^^^ column i
def upperSet (m : ℕ) (up : Bool) : ℕ :=
  (List.range 10).foldl (fun d i => if m.testBit i == up then d &&& signedColumn up i else d) allWords
def orderWords (up : Bool) (x y : Fin 1024) : Prop :=
  ∀ i : Fin 10, x.val.testBit i.val = up → y.val.testBit i.val = up
lemma upperSet_bit {m y : Fin 1024} (up : Bool) (h : orderWords up m y) :
    (upperSet m.val up).testBit y.val = true := by
  have loop (xs : List ℕ) (bd : ∀ i ∈ xs, i < 10) (d : ℕ) (hd : d.testBit y.val = true) :
      (xs.foldl (fun a i => if m.val.testBit i == up then a &&& signedColumn up i else a) d).testBit y.val = true := by
    induction xs generalizing d with
    | nil => exact hd
    | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih (fun j hj => bd j (by simp [hj]))
      split
      · rename_i eq
        rw [Nat.testBit_and,hd,Bool.true_and]
        have k : i < 10 := bd i (by simp)
        have he := h ⟨i,k⟩ (beq_iff_eq.mp eq)
        have hc : (column i).testBit y.val = y.val.testBit i := column_ok y ⟨i,k⟩
        cases up <;> simp [signedColumn,Nat.testBit_xor,allWords_bit,hc,he]
      · exact hd
  exact loop _ (by simpa using fun (i : ℕ) (h : i < 10) => h) allWords (allWords_bit y)
def growStep (up : Bool) (i d : ℕ) : ℕ :=
  if up then d ||| ((d &&& signedColumn false i) <<< (2^i))
  else d ||| ((d &&& column i) >>> (2^i))
def grow (up : Bool) (d : ℕ) := (List.range 10).foldl (fun a i => growStep up i a) d
lemma grow_mono {x y : ℕ} (up : Bool) (h : included x y) : included (grow up x) (grow up y) := by
  have step (i x y : ℕ) (le : included x y) : included (growStep up i x) (growStep up i y) := by
    intro j hj
    cases up <;> simp only [growStep,Bool.false_eq_true,↓reduceIte,Nat.testBit_or,
      Nat.testBit_shiftRight,Nat.testBit_shiftLeft,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true] at hj ⊢
    · exact hj.imp (le _) (fun v => ⟨le _ v.1,v.2⟩)
    · exact hj.imp (le _) (fun v => ⟨v.1,le _ v.2.1,v.2.2⟩)
  change included ((List.range 10).foldl _ x) ((List.range 10).foldl _ y)
  generalize List.range 10 = xs
  induction xs generalizing x y with
  | nil => exact h
  | cons i xs ih => exact ih (step _ _ _ h)
set_option maxRecDepth 10000 in
lemma grow_one : ∀ up : Bool, ∀ m : Fin 1024, grow up (2^m.val) = upperSet m.val up := by
  decide +kernel
lemma grow_contains {up : Bool} {D : ℕ} {x y : Fin 1024}
    (hx : D.testBit x.val = true) (rel : orderWords up x y) : (grow up D).testBit y.val = true := by
  apply grow_mono up (singleton_sub hx) y.val
  rw [grow_one]
  exact upperSet_bit up rel
def holdsWord (d : ℕ) (x : Fin 1024) : Prop := d.testBit x.val = true
def spanBits (d : ℕ) (b : Bool) := vectorBits (fun i => overlaps d (signedColumn b i)) 10
def someBits (m : ℕ) (b : Bool) : ℕ :=
  (List.range 10).foldl (fun d i => if m.testBit i then d ||| signedColumn b i else d) 0
lemma signedColumn_bit (x : Fin 1024) (i : Fin 10) (b : Bool) :
    (signedColumn b i.val).testBit x.val = true ↔ x.val.testBit i.val = b := by
  cases b <;> simp [signedColumn,Nat.testBit_xor,column_ok,allWords_bit]
lemma spanBits_bit {x : Fin 1024} {d : ℕ} {i : Fin 10} {b : Bool}
    (hx : holdsWord d x) (bit : x.val.testBit i.val = b) : (spanBits d b).testBit i.val = true := by
  simp only [spanBits,vectorBits_bit,decide_eq_true i.isLt,Bool.true_and]
  exact overlaps_bit hx ((signedColumn_bit x i b).mpr bit)
lemma someBits_keep {m d : ℕ} {b : Bool} (xs : List ℕ) (x : Fin 1024) (hx : holdsWord d x) :
    holdsWord (xs.foldl (fun q i => if m.testBit i then q ||| signedColumn b i else q) d) x := by
  induction xs generalizing d with
  | nil => exact hx
  | cons i xs ih =>
    apply ih
    change holdsWord (if m.testBit i then d ||| signedColumn b i else d) x
    split
    · change (d ||| signedColumn b i).testBit x.val = true
      simp only [Nat.testBit_or,Bool.or_eq_true]
      exact Or.inl hx
    · exact hx
lemma someBits_bit {m : ℕ} {b : Bool} {x : Fin 1024} {i : Fin 10}
    (mask : m.testBit i.val = true) (bit : x.val.testBit i.val = b) : holdsWord (someBits m b) x := by
  have aux (xs : List ℕ) (d : ℕ) (mem : i.val ∈ xs) :
      holdsWord (xs.foldl (fun q j => if m.testBit j then q ||| signedColumn b j else q) d) x := by
    induction xs generalizing d with
    | nil => simp at mem
    | cons j xs ih =>
      rcases List.mem_cons.mp mem with eq | mem
      · subst j
        simp only [List.foldl_cons,mask,↓reduceIte]
        apply someBits_keep
        change (d ||| signedColumn b i.val).testBit x.val = true
        rw [Nat.testBit_or]
        simp only [Bool.or_eq_true]
        exact Or.inr ((signedColumn_bit x i b).mpr bit)
      · exact ih _ mem
  exact aux _ _ (List.mem_range.mpr i.isLt)
def swapWord (x : ℕ) := ((x &&& 341) <<< 1) ||| ((x >>> 1) &&& 341)
set_option maxRecDepth 10000 in
lemma swapWord_bit : ∀ x : Fin 1024, ∀ s : Slot,
    (swapWord x.val).testBit (slotNum s) = x.val.testBit (slotNum (s.1,!s.2)) := by decide +kernel
abbrev Id := Fin 26
abbrev Valuation := Id → Fin 1024
def crossOrKeep (fl : Bool) (s : Slot) : Slot := (s.1,flipSide fl s.2)
lemma flipIndex_twice (fl : Bool) (s : Slot) : crossOrKeep fl (crossOrKeep fl s) = s := by
  cases s
  simp [crossOrKeep,flip_twice]
def twist (fl : Bool) (x : Fin 1024) : ℕ := if fl then swapWord x.val else x.val
lemma twist_bit (fl : Bool) (x : Fin 1024) (s : Slot) :
    (twist fl x).testBit (slotNum s) = x.val.testBit (slotNum (crossOrKeep fl s)) := by
  cases fl <;> simp [twist,crossOrKeep,flipSide,swapWord_bit]
def witnesses (w : Valuation) (vs : List Id) (j : Id) : Prop :=
  ∃ v ∈ vs, ∃ s : Slot, (w v).val.testBit (slotNum s) = true ∧ (w j).val.testBit (slotNum s) = false
def negNumber (i : ℕ) : ℕ :=
  if i < 7 then if i < 3 then if i < 1 then 50 else if i < 2 then 69 else 104 else if i < 5 then if i < 4 then 116 else 138 else if i < 6 then 201 else 208 else if i < 11 then if i < 9 then if i < 8 then 276 else 385 else if i < 10 then 402 else 521 else if i < 13 then if i < 12 then 548 else 554 else if i < 14 then 770 else 773
def posNumber (i : ℕ) : ℕ :=
  if i < 50 then if i < 25 then if i < 12 then if i < 6 then if i < 3 then if i < 1 then 51 else if i < 2 then 54 else 58 else if i < 4 then 71 else if i < 5 then 77 else 85 else if i < 9 then if i < 7 then 101 else if i < 8 then 105 else 106 else if i < 10 then 108 else if i < 11 then 114 else 117 else if i < 18 then if i < 15 then if i < 13 then 118 else if i < 14 then 120 else 124 else if i < 16 then 139 else if i < 17 then 142 else 154 else if i < 21 then if i < 19 then 170 else if i < 20 then 178 else 197 else if i < 23 then if i < 22 then 202 else 203 else if i < 24 then 205 else 209 else if i < 37 then if i < 31 then if i < 28 then if i < 26 then 210 else if i < 27 then 212 else 216 else if i < 29 then 217 else if i < 30 then 232 else 233 else if i < 34 then if i < 32 then 240 else if i < 33 then 244 else 277 else if i < 35 then 278 else if i < 36 then 284 else 306 else if i < 43 then if i < 40 then if i < 38 then 308 else if i < 39 then 325 else 340 else if i < 41 then 360 else if i < 42 then 372 else 387 else if i < 46 then if i < 44 then 389 else if i < 45 then 393 else 394 else if i < 48 then if i < 47 then 401 else 403 else if i < 49 then 404 else 406 else if i < 75 then if i < 62 then if i < 56 then if i < 53 then if i < 51 then 410 else if i < 52 then 417 else 434 else if i < 54 then 449 else if i < 55 then 457 else 464 else if i < 59 then if i < 57 then 466 else if i < 58 then 523 else 525 else if i < 60 then 537 else if i < 61 then 549 else 550 else if i < 68 then if i < 65 then if i < 63 then 553 else if i < 64 then 555 else 556 else if i < 66 then 558 else if i < 67 then 562 else 564 else if i < 71 then if i < 69 then 570 else if i < 70 then 581 else 585 else if i < 73 then if i < 72 then 612 else 616 else if i < 74 then 618 else 628 else if i < 87 then if i < 81 then if i < 78 then if i < 76 then 649 else if i < 77 then 650 else 676 else if i < 79 then 682 else if i < 80 then 713 else 720 else if i < 84 then if i < 82 then 771 else if i < 83 then 774 else 775 else if i < 85 then 777 else if i < 86 then 778 else 781 else if i < 93 then if i < 90 then if i < 88 then 786 else if i < 89 then 788 else 789 else if i < 91 then 802 else if i < 92 then 804 else 805 else if i < 96 then if i < 94 then 810 else if i < 95 then 834 else 837 else if i < 98 then if i < 97 then 897 else 898 else if i < 99 then 901 else 914
abbrev FeatureId := Fin 11
abbrev PositiveId := Fin 100
def featureOf (z : FeatureId) : Feature := atFeature z.val
def fid (z : Feature) : FeatureId := ⟨featureNum z,by cases z <;> simp [featureNum]; omega⟩
def primal (v : FeatureId) : Id := Fin.castLE (by decide) v
def dual (r : Fin 15) : Id := ⟨11+r.val,by omega⟩
def liftRow (r : Fin 15) : Fin 1024 := ⟨negNumber r.val,by revert r; decide +kernel⟩
def liftPoint (u : PositiveId) : Fin 1024 := ⟨posNumber u.val,by revert u; decide +kernel⟩
lemma featureOf_inv (z : Feature) : featureOf (fid z) = z := feature_inv z
set_option maxRecDepth 10000 in
lemma negNumber_spec : ∀ r : Fin 15, fsCode (liftRow r).val = rows r := by decide +kernel
def origin (u : PositiveId) : Fin 15 × V :=
  let n := liftPoint u
  ((List.finRange 15).flatMap (fun r => (List.finRange 10).map fun v => (r,v))).find?
    (fun p => !(liftRow p.1).val.testBit p.2.val && ((liftRow p.1).val ||| 2^p.2.val == n.val))
    |>.getD (0,0)
set_option maxRecDepth 10000 in
lemma origin_spec : ∀ u : PositiveId, (origin u).2 ∉ rows (origin u).1 ∧
    fsCode (liftPoint u).val = insert (origin u).2 (rows (origin u).1) := by decide +kernel
lemma posNumber_spec (u : PositiveId) : point (fsCode (liftPoint u).val) :=
  ⟨(origin u).1,(origin u).2,(origin_spec u).1,(origin_spec u).2⟩
noncomputable def wordAt (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (i : Id) : Fin 1024 :=
  if h : i.val < 11 then word (P (featureOf ⟨i.val,h⟩)) else
    word (fun s => ¬ M ⟨i.val-11,by omega⟩ s)
lemma primal_word (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (z : FeatureId) (s : Slot) :
    (wordAt P M (primal z)).val.testBit (slotNum s) = true ↔ P (featureOf z) s := by
  change (wordAt P M ⟨z.val,_⟩).val.testBit (slotNum s) = true ↔ _
  simpa only [wordAt,dif_pos z.isLt] using word_spec (P (featureOf z)) s
lemma dual_word (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (r : Fin 15) (s : Slot) :
    (wordAt P M (dual r)).val.testBit (slotNum s) = false ↔ M r s := by
  classical
  have addr : wordAt P M (dual r) = word (fun q => ¬M r q) := by
    unfold wordAt
    split
    · rename_i eq
      simp [dual] at eq
    · congr 1
      funext q
      congr 2
      apply Fin.ext
      dsimp [dual]
      omega
  rw [addr,Bool.eq_false_iff]
  exact (not_congr (word_spec (fun q => ¬M r q) s)).trans not_not
def encLayout (neg : Fin 15 → ℕ) (pos : PositiveId → ℕ) (w : Valuation)
    (O : Fin 5 → Prop) (R : Slot → Fin 5 → Prop) : Prop :=
  (∀ r k b d, (w (dual r)).val.testBit (slotNum (k,b)) = false →
    (w (dual r)).val.testBit (slotNum (k,d)) = false → b = d) ∧
  (∀ r k z, (neg r).testBit z.val = true → (w (primal z)).val.testBit (slotNum k) = true →
    (w (dual r)).val.testBit (slotNum k) = true) ∧
  (∀ r s k, (w (dual r)).val.testBit (slotNum s) = false → R s k →
    ∃ b, (w (dual r)).val.testBit (slotNum (k,b)) = false) ∧
  (∀ r k, O k → ∃ b, (w (dual r)).val.testBit (slotNum (k,b)) = false) ∧
  ∀ u : PositiveId, ∀ a : Fin 5 → Prop,
    (∀ k, (∀ b, (∃ z : FeatureId, (pos u).testBit z.val = true ∧
      (w (primal z)).val.testBit (slotNum (k,b)) = true) ∨ ∃ j, R (k,b) j ∧ a j) → a k) →
    ∃ k, O k ∧ a k
lemma frame_of_rooted {A B P O R M} (h : rooted A B P O R M) (neg : Fin 15 → ℕ)
    (pos : PositiveId → ℕ) (hn : ∀ r z, (neg r).testBit z.val = true → present A B (rows r) (featureOf z))
    (hp : ∀ u z, present A B (fsCode (liftPoint u).val) z → (pos u).testBit (fid z).val = true) :
    encLayout neg pos (wordAt P M) O R := by
  obtain ⟨uniq,avoid,closed,out,positive⟩ := h
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r k b d l rr
    exact uniq r k b d ((dual_word ..).mp l) ((dual_word ..).mp rr)
  · intro r k z hv hw
    cases e : (wordAt P M (dual r)).val.testBit (slotNum k) with
    | true => rfl
    | false => exact (avoid r k (featureOf z) ((dual_word ..).mp e) ((primal_word ..).mp hw) (hn r z hv)).elim
  · intro r s k mem ref
    obtain ⟨b,sel⟩ := closed r s k ((dual_word ..).mp mem) ref
    exact ⟨b,(dual_word ..).mpr sel⟩
  · intro r k hk
    obtain ⟨b,mem⟩ := out r k hk
    exact ⟨b,(dual_word ..).mpr mem⟩
  · intro u a cl
    apply positive _ (posNumber_spec u) a
    intro k both
    apply cl k
    intro b
    rcases both b with ⟨z,hz,pr⟩ | ref
    · exact Or.inl ⟨fid z,hp u z pr,(primal_word P M (fid z) _).mpr (by simpa only [featureOf_inv] using hz)⟩
    · exact Or.inr ref
lemma frame_hit {n p w O R} (h : encLayout n p w O R) (r : Fin 15) (u : PositiveId)
    (xs : List Id) (includedVars : ∀ z : FeatureId, (p u).testBit z.val = true →
      (n r).testBit z.val = false → primal z ∈ xs) : witnesses w xs (dual r) := by
  classical
  let a (k : Fin 5) := ∀ b, (w (dual r)).val.testBit (slotNum (k,b)) = true
  by_contra nf
  have step (k) (both : ∀ b, (∃ z : FeatureId, (p u).testBit z.val = true ∧
      (w (primal z)).val.testBit (slotNum (k,b)) = true) ∨ ∃ j, R (k,b) j ∧ a j) : a k := by
    intro b
    cases e : (w (dual r)).val.testBit (slotNum (k,b)) with
    | true => rfl
    | false =>
      rcases both b with ⟨z,hz,pz⟩ | ⟨j,ref,on⟩
      · cases present : (n r).testBit z.val with
        | true => have contra := h.2.1 r _ z present pz; simp [e] at contra
        | false => exact (nf ⟨_,includedVars z hz present,_,pz,e⟩).elim
      · obtain ⟨s,hs⟩ := h.2.2.1 r _ _ e ref
        have contra := on s
        simp [hs] at contra
  obtain ⟨k,out,on⟩ := h.2.2.2.2 u a step
  obtain ⟨b,absent⟩ := h.2.2.2.1 r k out
  have x := on b
  simp [absent] at x
lemma enc_sub {n p w O R} (h : encLayout n p w O R) {r : Fin 15} {z : FeatureId}
    (hz : (n r).testBit z.val = true) : orderWords true (w (primal z)) (w (dual r)) := by
  intro i
  simpa only [readSlotNum i] using h.2.1 r (readSlot i.val) z hz
lemma enc_cross {n p w O R} (h : encLayout n p w O R) {r s : Fin 15} {u : PositiveId}
    (sub : ∀ z : FeatureId, (p u).testBit z.val = true →
      (n r).testBit z.val = true ∨ (n s).testBit z.val = true) :
    ∃ q : Slot, (w (dual r)).val.testBit (slotNum q) = false ∧
      (w (dual s)).val.testBit (slotNum (crossOrKeep true q)) = false := by
  classical
  by_contra missing
  let active (k : Fin 5) := ¬((∃ b, (w (dual r)).val.testBit (slotNum (k,b)) = false) ∧
                             (∃ b, (w (dual s)).val.testBit (slotNum (k,b)) = false))
  have step (k) (both : ∀ b, (∃ z : FeatureId, (p u).testBit z.val = true ∧
      (w (primal z)).val.testBit (slotNum (k,b)) = true) ∨ ∃ j, R (k,b) j ∧ active j) : active k := by
    rintro ⟨⟨b,hb⟩,⟨d,hd⟩⟩
    have e : d = b := by
      by_contra ne
      have other : d = !b := by cases d <;> cases b <;> simp_all
      exact missing ⟨(k,b),hb,by simpa only [crossOrKeep,flipSide,↓reduceIte,other] using hd⟩
    subst d
    rcases both b with ⟨z,hz,pz⟩ | ⟨j,ref,act⟩
    · rcases sub z hz with rr | ss
      · have hit := h.2.1 r _ _ rr pz
        simp [hb] at hit
      · have hit := h.2.1 s _ _ ss pz
        simp [hd] at hit
    · exact act ⟨h.2.2.1 r _ j hb ref,h.2.2.1 s _ j hd ref⟩
  obtain ⟨k,out,act⟩ := h.2.2.2.2 u active step
  exact act ⟨h.2.2.2.1 r k out,h.2.2.2.1 s k out⟩
def gateWord (f : Fin 5 → Bool) := vectorBits (fun k => f ⟨k % 5,by omega⟩) 5
lemma gateWord_bit (f : Fin 5 → Bool) (k : Fin 5) : (gateWord f).testBit k.val = f k := by
  simp [gateWord,vectorBits_bit,k.isLt,Nat.mod_eq_of_lt k.isLt]
abbrev Marks := Fin 26 → Fin 5 → Bool → Bool
def turn (s b : Bool) := if s then !b else b
def moved (m : Marks) (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool) : Marks :=
  fun z k b => m z (π k) (turn (s k) b)
def digit (m : Marks) (z : Fin 26) (k : Fin 5) (s : Bool) : ℕ :=
  (m z k (turn s false)).toNat + 2 * (m z k (turn s true)).toNat
def history (m : Marks) (k : Fin 5) (s : Bool) : List (Fin 26) → ℕ
  | [] => 0
  | z::xs => digit m z k s + 4 * history m k s xs
lemma digit_bound (m : Marks) (z : Fin 26) (k : Fin 5) (s : Bool) : digit m z k s < 4 := by
  unfold digit
  cases m z k (turn s false) <;> cases m z k (turn s true) <;> decide
lemma history_div (m : Marks) (k : Fin 5) (s : Bool) (z : Fin 26) (xs : List (Fin 26)) :
    history m k s (z::xs) / 4 = history m k s xs := by
  simp only [history]
  have := digit_bound m z k s
  omega
def ordered (m : Marks) (xs : List (Fin 26)) : Prop :=
  (∀ k, history m k false xs ≤ history m k true xs) ∧ Monotone (fun k => history m k false xs)
lemma tail_ordered {m : Marks} {z xs} (h : ordered m (z::xs)) : ordered m xs := by
  exact ⟨fun k => by simpa only [history_div] using Nat.div_le_div_right (c := 4) (h.1 k),
    fun _ _ hle => by simpa only [history_div] using Nat.div_le_div_right (c := 4) (h.2 hle)⟩
lemma history_moved (m : Marks) (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool)
    (k : Fin 5) (b : Bool) (xs : List (Fin 26)) :
    history (moved m π s) k b xs = history m (π k) (turn (s k) b) xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    simp only [history, ih]
    congr 1
    unfold digit moved
    cases e : s k <;> cases b <;> simp [turn]
lemma make_ordered (m : Marks) (xs : List (Fin 26)) :
    ∃ (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool), ordered (moved m π s) xs := by
  let s k := decide (history m k true xs < history m k false xs)
  let key k := history m k (s k) xs
  let π := Tuple.sort key
  refine ⟨π,fun k => s (π k),?_,?_⟩
  · intro k
    rw [history_moved,history_moved]
    by_cases lt : history m (π k) true xs < history m (π k) false xs
    · simpa [s,turn,lt] using lt.le
    · simpa [s,turn,lt] using Nat.le_of_not_gt lt
  · intro i j hij
    change history _ i false xs ≤ history _ j false xs
    rw [history_moved,history_moved]
    have hf (b : Bool) : turn b false = b := by cases b <;> rfl
    simp only [hf]
    exact Tuple.monotone_sort key hij
lemma history_min (m : Marks) (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool) (k : Fin 5)
    (xs : List (Fin 26)) (h : ordered m xs) (g : ordered (moved m π s) xs) :
    history (moved m π s) k false xs = history m (π k) false xs := by
  have le := h.1 (π k)
  have rev := g.1 k
  rw [history_moved,history_moved] at rev
  rw [history_moved]
  cases e : s k <;> simp [turn,e] at rev ⊢
  exact le_antisymm rev le
lemma history_unique (m : Marks) (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool)
    (xs : List (Fin 26)) (h : ordered m xs) (g : ordered (moved m π s) xs) (k : Fin 5) :
    history (moved m π s) k false xs = history m k false xs := by
  let f k := history m k false xs
  have changed (j) := history_min m π s j xs h g
  have mp : Monotone (f ∘ π) := by
    intro i j hij
    change history m (π i) false xs ≤ history m (π j) false xs
    rw [←changed i,←changed j]
    exact g.2 hij
  have idm : Monotone (f ∘ Equiv.refl _) := h.2
  exact (changed k).trans (congrFun (Tuple.unique_monotone mp idm) k)
lemma history_reads {m m' : Marks} {k : Fin 5} {xs : List (Fin 26)}
    (eq : history m k false xs = history m' k false xs) :
    ∀ z ∈ xs, ∀ b, m z k b = m' z k b := by
  induction xs with
  | nil => simp
  | cons v vs ih =>
    have tail := congrArg (fun n : ℕ => n / 4) eq
    simp only [history_div] at tail
    have eqd : digit m v k false = digit m' v k false := by
      simp only [history,tail] at eq
      omega
    intro z mem b
    rcases List.mem_cons.mp mem with rfl | rest
    · unfold digit at eqd
      simp only [turn,Bool.false_eq_true,↓reduceIte] at eqd
      cases h : m z k false <;> cases h' : m z k true <;>
        cases q : m' z k false <;> cases q' : m' z k true <;> cases b <;> simp_all
    · exact ih tail z rest b
lemma extend_ordered {m : Marks} {xs} (h : ordered m xs) (z : Fin 26) :
    ∃ (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool),
      ordered (moved m π s) (z::xs) ∧ ∀ v ∈ xs, ∀ k b, moved m π s v k b = m v k b := by
  obtain ⟨π,s,hnew⟩ := make_ordered m (z::xs)
  refine ⟨π,s,hnew,fun v hv k b => ?_⟩
  exact history_reads (history_unique m π s xs h (tail_ordered hnew) k) v hv b
def rawNumber (m : Marks) (i : Id) : Fin 1024 :=
  ⟨vectorBits (fun j => m i (readSlot j).1 (readSlot j).2) 10, vectorBits_lt _ 10⟩
def represented (m : Marks) (i : Id) : Fin 1024 :=
  if i.val < 11 then rawNumber m i else ⟨1023-(rawNumber m i).val,by omega⟩
lemma rawNumber_bit (m : Marks) (i : Id) (k : Fin 5) (b : Bool) :
    (rawNumber m i).val.testBit (slotNum (k,b)) = m i k b := by
  simp [rawNumber,vectorBits_bit,slotNum_lt,flipSlotNum]
def rawFrom (i : Id) (v : Fin 1024) : ℕ := if i.val < 11 then v.val else 1023-v.val
lemma rawFrom_rep (m : Marks) (i : Id) : rawFrom i (represented m i) = (rawNumber m i).val := by
  have := (rawNumber m i).isLt
  by_cases h : i.val < 11 <;> simp [rawFrom,represented,h] <;> omega
def pairDigit (x : ℕ) (k : Fin 5) := (x >>> (2*k.val)) % 4
set_option maxRecDepth 10000 in
lemma pairDigit_bits : ∀ x : Fin 1024, ∀ k : Fin 5, pairDigit x.val k =
    (x.val.testBit (slotNum (k,false))).toNat + 2*(x.val.testBit (slotNum (k,true))).toNat := by decide +kernel
lemma digit_raw (m : Marks) (i : Id) (k : Fin 5) :
    pairDigit (rawNumber m i).val k = digit m i k false := by
  rw [pairDigit_bits,rawNumber_bit,rawNumber_bit]
  rfl
lemma digit_swap (m : Marks) (i : Id) (k : Fin 5) :
    (digit m i k false ≤ digit m i k true ↔ digit m i k false ≠ 2) ∧
    (digit m i k false = digit m i k true ↔ digit m i k false = 0 ∨ digit m i k false = 3) := by
  simp only [digit,turn,Bool.false_eq_true,Bool.not_false,Bool.not_true,↓reduceIte]
  cases m i k false <;> cases m i k true <;> decide
def prevGate (k : Fin 5) : Fin 5 := ⟨k.val-1,by omega⟩
def flagsMatch (m : Marks) (xs : List Id) (eq fl : ℕ) : Prop :=
  (∀ k : Fin 5, eq.testBit k.val = true → history m (prevGate k) false xs = history m k false xs) ∧
  (∀ k : Fin 5, fl.testBit k.val = true → history m k false xs = history m k true xs)
lemma flags_nil (m : Marks) : flagsMatch m [] 30 31 := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
def acceptMark (eq fl x : ℕ) : Prop := ∀ k : Fin 5,
  (fl.testBit k.val = true → pairDigit x k ≠ 2) ∧
  (eq.testBit k.val = true → pairDigit x (prevGate k) ≤ pairDigit x k)
lemma accepted_order {m : Marks} {xs eq fl i} (s : flagsMatch m xs eq fl) (h : ordered m (i::xs)) :
    acceptMark eq fl (rawNumber m i).val := by
  intro k
  constructor
  · intro free
    rw [digit_raw]
    apply (digit_swap m i k).1.mp
    have le := h.1 k
    simp only [history,s.2 k free] at le
    omega
  · intro tie
    rw [digit_raw,digit_raw]
    have hle : prevGate k ≤ k := by change k.val-1 ≤ k.val; omega
    have le := h.2 hle
    change digit m i (prevGate k) false + 4*history m (prevGate k) false xs ≤
      digit m i k false + 4*history m k false xs at le
    rw [s.1 k tie] at le
    omega
def sameMark (x : ℕ) := gateWord fun k => pairDigit x k == pairDigit x (prevGate k)
def freeMark (x : ℕ) := gateWord fun k => pairDigit x k == 0 || pairDigit x k == 3
lemma advance_flags {m : Marks} {xs eq fl i} (s : flagsMatch m xs eq fl) :
    flagsMatch m (i::xs) (eq &&& sameMark (rawNumber m i).val) (fl &&& freeMark (rawNumber m i).val) := by
  constructor
  · intro k h
    simp only [Nat.testBit_and,sameMark,gateWord_bit,digit_raw,Bool.and_eq_true,beq_iff_eq] at h
    simp only [history,s.1 k h.1,h.2]
  · intro k h
    simp only [Nat.testBit_and,freeMark,gateWord_bit,digit_raw,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at h
    have e := (digit_swap m i k).2.mpr h.2
    simp only [history,s.2 k h.1,e]
def fixedHistory (hist : List (Id × Fin 1024)) (m : Marks) : Prop :=
  ∀ iv ∈ hist, represented m iv.1 = iv.2
lemma rawNumber_congr {x y : Marks} {i : Id} (eq : ∀ k b, x i k b = y i k b) :
    rawNumber x i = rawNumber y i := by
  apply Fin.ext
  change vectorBits _ 10 = vectorBits _ 10
  congr 1
  funext j
  exact eq _ _
lemma fixed_move {x y : Marks} {hist : List (Id × Fin 1024)} (fixed : fixedHistory hist x)
    (eq : ∀ i ∈ hist.map Prod.fst, ∀ k b, y i k b = x i k b) : fixedHistory hist y := by
  intro iv mem
  have en := rawNumber_congr (eq iv.1 (List.mem_map.mpr ⟨iv,mem,rfl⟩))
  simpa only [represented,en] using fixed iv mem
lemma flags_move {x y : Marks} {hist : List (Id × Fin 1024)} {eq fl}
    (h : flagsMatch x (hist.map Prod.fst) eq fl)
    (same : ∀ i ∈ hist.map Prod.fst, ∀ k b, y i k b = x i k b) : flagsMatch y (hist.map Prod.fst) eq fl := by
  have congH (xs : List Id) (use : ∀ v ∈ xs, v ∈ hist.map Prod.fst) (k : Fin 5) (b : Bool) :
      history y k b xs = history x k b xs := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp only [history,digit,same i (use i (by simp)),ih (fun v hv => use v (by simp [hv]))]
  exact ⟨fun k hk => by simpa only [congH _ (fun _ hz => hz)] using h.1 k hk,
    fun k hk => by simpa only [congH _ (fun _ hz => hz)] using h.2 k hk⟩
def fieldMask := 2^1024-1
def strideFlags : List Bool → ℕ
  | [] => 0
  | f::fs => 2^1025 * strideFlags fs + f.toNat
lemma scatter_read (xs : List Bool) (d : ℕ) (small : d < 2^1025) (i j : ℕ) (hj : j < 1025) :
    (d * strideFlags xs).testBit (1025*i+j) = ((xs[i]?).getD false && d.testBit j) := by
  induction xs generalizing i with
  | nil => simp [strideFlags]
  | cons f fs ih =>
    have eq : d * strideFlags (f::fs) = 2^1025 * (d * strideFlags fs) + d * f.toNat := by
      simp only [strideFlags,Nat.mul_add]
      ring
    have bd : d * f.toNat < 2^1025 := by cases f <;> simp_all
    rw [eq,Nat.testBit_two_pow_mul_add _ bd]
    cases i with
    | zero => cases f <;> simp [hj]
    | succ i =>
      have ge : ¬ 1025*(i+1)+j < 1025 := by omega
      have diff : 1025*(i+1)+j-1025=1025*i+j := by omega
      simpa only [ge,↓reduceIte,diff,List.getElem?_cons_succ] using ih i
def laneRead (d i : ℕ) := (d >>> (1025*i)) &&& fieldMask
lemma laneRead_bit (d i : ℕ) (v : Fin 1024) :
    (laneRead d i).testBit v.val = d.testBit (1025*i+v.val) := by
  simp only [laneRead,fieldMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,
    decide_eq_true v.isLt,Bool.and_true,Nat.testBit_shiftRight,Nat.add_comm]
def insidePacked (d : ℕ) (w : Fin 26 → Fin 1024) : Prop :=
  ∀ i, d.testBit (1025*i.val+(w i).val) = true
def restrictPacked (d mask : ℕ) := d ^^^ (d &&& mask)
lemma restrictPacked_sound (d mask : ℕ) (w : Fin 26 → Fin 1024)
    (ok : insidePacked d w) (keep : ∀ i, mask.testBit (1025*i.val+(w i).val) = false) :
    insidePacked (restrictPacked d mask) w := by
  intro i
  simp [restrictPacked,Nat.testBit_xor,Nat.testBit_and,ok i,keep i]
lemma scatter_safe (xs : List Bool) (w : Fin 26 → Fin 1024) (filter : ℕ)
    (bound : filter < 2^1025)
    (safe : ∀ i : Fin 26, (xs[i.val]?).getD false = true → filter.testBit (w i).val = false) :
    ∀ i : Fin 26, (filter*strideFlags xs).testBit (1025*i.val+(w i).val) = false := by
  intro i
  rw [scatter_read xs filter bound _ _ (by have := (w i).isLt; omega)]
  cases h : (xs[i.val]?).getD false with
  | false => rfl
  | true => simpa only [Bool.true_and] using safe i h
def replacePacked (d i x : ℕ) := d ^^^ ((laneRead d i ^^^ x) <<< (1025*i))
lemma low_lane (d i : ℕ) : laneRead d i < 2^1024 := by
  exact (Nat.and_le_right (n := d >>> (1025*i)) (m := fieldMask)).trans_lt
    (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
lemma replacePacked_sound {d : ℕ} {w : Fin 26 → Fin 1024} (ok : insidePacked d w) (i : Fin 26) :
    insidePacked (replacePacked d i.val (1 <<< (w i).val)) w := by
  intro j
  let v := (w j).val
  have vlt : v < 1024 := (w j).isLt
  have wi : (w i).val < 1024 := (w i).isLt
  rw [Nat.one_shiftLeft]
  simp only [replacePacked,Nat.testBit_xor,Nat.testBit_shiftLeft,ok j,Bool.true_xor]
  by_cases e : j=i
  · subst j
    have eq : 1025*i.val + (w i).val - 1025*i.val = (w i).val := by omega
    simp [eq,laneRead_bit,ok i,Nat.testBit_two_pow]
  · have ne : j.val ≠ i.val := fun h => e (Fin.ext h)
    by_cases lt : j.val < i.val
    · have no : ¬1025*i.val ≤ 1025*j.val+(w j).val := by omega
      simp [no]
    · have ge : 1024 ≤ 1025*j.val+(w j).val-1025*i.val := by omega
      have pow : 2^1024 ≤ 2^(1025*j.val+(w j).val-1025*i.val) := Nat.pow_le_pow_right (by decide) ge
      have f := Nat.testBit_lt_two_pow ((low_lane d i.val).trans_le pow)
      have nw : (w i).val ≠ 1025*j.val+(w j).val-1025*i.val := by omega
      simp [Nat.testBit_two_pow,f,nw]
lemma heldLane {w : Valuation} {d : ℕ} (ok : insidePacked d w) (i : Id) :
    holdsWord (laneRead d i.val) (w i) := by
  change (laneRead d i.val).testBit (w i).val = true
  rw [laneRead_bit]
  exact ok i
def pairBits (k : Fin 5) : ℕ := 3 <<< (2*k.val)
lemma pairBits_hit : ∀ k : Fin 5, ∀ b : Bool,
    (pairBits k).testBit (slotNum (k,b)) = true := by decide +kernel
def barredRoot (d : ℕ) (r : Fin 15) (k : Fin 5) : Bool :=
  !overlaps (laneRead d (dual r).val) (someBits (pairBits k) false)
def barredArc (d : ℕ) (r : Fin 15) (s : Slot) (k : Fin 5) : Bool :=
  !overlaps (laneRead d (dual r).val) (column (slotNum s) ||| someBits (pairBits k) false)
def barredRaw (d u : ℕ) (s : Slot) : Bool :=
  (List.finRange 11).all fun z =>
    !u.testBit z.val || !overlaps (laneRead d (primal z).val) (column (slotNum s))
lemma barredRoot_sound {n p w O R d} (h : encLayout n p w O R) (ok : insidePacked d w)
    (r : Fin 15) (k : Fin 5) (bad : barredRoot d r k = true) : ¬O k := by
  intro out
  obtain ⟨b,hb⟩ := h.2.2.2.1 r k out
  have somebit := someBits_bit (i := ⟨_,slotNum_lt (k,b)⟩) (pairBits_hit k b) hb
  have no := overlaps_bit (heldLane ok (dual r)) somebit
  simp [barredRoot,no] at bad
lemma barredArc_sound {n p w O R d} (h : encLayout n p w O R) (ok : insidePacked d w)
    (r : Fin 15) (s : Slot) (k : Fin 5) (bad : barredArc d r s k = true) : ¬ R s k := by
  intro ref
  have mem : ((column (slotNum s)) ||| someBits (pairBits k) false).testBit (w (dual r)).val = true := by
    rw [Nat.testBit_or,Bool.or_eq_true]
    cases bit : (w (dual r)).val.testBit (slotNum s) with
    | true => exact Or.inl ((column_ok _ ⟨_,slotNum_lt s⟩).trans bit)
    | false =>
      obtain ⟨b,hb⟩ := h.2.2.1 r s k bit ref
      exact Or.inr (someBits_bit (i := ⟨_,slotNum_lt (k,b)⟩) (pairBits_hit k b) hb)
  have no := overlaps_bit (heldLane ok (dual r)) mem
  simp [barredArc,no] at bad
lemma barredRaw_sound {w : Valuation} {d u : ℕ} (ok : insidePacked d w) {s : Slot}
    (bad : barredRaw d u s = true) (z : FeatureId) (hz : u.testBit z.val = true) :
    (w (primal z)).val.testBit (slotNum s) ≠ true := by
  intro bit
  have no := overlaps_bit (heldLane ok (primal z)) ((column_ok _ ⟨_,slotNum_lt s⟩).trans bit)
  have row := List.all_eq_true.mp bad z (List.mem_finRange z)
  simp [hz,no] at row
def graphLeaf (d u on sw : ℕ) (r : Fin 5 → Fin 5 → Fin 15) : Bool :=
  (List.finRange 5).all fun k =>
    if on.testBit k.val then barredRoot d (r k 0) k else
      let s := (k,sw.testBit k.val)
      barredRaw d u s && (List.finRange 5).all fun j =>
        !on.testBit j.val || barredArc d (r k j) s j
lemma graphLeaf_impossible {n p w O R d} (h : encLayout n p w O R) (ok : insidePacked d w)
    (u : PositiveId) (on sw : ℕ) (r : Fin 5 → Fin 5 → Fin 15) (bad : graphLeaf d (p u) on sw r = true) : False := by
  let active (k : Fin 5) := on.testBit k.val = true
  have checked := List.all_eq_true.mp bad
  have cl (k : Fin 5) (both : ∀ b, (∃ z : FeatureId, (p u).testBit z.val = true ∧
      (w (primal z)).val.testBit (slotNum (k,b)) = true) ∨ ∃ j, R (k,b) j ∧ active j) :
      active k := by
    cases e : on.testBit k.val with
    | true => exact e
    | false =>
      have no := checked k (List.mem_finRange k)
      simp only [e,Bool.false_eq_true,↓reduceIte,Bool.and_eq_true] at no
      rcases both (sw.testBit k.val) with ⟨z,hz,bit⟩ | ⟨j,ref,act⟩
      · exact (barredRaw_sound ok no.1 z hz bit).elim
      · have ar := List.all_eq_true.mp no.2 j (List.mem_finRange j)
        simp only [active] at act
        simp only [act,Bool.not_true,Bool.false_or] at ar
        exact (barredArc_sound h ok _ _ _ ar ref).elim
  obtain ⟨k,out,act⟩ := h.2.2.2.2 u active cl
  have no := checked k (List.mem_finRange k)
  simp only [active] at act
  simp only [act,↓reduceIte] at no
  exact barredRoot_sound h ok _ _ no out
def orientation (i : Id) : Bool := decide (i.val < 11)
def relatedJoin (w : Valuation) (i j : Id) (a b flip : Bool) : Prop :=
  ∃ s : Slot, (w i).val.testBit (slotNum s) = a ∧
    (w j).val.testBit (slotNum (crossOrKeep flip s)) = b
abbrev Link := Fin 3 → Id → Id → Bool
def linkValid (net : Link) (w : Valuation) : Prop :=
  (∀ i j, net 0 i j = true → orderWords (orientation i) (w i) (w j)) ∧
  (∀ i j, net 1 i j = true → relatedJoin w i j (orientation i) (!(orientation i)) false) ∧
  (∀ i j, net 2 i j = true → relatedJoin w i j false false true)
def spread (net : Link) (mode : Fin 3) (i : Id) (mask : ℕ) :=
  (fieldMask &&& (fieldMask ^^^ mask)) * strideFlags (List.ofFn (net mode i))
lemma spread_safe {net : Link} {w : Valuation} {i : Id} {mode : Fin 3} {mask : ℕ}
    (safe : ∀ j : Id, net mode i j = true → mask.testBit (w j).val = true) (j : Id) :
    (spread net mode i mask).testBit (1025*j.val+(w j).val) = false := by
  apply scatter_safe
  · have bd : fieldMask &&& (fieldMask ^^^ mask) ≤ fieldMask := Nat.and_le_left
    have lo : fieldMask < 2^1024 := Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    exact (bd.trans_lt lo).trans_le (Nat.pow_le_pow_right (by decide) (by decide : 1024 ≤ 1025))
  · intro q hq
    have edge : net mode i q = true := by simpa only [List.getElem?_ofFn, q.isLt,↓reduceDIte,Option.getD_some] using hq
    have bit := safe _ edge
    simp [fieldMask,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,(w q).isLt,bit]
def filterOrder (d : ℕ) (i : Id) := grow (orientation i) (laneRead d i.val)
def filterJoin (d : ℕ) (i : Id) (a b fl : Bool) :=
  someBits (if fl then swapWord (spanBits (laneRead d i.val) a) else spanBits (laneRead d i.val) a) b
lemma filterJoin_safe {w : Valuation} {d : ℕ} (ok : insidePacked d w)
    {i j : Id} {a b fl : Bool} (hit : relatedJoin w i j a b fl) :
    (filterJoin d i a b fl).testBit (w j).val = true := by
  obtain ⟨s,hs,ht⟩ := hit
  let t := crossOrKeep fl s
  have same := flipIndex_twice fl s
  let n := spanBits (laneRead d i.val) a
  have hspan : n.testBit (slotNum s) = true := spanBits_bit (i := ⟨_,slotNum_lt s⟩) (heldLane ok i) hs
  have bd : n < 1024 := vectorBits_lt _ 10
  let ns : Fin 1024 := ⟨n,bd⟩
  have tr := twist_bit fl ns t
  change (if fl then swapWord n else n).testBit (slotNum t) = n.testBit (slotNum (crossOrKeep fl t)) at tr
  have val : (if fl then swapWord n else n).testBit (slotNum t) = true := tr.trans (by simpa only [t,same] using hspan)
  exact someBits_bit (i := ⟨_,slotNum_lt t⟩) val ht
def sourceCut (net : Link) (d : ℕ) (i : Id) : ℕ :=
  spread net 0 i (filterOrder d i) ||| spread net 1 i (filterJoin d i (orientation i) (!(orientation i)) false) |||
    spread net 2 i (filterJoin d i false false true)
lemma sourceCut_keep {net : Link} {w : Valuation} {d : ℕ} (ok : insidePacked d w) (v : linkValid net w) (i : Id) :
    insidePacked (restrictPacked d (sourceCut net d i)) w := by
  apply restrictPacked_sound _ _ _ ok
  intro j
  have a (j : Id) (edge : net 0 i j = true) :
      (filterOrder d i).testBit (w j).val = true := grow_contains (heldLane ok i) (v.1 i j edge)
  have b (j : Id) (edge : net 1 i j = true) :
      (filterJoin d i (orientation i) (!(orientation i)) false).testBit (w j).val = true :=
    filterJoin_safe ok (v.2.1 i j edge)
  have c (j : Id) (edge : net 2 i j = true) :
      (filterJoin d i false false true).testBit (w j).val = true := filterJoin_safe ok (v.2.2 i j edge)
  simp only [sourceCut,Nat.testBit_or,spread_safe a j,spread_safe b j,spread_safe c j,Bool.false_or]
def optionsBy (high : ℕ → ℕ) : ℕ → ℕ → Option (List ℕ)
  | 0,x => if x == 0 then some [] else none
  | n+1,x =>
    if x == 0 then some [] else
    let i := high x
    (optionsBy high n (x ^^^ (1 <<< i))).map (i :: ·)
lemma optionsBy_covers {high : ℕ → ℕ} {fuel x : ℕ} {xs : List ℕ}
    (ok : optionsBy high fuel x = some xs) {v : ℕ} (present : x.testBit v = true) : v ∈ xs := by
  induction fuel generalizing x xs with
  | zero => 
    by_cases empty : x = 0
    · simp [empty] at present
    · simp [optionsBy,empty] at ok
  | succ fuel ih =>
    by_cases empty : x = 0
    · simp [empty] at present
    · simp only [optionsBy,beq_iff_eq,empty,↓reduceIte] at ok
      cases h : optionsBy high fuel (x ^^^ (1 <<< high x)) with
      | none => simp [h] at ok
      | some ys =>
        simp only [h,Option.map_some,Option.some.injEq] at ok
        subst xs
        by_cases eq : high x = v
        · simp [eq]
        · apply List.mem_cons_of_mem
          apply ih h
          simp [Nat.one_shiftLeft,Nat.testBit_xor,present,eq]
lemma checkedList {α : Type} (f : ℕ → α → ℕ) (xs : List α) (start : ℕ)
    (pass : xs.foldl (fun t a => if t == 0 then 0 else f t a) start ≠ 0) :
    ∀ a ∈ xs, ∃ t ≠ 0, f t a ≠ 0 := by
  have zero (l : List α) : l.foldl (fun t a => if t == 0 then 0 else f t a) 0 = 0 := by
    induction l with
    | nil => rfl
    | cons a l ih => simpa only [List.foldl_cons,beq_self_eq_true,↓reduceIte] using ih
  induction xs generalizing start with
  | nil => simp
  | cons a l ih =>
    have hs : start ≠ 0 := fun eq => pass (eq ▸ zero _)
    have e : (start == 0) = false := beq_eq_false_iff_ne.mpr hs
    simp only [List.foldl_cons,e,Bool.false_eq_true,↓reduceIte] at pass
    have ha : f start a ≠ 0 := by
      intro eq
      rw [eq,zero] at pass
      exact pass rfl
    intro b hb
    rcases List.mem_cons.mp hb with rfl | m
    · exact ⟨_,hs,ha⟩
    · exact ih _ pass b m
abbrev Trail := List (Id × Fin 1024)
def pathBounds (P : Marks → Prop) (hist : Trail) (d : ℕ) : Prop :=
  ∀ m, P m → fixedHistory hist m → insidePacked d (represented m)
def searchTree (byte high : ℕ → ℕ) (settled : ℕ → ℕ → ℕ) (leaf : ℕ → ℕ → ℕ → ℕ)
    (allow : ℕ → ℕ → Bool → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,_,_,_,_,_ => 0
  | fuel+1,t,D,eq,fl,q =>
    let d := settled D q
    if d == 0 then t else
    let tag := byte t
    if lt : tag < 26 then
      let i : Id := ⟨tag,lt⟩
      let cand := laneRead d i.val &&& allow eq fl (!(orientation i))
      match optionsBy high 1024 cand with
      | none => 0
      | some values =>
        values.reverse.foldl (fun loc val =>
          if loc == 0 then 0 else
          if bd : val < 1024 then
            let raw := rawFrom i ⟨val,bd⟩
            let d' := replacePacked d i.val (1 <<< val)
            searchTree byte high settled leaf allow fuel loc d' (eq &&& sameMark raw)
              (fl &&& freeMark raw) (1 <<< (1025*i.val+1024))
          else 0) (t+1)
    else leaf d tag t
lemma tree_impossible (P : Marks → Prop) (mov : ∀ m π s, P m → P (moved m π s))
    (byte high : ℕ → ℕ) (settled : ℕ → ℕ → ℕ) (leaf : ℕ → ℕ → ℕ → ℕ)
    (allow : ℕ → ℕ → Bool → ℕ)
    (settles : ∀ m, P m → ∀ d q, insidePacked d (represented m) → insidePacked (settled d q) (represented m))
    (leaves : ∀ m, P m → ∀ d tag t, insidePacked d (represented m) → leaf d tag t = 0)
    (adm : ∀ (m : Marks) (i : Id) eq fl, acceptMark eq fl (rawNumber m i).val →
      (allow eq fl (!(orientation i))).testBit (represented m i).val = true)
    (fuel t d eq fl q : ℕ) (hist : Trail) (m : Marks) (hm : P m) (fixed : fixedHistory hist m)
    (ord : ordered m (hist.map Prod.fst)) (flags : flagsMatch m (hist.map Prod.fst) eq fl)
    (bounded : pathBounds P hist d) : searchTree byte high settled leaf allow fuel t d eq fl q = 0 := by
  induction fuel generalizing t d eq fl q hist m with
  | zero => rfl
  | succ fuel ih =>
    let dn := settled d q
    have bn : pathBounds P hist dn := fun n hn pin => settles n hn d q (bounded n hn pin)
    have dn_ne : dn ≠ 0 := by
      intro e
      have hv := bn m hm fixed (0 : Id)
      change dn.testBit _ = true at hv
      simp [e] at hv
    rw [searchTree]
    change (if dn == 0 then _ else _) = 0
    simp only [beq_eq_false_iff_ne.mpr dn_ne,Bool.false_eq_true,↓reduceIte]
    split
    · rename_i lt
      let i : Id := ⟨byte t,lt⟩
      obtain ⟨π,sw,ordered',same⟩ := extend_ordered ord i
      let n := moved m π sw
      have hn : P n := mov _ _ _ hm
      have fixed' : fixedHistory hist n := fixed_move fixed same
      have flags' : flagsMatch n (hist.map Prod.fst) eq fl := flags_move flags same
      let val := represented n i
      let cand := laneRead dn i.val &&& allow eq fl (!(orientation i))
      have member : cand.testBit val.val = true := by
        rw [show cand = _ &&& _ from rfl,Nat.testBit_and,Bool.and_eq_true]
        exact ⟨heldLane (bn n hn fixed') i,adm n i eq fl (accepted_order flags' ordered')⟩
      cases opts : optionsBy high 1024 cand with
      | none => rfl
      | some xs =>
        have inList := optionsBy_covers opts member
        dsimp only
        by_contra notZero
        obtain ⟨loc,nz,ran⟩ := checkedList _ xs.reverse _ notZero val.val (List.mem_reverse.mpr inList)
        let hist' : Trail := (i,val)::hist
        have extendPin : fixedHistory hist' n := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | h
          · rfl
          · exact fixed' a h
        have bound' : pathBounds P hist' (replacePacked dn i.val (1 <<< val.val)) := by
          intro z hz fixedZ
          have old : fixedHistory hist z := fun a ha => fixedZ a (List.mem_cons_of_mem _ ha)
          have pin : represented z i = val := fixedZ (i,val) (List.mem_cons_self)
          rw [←pin]
          exact replacePacked_sound (bn z hz old) i
        have recursiveResult :=  ih loc _ _ _ (1 <<< (1025*i.val+1024)) hist' n hn extendPin ordered' (advance_flags flags') bound'
        change searchTree byte high settled leaf allow fuel loc _ _ _ _ = 0 at recursiveResult
        have raw : rawFrom i val = (rawNumber n i).val := rawFrom_rep n i
        apply ran
        rw [←raw] at recursiveResult
        simpa only [val.isLt,↓reduceDIte] using recursiveResult
    · exact leaves m hm dn (byte t) t (bn m hm fixed)
noncomputable def marksFor (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) : Marks := by
  classical
  exact fun i k b => if h : i.val < 11 then decide (P (featureOf ⟨i.val,h⟩) (k,b)) else
    decide (M ⟨i.val-11,by omega⟩ (k,b))
def world (A B : Finset V) (m : Marks) : Prop :=
  ∃ P O R M, capacity A B P ∧ rooted A B P O R M ∧ marksFor P M = m
def rotSlot (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) (s : Slot) :=
  (π s.1,flipSide (sw s.1) s.2)
lemma root_changed {A B P O R M} (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) (h : rooted A B P O R M) :
    rooted A B (relabel P π sw) (fun k => O (π k)) (fun s k => R (rotSlot π sw s) (π k))
      (fun r s => M r (rotSlot π sw s)) := by
  obtain ⟨uniq,avoid,closed,out,positive⟩ := h
  let f := rotSlot π sw
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r k b d hb hd
    have eq := uniq r (π k) (flipSide (sw k) b) (flipSide (sw k) d) hb hd
    simpa only [flip_twice] using congrArg (flipSide (sw k)) eq
  · intro r s z hm hp
    exact avoid r (f s) z hm hp
  · intro r s j hm ref
    obtain ⟨b,hb⟩ := closed r _ _ hm ref
    exact ⟨flipSide (sw j) b,by simpa only [f,rotSlot,flip_twice] using hb⟩
  · intro r k hk
    obtain ⟨b,hb⟩ := out r _ hk
    exact ⟨flipSide (sw k) b,by simpa only [f,rotSlot,flip_twice] using hb⟩
  · intro U hu a cl
    let active (k : Fin 5) := a (π.symm k)
    have step (k : Fin 5) (hh : ∀ b, (∃ z, P z (k,b) ∧ present A B U z) ∨
        ∃ j, R (k,b) j ∧ active j) : active k := by
      apply cl (π.symm k)
      intro b
      rcases hh (flipSide (sw (π.symm k)) b) with ⟨z,hz,pr⟩ | ⟨j,ref,act⟩
      · exact Or.inl ⟨z,by simpa only [relabel,Equiv.apply_symm_apply] using hz,pr⟩
      · exact Or.inr ⟨π.symm j,by simpa only [f,rotSlot,Equiv.apply_symm_apply] using ref,act⟩
    obtain ⟨k,hk,ak⟩ := positive U hu active step
    exact ⟨π.symm k,by simpa only [Equiv.apply_symm_apply] using hk,ak⟩
lemma move_world {A B m} (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) (h : world A B m) :
    world A B (moved m π sw) := by
  classical
  obtain ⟨P,O,R,M,cap,root,rfl⟩ := h
  refine ⟨relabel P π sw,fun k => O (π k),fun s k => R (rotSlot π sw s) (π k),
    fun r s => M r (rotSlot π sw s),cap_relabel π sw cap,?_,?_⟩
  · exact root_changed π sw root
  · funext i k b
    by_cases hi : i.val < 11 <;> apply Bool.eq_iff_iff.mpr <;> simp [moved,marksFor,relabel,rotSlot,turn,flipSide,hi] <;> exact ⟨fun hh => decide_eq_true hh,fun hh => of_decide_eq_true hh⟩
lemma word_ext {a b : Fin 1024} (h : ∀ k : Fin 5, ∀ s : Bool,
    a.val.testBit (slotNum (k,s)) = b.val.testBit (slotNum (k,s))) : a=b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10
  · let t := readSlot i
    have r := readSlotNum (⟨i,hi⟩ : Fin 10)
    simpa only [t,r] using h t.1 t.2
  · have le : 2^10 ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le le),Nat.testBit_lt_two_pow (b.isLt.trans_le le)]
set_option maxRecDepth 10000 in
lemma mirror_bits : ∀ x : Fin 1024, ∀ k : Fin 5, ∀ b : Bool,
    (1023-x.val).testBit (slotNum (k,b)) = !(x.val.testBit (slotNum (k,b))) := by decide +kernel
lemma rep_primal (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (z : FeatureId) (k : Fin 5) (b : Bool) :
    (represented (marksFor P M) (primal z)).val.testBit (slotNum (k,b)) = true ↔ P (featureOf z) (k,b) := by
  change ((if z.val < 11 then rawNumber (marksFor P M) (primal z) else _).val).testBit _ = true ↔ _
  simp [z.isLt,rawNumber_bit,marksFor,primal]
lemma rep_dual (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (r : Fin 15) (k : Fin 5) (b : Bool) :
    (represented (marksFor P M) (dual r)).val.testBit (slotNum (k,b)) = false ↔ M r (k,b) := by
  have ge : ¬(dual r).val < 11 := by change ¬11+r.val < 11; omega
  simp only [represented,ge,↓reduceIte,mirror_bits,rawNumber_bit,marksFor,↓reduceDIte]
  have er : (⟨(dual r).val-11,by change 11+r.val-11 < 15; omega⟩ : Fin 15) = r := by
    apply Fin.ext
    change 11+r.val-11=r.val
    omega
  simp [er]
lemma represented_actual (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) :
    represented (marksFor P M) = wordAt P M := by
  funext i
  apply word_ext
  intro k b
  by_cases hi : i.val < 11
  · let z : FeatureId := ⟨i.val,hi⟩
    have e : i = primal z := Fin.ext rfl
    rw [e]
    apply Bool.eq_iff_iff.mpr
    exact (rep_primal P M z k b).trans (primal_word P M z (k,b)).symm
  · let r : Fin 15 := ⟨i.val-11,by omega⟩
    have e : i = dual r := by apply Fin.ext; change i.val=11+(i.val-11); omega
    rw [e]
    have h := (rep_dual P M r k b).trans (dual_word P M r (k,b)).symm
    cases x : (represented (marksFor P M) (dual r)).val.testBit (slotNum (k,b)) <;>
      cases y : (wordAt P M (dual r)).val.testBit (slotNum (k,b)) <;> simp_all
lemma numeric_world {A B m} (n : Fin 15 → ℕ) (p : PositiveId → ℕ)
    (neg : ∀ r z, (n r).testBit z.val = true → present A B (rows r) (featureOf z))
    (pos : ∀ u z, present A B (fsCode (liftPoint u).val) z → (p u).testBit (fid z).val = true)
    (h : world A B m) : ∃ O R, encLayout n p (represented m) O R := by
  obtain ⟨P,O,R,M,_,root,rfl⟩ := h
  rw [represented_actual]
  exact ⟨O,R,frame_of_rooted root n p neg pos⟩
def decodeId (i : Id) : FeatureId ⊕ Fin 15 :=
  if h : i.val < 11 then .inl ⟨i.val,h⟩ else .inr ⟨i.val-11,by omega⟩
lemma at_primal (z : FeatureId) : decodeId (primal z) = .inl z := by
  simp [decodeId,primal,z.isLt]
lemma at_dual (r : Fin 15) : decodeId (dual r) = .inr r := by
  have neg : ¬(dual r).val < 11 := by change ¬11+r.val < 11; omega
  simp only [decodeId,neg,↓reduceDIte,Sum.inr.injEq]
  apply Fin.ext
  change 11+r.val-11=r.val
  omega
lemma id_cases (i : Id) : (∃ z, i=primal z) ∨ ∃ r, i=dual r := by
  by_cases lt : i.val<11
  · exact Or.inl ⟨⟨i.val,lt⟩,Fin.ext rfl⟩
  · refine Or.inr ⟨⟨i.val-11,by omega⟩,?_⟩
    apply Fin.ext
    change i.val=11+(i.val-11)
    omega
def delta (x y : ℕ) := x &&& (2047 ^^^ y)
def unitLink (neg : Fin 15 → ℕ) (pos : PositiveId → ℕ) (r : Fin 15) (z : FeatureId) : Bool :=
  (List.finRange 100).any fun u => delta (pos u) (neg r) == 1 <<< z.val
def crossLink (neg : Fin 15 → ℕ) (pos : PositiveId → ℕ) (r s : Fin 15) : Bool :=
  r != s && (List.finRange 100).any fun u => pos u &&& (neg r ||| neg s) == pos u
def generatedNet (n : Fin 15 → ℕ) (p : PositiveId → ℕ) (mode : Fin 3) (i j : Id) : Bool :=
  match decodeId i,decodeId j with
  | .inl _, .inl _ => false
  | .inl z, .inr r | .inr r, .inl z =>
    if mode.val=0 then (n r).testBit z.val else if mode.val=1 then unitLink n p r z else false
  | .inr r, .inr s => mode.val=2 && crossLink n p r s
lemma unit_link_valid {n p w O R} (h : encLayout n p w O R) {r : Fin 15} {z : FeatureId}
    (ok : unitLink n p r z = true) : ∃ s : Slot,
    (w (primal z)).val.testBit (slotNum s) = true ∧ (w (dual r)).val.testBit (slotNum s) = false := by
  obtain ⟨u,_,eq⟩ := List.any_eq_true.mp ok
  have mask := beq_iff_eq.mp eq
  have cnt : ∀ v : FeatureId, (2047 : ℕ).testBit v.val = true := by decide +kernel
  have hit := frame_hit h r u [primal z] (by
    intro v present absent
    have read := congrArg (fun t : ℕ => t.testBit v.val) mask
    simp only [delta,Nat.testBit_and,Nat.testBit_xor,present,absent,cnt,Bool.true_xor,Bool.not_false,
      Bool.true_and,Nat.one_shiftLeft,Nat.testBit_two_pow,Bool.true_eq] at read
    have ev : z.val = v.val := of_decide_eq_true read
    exact Fin.ext ev ▸ List.mem_singleton_self _)
  obtain ⟨i,hi,s,l,r'⟩ := hit
  exact ⟨s,List.mem_singleton.mp hi ▸ l,r'⟩
lemma cross_link_valid {n p w O R} (h : encLayout n p w O R) {r s}
    (ok : crossLink n p r s = true) : relatedJoin w (dual r) (dual s) false false true := by
  obtain ⟨_,ex⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨u,_,eq⟩ := List.any_eq_true.mp ex
  apply enc_cross (u := u) h
  intro z hit
  have ev := congrArg (fun t : ℕ => t.testBit z.val) (beq_iff_eq.mp eq)
  simpa only [Nat.testBit_and,Nat.testBit_or,hit,Bool.true_and,Bool.or_eq_true] using ev
lemma generated_valid {n p w O R} (h : encLayout n p w O R) : linkValid (generatedNet n p) w := by
  have orientP (z : FeatureId) : orientation (primal z) = true := decide_eq_true z.isLt
  have orientN (r : Fin 15) : orientation (dual r) = false := by
    simp [orientation,dual]
  constructor
  · intro i j edge
    rcases id_cases i with ⟨z,rfl⟩ | ⟨r,rfl⟩ <;> rcases id_cases j with ⟨v,rfl⟩ | ⟨s,rfl⟩ <;>
      simp [generatedNet,at_primal,at_dual] at edge
    · rw [orientP]
      exact enc_sub h edge
    · rw [orientN]
      intro k off
      cases e : (w (primal v)).val.testBit k.val with
      | false => rfl
      | true => have bad := enc_sub h edge k e; simp [off] at bad
  constructor
  · intro i j edge
    rcases id_cases i with ⟨z,rfl⟩ | ⟨r,rfl⟩ <;> rcases id_cases j with ⟨v,rfl⟩ | ⟨s,rfl⟩ <;>
      simp [generatedNet,at_primal,at_dual] at edge
    · obtain ⟨q,l,right⟩ := unit_link_valid h edge
      rw [orientP]
      exact ⟨q,l,right⟩
    · obtain ⟨q,l,right⟩ := unit_link_valid h edge
      rw [orientN]
      exact ⟨q,right,l⟩
  · intro i j edge
    rcases id_cases i with ⟨z,rfl⟩ | ⟨r,rfl⟩ <;> rcases id_cases j with ⟨v,rfl⟩ | ⟨s,rfl⟩ <;>
      simp [generatedNet,at_primal,at_dual] at edge
    exact cross_link_valid h edge
def occupied (x : Fin 1024) : Finset (Fin 5) := Finset.univ.filter fun k =>
  x.val.testBit (slotNum (k,false)) || x.val.testBit (slotNum (k,true))
lemma occupied_mem {x : Fin 1024} (k : Fin 5) :
    k ∈ occupied x ↔ ∃ b : Bool, x.val.testBit (slotNum (k,b)) = true := by
  simp only [occupied,Finset.mem_filter,Finset.mem_univ,true_and,Bool.or_eq_true]
  exact ⟨fun h => h.elim (fun q => ⟨false,q⟩) (fun q => ⟨true,q⟩),
    fun ⟨b,q⟩ => by cases b <;> simp [q]⟩
def consistent (x : Fin 1024) : Prop :=
  ∀ k : Fin 5, ∀ b d : Bool, x.val.testBit (slotNum (k,b)) = false →
    x.val.testBit (slotNum (k,d)) = false → b=d
def seedRows (hot : ℕ) := Finset.univ.filter fun r : Fin 15 => hot.testBit r.val
def packDomains : List ℕ → ℕ
  | [] => 0
  | x::xs => (packDomains xs <<< 1025) ||| x
lemma packed_reads {xs : List ℕ} {i v : ℕ} (slot : ((xs[i]?).getD 0).testBit v = true) :
    (packDomains xs).testBit (1025*i+v) = true := by
  induction xs generalizing i with
  | nil => simp at slot
  | cons x xs ih =>
    rw [packDomains,Nat.testBit_or,Bool.or_eq_true]
    cases i with
    | zero => right; simpa using slot
    | succ i =>
      left
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true]
      have ge : 1025 ≤ 1025*(i+1)+v := by omega
      have ee : 1025*(i+1)+v-1025=1025*i+v := by omega
      exact ⟨decide_eq_true ge,ee ▸ ih (by simpa using slot)⟩
def budgetOne : ℕ := 0x100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000010000000000000001000100010001111f
def budgetTwo : ℕ := 0x100000000000000010000000000000001000100010001111f000000000000000100000000000000010000000000000001000100010001111f000000000000000100000000000000010000000000000001000100010001111f000100010001111f000100010001111f000100010001111f111f111f111fffff
def cutDomain : ℕ := 0xeee0eee0eee00000eee0eee0eee00000eee0eee0eee000000000000000000000eee0eee0eee00000eee0eee0eee00000eee0eee0eee000000000000000000000eee0eee0eee00000eee0eee0eee00000eee0eee0eee0000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def virtualDomain (n : ℕ) : ℕ :=
  if n ≤ 1 then 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else if n ≤ 2 then 0x111f111f111fffff111f111f111fffff111f111f111fffffffffffffffffffff111f111f111fffff111f111f111fffff111f111f111fffffffffffffffffffff111f111f111fffff111f111f111fffff111f111f111fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else if n ≤ 4 then 0x100010001111f000100010001111f000100010001111f111f111f111fffff000100010001111f000100010001111f000100010001111f111f111f111fffff000100010001111f000100010001111f000100010001111f111f111f111fffff111f111f111fffff111f111f111fffff111f111f111fffffffffffffffffffff else if n ≤ 8 then 0x100000000000000010000000000000001000100010001111f000000000000000100000000000000010000000000000001000100010001111f000000000000000100000000000000010000000000000001000100010001111f000100010001111f000100010001111f000100010001111f111f111f111fffff else if n ≤ 16 then 0x100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000010000000000000001000100010001111f else if n ≤ 32 then 0x1 else 0
set_option maxRecDepth 10000 in
lemma budgetOne_ok : ∀ x : Fin 1024, (occupied x).card ≤ 1 → budgetOne.testBit x.val = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma budgetTwo_ok : ∀ x : Fin 1024, (occupied x).card ≤ 2 → budgetTwo.testBit x.val = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma cutDomain_ok : ∀ x : Fin 1024, consistent x → cutDomain.testBit x.val = true := by
  unfold consistent
  decide +kernel
set_option maxRecDepth 10000 in
lemma virtualDomain_aux : ∀ k : Fin 16, ∀ x : Fin 1024, k.val ≤ 2^(5-(occupied x).card) →
    (virtualDomain k.val).testBit x.val = true := by decide +kernel
lemma virtualDomain_ok (k : ℕ) (x : Fin 1024) (bd : k ≤ 15) (h : k ≤ 2^(5-(occupied x).card)) :
    (virtualDomain k).testBit x.val = true := virtualDomain_aux ⟨k,by omega⟩ x h
def startingField (support hot : ℕ) (i : Id) : ℕ :=
  if i.val < 10 then if support.testBit i.val then budgetOne else budgetTwo
  else if i.val=10 then virtualDomain (seedRows hot).card else cutDomain
def initialPacked (support hot : ℕ) := packDomains (List.ofFn (startingField support hot))
lemma start_preserved {A B : Finset V} {m : Marks} (support hot : ℕ)
    (support_ok : ∀ v : V, support.testBit v.val = true → v ∈ A ∨ v ∈ B)
    (hot_ok : ∀ r ∈ seedRows hot, present A B (rows r) none)
    (h : world A B m) : insidePacked (initialPacked support hot) (represented m) := by
  classical
  obtain ⟨P,O,R,M,cap,root,rfl⟩ := h
  let w := represented (marksFor P M)
  have used (z : FeatureId) (k : Fin 5) :
      k ∈ occupied (w (primal z)) ↔ ∃ b, P (featureOf z) (k,b) := by
    rw [occupied_mem]
    exact exists_congr fun b => rep_primal P M z k b
  intro i
  apply packed_reads
  simp only [List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  change (startingField support hot i).testBit (w i).val = true
  by_cases vert : i.val<10
  · let v : V := ⟨i.val,vert⟩
    let z := fid (some v)
    have addr : i=primal z := Fin.ext rfl
    obtain ⟨S,hs,two,one⟩ := cap v
    have eql : occupied (w i)=S := by
      ext k
      rw [addr,used,hs]
      simp [z,featureOf_inv]
    simp only [startingField,vert,↓reduceIte]
    split
    · rename_i bit
      apply budgetOne_ok
      rw [eql]
      exact one (support_ok v bit)
    · apply budgetTwo_ok
      rwa [eql]
  · by_cases mid : i.val=10
    · let z := fid none
      have addr : i=primal z := Fin.ext mid
      let idle := (occupied (w i))ᶜ
      have spec (k) : k ∈ idle ↔ ∀ b, ¬ P none (k,b) := by
        change k ∈ (occupied (w i))ᶜ ↔ _
        rw [Finset.mem_compl,addr,used]
        simp [z,featureOf_inv]
      have count := idle_capacity root (seedRows hot) hot_ok idle spec
      have eq : idle.card = 5-(occupied (w i)).card := by simp [idle,Finset.card_compl]
      rw [eq] at count
      simp only [startingField,vert,mid,↓reduceIte]
      apply virtualDomain_ok
      · exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin 15)
      · exact count
    · let r : Fin 15 := ⟨i.val-11,by omega⟩
      have addr : i=dual r := by apply Fin.ext; change i.val=11+(i.val-11); omega
      simp only [startingField,vert,mid,↓reduceIte]
      apply cutDomain_ok
      intro k b e hb he
      rw [addr] at hb he
      exact root.1 r k b e ((rep_dual P M r k b).mp hb) ((rep_dual P M r k e).mp he)
def admissibleTable (negative : Bool) (v : Fin 1024) : ℕ := if negative then 1023-v.val else v.val
def sideMask (neg : Bool) (k : Fin 5) : ℕ :=
  if neg then
    if k.val=0 then 0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd else if k.val=1 then 0xff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f else if k.val=2 then 0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff else if k.val=3 then 0xffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  else
    if k.val=0 then 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb else if k.val=1 then 0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0ff else if k.val=2 then 0xffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffff else if k.val=3 then 0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def orderMask (neg : Bool) (k : Fin 5) : ℕ :=
  if neg then
    if k.val=0 then 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else if k.val=1 then 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef else if k.val=2 then 0xf000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0ffff else if k.val=3 then 0xffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffff else 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  else
    if k.val=0 then 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else if k.val=1 then 0xf731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731 else if k.val=2 then 0xffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000f else if k.val=3 then 0xffffffffffffffff0000ffffffffffff00000000ffffffff000000000000ffffffffffffffffffff0000ffffffffffff00000000ffffffff000000000000ffffffffffffffffffff0000ffffffffffff00000000ffffffff000000000000ffffffffffffffffffff0000ffffffffffff00000000ffffffff000000000000ffff else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff
set_option maxRecDepth 10000 in
lemma sideMask_ok : ∀ b k (v : Fin 1024), pairDigit (admissibleTable b v) k ≠ 2 →
    (sideMask b k).testBit v.val = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma orderMask_ok : ∀ b k (v : Fin 1024),
    pairDigit (admissibleTable b v) (prevGate k) ≤ pairDigit (admissibleTable b v) k →
    (orderMask b k).testBit v.val = true := by decide +kernel
def negativeSig (m : ℕ) : ℕ := Nat.lor (if m.testBit 9 then 0x7c00 else 0) (Nat.lor (if m.testBit 8 then 0x6380 else 0) (Nat.lor (if m.testBit 7 then 0x370 else 0) (Nat.lor (if m.testBit 6 then 0x6e else 0) (Nat.lor (if m.testBit 5 then 0x180d else 0) (Nat.lor (if m.testBit 4 then 0x2c9 else 0) (Nat.lor (if m.testBit 3 then 0x1434 else 0) (Nat.lor (if m.testBit 2 then 0x488a else 0) (Nat.lor (if m.testBit 1 then 0x3211 else 0) (Nat.lor (if m.testBit 0 then 0x4522 else 0) (0))))))))))
def positiveSig (m : ℕ) : ℕ := Nat.lor (if m.testBit 9 then 0xffffffffffe00000000000000 else 0) (Nat.lor (if m.testBit 8 then 0xffffe000001fffffe00000000 else 0) (Nat.lor (if m.testBit 7 then 0xf0001f80001fffc01ffff8000 else 0) (Nat.lor (if m.testBit 6 then 0xc00187e001e003c1fff07ff8 else 0) (Nat.lor (if m.testBit 5 then 0x3c00679ff0180331e00c7fc7 else 0) (Nat.lor (if m.testBit 4 then 0x80381041c0997c2bf9f0a7c27 else 0) (Nat.lor (if m.testBit 3 then 0x2070db53ce44310878e7e394 else 0) (Nat.lor (if m.testBit 2 then 0x49b4c24ab34030aef04915a7a else 0) (Nat.lor (if m.testBit 1 then 0xa64ae5216a316a414026f950f else 0) (Nat.lor (if m.testBit 0 then 0x5925a8860de68dc4251d088f9 else 0) (0))))))))))
def incidence (i : ℕ) : ℕ := (match Nat.blt i 5 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x4522 | false => 0x3211) | false => (match Nat.blt i 3 with | true => 0x488a | false => (match Nat.blt i 4 with | true => 0x1434 | false => 0x2c9))) | false => (match Nat.blt i 7 with | true => (match Nat.blt i 6 with | true => 0x180d | false => 0x6e) | false => (match Nat.blt i 8 with | true => 0x370 | false => (match Nat.blt i 9 with | true => 0x6380 | false => 0x7c00))))
def permNumBlock (i : ℕ) : ℕ := 0x130246857900000031826405790000000815643279000000803546127900000020314758690000000251743869000000530847216900000035287401690000001520768349000000518067234900000028136750490000008253761049000000024135796800000020715349680000004709532168000000742935016800000014203697580000004190632758000000291763405800000092473610580000001702569438000000719265043800000009146572380000009074561238000000031425869700000030845216970000001806523497000000813625049700000041302968570000001460923857000000631829405700000036489210570000000641958327000000608159432700000048035961270000008463950127000000302418579600000003548127960000005207183496000000253781049600000042031975860000002473910586000000702519438600000007459123860000004530897216000000547098321600000037429850160000007352894016000000241307968500000042937016850000001926704385000000914607238500000031420869750000001362804975000000641908327500000046398012750000002631879405000000629178340500000039247861050000009364872105000000182630579400000081560327940000002517038694000000528730169400000071520968340000001762905834000000651809723400000056789012340000002671938504000000628139750400000078253961040000008765932104000000071524968300000070954216830000001906427583000000917624058300000015608279430000005170286943000000671928504300000076598210430000000651849723000000609148572300000059074861230000009567840123000000084531697200000080651349720000004609138572000000648931057200000009547168320000009064175832000000560817943200000065987104320000005480379612000000459073861200000098463750120000008956734012000000354802796100000053782049610000004739205861000000745902386100000084530697210000004893605721000000954706832100000059876043210000009374268501000000398462750100000087352694010000007895623401000000293741685000000092671438500000003628149750000000639841275000000082631579400000002873516940000000762915834000000067895123400000003782549610000000739245861000000089364572100000009876543210
def permNum (i : ℕ) := Nat.land (Nat.shiftRight (permNumBlock (Nat.shiftRight i 7)) (Nat.shiftLeft (Nat.land i 127) 6)) 18446744073709551615
def repNumBlock (i : ℕ) : ℕ := 0x3ff01ff017f00ff00fd00fb00fa00bf00bd007f007d007700750074006f006d003f003e0037003600330032002f002d002b002a001f000f000b00070005000300010000
def repNum (i : ℕ) := Nat.land (Nat.shiftRight (repNumBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def envRecordBlock (i : ℕ) : ℕ := (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x1b37bf59ffffffbdffbfb7fdfe11ac7d00b61e4f17f7178f5ffec3ffd623307701361d49d7f4d78ddeaba3b5f622a87711b71f4ffff7ff8ffffff7fffe29247709249500c1bcd19884a3a111f30088771b35bf59fffffdbdefbfb7fdff292c7709369d49d7fcd79ddeaba3b5f722a87719b79f4fffffff9ffffff7ffff2b2c771bedbd94edfefdb8aca7ff3bff488c771dffddedfffeffddfeafffbffe6a2c771bffbfdfffffffbffffffffffe6324770924b510c1bcd13884a3a111f310886f1fedfdb4edfefdf8aca7ff3bfe40446f0becbd96effef5babcf7fbfffe40946f0964f5b6e7bcd97a94f3efd7fb40d86f1fedfdb6effefdfabcf7fffffe40d46f0be4f7bfe7bfd9ff97ffeffffa00b86f1fedffbfeffffdffbffffffffe40bc6f09fc99cfffeaf416fff7faffff20b86f01b0bf5fd7ffd52fdbffe3fff630a06f0bfebfdffffff7bffffffbffff34a86f01f8fffffffffd6ffbfffffffe60f06f0bf4fffff7ffddffdfffefffff70f86f0bf6fffff7ffdfffdfffefffff62f86f0924b510c1bc91b884a3a111f310883f1fedfdb4edfefdf8aca7ff3bfe48443f1ffdfdfdfffefdfcffb7fffffe60643f1079fdffbffebd6e7bf5dfffbe48143f1ffdfdfffffefdfefff7ffffff401c3f0036bd5997fc97ad5eab83b5f632a03f004e5cac3d542fcd7f3adffa5e42643f107fe3fdbfffbfe57fbfdfffee7ae43f14fffffdbfffbfed7fbfdffffeca643f14ff5cef3ff63fcf7ffedfffde62703f14fffdffbffebfef7fffdffffe72b43f0936bd59d7fc97bddeaba3b5f732a83f097edced7f7c2fddff3bfffeff626c3f1dffdeed7f7f2fddff3ffffeff6a6c3f1dfffdfffffebfffffffffffff62383f19769acf77fb3f97dfff3effff4938fd0b76b1fff7fcdfffdefbeff7fe0488fd1ee4f7ffa7bfffff17fffffffa11f0fb0be4f7bfe7bfd9ff97ffeffffa44d8fb14cdffbebfdfafef7fffdfff7e4844fb1fedfdb4edfefdf8aca7ff3bfe5cccfb0a36bd5997fcd7bd5eaba3b5f636a0bf0078e1fdbffcb86473f1dfffae70e4bf14f9fdfdbffebd6c7bf5dfffbe38e4bf0a76fdffb7fcdfff5efbeff7fe66f0bf147fffffbfffbfef7fffdffffe58d4bf0b76ddff77fcdfffdefbeff7ff44d8bf1feffffeffffffffffffffffff480cbf1b37bf59ffffffbdffbfb7fdfe20287f19ff9bcffffbff97fffffeffff001c7f10ffbfdfbfffbfaf7fffdffffe30b47f1bedbd96effefdbabcf7ffffff5c9c7f09f6deef77ff1fdfdfffeffffe63707f0976ddeff7fcdfdfdefbeff7fe40d87f0976fdfff7fcdfffdefbeff7fe50d87f1bfffdfdfffefffdfeafffbfff484c7f10f9fdffbffebd6e7bf5dfffbe68747f1bedfdb6effefdfabcf7ffffff58dc7f14f9fddfbffebd6e7bf5dfffbeb8b57f196f9acf7ffb3f97ffff3effff493cff | false => 0x97491cff7e8d017d7fbeafffe00986d0934b159d7fcd035d6aba3b5f610886d0974f1fff7fcd877d6fbeff7fe70b86d0976f9fff7fcde77dffbefffff62b86d09f6fbfff7ffde77dfffeffffe01b86d0bb6bf5fd7ffd7bfdfffe3fff714a86d0bf6bfdff7ffd7bfdfffebffff54986d0bfeffffffffffffffffffffff54f86d00369849166806055e0902b4f422203e097ed8ed7f7c2e55ff39fffefe40643e104958a42d462d402804df2a1e48443e107fc2ed3f7f2fc57f3fdffeee6a643e197fdaed7f7f2fd5ff3ffffeff6a6c3e1dffdeed7f7f2fddff3ffffefec8643e1049f9b6afdead6238f5dfef3e48143e1079f9ffbffebd667bf5dfffbe68343e107fd8ef3ffe3f477ffddffffe62303e197ff9fffffebf77fffdffffff62783e14f9dcef3ffe3d4e7bf5dfffbec8543e14ffffffbfffbfef7fffdffffeea743e1dffffffffffbfffffffffffffea7c3e10491c842d462d0828049f2a1e48043714cf5eac3d572fcd7f3edffa5e0224370924940041bc119884a3a111f30008371deddca46dfe3dd8aca7ff3bff480c371defdcac7dee3f5dff8dfffbff022c371defdeac7dff3fddffbffffbff0b2c371b6dbd94edfefdb8aca7bf3bff5c8c371fefffbcfdfffffdffbffffbff16ac3709369c4957fc179ddeaba3b5f62220371b37bd59fffeffbdffafb7fdff2a2c371b7fbdddfffeffbdfeafbfbffe6a24371ffffdfdfffefffdffaffffffeea643714ff5eef3ff73fcf7ffedfffde2b24371fffffffffffffffffffffffff2b2c370924b510c1bc913884a1a111f310882f00485ca42d442d482800df2a1e40442f1fedfdb4edfefdf8aca7ff3bff50cc2f0964f5b6e7bc997a94f1efd7fb40582f0048fdb6afdcad6a38f1dfef3e50942f1fedfdb6effefdfabcf7ffffff401c2f0030bd5997fc952c5aa183b5b630a02f14f9fdfdbffebd6c7aa5dfbfbe70e42f1ffffdfdfffefffdfeafffbfff34a82f1ffffdfffffefffffffffffffe70f02f1b25bd10effefdb8bcb7b7fdff10881f1fedfdb6effefdfabcf7ffffff58cc1f0006bd1897dc87ad5eab83b57612a01f0b26bd18d7fcd7bddeaba3b5f716a81f1b77fdfdfffefffdfeafffbfff5eec1f1ffffffffffffffffffffffffedae41f14c95fffbfd7bfef7bffdffffe4844fa14cfe3ffbfdfffef7ffffffffe59f4fa0a76e1ffb7fcdfff5efbeff7ee26a0bd196492c667bb3f9297ff3ed7fb4918bd0b6491b667b8d9fa94f3efd7fb44d8bd1b769bff77fbffffdffffff7ff6238bd0b64b596e7bcd9ba94f3efd7fb00887d0be4b79fe7bfd9bf97ffeffffb01387d09f69bcff7fbdf97dfffeefffe62387d0b76fdfff7fcdfffdefbeff7fe32a87d1967928f7fbb3f97ffff3efffe02247d0186030ff813ef87fffff4fffe02bc7d09fe9bcffffbff97fffffeffff202c7d) | false => (match Nat.blt i 3 with | true => 0x14c95ca62fc62d4a28c4dfef1ec8542a14f9fdffbffebd6e7bf5dfffbef8f42a0000b510819c812800a181013210800b0040e1b4a59c886000a1cf032850c00b0040f5b6a79c896a10f1cfc73a50d00b0b64f5b4e5bcd9f884a3ef13fb54c80b1fedfdb6effefdfabcf7ffffffdcdc0b09249400412c01188401a110f30008070b24bd10c5fcd5b88ca3a331f71488071deddca46d6e2d58ac05ff3affc84c071ffffdfdfffefffdfeafffbffffeec070136004956600605de0920b4f422287409369a497e6b2615ff3f32fcfe212c7419ff9bcffffbff97fffffeffff2b3c74104918842d422d0028041e2a1e480436104f188c3d422f057f0c1efa5e02243614cf5cac3d462f4d7f0cdffa5eca643600361849166006055e0802b4d422203614ff5ced3f662f4d7e0cdfbede6a24361dffdced7f6e2f5dff0dfffeff2a2c36107f1acd3f732f857f3e1efede0b243614ff5eed3f772fcd7f3edffedeeb6436107f1acf3ff33f877ffe1effde6b34361dffdeef7fff3fdfffffffffff6b2c36106d14842df63d882ca69d3bde48043314ed5ca42df63dc82ca6df3bdec844331b6db594edfefdb8aca7bd3bff5c8c3314cd5cac3d562dcc6f26dffa5ec8643314ef5eac3df73fcd7fbedffbdecb64331fffffffffffffffffffffffffdcec330030a15997fc902452a183b5a630a02d0924b110c1bc903084a1a111f310882d0b34b559d7fcd1bcd6a3a3b5f734a82d0974b1dff7fc8036c6e1a9f7fd70b82d0b7efdfffffcfffffffbffffff72b82d0020b51081bc912800a18111b210802b004854a42d4429482000df2a1e40442b14e9fdb4adfebd6828a5df3bbe50c42b0b6cf5b4edfcf9f8a4a3ff3bff54cc2b0060f5b6a7bc996a10f1cfd7ba40502b0b6cf5b6effcf9fab4f3fffffe50d42b14e95ca62fe63d4a28c4dfff9ec8542b14e9fdb6affebd6a38f5dfffbed8d42b1ffdfdfffffefdfefff7fffffffcfc2b0000bd1087dc852818a183a53610800f0924b510c1bc813884a1a111f310880f0936bd59d7fc873ddea9a3b5f732a80f00405ca425440d480800cf221e40400f0964d4a4672c09589401ef96fb40480f0964f9b4e5fc8c708ca1ef33fd50c80f1deddca46f6e2d58bc05ffbeffc84c0f1dedfdb4edfead78aca5ff3bffd8cc0f1dfffdfdfffeaf7dfeadffbffffaec0f0b24bd10c7fcd5b89ca3a3b5f714880f0b64fdb4e7fcddf89ca3efb7ff54c80f0b76fdfdf7fcdffddeabefb7ff76e80f0b64fdb6e7fcddfa9cf3eff7ff54d80f1ffffdfffffefffffeffffffffdccc0f09249100c1b8d19084a3a011f30088751b27b718f9bfffbdffbfb5f9fe03247509369949d7f8d795deaba2b5f622a8751b37bf59ffffffbdffbfb7fdfe212c7519379a4f7ffb3f97ffff36fffe2330751bffbfdfffffffbfffffffffff23b875 | false => 0x14e456ef27b73fcf17fedfffda4970fb0b24b510c1bcd1b884a3a111f3148801092490004028001084012010f10008050b36bd59d7fcd7bddeaba3b5f736a8051fedfdb4edfefdf8aca7ff3bffdccc03104900842d422d0028041c2a0e48043214c95cac3d462d4c6b04dffa1ec8643214ff5eef3ff73fcf7ffedfffdeeb7432004840a42d4428402000df2a0e40442a))
def envRecord (i : ℕ) := Nat.land (Nat.shiftRight (envRecordBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def suppNum (i : ℕ) := Nat.land (envRecord i) 1023
def hotNum (i : ℕ) := Nat.land (Nat.shiftRight (envRecord i) 10) 32767
def pointNum (i : ℕ) := Nat.shiftRight (envRecord i) 25
def firstKeyBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0xf000e700e3c0b9c0e170d3e0b6209220e1d0da50d310b3c0b470adb08ef07df0ea10c900b8408450b5e091f0a6e07550c3d0bc509350575080b055f073f031f0e340b940d4409540d9f0b1c0aea07d20d2d0b340cb508dc0acf0a03087706fb0b7c08400b1005940ae607c809f604ab0930057008b804f80793048306c702b30e8d0ba40c5c08540b4a0adc080c05620b450ad908ed07dc0a5509e9071c04710c5908510839038908f207d9074203210809055d073d031d0719046d0629022d0b640a74091007700ad209fc079404880acd0a00087506f809dd096506a403f9090c076c07c10341087a06f406ca02b40791048006c502b106a103f505b101b50e880ba00b6c0a7c0c37094a081a07360b420ad70aca0a0607fa0782052f045a0c56084e091407680816072e072606360807055a078f0485034a030202d7020a0c54084c0916076a0bbf058a0556031608ea07d4087206f2052a045204b202be0834038407bc033c054e030e045e0242073a031806c202ae02d20206027e01160c34094808180734080007880350030808f7087f07a006bc070f069702e6027a0bbc0588055403140532045602da020c053704bf0449029c02df027601e7010e0814072c072406340530045402d8020e079c06b406ac05bc043a03c202600196054c030c045c024004b802b80284011c0447029403cf01c8025a018e016f00960e100d380d980b240d200ca80b0208aa0b410ad50ac90a0508f5087d07a306bf0b5909190ae107cd0af908a10a0f06dd08050559078d0487053504bd044b029f0b5809180ae007cc0af808a00a0e06dc08e907d7087106f1079f06b706af05bf0a68075009f004a40a0806d80978042c0739031b06c102ad0445029703cd01cb0c3009500bb8059008fc0884053c04c407f90781052d0459070d069502e502790811073105510311079906b9044c02990349030102d5020902dd027501e5010d0810073005500310079806b8044d02980529045004b102bd043903c102630195072006300460024806a805b803d401d002d10205027d01150259018d016d00950b400ad40ac80a0408f4087c07a206be0a5009e409d80960070a0692043e03c608e807d6087006f0079e06b606ae05be07150469069d03f102e30273025f019208040558078c0486053404bc044a029e07140468069c03f002e20272025e01930738031a06c002ac0444029603cc01ca0624022805ac01b001e2010a016a009207f80780052c0458070c069402e4027807080690043c03c4061805a001f4017c0528045104b002bc043803c00262019402e10271025d019101ed017500f500890348030002d4020802dc027401e4010c02e00270025c019001ec017400f4008802d00204027c01140258018c016c009401e001080168009000f0008400780000 | false => 0xf780f6c0f380ee40f060e7a0eaa0c9a0f030e730e3f0b9f0e8f0ba70c5f08570f310edd0e5d0c7d0e3a0b9b0b83084b0ea30c930b8708470c5a0853083b038b0f300edc0e5c0c7c0e3b0b9a0b82084a0e370b970d4709570b670a77091307730e580c780de00c000d4a095a0b1a059a0b7f08430b130597090f076f07c303430f040e780ea80c980e240dac0c440bcc0e150d3d0b6109210b490adf080f05610e390b990b8108490d340b39093905790b5d091d0a6d075708f107db074103230e380b980b8008480d350b38093805780d9d0b1f0ae907d00ad109ff0797048a0d4809580b1805980cbc08e008c005000ae507cb09f504a9087906f706c902b70f020e720e3e0b9e0e8e0ba60c5e08560e120d3a0d9a0b260c3209520bba05920e360b960d4609560b660a76091207720b5b091a0ae307cf08130732055203130ea20c920b8608460c5b0852083a038a0b5a091b0ae207ce08120733055303120b7e08420b120596090e076e07c203420a6a075209f204a6072206320462024a0e140d3c0b6009200b480ade080e05600d220caa0b0008a808fe0886053e04c60d9c0b1e0ae807d10ad009fe0796048b0afa08a20a0d06df079b06ba044f029b0b5c091c0a6c075608f007da074003220afb08a30a0c06de079a06bb044e029a0ae407ca09f404a8087806f606c802b60a0a06da097a042e06aa05ba03d601d20f010e710e3d0b9d0e160d3f0b6309230e890ba10b6d0a7d0c36094b081b07370e350b950d4509550d9e0b1d0aeb07d30c55084d0917076b0bbe058b055703170ea00c910b8508440b5f091e0a6f07540c57084f091507690817072f072706370b7d08410b1105950ae707c909f704aa0835038507bd033d054f030f045f02430e8c0ba50c5d08550b4b0add080d05630c3509490819073508010789035103090b650a75091107710ad309fd079504890815072d072506350531045502d9020f0c5808500838038808f307d8074303200bbd0589055503150533045702db020d090d076d07c00340087b06f506cb02b5054d030d045d024104b902b90285011d0e1c0da40d300b3d0b460ada08ee07de0b430ad60acb0a0707fb0783052e045b0d2c0b350cb408dd0ace0a02087606fa08eb07d5087306f3052b045304b302bf0c3c0bc409340574080a055e073e031e0806055b078e0484034b030302d6020b0931057108b904f90792048206c602b2073b031906c302af02d30207027f01170b440ad808ec07dd0a5409e8071d047008f6087e07a106bd070e069602e7027b0acc0a01087406f909dc096406a503f8079d06b506ad05bd043b03c3026101970808055c073c031c0718046c0628022c053604be0448029d02de027701e6010f0790048106c402b006a003f405b001b40446029503ce01c9025b018f016e0097)
def firstKey (i : ℕ) := Nat.land (Nat.shiftRight (firstKeyBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def permuteBits (pw x : ℕ) : ℕ := (List.range 10).foldl (fun acc i =>
  if x.testBit i then acc ||| (1 <<< ((pw >>> (4*i)) &&& 15)) else acc) 0
def bitSub (a b : ℕ) : Bool := a &&& b == a
def coldMask (a b : ℕ) := negativeSig a &&& negativeSig b
def stableSig (a b na nb v : ℕ) : ℕ :=
  (32767 ^^^ incidence v) &&& ((32767 ^^^ ((if a.testBit v then 32767 else na) &&&
    (if b.testBit v then 32767 else nb))) ||| (na &&& nb))
def validClique (a b c : ℕ) : Bool :=
  let xs := (List.range 10).filter (fun v => c.testBit v)
  bitSub c (a ||| b) && xs.length == 6 &&
    let na := negativeSig a
    let nb := negativeSig b
    let ss := xs.map fun v => (v,stableSig a b na nb v,incidence v)
    ss.all fun v => ss.all fun w => v.1 == w.1 || (v.2.1 &&& w.2.1 != 0 && v.2.1 &&& w.2.2 != 0)
def validEnv (e a b : ℕ) : Bool :=
  bitSub (suppNum e) (a ||| b) && bitSub (hotNum e) (coldMask a b) &&
    bitSub (positiveSig a &&& positiveSig b) (pointNum e)
def vertexMark (π : Equiv.Perm V) (P : Feature → Slot → Prop) (z : Feature) := P (z.map π.symm)
lemma meet_map (π : Equiv.Perm V) (L U : Finset V) :
    meets (L.map π.toEmbedding) (U.map π.toEmbedding) ↔ meets L U := by
  constructor
  · rintro ⟨x,hx,ux⟩
    exact ⟨π.symm x,Finset.mem_map_equiv.mp hx,Finset.mem_map_equiv.mp ux⟩
  · rintro ⟨x,hx,ux⟩
    exact ⟨π x,Finset.mem_map.mpr ⟨x,hx,rfl⟩,Finset.mem_map.mpr ⟨x,ux,rfl⟩⟩
lemma present_push (π : Equiv.Perm V) (A B U : Finset V) (z : Feature) :
    present (A.map π.toEmbedding) (B.map π.toEmbedding) (U.map π.toEmbedding) z ↔
      present A B U (z.map π.symm) := by
  cases z with
  | none => exact (meet_map π A U).and (meet_map π B U)
  | some v => exact Finset.mem_map_equiv
lemma Vcap {A B P} (π : Equiv.Perm V) (h : capacity A B P) :
    capacity (A.map π.toEmbedding) (B.map π.toEmbedding) (vertexMark π P) := by
  intro v
  obtain ⟨S,mem,le,one⟩ := h (π.symm v)
  exact ⟨S,mem,le,fun hv => one (hv.imp Finset.mem_map_equiv.mp Finset.mem_map_equiv.mp)⟩
lemma Vlayout {A B P} (π : Equiv.Perm V) (ρ : Equiv.Perm (Fin 15))
    (row : ∀ r, (rows r).map π.toEmbedding = rows (ρ r)) (h : layout A B P) :
    layout (A.map π.toEmbedding) (B.map π.toEmbedding) (vertexMark π P) := by
  obtain ⟨O,R,M,uniq,avoid,refs,out,pos⟩ := h
  refine ⟨O,R,fun r s => M (ρ.symm r) s,fun r => uniq (ρ.symm r),?_,fun r => refs (ρ.symm r),
    fun r => out (ρ.symm r),?_⟩
  · intro r s z mr pm pr
    apply avoid (ρ.symm r) s (z.map π.symm) mr pm
    apply (present_push π A B (rows (ρ.symm r)) z).mp
    simpa only [row,Equiv.apply_symm_apply] using pr
  · rintro _ ⟨r,v,miss,rfl⟩ a cl
    let T := insert (π.symm v) (rows (ρ.symm r))
    have er : (rows (ρ.symm r)).map π.toEmbedding = rows r := by rw [row,Equiv.apply_symm_apply]
    have pushed : T.map π.toEmbedding = insert v (rows r) := by
      simp only [T,Finset.map_insert,Equiv.coe_toEmbedding,Equiv.apply_symm_apply,er]
    have hv : π.symm v ∉ rows (ρ.symm r) := by
      intro inside
      exact miss (er ▸ Finset.mem_map_equiv.mpr inside)
    apply pos T ⟨ρ.symm r,π.symm v,hv,rfl⟩ a
    intro k both
    apply cl k
    intro b
    rcases both b with ⟨z,hz,pr⟩ | ref
    · let t := z.map π
      have inv : t.map π.symm = z := by cases z <;> simp [t]
      refine Or.inl ⟨t,by simpa only [vertexMark,inv] using hz,?_⟩
      rw [←pushed]
      exact (present_push π A B T t).mpr (inv.symm ▸ pr)
    · exact Or.inr ref
def positiveColumn (i : ℕ) : ℕ := (match Nat.blt i 5 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x5925a8860de68dc4251d088f9 | false => 0xa64ae5216a316a414026f950f) | false => (match Nat.blt i 3 with | true => 0x49b4c24ab34030aef04915a7a | false => (match Nat.blt i 4 with | true => 0x2070db53ce44310878e7e394 | false => 0x80381041c0997c2bf9f0a7c27))) | false => (match Nat.blt i 7 with | true => (match Nat.blt i 6 with | true => 0x3c00679ff0180331e00c7fc7 | false => 0xc00187e001e003c1fff07ff8) | false => (match Nat.blt i 8 with | true => 0xf0001f80001fffc01ffff8000 | false => (match Nat.blt i 9 with | true => 0xffffe000001fffffe00000000 | false => 0xffffffffffe00000000000000))))
def accumulateSig (col : ℕ → ℕ) (x : ℕ) := (List.range 10).foldl
  (fun a v => (if x.testBit v then col v else 0) ||| a) 0
lemma accumulates (col : ℕ → ℕ) (x j : ℕ) :
    (accumulateSig col x).testBit j = true ↔
      ∃ v : V, x.testBit v.val = true ∧ (col v.val).testBit j = true := by
  have go (xs : List ℕ) (a : ℕ) :
      (xs.foldl (fun d v => (if x.testBit v then col v else 0) ||| d) a).testBit j = true ↔
        a.testBit j = true ∨ ∃ i ∈ xs, x.testBit i = true ∧ (col i).testBit j = true := by
    induction xs generalizing a with
    | nil => simp
    | cons i xs ih =>
      simp only [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true,List.mem_cons]
      cases e : x.testBit i <;> simp [e] <;> aesop
  rw [accumulateSig,go]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,List.mem_range]
  exact ⟨fun ⟨v,hv,hit⟩ => ⟨⟨v,hv⟩,hit⟩,fun ⟨v,hit⟩ => ⟨v.val,v.isLt,hit⟩⟩
lemma negative_join (x : ℕ) : negativeSig x = accumulateSig incidence x := by rfl
lemma positive_join (x : ℕ) : positiveSig x = accumulateSig positiveColumn x := by rfl
lemma incidence_ok : ∀ v : V, ∀ r : Fin 15, (incidence v.val).testBit r.val = true ↔ v ∈ rows r := by
  decide +kernel
set_option maxRecDepth 10000 in
lemma col_point_ok : ∀ v : V, ∀ u : PositiveId, (positiveColumn v.val).testBit u.val = true ↔
    v ∈ fsCode (liftPoint u).val := by decide +kernel
lemma negative_has (x : ℕ) (r : Fin 15) :
    (negativeSig x).testBit r.val = true ↔ meets (fsCode x) (rows r) := by
  rw [negative_join,accumulates]
  unfold meets
  apply exists_congr
  intro v
  simp [fsCode,incidence_ok]
lemma positive_has (x : ℕ) (u : PositiveId) :
    (positiveSig x).testBit u.val = true ↔ meets (fsCode x) (fsCode (liftPoint u).val) := by
  rw [positive_join,accumulates]
  unfold meets
  apply exists_congr
  intro v
  exact and_congr (by simp [fsCode]) (col_point_ok v u)
lemma bitSub_use {a b : ℕ} (h : bitSub a b = true) (i : ℕ) (e : a.testBit i = true) : b.testBit i = true := by
  have t := congrArg (fun z : ℕ => z.testBit i) (beq_iff_eq.mp h)
  simpa only [Nat.testBit_and,e,Bool.true_and] using t
def modelNeg (e : ℕ) (r : Fin 15) := (liftRow r).val ||| (if (hotNum e).testBit r.val then 1024 else 0)
def modelPos (e : ℕ) (u : PositiveId) := (liftPoint u).val ||| (if (pointNum e).testBit u.val then 1024 else 0)
lemma base_bit (x : Fin 1024) (hit : Bool) (v : V) :
    (x.val ||| (if hit then 1024 else 0)).testBit v.val = x.val.testBit v.val := by
  have h : (1024 : ℕ).testBit v.val = false := by revert v; decide +kernel
  cases hit <;> simp [h,Nat.testBit_or]
lemma seed_bit (x : Fin 1024) (hit : Bool) :
    (x.val ||| (if hit then 1024 else 0)).testBit 10 = hit := by
  have h : x.val.testBit 10 = false := Nat.testBit_lt_two_pow x.isLt
  cases hit <;> simp [h,Nat.testBit_or] <;> decide
lemma compatible_support {e a b : ℕ} (good : validEnv e a b = true) :
    ∀ v : V, (suppNum e).testBit v.val = true → v ∈ fsCode a ∨ v ∈ fsCode b := by
  intro v hv
  have inc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp good).1).1
  have bit := bitSub_use inc _ hv
  simpa [Nat.testBit_or,fsCode] using bit
lemma compatible_hot {e a b : ℕ} (good : validEnv e a b = true) :
    ∀ r ∈ seedRows (hotNum e), present (fsCode a) (fsCode b) (rows r) none := by
  intro r hr
  have inc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp good).1).2
  have bit := bitSub_use inc _ (Finset.mem_filter.mp hr).2
  change ((negativeSig a) &&& negativeSig b).testBit r.val = true at bit
  rw [Nat.testBit_and,Bool.and_eq_true] at bit
  exact ⟨(negative_has a r).mp bit.1,(negative_has b r).mp bit.2⟩
lemma compatible_neg {e a b : ℕ} (good : validEnv e a b = true) :
    ∀ r z, (modelNeg e r).testBit z.val = true → present (fsCode a) (fsCode b) (rows r) (featureOf z) := by
  intro r z bit
  rcases eq_or_lt_of_le (Nat.le_of_lt_succ z.isLt) with eq | lt
  · have en : featureOf z = none := by simp [featureOf,atFeature,eq]
    rw [en]
    have hit : (hotNum e).testBit r.val = true := by simpa only [eq,modelNeg,seed_bit] using bit
    exact compatible_hot good _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩)
  · let v : V := ⟨z.val,lt⟩
    have en : featureOf z = some v := by simp [featureOf,atFeature,v,lt]
    rw [en]
    have hit : (liftRow r).val.testBit v.val = true := (base_bit (liftRow r) _ v) ▸ bit
    have mem : v ∈ fsCode (liftRow r).val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
    exact negNumber_spec r ▸ mem
lemma compatible_pos {e a b : ℕ} (good : validEnv e a b = true) :
    ∀ u z, present (fsCode a) (fsCode b) (fsCode (liftPoint u).val) z →
      (modelPos e u).testBit (fid z).val = true := by
  intro u z hz
  cases z with
  | none =>
    change (modelPos e u).testBit 10 = true
    rw [modelPos,seed_bit]
    have inc := (Bool.and_eq_true_iff.mp good).2
    apply bitSub_use inc
    change ((positiveSig a) &&& positiveSig b).testBit u.val = true
    rw [Nat.testBit_and,Bool.and_eq_true]
    exact ⟨(positive_has a u).mpr hz.1,(positive_has b u).mpr hz.2⟩
  | some v =>
    change (modelPos e u).testBit v.val = true
    rw [modelPos,base_bit _ _ v]
    exact (Finset.mem_filter.mp hz).2
def inverseNumBlock (i : ℕ) : ℕ := 0x5f2f75616b725727524c231f736a5626534d221e5e2e746077635d2d4f51211d71695525676f5a2b5b2a666e4b4a1b1a43373a4447394135171413113b454236463840341615121076625c2c504e201c706854246d6559296c645828494819183f33323e3d313c300f0d0e0c070a09050b06080403020100
def inverseNum (i : ℕ) := Nat.land (Nat.shiftRight (inverseNumBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
def rowPermCodeBlock (i : ℕ) : ℕ := 0xc490d5a21e837b60c452a9d07e831b60e851a9d70c432b60e897d5a12c430b60e137b5a84c290d60e158a3b70c294d60c230b5a48e197d60c254a3b07e198d60c094d3b21e758a60c032b9d48e751a60e731b9d84c052a60e798d3b12c054a60e15a837b096c4d20e13b758a496c0d2096307584ae1cbd2096548370be1cad2090c4d3761eb5a82090367cd4aeb51820eb317cda49056820ebcad3716905482094c0d5861ea3b72094568cd0bea31720ea518cdb09436720eacbd581694307205ae18c4209d376b05ac24e8179d306b09dc04e8715a326b09de78c4025a316b090376c4da52e18b090cd4367152ea8b052316c4ad90e78b052ca4361790ed8b051ea8362097cd4b051326e8ad97c04b097306e8da51c24b097ed8360251ca4b05ac42e1873b906d05ae81c2403b976d03bc02e1785a946d03be71c2045a986d037906e1ba58c42d037eb1960458ca2d058946e1ab37c02d058ea1964037cb2d030976c2ba54e81d030cb2967854ea1d054ca2968730eb1d054986c2ab30e71d037e1b9064cd5a28037960eb1acd54280cd940eba13756280cdeab90463751280c45a290d736e1b80c49d052a136e7b8036512907dc4eab8036970521ac4edb8031e7b5264ca9d08031562eb7dca94080ca542ebd73196080caedb524631970809dc40e7813b526a09de87c0423b516a03be17c0249d586a03bc20e7189d546a094586c0db32e17a094cd0568132eb7a032516c0bd94e87a032cb0561894ed7a031eb7562498cd0a031526e7bd98c40a098546e7db31c20a098ed7564231cb0a058e1a9460cd3b27058964ea1bcd30270cd904eab15836270cdeba94065831270c09d432b156e8a70c03b294d856e1a7056312948dc0eba7056984321bc0eda7051e8a3260cb9d47051362ea8dcb90470cb302ead85196470cbeda32065198470e85a197d036c2b40e89d751a236c0b4036907512ae8cdb4036521970de8cab40ea581cbd03296740eacdb5186329074032c0b5168ea9d74032561cb0dea9874030c2b9768ed5a14030967cb2aed58140edcab97863052140ed987cba23056140c25a430b796e8d10c23b054a896e7d1096370548ac2ebd1096584307bc2ead1097e8d3062cb5a41097360ed8acb52410cbead30269758410cb320eda89756410caebd54269837010ca524edb7983601098e7d5462ca3b01098564ed7bca32010eb371cad45296800ebcda3176529480052c4a3167eb9d80052361ca4deb97800e79d831b256c4a00e73b198d456c2a0056948312be7cda0056321984de7cba0054c2a9867ed3b10054968ca2bed37100ed978cab25436100edcba9876543210
def rowPermCode (i : ℕ) := Nat.land (Nat.shiftRight (rowPermCodeBlock (Nat.shiftRight i 7)) (Nat.shiftLeft (Nat.land i 127) 6)) 18446744073709551615
abbrev PIndex := Fin 120
def destVertex (pw i : ℕ) := (pw >>> (4*i)) &&& 15
def coord (p : PIndex) (v : V) : V := ⟨(destVertex (permNum p.val) v.val) % 10,by omega⟩
def inverseId (p : PIndex) : PIndex := ⟨inverseNum p.val % 120,by omega⟩
def coordRow (p : PIndex) (r : Fin 15) : Fin 15 := ⟨destVertex (rowPermCode p.val) r.val % 15,by omega⟩
lemma coord_value : ∀ p : PIndex, ∀ v : V, destVertex (permNum p.val) v.val = (coord p v).val := by
  decide +kernel
lemma coordInv : ∀ p : PIndex, ∀ v : V, coord (inverseId p) (coord p v) = v ∧
    coord p (coord (inverseId p) v) = v := by decide +kernel
lemma rowInv : ∀ p : PIndex, ∀ r : Fin 15, coordRow (inverseId p) (coordRow p r) = r ∧
    coordRow p (coordRow (inverseId p) r) = r := by decide +kernel
def vEquiv (p : PIndex) : Equiv.Perm V :=
  ⟨coord p,coord (inverseId p), fun v => (coordInv p v).1,fun v => (coordInv p v).2⟩
def rEquiv (p : PIndex) : Equiv.Perm (Fin 15) :=
  ⟨coordRow p,coordRow (inverseId p), fun r => (rowInv p r).1,fun r => (rowInv p r).2⟩
set_option maxRecDepth 10000 in
lemma preserveRows : ∀ p : PIndex, ∀ r : Fin 15,
    (rows r).map (vEquiv p).toEmbedding = rows (rEquiv p r) := by decide +kernel
lemma permute_member (pw x j : ℕ) : (permuteBits pw x).testBit j = true ↔
    ∃ v : V, x.testBit v.val = true ∧ destVertex pw v.val = j := by
  let f m i := if x.testBit i then m ||| (1 <<< (destVertex pw i)) else m
  have go (xs : List ℕ) (a : ℕ) : (xs.foldl f a).testBit j = true ↔
      a.testBit j = true ∨ ∃ i ∈ xs, x.testBit i = true ∧ destVertex pw i = j := by
    induction xs generalizing a with
    | nil => simp
    | cons i ts ih =>
      simp only [List.foldl_cons,ih,List.mem_cons]
      cases e : x.testBit i <;> simp [f,e,Nat.one_shiftLeft,Nat.testBit_or,Nat.testBit_two_pow] <;> aesop
  change ((List.range 10).foldl f 0).testBit j = true ↔ _
  rw [go]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,List.mem_range]
  exact ⟨fun ⟨v,hv,mem⟩ => ⟨⟨v,hv⟩,mem⟩,fun ⟨v,mem⟩ => ⟨v.val,v.isLt,mem⟩⟩
lemma permute_set (p : PIndex) (x : ℕ) :
    fsCode (permuteBits (permNum p.val) x) = (fsCode x).map (vEquiv p).toEmbedding := by
  ext v
  simp only [fsCode,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,permute_member]
  constructor
  · rintro ⟨w,bit,eq⟩
    exact ⟨w,bit,Fin.ext ((coord_value p w).symm.trans eq)⟩
  · rintro ⟨w,bit,rfl⟩
    exact ⟨w,bit,coord_value p w⟩
lemma permute_bound (p : PIndex) (x : ℕ) : permuteBits (permNum p.val) x < 1024 := by
  by_contra! ge
  obtain ⟨i,large,hit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (n := 10) ge
  obtain ⟨v,_,eq⟩ := (permute_member _ _ _).mp hit
  have e := (coord_value p v).symm.trans eq
  have := (coord p v).isLt
  omega
def chooseP (x : Fin 1024) : PIndex := ⟨firstKey x.val % 120,by omega⟩
def chooseRow (x : Fin 1024) : Fin 34 := ⟨firstKey x.val / 120 % 34,by omega⟩
set_option maxRecDepth 10000 in
lemma canonical_row : ∀ x : Fin 1024, permuteBits (permNum (chooseP x).val) x.val = repNum (chooseRow x).val := by
  decide +kernel
lemma transfer_layout {a b : ℕ} {P} (c : capacity (fsCode a) (fsCode b) P)
    (h : layout (fsCode a) (fsCode b) P) (p : PIndex) :
    capacity (fsCode (permuteBits (permNum p.val) a)) (fsCode (permuteBits (permNum p.val) b)) (vertexMark (vEquiv p) P) ∧
    layout (fsCode (permuteBits (permNum p.val) a)) (fsCode (permuteBits (permNum p.val) b)) (vertexMark (vEquiv p) P) := by
  rw [permute_set,permute_set]
  exact ⟨Vcap (vEquiv p) c,Vlayout (vEquiv p) (rEquiv p) (preserveRows p) h⟩
lemma meets_insert_bits (a : ℕ) (v : V) (r : Fin 15) :
    meets (fsCode a) (insert v (rows r)) ↔ a.testBit v.val = true ∨ (negativeSig a).testBit r.val = true := by
  rw [negative_has]
  constructor
  · rintro ⟨u,ha,hu⟩
    rcases Finset.mem_insert.mp hu with rfl | hr
    · exact Or.inl (Finset.mem_filter.mp ha).2
    · exact Or.inr ⟨u,ha,hr⟩
  · rintro (hv | ⟨w,ha,hr⟩)
    · exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,Finset.mem_insert_self ..⟩
    · exact ⟨w,ha,Finset.mem_insert_of_mem hr⟩
lemma all_rows_bits : ∀ r : Fin 15, (32767 : ℕ).testBit r.val = true := by decide +kernel
lemma incidence_bound : ∀ v : V, incidence v.val < 2^15 := by decide +kernel
def signature (a b : ℕ) (v : V) := stableSig a b (negativeSig a) (negativeSig b) v.val
lemma stable_witness {a b : ℕ} {v : V} {r : Fin 15} (h : (signature a b v).testBit r.val = true) :
    stable (fsCode a) (fsCode b) r v := by
  have augment (x : ℕ) (e : meets (fsCode x) (insert v (rows r))) :
      (if x.testBit v.val then 32767 else negativeSig x).testBit r.val = true := by
    rcases (meets_insert_bits x v r).mp e with hit | old
    · simp [hit,all_rows_bits]
    · cases bit : x.testBit v.val <;> simp [bit,old,all_rows_bits]
  simp only [signature,stableSig,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,all_rows_bits,
    Bool.true_xor,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  constructor
  · intro mem
    have bit := (incidence_ok v r).mpr mem
    simp [bit] at h
  · rintro ⟨l,rr⟩
    have la := augment a l
    have rb := augment b rr
    rcases h.2 with off | ⟨p,q⟩
    · simp [la,rb] at off
    · exact ⟨(negative_has a r).mp p,(negative_has b r).mp q⟩
lemma overlap_row {a b y : ℕ} (v : V) (nz : signature a b v &&& y != 0) :
    ∃ r : Fin 15, (signature a b v).testBit r.val = true ∧ y.testBit r.val = true := by
  obtain ⟨i,_,bit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (n := 0) (x := signature a b v &&& y)
    (by have ne := bne_iff_ne.mp nz; omega)
  rw [Nat.testBit_and,Bool.and_eq_true] at bit
  have lt : i<15 := by
    by_contra! ge
    have p : 2^15 ≤ 2^i := Nat.pow_le_pow_right (by decide) ge
    have hi := Nat.testBit_lt_two_pow ((incidence_bound v).trans_le p)
    have no := Nat.testBit_lt_two_pow ((by decide : 32767 < 2^15).trans_le p)
    have z := bit.1
    simp [signature,stableSig,Nat.testBit_and,Nat.testBit_xor,hi,no] at z
  exact ⟨⟨i,lt⟩,bit⟩
lemma clique_check_sound {a b c : ℕ} {P} (check : validClique a b c = true)
    (cp : capacity (fsCode a) (fsCode b) P) (lh : layout (fsCode a) (fsCode b) P) : False := by
  let xs := (List.range 10).filter (fun v => c.testBit v)
  let sig (v : ℕ) := (v,stableSig a b (negativeSig a) (negativeSig b) v,incidence v)
  have H := Bool.and_eq_true_iff.mp check
  have base := Bool.and_eq_true_iff.mp H.1
  have size : xs.length = 6 := beq_iff_eq.mp base.2
  have spec : (xs.map sig).all (fun v => (xs.map sig).all fun w => v.1 == w.1 ||
      (v.2.1 &&& w.2.1 != 0 && v.2.1 &&& w.2.2 != 0)) = true := H.2
  have atPos (i : Fin 6) : i.val<xs.length := by rw [size]; exact i.isLt
  let val (i : Fin 6) := xs[i.val]'(atPos i)
  have inList (i : Fin 6) : val i ∈ xs := List.getElem_mem (atPos i)
  have bounds (i : Fin 6) : val i < 10 := List.mem_range.mp (List.mem_filter.mp (inList i)).1
  let f (i : Fin 6) : V := ⟨val i,bounds i⟩
  have inj (i j : Fin 6) (ne : i ≠ j) : val i ≠ val j := by
    intro e
    have nd : xs.Nodup := (List.nodup_range (n := 10)).filter _
    exact ne (Fin.ext (nd.getElem_inj.mp e))
  have pair (i j : Fin 6) (ne : i ≠ j) :
      (signature a b (f i) &&& signature a b (f j) != 0) ∧
      (signature a b (f i) &&& incidence (f j).val != 0) := by
    have l := List.all_eq_true.mp spec (sig (val i)) (List.mem_map_of_mem (inList i))
    have rr := List.all_eq_true.mp l (sig (val j)) (List.mem_map_of_mem (inList j))
    simpa [sig,val,f,signature,show xs[i.val] ≠ xs[j.val] from inj i j ne] using rr
  apply six_conflict cp lh f
  · intro i
    have on := (List.mem_filter.mp (inList i)).2
    have bit := bitSub_use base.1 _ on
    simpa only [fsCode,Finset.mem_filter,Finset.mem_univ,true_and,Nat.testBit_or,Bool.or_eq_true] using bit
  · intro i j ne
    have ij := pair i j ne
    have ji := pair j i ne.symm
    obtain ⟨r,rv,rw⟩ := overlap_row (f i) ij.1
    obtain ⟨s,sv,sw⟩ := overlap_row (f i) ij.2
    obtain ⟨t,tw,tv⟩ := overlap_row (f j) ji.2
    exact ⟨⟨r,stable_witness rv,stable_witness rw⟩,
      ⟨s,stable_witness sv,(incidence_ok _ _).mp sw⟩,
      ⟨t,stable_witness tw,(incidence_ok _ _).mp tv⟩⟩
abbrev EnvelopeId := Fin 201
def rejectsEnvelope (e : EnvelopeId) : Prop :=
  ∀ a b P, validEnv e.val a b = true →
    capacity (fsCode a) (fsCode b) P → layout (fsCode a) (fsCode b) P → False
lemma dirty_moves {a b : ℕ} (p : PIndex) (dirty : ∃ r, present (fsCode a) (fsCode b) (rows r) none) :
    ∃ r, present (fsCode (permuteBits (permNum p.val) a)) (fsCode (permuteBits (permNum p.val) b)) (rows r) none := by
  obtain ⟨r,hot⟩ := dirty
  refine ⟨rEquiv p r,?_⟩
  rw [permute_set,permute_set,←preserveRows]
  exact (present_push (vEquiv p) (fsCode a) (fsCode b) (rows r) none).mpr hot
def silentZero (m : Marks) : Prop := ∀ k b, m 0 k b = false
lemma silent_move {m : Marks} (h : silentZero m) (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) :
    silentZero (moved m π sw) := fun k b => h (π k) (turn (sw k) b)
lemma silent_value {m : Marks} (h : silentZero m) : represented m 0 = 0 := by
  apply word_ext
  intro k b
  change (rawNumber m 0).val.testBit (slotNum (k,b)) = (0 : ℕ).testBit _
  rw [rawNumber_bit,h,Nat.zero_testBit]
lemma zero_set : fsCode 1 = {0} := by decide +kernel
lemma zero_present (U : Finset V) : present (fsCode 1) (fsCode 1) U none ↔ (0 : V) ∈ U := by
  simp [present,meets,zero_set]
lemma diagonal_limit : validEnv 199 1 1 = true := by decide +kernel
lemma diagonal_neg : ∀ r : Fin 15, (hotNum 199).testBit r.val = true ↔ (0 : V) ∈ rows r := by decide +kernel
lemma diagonal_pos : ∀ u : PositiveId, (pointNum 199).testBit u.val = true ↔ (0 : V) ∈ fsCode (liftPoint u).val := by decide +kernel
set_option maxRecDepth 10000 in
lemma point_indices : ∀ r : Fin 15, ∀ v : V, v ∉ rows r → ∃ u : PositiveId,
    fsCode (liftPoint u).val = insert v (rows r) := by decide +kernel
def mergedZero (P : Feature → Slot → Prop) : Feature → Slot → Prop
  | none,s => P none s ∨ P (some 0) s
  | some v,s => v ≠ 0 ∧ P (some v) s
lemma diagonal_world {a b : ℕ} {P} (env : validEnv 199 a b = true)
    (cap : capacity (fsCode a) (fsCode b) P) (layout_ok : layout (fsCode a) (fsCode b) P) :
    ∃ m, world (fsCode 1) (fsCode 1) m ∧ silentZero m := by
  classical
  obtain ⟨O,R,M,uniq,avoid,refs,out,positive⟩ := layout_ok
  let m := marksFor (mergedZero P) M
  have capacity' : capacity (fsCode 1) (fsCode 1) (mergedZero P) := by
    intro v
    by_cases e : v=0
    · subst v
      refine ⟨∅,?_,by simp,by simp⟩
      simp [mergedZero]
    · obtain ⟨S,he,le,_⟩ := cap v
      refine ⟨S,fun k => ?_,le,?_⟩
      · simp [he,mergedZero,e]
      · simp [zero_set,e]
  refine ⟨m,⟨mergedZero P,O,R,M,capacity',⟨uniq,?_,refs,out,?_⟩,rfl⟩,?_⟩
  · intro r s z cut pos pr
    cases z with
    | none =>
      have v := (zero_present _).mp pr
      rcases pos with mem | mem
      · exact avoid r s none cut mem (compatible_hot env _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,(diagonal_neg r).mpr v⟩))
      · exact avoid r s (some 0) cut mem v
    | some v => exact avoid r s (some v) cut pos.2 pr
  · intro U pointU active closed
    apply positive U pointU active
    intro k both
    apply closed k
    intro d
    rcases both d with ⟨z,pz,pr⟩ | ref
    · cases z with
      | none =>
        refine Or.inl ⟨none,Or.inl pz,(zero_present _).mpr ?_⟩
        obtain ⟨r,v,hv,rs⟩ := pointU
        obtain ⟨u,eq⟩ := point_indices r v hv
        have e : U = fsCode (liftPoint u).val := rs.trans eq.symm
        rw [e] at pr ⊢
        apply (diagonal_pos u).mp
        have actual := compatible_pos env u none pr
        change (modelPos 199 u).testBit 10 = true at actual
        simpa only [modelPos,seed_bit] using actual
      | some v =>
        by_cases eq : v=0
        · subst v
          exact Or.inl ⟨none,Or.inr pz,(zero_present _).mpr pr⟩
        · exact Or.inl ⟨some v,⟨eq,pz⟩,pr⟩
    · exact Or.inr ref
  · intro k side
    change decide (mergedZero P (some 0) (k,side)) = false
    simp [mergedZero]
def permittedWorld (e : ℕ) (A B : Finset V) (m : Marks) : Prop :=
  if e=199 then world (fsCode 1) (fsCode 1) m ∧ silentZero m else world A B m
def actualStart (e : ℕ) : ℕ :=
  let d := initialPacked (suppNum e) (hotNum e)
  if e=199 then replacePacked d 0 1 else d
def incidentRows (v : V) := Finset.univ.filter (fun r : Fin 15 => v ∈ rows r)
lemma fiveIncident : ∀ v : V, (incidentRows v).card = 5 := by decide +kernel
lemma opposedSlots {A B P O R M} (h : rooted A B P O R M) (v : V)
    (hot : ∀ r, v ∈ rows r → present A B (rows r) none) :
    ∃ S : Finset (Fin 5), (∀ k, k ∈ S ↔ ∃ b, P (some v) (k,b) ∨ P none (k,b)) ∧ S.card ≤ 2 := by
  classical
  let S := Finset.univ.filter fun k : Fin 5 => ∃ b, P (some v) (k,b) ∨ P none (k,b)
  have mem (k : Fin 5) : k ∈ S ↔ ∃ b, P (some v) (k,b) ∨ P none (k,b) := by simp [S]
  refine ⟨S,mem,?_⟩
  let code (r : ↥(incidentRows v)) (k : ↥Sᶜ) := decide (M r.val (k.val,true))
  have inj : Function.Injective code := by
    intro r t eq
    by_contra ne
    have hr := (Finset.mem_filter.mp r.property).2
    have ht := (Finset.mem_filter.mp t.property).2
    have neq : r.val ≠ t.val := fun e => ne (Subtype.ext e)
    obtain ⟨k,b,mr,mt⟩ := apart_cut h (hot_apart neq (hot r.val hr))
    have idle : k ∉ S := by
      intro ks
      obtain ⟨d,hd⟩ := (mem k).mp ks
      by_cases side : d = b
      · subst d
        exact hd.elim (fun hz => h.2.1 _ _ _ mr hz hr) (fun hz => h.2.1 _ _ _ mr hz (hot _ hr))
      · have side' : d = !b := by cases d <;> cases b <;> simp_all
        rw [side'] at hd
        exact hd.elim (fun hz => h.2.1 _ _ _ mt hz ht) (fun hz => h.2.1 _ _ _ mt hz (hot _ ht))
    let i : ↥Sᶜ := ⟨k,Finset.mem_compl.mpr idle⟩
    have ee := congrFun eq i
    change decide (M r.val (k,true)) = decide (M t.val (k,true)) at ee
    have link := decide_eq_decide.mp ee
    cases b with
    | false => exact Bool.noConfusion (h.1 _ _ _ _ mr (link.mpr mt))
    | true => exact Bool.noConfusion (h.1 _ _ _ _ (link.mp mr) mt)
  have bound := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_coe,Fintype.card_fun,Fintype.card_bool, fiveIncident,
    Finset.card_compl,Fintype.card_fin] at bound
  by_contra! lt
  have small : 5 - S.card ≤ 2 := by omega
  have bad := Nat.pow_le_pow_right (by decide : 0 < 2) small
  omega
def repaint (T : Finset V) (P : Feature → Slot → Prop) : Feature → Slot → Prop
  | none,s => P none s
  | some v,s => P (some v) s ∨ v ∈ T ∧ P none s
lemma changeFeature {A B X Y T : Finset V} {P : Feature → Slot → Prop}
    (support : ∀ v, v ∈ X ∨ v ∈ Y → (v ∈ A ∨ v ∈ B) ∧ v ∉ T)
    (neg : ∀ r, present X Y (rows r) none ∨ meets T (rows r) → present A B (rows r) none)
    (pos : ∀ U, point U → present A B U none → present X Y U none ∨ meets T U)
    (cap : capacity A B P) (lh : layout A B P) :
    capacity X Y (repaint T P) ∧ layout X Y (repaint T P) := by
  classical
  obtain ⟨O,R,M,h⟩ := lh
  change rooted A B P O R M at h
  constructor
  · intro v
    by_cases vt : v ∈ T
    · obtain ⟨S,mem,le⟩ := opposedSlots h v (fun r hr => neg r (Or.inr ⟨v,vt,hr⟩))
      refine ⟨S,fun k => ?_,le,fun hv => ((support v hv).2 vt).elim⟩
      simpa only [repaint,vt,true_and] using mem k
    · obtain ⟨S,mem,le,strict⟩ := cap v
      refine ⟨S,fun k => ?_,le,fun hv => strict (support v hv).1⟩
      simpa only [repaint,vt,false_and,or_false] using mem k
  · refine ⟨O,R,M,h.1,?_,h.2.2.1,h.2.2.2.1,?_⟩
    · intro r s z cut mark hit
      cases z with
      | none => exact h.2.1 _ _ _ cut mark (neg r (Or.inl hit))
      | some v =>
        rcases mark with pm | ⟨vt,pm⟩
        · exact h.2.1 _ _ _ cut pm hit
        · exact h.2.1 _ _ _ cut pm (neg r (Or.inr ⟨v,vt,hit⟩))
    · intro U hu a cl
      apply h.2.2.2.2 U hu a
      intro k both
      apply cl k
      intro d
      rcases both d with ⟨z,pm,hit⟩ | ref
      · cases z with
        | none =>
          rcases pos U hu hit with kept | ⟨v,vt,vu⟩
          · exact Or.inl ⟨none,pm,kept⟩
          · exact Or.inl ⟨some v,Or.inr ⟨vt,pm⟩,vu⟩
        | some v => exact Or.inl ⟨some v,Or.inl pm,hit⟩
      · exact Or.inr ref
def rawOnlyZero (P : Feature → Slot → Prop) : Feature → Slot → Prop
  | none,s => P (some 0) s
  | some v,s => v ≠ 0 ∧ P (some v) s
lemma emptyIntoDiagonal {P} (cap : capacity ∅ ∅ P) (lh : layout ∅ ∅ P) :
    capacity (fsCode 1) (fsCode 1) (rawOnlyZero P) ∧ layout (fsCode 1) (fsCode 1) (rawOnlyZero P) := by
  obtain ⟨O,R,M,uniq,avoid,ref,out,pos⟩ := lh
  constructor
  · intro v
    by_cases e : v=0
    · subst v
      exact ⟨∅,by simp [rawOnlyZero],by simp,by simp⟩
    · obtain ⟨S,mem,le,_⟩ := cap v
      exact ⟨S,fun k => by simp [rawOnlyZero,mem,e],le,by simp [zero_set,e]⟩
  · refine ⟨O,R,M,uniq,?_,ref,out,?_⟩
    · intro r s z cut pm hit
      cases z with
      | none => exact avoid r s (some 0) cut pm ((zero_present _).mp hit)
      | some v => exact avoid r s (some v) cut pm.2 hit
    · intro U hu act cl
      apply pos U hu act
      intro k both
      apply cl k
      intro b
      rcases both b with ⟨z,pm,hz⟩ | rd
      · cases z with
        | none => simpa [present,meets] using hz
        | some v =>
          by_cases e : v=0
          · subst v
            exact Or.inl ⟨none,pm,(zero_present _).mpr hz⟩
          · exact Or.inl ⟨some v,⟨e,pm⟩,hz⟩
      · exact Or.inr rd
def eraseMask (a t : ℕ) := a ^^^ (a &&& t)
lemma eraseMask_set (a t : ℕ) : fsCode (eraseMask a t) = fsCode a \ fsCode t := by
  ext v
  simp only [fsCode,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,eraseMask,
    Nat.testBit_xor,Nat.testBit_and]
  cases a.testBit v.val <;> cases t.testBit v.val <;> decide
lemma erasedMeets {A U T : Finset V} (hit : meets A U) (absent : ¬meets T U) : meets (A \ T) U := by
  obtain ⟨v,va,vu⟩ := hit
  exact ⟨v,Finset.mem_sdiff.mpr ⟨va,fun vt => absent ⟨v,vt,vu⟩⟩,vu⟩
lemma retainedMeets {A U T : Finset V} : meets (A \ T) U → meets A U := by
  rintro ⟨v,vt,vu⟩
  exact ⟨v,(Finset.mem_sdiff.mp vt).1,vu⟩
lemma eligibleRows {a b t : ℕ} (ok : bitSub (negativeSig t) (coldMask a b) = true)
    (r : Fin 15) (ht : meets (fsCode t) (rows r)) : present (fsCode a) (fsCode b) (rows r) none := by
  have bit := bitSub_use ok _ ((negative_has _ r).mpr ht)
  change ((negativeSig a) &&& negativeSig b).testBit r.val = true at bit
  rw [Nat.testBit_and,Bool.and_eq_true] at bit
  exact ⟨(negative_has _ r).mp bit.1,(negative_has _ r).mp bit.2⟩
lemma strippedOrdinary {a b t : ℕ} {P}
    (ok : bitSub (negativeSig t) (coldMask a b) = true)
    (cp : capacity (fsCode a) (fsCode b) P) (lh : layout (fsCode a) (fsCode b) P) :
    ∃ Q, capacity (fsCode (eraseMask a t)) (fsCode (eraseMask b t)) Q ∧
      layout (fsCode (eraseMask a t)) (fsCode (eraseMask b t)) Q := by
  rw [eraseMask_set,eraseMask_set]
  refine ⟨_,changeFeature (T := fsCode t) ?_ ?_ ?_ cp lh⟩
  · intro v mem
    rcases mem with mem | mem
    · exact ⟨Or.inl (Finset.mem_sdiff.mp mem).1,(Finset.mem_sdiff.mp mem).2⟩
    · exact ⟨Or.inr (Finset.mem_sdiff.mp mem).1,(Finset.mem_sdiff.mp mem).2⟩
  · intro r hit
    rcases hit with ⟨ha,hb⟩ | ht
    · exact ⟨retainedMeets ha,retainedMeets hb⟩
    · exact eligibleRows ok r ht
  · intro U _ h
    by_cases ht : meets (fsCode t) U
    · exact Or.inr ht
    · exact Or.inl ⟨erasedMeets h.1 ht,erasedMeets h.2 ht⟩
lemma strippedLinear {a b t : ℕ} {P} (ok : bitSub (negativeSig t) (coldMask a b) = true)
    (cov : bitSub (positiveSig a &&& positiveSig b) (positiveSig t) = true)
    (cp : capacity (fsCode a) (fsCode b) P) (lh : layout (fsCode a) (fsCode b) P) :
    ∃ Q, capacity (fsCode 1) (fsCode 1) Q ∧ layout (fsCode 1) (fsCode 1) Q := by
  have step := @changeFeature (fsCode a) (fsCode b) ∅ ∅ (fsCode t) P
  have empty := step (by simp) (fun r hh => by
    rcases hh with hl | hr
    · simpa [present,meets] using hl
    · exact eligibleRows ok r hr) (fun U hu ht => by
      right
      obtain ⟨r,v,miss,rfl⟩ := hu
      obtain ⟨u,eq⟩ := point_indices r v miss
      rw [← eq] at ht ⊢
      have bit : (positiveSig a &&& positiveSig b).testBit u.val = true := by
        rw [Nat.testBit_and,Bool.and_eq_true]
        exact ⟨(positive_has _ u).mpr ht.1,(positive_has _ u).mpr ht.2⟩
      exact (positive_has _ u).mp (bitSub_use cov _ bit)) cp lh
  exact ⟨_,emptyIntoDiagonal empty.1 empty.2⟩
def routeByteBlock (i : ℕ) : ℕ := (match Nat.blt i 17 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => 0x5252545452525454c1c1c2c25252d2d24f4fd1d14f4fd1d1bcbcd0d0cfcf0b0a818182828181cdcda2a2cccccbcb0908c6c6c9c9c8c80706c6c60504030201003d3dc2c23f3fc3c3c1c1c2c2c1c11f1ebcbcbfbfbebe1d1cbcbc1b1a191817169191b9b9b8b81514b6b6131211100f0eb3b30d0c0b0a090807060504030201009a9a9b9b6868afaf6666aeaeadad1f1ea8a8ababaaaa1d1ca8a81b1a191817169191a5a5a4a41514a2a2131211100f0e9f9f0d0c0b0a090807060504030201009a9a9b9b9a9a3332989831302f2e2d2c95952b2a292827262524232221201f1e91911d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010077778c8c77778c8c66668b8b8a8a1f1e1616888887871d1c85851b1a1918171681818282818115147f7f131211100f0e7c7c0d0c0b0a090807060504030201007777787877773332757531302f2e2d2c72722b2a292827262524232221201f1e6e6e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201006868696968683332666631302f2e2d2c63632b2a292827262524232221201f1e5f5f1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201005a5a3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3f5454525254545252535352521f1e4f4f50504f4f1d1c4d4d1b1a1918171612124a4a494915144747131211100f0e44440d0c0b0a090807060504030201003f3f40403f3f33323d3d31302f2e2d2c3a3a2b2a292827262524232221201f1e36361d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201002e2e3131303033322e2e31302f2e2d2c2b2b2b2a292827262524232221201f1e27271d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010022223d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010019191c1c1b1b3332191931302f2e2d2c16162b2a292827262524232221201f1e12121d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201000d0d3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010007073d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010037363534333231302f2e2d2c2b002a00292827262524232221201f1e1d001c001b1a191817161514131211100f000e000d0c0b0a090807060504030201000000) | false => (match Nat.blt i 3 with | true => 0x4444c044c0c0c0c0c6c6c0c6c0c0c0c044444444c8c8bdc8c6c6c6c60b0a09087c7c7c7cc8c8b7c8c6c6c6c60706050444444444c8c8c8c8c6c6c6c60302010076767676c0c0c0c0c0c0c0c0c0c0c0c0b3b3bdb3bdbdbdbd1a19181716151413b3b3b7b3b7b7b7b71211100f0e0d0c0bb3b3b3b30a0908b107060504030201009f9f999f99999999aeaeaeae272625249f9f9f9f232221201f1e1d1c1b1a19189f9f9f9f17161514131211100f0e0d0c9f9f9f9f0b0a09080706050403020100999999999999999937363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201007c7c767c767676768b8b8b8b272625247c7c7c7c232221201f1e1d1c1b1a19187c7c7c7c17161514131211100f0e0d0c7c7c7c7c0b0a09080706050403020100767676767676767637363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100696969693b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010044443e443e3e3e3e535353532726252444444444232221201f1e1d1c1b1a19184444444417161514131211100f0e0d0c444444440b0a090807060504030201003e3e3e3e3e3e3e3e37363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100313131313b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201001c1c1c1c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010000 | false => 0xc9c9c9c9acc9acc9acacacacacacacacc9c9c9c9c9c9c9c9cfcf0f0ecfcf0d0cc9c9c9c9c9c9c9c9cbcb0b0acbcb0908c9c9c9c9c9c9c9c907060504030201003f3fc3c3773fc3c3c1c12b2ac1c12928bebe2726bebe2524232221201f1e1d1cb8b81b1ab8b8191817161514131211100f0e0d0c0b0a09080706050403020100acacacacacacacacacacacacacacacacaaaa2726aaaa2524232221201f1e1d1ca4a41b1aa4a4191817161514131211100f0e0d0c0b0a090807060504030201009a9a3b3a9a9a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201001b1b8c8c1b1b8c8c8a8a2b2a8a8a29288787272687872524232221201f1e1d1c81811b1a8181191817161514131211100f0e0d0c0b0a0908070605040302010077773b3a7777393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010068683b3a6868393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201001b1b54541b1b545452522b2a525229284f4f27264f4f2524232221201f1e1d1c49491b1a4949191817161514131211100f0e0d0c0b0a090807060504030201003f3f3b3a3f3f393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010030303b3a3030393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201001b1b3b3a1b1b393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201000000)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0x90909090a090a090a0a0a0a0a0a0a0a0909090909090909131313131313131308080808080808080f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e7979797979797979090909090a090a090a0a0a0a0a0a0a0a0909090909090909373737376f376f3708080808080808086b6b6b6b6b6b6b6b3232323232323232b0b0b0b0b0b0b0b0010101010101010104040404040404040303030303030303282828282828282802020202020202025c5c5c5c5c5c5c5c23232323232323239c9c9c9c9c9c9c9c010101010101010157575757575757571e1e1e1e1e1e1e1e9292929292929292555555551d551d558e8e8e8e8e8e8e8e8d8d8d8d8d8d8d8d0706050403020100080808080a080a080a0a0a0a0a0a0a0a1313131313131313131313131313131308080808080808080f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e7979797979797979080808080a080a080a0a0a0a0a0a0a0a09090909090909096f6f6f6f6f6f6f6f08080808080808086b6b6b6b6b6b6b6b6a6a6a6a6a096a080706050403020100020202020202020204040404040404040303030303030303606060606060606002020202020202025c5c5c5c5c5c5c5c5b5b5b5b5b5b5b5b07060504030201000101010101010101575757575721572056565656565656561f1e1d1c1b1a1918555555555555555517161514131211100f0e0d0c0b0a09080706050403020100090909090109010913131313131313130909090909090909131313131313131302020202020202020f0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e414141414141414109090909010901090a0a0a0a0a0a0a0a0909090909090909373737373737373708080808080808083333333333333333323232323209320807060504030201000101010101010101040404040404040403030303030303032828282828282828020202020202020224242424242424242323232323232323070605040302010001010101010101011f1f1f1f1f211f201e1e1e1e1e1e1e1e1f1e1d1c1b1a19181d1d1d1d1d1d1d1d17161514131211100f0e0d0c0b0a09080706050403020100090909090a090a090a0a0a0a0a0a0a0a0909090909090909131313131313131308080808080808080f0f0f0f0f0f0f0f0e0e0e0e0e090e080706050403020100090909090a090a090a0a0a0a0a250a24090909090923092221201f1e1d1c1b1a080808080819081817161514131211100f0e0d0c0b0a090807060504030201000101010101010101040404040421042003030303030303031f1e1d1c1b1a1918020202020202020217161514131211100f0e0d0c0b0a090807060504030201000101010101380137363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010000 | false => 0x61611461616161616161146161616161141414146161146114141414616114619d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d3838383838383838383838383838383838383838383838383838383838383838b1b1b1b1b1b1b1b1b3b3b7b1b7b7b7b1b1b1b1b1b1b1b103b3b3b3b1020100b161616161616161616161616161616161616161616161616161616161616161619d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d93939393939393939393939393939393939393939393939393939393939393931f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010061611461616161616161146161616161141414146161146114141414616114617a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a70707070707070707070707070707070707070707070707070707070707070701f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010061616161616161616161616161616161616161616161616161616161616161611f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201001414141414141414141414141414141414141414141414141414141414141414424242424242424242424242424242424242424242424242424242424242424238383838383838383838383838383838383838383838383838383838383838381f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010029292929292929292929292929292929292929292929292929292929292929291f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010014141414141414141414141414141414141414141414141414141414141414141f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010000) | false => (match Nat.blt i 7 with | true => 0x1d1d1d1d011d1d1d011d011d0101011d323232320332323203320332030303321d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d323232323232323232323232323232321d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d323232323232323232323232323232bd1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d323232323232323232323232323232b301010101010101010101010101010101030303030303030303030303030303a91d1d1d1d1d1d1d1d1d1d1d1d1d1d1da3232323232323239f232323232323239f1d1d1d1d011d1d1d011d011d0101011d1e1e1e1e1e1e1e1e1e1e1e1e1e1e1e941d1d1d1d1d1d1d1d1d1d1d1d1d1d1d8e8d8d8d8d8d8d8d8d8d8d8d018d8d8d000101010101010101010101010101010103030303030303030303030303030303080808080208080802080208020202080e0e0e0e0e0e0e0e0e0e0e7c0e790e790101010101010101010101010101017609090909090909090909090909096f6f080808080808086d0808086e08086c6d6a6a6a6a6a036a026a6a6a6a6a016a000101010101010101010101010101010103030303030303030303030303030360020202020202025e02020202025c5d5d5b5b5b5b5b5b5b5b5b5b03025b5b01000101010101010101010101010101015a56565656565656565656565656145613555555555555555555555512551155100f0e0d0c0b0a090807060504030201001d1d1d1d011d1d1d011d011d0101011d3232323203323232033203320303034c1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d323232323232323232323232323232421d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d32323232323232323232323a323232391d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d3232323232043203323232023201320001010101010101010101010101010101030303030303030303030303032803291d1d1d1d1d1d1d1d1d1d1d1d1d1d1d24232323232323232323230302232301001d1d1d1d011d1d1d011d011d010101191e1e1e1e1e1e1e1e1e1e1e181e171e161d1d1d1d1d1d1d1d1d1514131d1211100f0e0d0c0b0a090807060504030201000101010101010101010101010101010103030303030303030303030303030315080808080208080802080208020202080e0e0e0e0e060e050e0e04030e0201000101010101010101010101010101010d09090909091809170909090909160915080808080814081308080812081108100f0e0d0c0b0a090807060504030201000101010101010101010101010101010103030303030303030303191803171615020202020202020202021413021211100f0e0d0c0b0a090807060504030201000101010101340133013201310130012f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010000 | false => 0x555508551d551d5555085555555555551d1d1d1d021d1d1d08080808020201d255555555555555550202555555555555020255550202555502020202020255c808080808010801080108010801010101080808080108010808080808010801c255550855555508555555085555550855085508085555085508550808555508b51d1d1d1d1d1d1d1d02021d1d02021d1d021d1d1d021d1d1d0202021d020202ad555555551d551da3555555551d551da31d551d551d1d1da5555555551d551da41d1d01011d1d1d1d011d01011d1d011d1d1d01011d1d1d1d011d01011d1d0194555555551d551d905555551d1d551d8e1d551d551d1d558d5555551d1d555500550855555555555555085555555555550808080855085555080808085508558a080208020202080208080808080208080802080202020802087c087c0879087f55550101555501015555555555557676015501010155010155550155555573745555086d5555086d5555086d55556c6d0855086e55085501086a086e556c6a005555555502020202555555555555555502025555020202025555555502025568555555550202025e555555555d5d5d5d020255550202555b555b025e5c5c01005555010155550101555555555501585a0155010101555555555501555501560f55555555555555555555550e550d550c55550b0a0908070655550504030201001d1d1d1d011d1d1d011d011d0101011d1d1d1d1d011d1d1d011d011d0101014c1d021d021d021d0202021d0202021d021d1d1d1d1d1d1d1d1d021d1d1d021d491d1d08081d1d0808080808081d1d08081d1d1d401d1d1d401d1d083a1d1d1d391d1d08081d1d08080808081d1d1d081d1d1d1d361d081d341d1d08331d081d000202010202020202020201020202020201010101020201020101010128282c291d021d021d021d2602021d1d02021d241d271d271d271d271d230201242326001d1d01011d1d2121011d011d1d0120101d1d01221d1d2121011d011f1f22200f1d1d1d1d1d1d1d1d1d0e0d0c1d0b0a091d1d1d1d1d0807061d0504031d0201000808080801080108080808080808080801010101010101010808080801080115080208020202080208080808080208080802080202080808080e02110810020008080808010801080808080808010b0d0101010d0108010b090909090a100a0f08080808080e080d0808080c080b080a08080808090807060808050403020100020201020202020202020102020102010101010102020102010102020407060f020202020202020202020e0d020c0b0a0202090802070605020204030202010001010101012d012c012b012a012901280101010101272625012423220121201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010000))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0x514a4a4a51545154514a514a51545154cec9cec9ced1ced1cec9cec9ced1ced14a4a4a4a515451540f4a514a5154515479c9cec9ced1ced179c9cec9ced1ced1b9b9b9b9c0c3c0c3c0b9c0b9c0c3c0c31f1e1d1c1b1a19181716151413121110b9b9b9b9c0c3c0c3b9b9b9b9c0c3c0c30f0e0d0c0b0a09080706050403020100a5a5a5a5acafacaf5ca5a5a5acafacaf1f1e1d1c1b1a19181716151413121110a5a5a5a5acafacaf5ca5a5a5acafacaf0f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201000f120f12171b171b0f120f12171b171b797c797c83878387797c797c838783870f120f12171b171b0f120f12171b171b797c797c83878387797c797c838783876b6e6b6e737773776b6e6b6e737773771f1e1d1c1b1a191817161514131211106b6e6b6e737773776b6e6b6e737773770f0e0d0c0b0a090807060504030201005c5f5c5f646864685c5f5c5f646864681f1e1d1c1b1a191817161514131211105c5f5c5f646864685c5f5c5f646864680f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100514a4a4a51545154514a514a515451541f1e1d1c1b1a191817161514131211104a4a4a4a515451540f4a514a515451540f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201000f120f12171b171b0f120f12171b172221201f1e1d1c1b1a19181716151413120f120f12171b17110f120f121710171b0f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201003e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010000 | false => 0x20202020202020202020202020202020383838383838383838383838383838ce01012020202020200101202020202020030338383838383803033838383838d120202020202020202020202020202020383838383838383838383838383838bd202020202020202020202020202020203838383838383838383838bf383838b101010101202020200101010120202020030303032929292903030303292929a901010101202020a401010101202020af03030303292929aa0303039f2929a6aa202020202020202020202020202020201e1e1e1e939393931e1e1e1e93939393010120202020209901012020202099961e1e1e95939393931e1e1e1e93930100010101010b0b0b0b010101010b0b0b0b030303031414141403030303141414830101010105050b0b0101010105050b0b03030303141414870379037c14831483010101010b0b0b0b010101010b0b767609090909707070700909090970707070010101780b0b0b760101016e0b6c73760909097270707070096a6f72707001000101010105050505010101010505056703030303616161610303030361616161010101010505055d010101015d5d645d0303030361616161035b036261610100010101015858585801010101581558145656565613121110565656560f0e0d0c010101555858585801015557580b580a56565656090807065656050403020100202020202020202020202020202020203838383838383838383838383838384f01012020202020200101202020202020030338383838383803033838384f38422020202020202020202020202020202038383839383838383838383a38383838202020202020202020202020202038073838383a38380605383a3804030201000101010120202020010101012020202f03030303292929290303032b292929290101010120202030010101012020202c0323032b29292929032b03022929010020202020202020202020201f201820171e1e1e1e161514131e1e1e1211100f0e0101202020202020011f1f1f200d0c0b1e1e1e1e0a0908071e06050403020100010101010b0b0b0b010101010b0b0b0b030303031414141403030316141414140101010105050b0b0101010105050b0b03030303141414140316031514140100010101010b0b0b0b010101010b160b15090909091413121109090909100f0e0d0101010d0b0b0b0b0108010a0b0c0b0a09090909090807060909050403020100010101010505050501010101051b051a0303030319181716030315141312111001010101050505050101030f050e0d0c03030b0a0908070603030504030201000101010133323130012f012e2d2c2b2a292827262524232221201f1e1d1c1b1a0101010119181716011514131211100f0e0d0c0b0a0908070605040302010000) | false => (match Nat.blt i 11 with | true => 0x39393939213921390939393921392139393939393939393909393939093939d101392139212121210909393901392139093939393939393909093939093939d139393939213921390939393921392139393939393939393909393939093939bd013921392121212109093939013921c209393939393939bf090939bf093939b22121212121212121012121212121212194942a2a94942a2a56942a2a94942aa901012121212121af01012121012121af56942a2a94942aab56562aab5694a9ab2121212121212121012121212121219994949494949494945694949494949494010121212121219b0101212101219997569494949494949456569402569401000909151501090615090915150909061509097171090971710909717109097184010106150101060609091515010906150909717109097188098571880985848809097171010959710909717109097476090971710909717109097171096f717101015978010159780909716d017574780909717109097102096a71716f7001000101595901015959010159590101596703036262030362620303626203600504010159590101595e0101595e5d5d676703036203035b6202035b6201606000620101595901015959010159590101591556561413565612115656100f560e0d0c01015959015559590155590b575a590a56560908560706055656040356020100393939392139213909393939213921393939393939393939093939390939394c01392139212121210909393901392139093939393939395009093950094f39433939393921392139093939392139213e39393939393939390939393909373939013921392121214009093921013939070939393939090605093a0403390201002121212121212121012121212121212f2a2a2a2a2a2a2a2a032a2a2a29282a2a01012121212121260101212101302f2d032b2a2a2a232a2a032b2a02292b010021212121212121210121211b2101211a1e1e19181e1e17161e1e15141e13121101012121211d21210121100f200e0d0c1e1e0b0a1e0908071e060504030201000909151501090615090915150909061509091515090915150909151509091515010106150101060609091515010906150909151509091502091615151314010009090c0c01090c0c09090c0c09010c1b09091a1909181716090915140913121101010c0c01090c1009080c0f0a0e0d0c09090b0a0908070609090504030201000101060601010606010106060101061503031413030312110303100f030e0d0c01010606010206060102060b0507060a030309080307060503030403030201000101343301323130012f2e2d012c2b2a292827262524232221201f1e1d1c1b1a0101191801171615011413120111100f0e0d0c0b0a0908070605040302010000 | false => 0x9090909010901090909090909090909090909090909090909090909090909d00101010101010101090909090109010909090909090909d109090909090909d1090909090109010909090909090909c009090909090909bf09090909090909bd01010101010101b909090909010901c2090909bf090909bf090909bf090909b3010101010101010101010101010101af0303030303030303030303030303a6a901010101010101a301010101010101af0303039f030303ab0303039f0303a6aa010101010101019901010101010199991e1e1e1e1e1e1e941e1e1e1e1e1e9393010101010101019b01010101010199961e1e1e951e1e1e951e1e1e1e1e1e1e1e0909090901090109090909090909090909090909090909090909090909090984010101010101010109090909010901090909097c090909880979097c09798485090909090109017809090909090976760909090909090971090909096f6f6f6f0101017801010178096e746e7375737409090972090909706f6a6f726f706a090101010101010101010101010101646703030303030303030303030360606060010101010101015e0101015e5c5c645d035b035b035b035b035b0362606062030101010101010159010101010101585a56565656565656565656565656085607015501550155015555555557575a58015656565656065605565604035602010009090909010901090909090909090909090909090909090909090909094b094c01010101010101010909090901090109090909090909095009440944094109420909090901090109090909090909093e09090939090909390937093a0937093901010101010101400909090a0109081e0909093a09093703093a3202320132000101010101010101010101010101012f03030303030303030328032b282829290101010101270126010101012c242c2e0323032b2323292b032b03022928010001010101010121210101011d010120101e1e1e1e1e1e1e1e1e1e1e0f1e0e1e0d010101011d1d2021011f1f1f200c0b0a1e1e1e1e1e0908071e0605040302010009090909010901090909090909090909090909090909090909090916091313150101010101010101090909090109010909090916090909090916031513140100090909090109010b0909090d09010b0d09090909090f090e09090909090d090c0101010d01090b0b0908080a0a0b080a090909090908070609090504030201000101010101010101010101010101050103030303030303030303100f030e0d0c01010102020205060102030b0507060a0303090803070605030304030302010001010101012c012b012a012901280127262524232221201f1e1d1c1b1a1918170101010101160115011413120111100f0e0d0c0b0a0908070605040302010000)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xc752433fc752c752c5c1c5c15252c1c1c752c752c752c752c5c1c5c1525252d2c7687b77c768c768c566c5c15252c1c1c566c752c752c7cdc566c5d0525252cfb23db23d3f3f3f3fc1c1c1c1c1c1c1c1b23db23d3f3f3fc33d3dc1c1c1c1c1c1b25ab25a777777c3c1c1c1c1c1c1c1c1b23db2bf3f3f3fb83d3dc1c2c1c101009e9a9e9a68689a9a66666666adadadad9e2e9e9a68689a9a2e2e2e2eadadadad9e9a9e9a686868af66666666adadadad9e2e9e9f686868a4666666a2adadadad9a9a9a9a9a9a9a9a98989898181716159a9a9a9a9a9a9a9a989814131211100f5a5a9a9a9a9a9a9a98980e0d0c0b0a095a5a9a9b9a9a080706050498030201007b777b7777777777666666668a8a8a8a7b197b7777777777191919198a8a8a8a7b777b7768687777666666668a8a8a8a7b197b826868778c667f667f8a8a8a8a77777777777777777575757511100f0e7777777777777777757575750d0c0b0a5a5a77787777777775757575090807065a5a7778777705047575757503020100686868686868686866666666131211106666686868686868666666660f0e0d0c6868685f68686868666666660b0a0908665f68696868070666660504030201005a5a5a5a31302f2e2d2c2b2a292827265a5a5a5a2524232221201f1e1d1c1b1a5a5a5a5a191817161514131211100f0e5a5a0d0c0b0a09080706050403020100433f433f52523f3f5252525252525252433f433f525252525252524d525252524307433f52523f3f2e2e525252525252430743505252524f2e4d5253525201003f3f3f3f3f3f3f3f3d3d3d3d131211103d3d3f403f3f3f3f3d3d3d3d0f0e0d0c3f3f3f3f3f3f3f3f3d3d3d3d0b0a09083d3d3f403f3f07063d3d0504030201002e2e2e2e303030302e2e2e2e11100f0e2e2e2e2e303030302e2e2e2e0d0c0b0a07070707303030302e2e2e2e090807062e2b2e2b303030302e2e050403020100222222222f2e2d2c2b2a29282726252422222222232221201f1e1d1c1b1a19182222222217161514131211100f0e0d0c222222220b0a09080706050403020100191919191b1b1b1b1919191918171615191919191b1b1413191919191211100f070707071b1b0e0d191919190c0b0a09191919160807061b19190504030201000d0d0d0d2f2e2d2c2b2a2928272625240d0d0d0d232221201f1e1d1c1b1a19180d0d0d0d17161514131211100f0e0d0c0d0d0d0d0b0a090807060504030201000707070731302f2e2d2c2b2a29282726070707072524232221201f1e1d1c1b1a07070707191817161514131211100f0e07070d0c0b0a090807060504030201003d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201000000 | false => 0x2c2c20202c2c2c2c737373732c2c73732c2c2c2c2c2c2c2c737373732c2c2cd26464737364646464646473732c2c737364642c2c2c2c2ccd646473d02c2c2ccf0a0a0a0a3b3b3b3b73737373737373c00a0a0a0a3b3b3bbd0a0a7373737373c001010101585858b773737373737373c00a0a0abf3b3b3bb80a0a73c273733bb4202020206464202064646464646464ad2c2c2020646420202c2c2c2c2c2ca6ad20202020646464af646464646464a0ad2c2c209f646464a4646464a264a6a0ad2020202020202099969696969696969620202020202020991f1f969696969696010120202020209957579696969696960101209b202058935757969896960100737373737373737364646464737373730a0a7373737373730a0a0a0a738a898a737373736464737364646464646473890a0a73826464738c647f647f7d8a898a7373737373737376737373737373737373737373737373760a0a7374737373730101737873737376737574757373737301017378737358706f7574757373010058585858646464646464646464646464040458586464646464646464646464645858585e645d645d645c645c64646464045b5869645d5861645c0465646401000101010158585858575757571716151401010101585813125757575711100f0e0155015558585858575757570d0c0b0a01555856090807065757050403020100202020202c2c20203b3b3b3b2c2c2c2c202020202c2c2c2c3b3b3b4c2c4b2c4b010120202c2c202004043b3b2c2c2c2c010120502c2c2c4f04413b532c4b3b45202020202020203e0a0a0a0a3b3b3b3b0a0a20402020203e0a370a373b3b3b3b202020202020203e0a0a0a0a3b3b05040a0a204020203b340a373b33030201002c2c2c2c2c2c20202c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2f2c282c282c2c2c2c010101012c302f302c2c2c2c2c2c2c2c2c2b2c2b293029302c28042d2c2c010020202020202020201f1f1f1f1312111020222122202020201f1f1f1f0f0e0d0c01012021202020201f1f1f1f0b0a09081d222122202007061f1f0504030201000a0a0a0a17170b0b0a0a0a0a171717170a0a0a0a171717170a130a13171717170101010105050b0b0a0a0a0a171717170a0a0a161717171b0a130418171701000a0a0a0d0b0b0b0b0a0a0a0a131211100a0a090d0b0b0b0b0a0a0a0a0f0e0d0c0101080d0b0b0b0b0a0a0a0a0b0a09080a09090d0b0b07060a0a0504030201000101010105050505040404041716151401010101050505050404131211100f0e010201020505050504040d0c0b0a09080102040605050706040405040302010001010101302f2e2d2c2b2a29282726250101010124232221201f1e1d1c1b1a19010101011817161514131211100f0e0d01010c0b0a0908070605040302010000) | false => (match Nat.blt i 15 with | true => 0x17191719171917191719171917191719171917191719171917191719171917cf0507050705070507171917191719171917191719171917cd171917c6171917d00b0d0b0d0b0d0b0d73757375737573c20b0d0b0d0b0d0bbf73757375737573c20b0d0b0d0b0d0bb973757375737573c20b0d0bbf0b0d0bbf737573bc73b63bb6050705070507050764666466646664ad0507050705070507646664666466a6ad05070507050705a42c2e2c2e2c2ea0ad0507059f050705a5646664a264a8a0ad202220222022209b9698969896989698202220222022209b9698969896989606202220222022209b969896989698960520222091209558959604960396020100171917191719171917191719171917191719171917191719171917191785898a1719171917191719171917191719177f1719177c17191782177f17857f8589850b0d0b0d0b0d0b7873757375737573750b0d0b0d0b0d0b7873757375737573750b0d0b6e0b0d0b7873757375737573750b0d0b6e0b0d5a03757575757302010005070507050705076466646664666466050705070507056864666466646664660507055f055f055f6466646664666466055f0563055f58636466030264660100585a585a585a585a262524232221201f585a585a585a1e1d1c1b1a1918171615585a585a585a585a14131211100f0e0d585a580c0b0a090807060504030201000507050705070507171917191719171905070507050705071719174d174d174d050705070507050717191719171917520507054405070550174d1747174d3b470b0d0b0d0b0d0b403b3d3b3d3b3d3b3d0b0d0b3a0b0d0b403b3d3b3d3b3d3b3d0b0d0b0d0b0d0b403b3d3b3d3b3d07060b0d0b3a0b0d3d053b3d3b040302010005070507050705072c2e2c2e2c2e2c2e050705070507052b2c2e2c2e2c2e2c2e0507050705272f302c2e2c2e2c2e2c2e052b05272b272f272c2e03022c2e010020222022202220222221201f1e1d1c1b20222022202220221a1918171615141320222022202220221211100f0e0d0c0b22222222200a0908070605040302010017191719171917191719171917191719171917191719171917191719171917190507050705070507171917191719171917191716170d170d17190403170201000b0d0b0d0b0d0b0d262524232221201f0b0d0d0d0b1e0b1d1c1b1a19181716150b0d0d0d0b140b131211100f0e0d0c0b0b0d0d0d0d0a09080706050403020100050705070507050724232221201f1e1d05070507050705071c1b1a1918171615050705070507050714131211100f0e0d05070c0b050a090807060504030201003e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a0908070605040302010000 | false => (match Nat.blt i 16 with | true => 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0ace01010101010101010a0a0a0a0a0a0ad20a0a0a0a0a0a0acd0a0a0ac60acf0ad00a0a0a0a0a0a0a0a0a0a0a0a0a0a0ac00a0a0a0a0a0a0abf0a0a0a0a0a0abbc201010101010101b90a0a0a0a0a0a0ac20a0a0abf0a0a0abf0a0a0abc0ac13cb5010101010101010104040404040404ad01010101010101af0404040404a6a6ad01010101010101a30404040404a0a0ad0101019f01a401a5049c04a2a6a6a0ad01010101010101995757575757579696010101010101019b5757579757969696010101010101909b1f1f1f971f96969601010191019a599457925798929201000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a890a0a0a0a0a0a0a0a0a0a0a0a0a8589840a0a0a0a0a0a0a0a0a0a0a7f0a0a0a890a0a0a7c0a0a0a820a7f0a857d8589850a0a0a0a0a0a0a760a0a0a740a0a74740a0a0a780a0a0a780a6f6f6f6f6f73740a0a0a6e0a0a6d780a757475737573740a6e0a6e0a0d59706f756f756f73010004040404040404040404040404046464040404040404046804040466646064660404045e045d045e045c045c5c5c645c045b0463045b555b045c0465645c0100010101010101585957575757570e570d0101015a0101555557575757570c0b0a01555555555555555757575757095708015558565907560657570504030201000101010101010101040404040404040401010101010101010404044c044b044c0101010101010101040404040404045201010144010101500441044704413741010101010101013e0a0a0a0a0a0a3b3c0101013a010139400a3737373737373701010140010101400a0a0a3d0a0a3737013a013a010d3c340a373b333c013300010101010101012f0404040404042c2c0101012b0101012f0428042828282c280101010101272f260404042e2c242c2e012b012729272f270428042d2c28010001010121010121211f1f1f1f1f0e1f0d01222122202220211f1f1f1f1f0c1f0b011d1d1d1d1d20211f1f1f1f1f0a09081d221d221d2007061f1f0504030201000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a180a0a0a0a0a0a0a150a130a131313171801010101010101110a0a0a190a0f17180a0a0a160a080a0d0a130418131701000a0a0a0d0a0a0b0b0a0a0a0a0a0e0a0d0a0a090d0a080b0b0a0a0a0a0a0c0a0b0101080d01090b0b0a0a0a0a0a0a09080909090d0d0b07060a0a0504030201000101010101010106040404040412041101010107010305060404100f040e0d0c010201020202050604040b0a040908070102040602050605040404030402010001010101012b012a2928272625242322010101010121201f1e1d1c1b1a191817010101010116011514131211100f0e0d01010c0b0a0908070605040302010000 | false => 0x15a015a015a015a0107015a015a015a0107015a0107015a01070107010701d1015a015a015a015a0107015a015a01cd0107015a010701cd010701c601c6ced1015a015a015a015a015a015a015a01c2015a015a015a01bf015a01bf015ac0c2015a015a015a01b9015a01b9015a01c2015a01b9015a01b901b601bf01b63cb6015a015a015a015a015a015a015a01af015a015a015a01aa015a01ae01aaa6ad015a015a015a01a4015a01a501a4a3af015a019f019fa3a5019f019fa09fa6a4015a015a015a019b015a015a015a999b015a0195015a019b015a019b019a969b015a019b015a909b015a0122019199220195019101955995019101228e9501000107010701070107010701070107018b01070107010701870107018b0185898a010701070107018201070182017f7d8201070182017c0182017f797c7985897f015a015a015a0178015a017801777678015a0178015a7678017274786f757378015a0178016e6d78016e6d6e73757378016e016e010d59016f756f6e6f776a00015a015a015a01690107015a016864680107015a010701680163016664666468015a015f015f5d5f015f5c5f5d5f645f015f01695d5f55635c5f0269645f6200015a015a015a585a015a015a585a585a015a015a015a550b015a575a575a560a015a555a555a555a555a5509575a5808555a580759065605575a04035602010001070107010701070107010701070107010701070107015001070150014f4b4f01070107010701490107010701070149010701440144015001440144014f38490122012201220140010d014001223e40010d0140013a3940013a393a373a3e3a0122014001223e40010d012201223804013a3940010d3c03373a38023c013400010701070107013101070107012e2f300107012b012b292b012b282b282b2c2b0107012701272f30012701222c302f2e012b012723272f27232b03012c2b26000122012201222122012221112022201001222122202221221f221f0f1f22200e01221d221d2220221d0d220c200b0a091d221d221d0807061f0504031d020100010701070107010701070107010701190107011c0107011601160116131617160107011c010701120107011c0112101c01160112010d010d0e16031c130d0100010d010d010d0b0d010d0a0d0a0d0b0d010d090d09110b10090d090d0a0f0a0e010d080d080d0b0c080d080b0a0a0809080d080d0d0807060a0d0504030201000107010701070107010701070407050701070107010705070407020b0407060a01070207020705070207030905070608020704070206050402070603040201000129012801270126012501240123012201210120011f1e1d011c1b1a01191817011601150114011301121110010f0e0d010c0b0a090807060105040302010000))))) | false => (match Nat.blt i 25 with | true => (match Nat.blt i 21 with | true => (match Nat.blt i 19 with | true => (match Nat.blt i 18 with | true => 0x101010101010101010101010101010101010101010101d1010101d00101cece01010101010101cd01010101010101cd01010101010101cd01c601c601c6ced1010101010101010101010101010101c001010101010101bf010101bf01bec0bd01010101010101b9010101b90101c0b7010101b9010101b901b001bf01b63cb501010101010101af01010101010101af01010101010101af010101a7a6a6a6a90101010101a4a3a3010101a5a0a0a0af019f019f01a4a3a5019f019fa0a0a6af01010101010101990101010101019999010101950101999b010101949293969301010190019a909b010101218e8f999601950191019a5994018d01228e8e011e01010101010101010101010101018989010101010101018601850185018589840101018201010182017f017f7d7d7d7d01010182017c01827979797c7d8589850101017801017676010101747373767601010178010176786f6f746f6f6f737401010178016e6d78016e6d6e736c736d016e6d6e010d59706f6a6f6e6f776a0901010101010101690101010164646467010101010101016801630166646064680101015e5d5d5d5e5c5c5c5e5d5d645d015b01695d5b555b5c5b025e645c62590101015a01015859010157595801585a0101015a010155555656575657015606555555555555555555555557575a58015555585659055604575603025601000101010101010101010101010101010153010101010101015001010150014b4b4c010101010101014801010101010101490101014401440150014401444b4138420101014001013e3e0101014001013e3e013a3940013a39403737393a37373e390101014001013e40010101220101381e013a3940010d3c34373a38333c0c34010101010101012f2f010101012c2c2f2f012b012b0129292f2828282b28282c290101012701272f26012701222c242f2e012b232723272f27232b032d2c23262101012121202021210101211d2001200a01222122202220211f1f1f1f1f2220091d1d1d1d1d1d20211d21221f200807061d221d221d2005041f1f03021d01000101010101010101010101010101011a180101011c0101011501131316131317180101011c0101011101190119100f1010010e01120109010d0e1603151317010c0101010d01010b0b0a0a0a0d0a010b0d0909090d09080b0b09090a090a0a0a090808080d08090b0b0808080a0a0808070808080d0d0b06050a090403020100010101010101010606010101010401050101070107050305060403020204070606020202020202050602020305050706040202040602050302020206010401000101010101012201210120011f011e011d01010101011c1b1a011918170116151401010101011301120111100f010e0d0c01010b0a090807060105040302010000 | false => 0x393939392139213909393939213921d239393939393939d1093939d009cfced001392139212121cd09093939013921d209393939393939d109c639d009cfced13939393921392139093939392139c0c0393939bf393939bf093939bf09cfbbd1013921b9212121b9090939b90139c0d2093939bf39bfbfbf09c639bf6fa84cb221212121212121af01212121212121af2a2a2a2a2a2a2aab032a2aa7a6aaa9a9010121a521a4a3a3010121a5a0a4a3af039f2aab2aaa9eab039c2aab9caaa9ab212121212121999901212199219999992a2a2a942a2a94a9032b2a94a69da9940101219021a499af01552126a09d9997039f2aab29a89494039d2a02a89301000909151501090615090915150909898b090915150909158609851588098584840101068201010680097f158b7d7f808b097c1588097c158879857b88797984880909157801097678090974787373747609091588090986716f6f84716f6f8484016e6d78016e7678096e746d737f747809727b886f1686866f7971886f707b0001010606010106690101060664646767030362620303626203636262606062620101065e5d5d675e5c5c655e5d5c6767035b6262615b6262605b62626060620001010669010167590155656958056769030362620303626256566262600a090855555e5e5555595e555559655c5a6707565b6206560562045b56620356020100393939392139213909393939213921533939395039393950093939504b4b4e4c013921392121214809093939013921540944395039443950094450504b4f39433939394021393e3e0939394021393e3e393a3939393a395037373950374b39500139214021213e40090939210139392a093a395029164c0337444e024c0143002121212121212f2f012121212c2c2f2f2a2b2a2a292b2a2a282b2a2a29282a2a0127213121272f2601272f212c302f2d232b2a2a29232a2a282b2a02292b0100212121212020212f012b212620052f102a2b2a2a29292a2a282b2a0f290e2a0d1d1d21211d272f2f1d26312d2c0c0b0a232b2a2a290908072306050403020100090915150109061a0909151509091818090915150909151513131515131315150101061c010106110919151c100f1a18090e15150909150213161515131401000909150c01090c1a0a0a0c0c0a010c1c09091515090e150b09131515130a150908080c0c08090c1a080811180a031108090915151614070613130504030201000101060601020606010106060401061503031413030312110303100f030e0d0c02020606020206060202060b0507060a030309080307060503030403030201000101060601040621010506200107061f03031e1d031c1b1a031918170316151401020606021306120211100f020e0d0c03030b0a090807060305040302010000) | false => (match Nat.blt i 20 with | true => 0x90909090109010909090909090909d209090909090909d1090909d009cfcecf01010101010101cd090909c60109a0d20909090909d109d109c609c679c6ced10909090901090109090909090909c0c0090909bf0909bfbf093709d06fcfced1010101b9010101b9090909b90109c0d2090909bf09bfbfbf09c609bf6fa84cb301010101010101af0101010101af01af0303039f0303a6aa032803a7a6aaa6a9010101a501a4a3a4015c01a5a0a0a0af039f039f23aa9eab039c039f9c9ca6aa0101019901019999010101990199999903030394030394a9032803a7a69da993015501a51da4a3af01550126a09d9996039f03ab23a89e95039d0329a88d2b1e090909090109017809090909090989890909097c0909098609850985098584840101018201010182097f747f7d7f7d7f097c097c097c09887985797c797984850909097801097678097f74747373737609090972090986716f6f6f6f6f6f8484016e6d6e7d6e6d78097f746e7d7f73746f727b886f167b876f796f856f707b0901010101010164690101010164646467030303630303616360636060606060600101015e5d5d5d5e5c5c5c5e5d5c645d5b5b5b5b615b5b5b605b03626060620301010169010158595555656558056768030356630303616256566056600660055555555e5555555e555555655c5a5d01565b5b5b560456035b560302560100030909090901090109090909090909095209090950094b0950090909504b4b4b4f01010101010101490909094401092c520944094409440950444444444b4138420909094001093e3e0909094009093e3e093a3939293a395037373750374b4b500101014001013e40090908220109382a093a395023164c42374438414c0042030101010101272f2f010101012c2c2c2f032b2a2b292b292b2828282b282829290127012701272f302c272c222c242c2e2323232b2323292b282b030229280100012b21212020212f2828212620052f2e032b2a2a29292a2a28282a28280a29091d1d1d271d272f2f1d26222e2c08240323232a2b230723062305040302010003090909090109011a0909090909131a18090909150913091513131316131313150101011c0102011109190819100f1019090e09160909090913160315131401000909090d010b0b1a0a0a0a0d0a010b0d09090909090e091409130909130809070808080d08090b0b080808190a031003090909091614060513130403020100030101010102020606010101010401050103030303030303030303100f030e0d0c02020202020205060202030b0507060a0303090803070605030304030302010001010101010401070105011c0107011b03030303031a03190318171603151413010201010212011102100f0e020d0c0303030b0a090807060305040302010000 | false => 0xd282d2d2d2d0d2d289d0d2d289d0d2d25050d250d2d0d2d185d0d2d089cfced28282af82afa5afcd8585d2d064d0cad27f82d282d0cdd2cd85c6d2d07dcfced0788278788982d2d289d089d289d0c0d2505040bfd250d1d113bcd2d06fcfced2828278b9af82cdcd898589cc89d0c0d282bf78bfd2cdcdcd85c6d2d07dad4c002fa5afaf2fa5afaf64aeaeae64adaeae2727afa52ca5a9af2ca8aeaea6a8acae27a5afa52fa4a3af64a2aeaea0a2acae279fafa529a4a3a564a865aea6adacae2fa52faf2fa599af64ae65ae96adacae2f272fab2fa599af2ca8aeaea6a2ac060291afa51da4a3af64a2aeaea0a8ac05279fafa529ad5e0464adae03a80201007f82788274827478897f898b8985898b7f7f78827f7f748c8585898b8985898b7f8278825c8178827f7f748b7d7f898b7f7c78827f7c7882797f7e8b7d85898b7482787874827678747f748b7375898b0a827178748276786f85748b6f85898b7f6e6d827d6e76787f7f748b7d7f748b6f7c6d827d1667036f7f748b7d0201005c6969695c6967695c666509646665085c6669695c69676964666507646665065c695e695d5f67695c6665055c6665045b5f5e695d5f59035c66650264660100026959695c6667695c66651464666513026959695c695e125766651164100f0e555f59695d5f67695c66650d5c0c650b555f670a670908075c060504030201002b5040502150214028535353285351532b504050284f405028534c534b4d51532b2b40502b2b2154282e5353285351532b4440502b444050414d4c534b4d3c002150404021503e4013533c53282e51532b3a3950293a3e40374d3c534b4d51530150354021503e4013533c5328534c051d44395029125104374d5103510201002f2b2f312f272f31282e2d082c2e2d072b2b2131292b2f31282e2d06282e2d0527272f312f272f312c2e2d042c2e2d03232b2a3129272f31282e2d022c2e0100212b213120302f31282e2d122c2e2d112b2b2131292b2131282e2d10280f2d0e1d2721311d272f311f2e2d0d2c0c0b0a1d2b21312909080728060504030201000a1c1c1c0a1c181c1319180a131918090a161c1c0a161c1c131918081319180701121c1c01121c1c0a1918060f1918050a12181c0a0d1c0413191803130201000a0d1c1c0b0d0c1c0a1918130a19181209160c1c09120c1113191810130f180e08120c1c08160c0d0a19180c0a0b0a0909160c1c160807060a190504030201000207062102070620041f1e1d041c1b1a010706190307061804171615041413120207061102070610040f0e0d040c0b0a020706090208070604050403040201000107062601070625042423220421201f0107061e011d1c1b041a19180417161502070614021306120411100f040e0d0c01070b0a090807060405040302010000)) | false => (match Nat.blt i 23 with | true => (match Nat.blt i 22 with | true => 0x646465656464656564646565646465d22c2c2d2d2c2c2dd1646465d064cfcece64646565646465cd646465d06464cad26464656564cd65cd64c665d07dcfced00a0a181864646565646465c06464c0c00a0a18bf2c2cd1d1643765bb73cfc0d2010106b96464cdcd646465b5647dc0d20abf18bf64cdcdcd64c6bbd073ad3cb52c2c2d2d2c2c2daf6464656564ad65ac2c2c2da52c2ca9af2c282da7a6a6acac2c2c2da52ca4a3a3645c65a1a0a0acac2c9f2da529a4a3a5649ca7aea6a6acac2c2c2d992c2c9999646465979696ac972c2c2d942c2999af2c2897a7a6a0ac972c552d9020a499af645c97a1a0a6ac972c9f90a520ad599464a6a7aca89201000a0a18180a0a187664646565648589890a0a18820a0a18860a85898b648589840a0a18820a5d1880647f748b7d7d89890a7c18820a7c8082797f7e8b7d85898b0a0a18780a0a76760a7f7474737389740a0a71780a6f76786f6f7474738589890a6e6d6d736e76780a7f747e737f74746f6e6d82730d67866f7f748b73730100040465650404676964646565646465650404656904046767646665656460656504045e5e5d5d5e5e5c5c6565645c65655b5b5e5e5d5b59595c5c6565645c010004045969045d67675c5c65656404650e04045959585d5e5e57606565640d0c0b55555e5e5d5d675e5c5c65655c0a6509555b6767670807065c57050403020100010106060101063e04042d2d0404515301010650014b064e04044c4c4b4b4c4c010106500101064804042d53040451510144065001444e5041414c4c4b413c3c0101064001013e3e04043c53044b5151013a3939203a3e4037374c4c4b4b514c01013540011d3e4004043c3c3b4b4c4c1d3a3950200d514837415151510201002c2c2d2d2c272f2f2c2c2d2d2c2c2d2d2c2b213129292f2f28282d2d2c282d2d01272f312c272f262c2e2d2d2c242d2d232b2a3129272f3128282d2d2c280100012b212120202f2f28282d2d2c042d0d012b212a202b212128282d2d280c2d0b1d1d212120272f2f1f242d2d2c0a09081d2b213120200706281f0504030201000a0a18180a0a181a0a0a1818131318180a1318150a131a1513131818131318180102061101021a110a191818170f18180a0e151c0a08150c13131818131701000a0d180c0b0b0c1a0a0a18180a04180d09090c0c09080c1a0a131818130c180b08080c0c08090c1a0a0f18180a0a090809090c0c161407060a130504030201000101060602020606040415140413121101070606050306060404100f040e0d0c020206060202060604040b0a0409080702020606020506050404040304020100010106060104062304222120041f1e1d01030606011c1b1a041918170416151401020606021306120411100f040e0d0c01020b0a090807060405040302010000 | false => 0x282864286464646413136413646464d22828282828282cd1131313d013cfcecf5c5c5c5c5c5c64cd646464c6647da0d22828282864cd64cd13c613c67dcfced00a0a0a0a64646464131313c06464c0c013130abf2828d1d113376fd06fcfced2020201b95c5ccdcd131364b5647dc0d20abf0abf28cdcdcd13c66fd07dad4cb502022c022c2c2caf6464646464ad64ad2c2c2c9f2c29a6af2c282caea6a6a6ad020202a502a4a3a4645c64aea0a0a0ad029f029f29a4a3a5a69ca6a2a6a6a0ad020202992c2c9999646464979696969702022c942c2999af2c28a7a7a6a0969602551da51da4a3af645ca1a1a0a69696029f1da529ad5e949ca6a6ada89200045c5c0a5c5c5c5c7613136489648589890a0a0a7c5c5c0a87138589851385898a5c5c5c825c5d7d825c7f747f7d7d7d895c7c5c7c5c7c7d82797f797f7d8589850a0a0a780a0a76760a7f7474737389740a6f09780a6f76786f6f6f856f8589895c6e6d6d7d6e6d785c7f747e7d7f74746f6e6d827d0d5e876f7f747f7d7379045c5c5c5c5c5c64695c5c6465646464645c5c5c635c68646864666466646064665c5c5e5e5d5d5d5e5c5c5c5c5c5c64645b5b5b635d5b555b5c5c0465645c0100020201695d5d58675c5c656564046466025a015a585d5d5e57605766640960085555555e5d5d5d5e5c5c57655c076406555b5d5b670561045c57040302010004282801282828283e2828282828282c5328282850284b295028284c4c4b4b4b4c01010144282801492828284728522c522844284428442950414141474b4137410101014001013e3e13130a534b4b3b51283a3939293a39403737374c4b4b4b4c011d0840011d3e40133d0a3d3b4b4b4c1d3a3950290d4c4937414b415100450428282c2f2c272f2f28282c2d2c2c2c2c282b212b2929292f2828282828282c2c02272f2702272f302c2e2c2e2c242c2e232b232b29272f272828042d2c280100012b212120202f2f28282d2d2c042c2e282b212a292b212128281f2d28082c071d1d1d271d272f2f1f241f2e2c0624051d2b212b29202304281f0403020100040a0a0a0a0a0a0a1a13130a19131318180a130a1c0a13151513131313131317180102011c010211110a190a190f0f1718090e09160e08090d13130418131701000a0d0a0d0b0b0b1a0a0a0a0a0a040a190909090d09080b0b13130a1313090a080808080d08090b0b0a0f0a190a070f060909090d161405040a130403020100040202010702020606040404040412041101070107030305060404100f040e0d0c020202020202050604040b0a04090807020204060205060504040403040201000101010101040107041e041d041c041b01030107011a03190418171604151413020201020212011104100f0e040d0c0b01020a09080706040405040302010000) | false => (match Nat.blt i 24 with | true => 0x212121212121212101212121212121d221212121212121d1012121d021cfced101012121212121cd010121d001a4a3cd0101212121cdcdcd01c6d0d07dcfced02121212121212121012121c021c0c0c0212121bf2121bfbf0137c0bf73cfc0d1010121b92121b9b9016e21b973cdc0cd01b9b9b921b9b9b901c6bfd073ad3cb521212121212121af012121af21af21af212121a52129a9af012b21a7a6a6a9a9010121a521a4a3a3015ca3a5a0a4a3a3019f21a529a4a3a5239fa1aba0a4a9af21212199219999990121999999999999212b2194202999af282b9794a69da994015599901da499af55559926a09d99971d9f90a51dad5994239d992fa20600060101060601010676010106780185898b01010682018589860185898b0185898401010682015d7680017f6d8b7d7d8080017c82827d7c808279797b887d85898b0101067801017676016e747873737676016e7178736f76786f6f747873858974016e6d6d736e7678016e6d6d737d74766f6e6d82730d67866f79747873777b0601010669015d6769015c6565646467670101066964686767646365696460676701015e5e5d5d675e5c5c655e5d5d67675b5b5e5e5d5b59625c5b5e5e645c625901555969555567595555656958056769015a595958555e5e5656596964025e0555555e5e5555595e555559655c5a6704555b6767590362025c56670156060006212121212121213e0121212121212f5321212150214b3e4e012150504b4b4e4c01012150212121480101215001492f540144215029444e50444450504b4f394a2121214021213e3e01213c4020373e3e213a3939203a3e4037373950374b3e39011d3540211d3e40013a3521201d392a1d3a39501d0d514837443e263c2f48062121212121272f2f012b2f2f2c2c2f2f212b213129292f2f282b2d2a2c282f2f01272f3121272f262c272f212c302f2d2327263129272f31232b2a2d2c292621212b212120202121282b212620052f09212b212a202b2121282b2a2d28222f081d1d21211d272f2f1d26312d2c0706051d2b21311d200403281f02011d0600060101061c01011a1a0101181c13131a180113151c01131a1513131815131318180102111101021a110819111c100f1a11080e111c0e091a0c0e16151c13170c0c010d060c0b0b0c1a0a0a0c0c0a010c1c09090c0c09080c1a09130c0c13050c0508080c0c08090c1a080811180a03110408080c0c121003020a0911011006000601020606020206060102060604010608010706060503060604030606040706070202060602020606020206060507060502020606020504030202060204010100010106060104061c0105061b0107061a01030606011918170307061604151413010206060212061101100f0e020d0c0b01020a09080706050104030201060000 | false => 0x202010202020202020201d2020202d20101010102cfced1010101d002cfcecf0202020202a402cd027f02c6a0a0a0cd0202020202cdcdcd79c6c6c67dc6ced10101010101010101010174c073c0c0c0010139bf01bfbfbf373737bf6fcfc0d1020201b902b9b9b9026e6db97d7dc0cd01b9b9b902b9b9b96fc66fbf7da23cb50202020202a402af020202af02af02af0202029f2929a6af0228a6a7a6a6a6a9020202a502a4a3a3025ca0a5a0a0a0af239f9f9f23a4a3a5239fa09fa0a0a6af02020299209999990202999999999999022b2195202999af28289294a69d96931d551da51da4a3af5555a326a09d99961d9f1da51dad5e95239d1d30a206011e0202018202028976027f747f028589890185017c02858987018589850285898a02026d827d5d7d82027f6d7f7d7d7d7d797c7c7c7d7c7d827979797c7d858985016e017873767676016e7474737373766f6f09786f6f76786f6f6f6f6f858989026e6d6d7d6e6d78026e6d6d7d7d736d6f6e6d827d0d5e876f796f6e7d777b5d020202695d5d64695c5c6466646464670263026364686468646364666460646602025e5e5d5d5d5e5c5c5c5e5d5c645d5b5b5b635d5b555b5c5b025e645c620355550169555558595555656558056768015a015a58555d5e565657566402605f5555555e5555555e555555655c5a5d01555b5d5b590056045c56050556060705010101010101013e01010150014b2c5201013950294b2950010150504b4b4b4f0101014401272f48014401442c452c492344444423442950444444444b41384201010140203e3e3e01370a4020373e3e013a393a203a394037373750374b37501d1d08401d1d3e40083a0822201d382a1d3a39501d0d4c48374438413c0207250227212702272f2f28282c2f2c2c2c2f012b212b2929292f2828282b28282c2902272f2702272f262c272c222c242c2e2327232723272f27232b032d2c232621012b2121202021212828212620052f2e012b2122202b212128281f2d282220271d1d1d271d272f2f1d26222e2c0124031d2b212b1d202304281f00051d0607060101011c01011a1a0a130a1813131a180913091c1313151513131316131317180802081c0202111108190819100f1010080e08120e09080d0e1603151317010c010d010d0b0b0b1a0a0a0a0d0a010b0d0909090d09080b0b09130a09131b0a050808080d08090b0b080808190a0310030808080d121000040a091102100607030202010702020606020201020401050101070107030305060403020204070606020202020202050602020305050706040202040602050302020206010401000101010101010401070105011401070113010301070112031103070610040f020202020102020e010d010c0b0a0209080301020706050403040102010500060700))) | false => (match Nat.blt i 29 with | true => (match Nat.blt i 27 with | true => (match Nat.blt i 26 with | true => 0x787878783e783e78747876d274d276d2393940403ed1d1d10939d0d074cfced26d78787876cdcdcd747f78d07dd2a3d2097878783ecdcdcd79c6d0d07dcfced0787878783e783e78747874c0c0c0c0c039bf39bf3ebfbfbf6f3774bf6fc1c0c26db96db976b9b9b9746e74b973c1c0c209bfbfbf3ebfbfbf6fb674bf6fc13cb521403eaf3eaf3eaf0a783ed23ed23ed2392b3ea529d1ced1282bced0a6cfcece086da3a521a4a3cd5c7fa3a5a0a4a3a3239fa5a529a4a3a579c6c5cca6cfcad221402199999999990a78c0c0c0c0c0c0393a39bf20be99bd3737397193bec09455556db91db899b755556d35b4b899b51d9521b91d9a5994b0b0740c92c10c0c746d787874747678747f74787485898b0a857882748589860a85898b748589846d6d6d827d5d7680747f748b7d7f808b797c82827d7c8082797f7b887d85898b7478787876787678746e747873737476097871786f7876786f6f74786f6f74746d6e6d78736e7678746e746d737574786f6e6d786f0d59026f7574786f770100086d76825d5d89695c7f898b64648989087c78826487898c64858978648a8967086d82825d5d805e5c7f65827d5d67807c7c82825d817688797c7e5e647f8476015559787676767655557471730b760a0909717401786d096f717859730c080755556d6d5555766d55556d066c777605556e7604590c71036a560201560c000c39393e4021393e3e09393e504b4b2f5339393950294b3e4e093950504b4b4e4c0127405021272f4809443e502c522f542344505029444e50444450504b4f3e4a39403e403e3e3e3e0a373c403e3e3e3e393a3939203a3e403737393937373e39084035401d403e4008083c210a3e39031d3a39401d0d3c02373a3e013c0c3500212b214021272f31282b2f312c2c2f2f392b3931292b4e4e282b2d50294b514e01272f3121272f262c272f402c302f51232b434a29272f3128442a4c2c2b2640213a214020203e3e37372135200b3e09393a39392038213e37373908383f3e071d1d21401d1d21211d35403c200c06051d2221401d3f040332330201330c000c09091c1c0a091a1c0a13181c131318180913151513131a1513131515131318150802111c02021a110819181c100f1a18090e151c0e081a0c0e16151513170c0c090d0c0c0b0d0c0c0a0a0c0c0a010c1009090c0c09080c0f09090c0c0a0e0c0d08080c0c08090c0c08080c0b0a0a090809090c0c0d0b07060a090504030201000102061c02021a060a04181c040a1a0c0907151c14031a150413180c1716180c02021111020206060402060c0512060c0e12111102050c0c0e0e150c040a0c0c01010c0c010a0c1f0a0b0c1e0a0d0c1d09090c1c011b1a19091817160a15141308080c0c01120c1108100f0e010d0c0b01080a090807060509040302010c0000 | false => 0x90909090a090ad20a0a0ad20acfc0d2090909bf09cfd1d10909d0d00acfced0080808b908a4cdcd087f08c67d7fa0d2097c09bf09cdcdcd79c6c6c679c6ced0090909780a093e780a0a74c073c0c0c0093a39bf09bfbfbf6f3774bf6fc1c0c2086e6db908b9b9b9086e74b973b6c0c209bfbfbf09bfbfbf6fb074bf6fb63cb5010101af01a499af0a0a0ad264d2c0d2092b099f292ba6d12828a6d0a6a6a6ce0808a3a501a4a3a35c5ca0a5a0a0a0a3239f9f9f239fa3a579c6c6c6a6c6a0d201012199209999990a0ac0c0c0c0c0c0093a39bf209599bd373739719293c09455556db91db899b755556d358eb499b51d8d21b91d955994b0b0740d92b00b6b080808780a0876780a7f7474738589890a850a820a8589866f8589856f858984086e6d827d5d6d82087f747f7d7f7d7f797c8282797c7d827979797c7985898508787478767876780a6e747473737676090909786f6f76786f6f746f6f6f7374086e6d78736e6d78086e746e737573746f6e6d6e6f0d59706f6a6f6e6f776a09080808825d5d89695c5c897f64648989087c0882646189876485897564608966555582825d5d5d5e5c5c5c825c5d645d7c7c82825d5b6c7a797c0f5e6479846d015501780155767655557471730b735a0909097501096c6b6f717556730c560855556d6e5555556d5555555757777301556e6c56590c560a6a56000b560c0d0d0909094001093e3e090909504b4b2f53093a3950294b3950373750504b4b4b4c0127015001272f48094409502c472f522344505023442950444450504b413842094039403e3e3e3e0a370a400a373e3e093a3940203a39403737393a37373739080808401d1d3e40080808220a08381e1d3a393a1d0d3c34373a38333c0c3301012b212120272f2f28282f2b2c2c2f2f092b392b292b292928282850284b2c4b1d272f271d272f262c272f222c242f2e2323234423272f272844034c2c282639013a212120203e3e37372135200b203d093a393a203820393737371f1f3f200a1d1d211d1d1d20211d352233200c33091d321d3a1d3f32083233000b330c0d0b0909091c0a091a1c0a130a1813131a180913091c1313151513131316131317150802081c0202111108190819100f1019090e09160e08090d0e1603151317010c090d090d0b0d0b0d0a0a0a0d0a010b0d0909090d09080b0b090909090a0a0a090808080d08090b0b0808080a0a0808070909090d0d0b06050a090403020100010102010602021a060a040a0a040a170b090709071403141404130f081716180c0202021202020506040203090512060c0e120f1102050a0c0e0e150c040a0c090101010d010a0b0d0a0b0a170a0d0b160909090101150914091312110a100f0808080808010e010d080c0b0a01090809010807060504030a0902010b000c0d00) | false => (match Nat.blt i 28 with | true => 0x82828282d2d289d27fd1d2d0d2d2d2d2d1d1d1d1d2d1ced17fd0d0d0a6cfced2cdcd82cdafcda3cd7fc682d0a0d2a0d27c7c82cdd2cdcdcdc6c6d0d07dcbced16e8282bf89d2c0d2738274d2c0d2c0d23abfbfbf2fd1d1d16f3ad0d073cfced26eb96db989cdcdcd7f7f74b97dd2c0d27cbfbfbfd2cdcdcd6fc6d0d07dad51b8afcdafa5afafafaf2ccdd2d264d2d2d2299fd19fa6d1a6d1a62ba6d0a6aaa6d2cd9fa3a5a0a4a3cda07fa0a5a0cba0af9f9f9f9f29aaa3cdc6c6c6c6a6cba0d2205099af99af99af2c82c0d2c0d2c0d2292b39bf29d199d1372bce88a6c8ce9a556ea3b920a4a3cd557fa34aa0c8a3c11d9fb9a529ad67be79c8d08aadc1811b7f826e82898c898c7f7f7482898a898c7f7c7f82898789876f85898b898a898a7d826d827d81898c7f7f74827d81898c797c82827d87898c797f797c7d8a898a6e6e74787377768c737f748b7377898c6f7c09727377768c6f72748b738a898c6e6e6d827d77808c7f7f746e7d8a738c6f7c6d827d8767876f7f74827d777a007d827d82646889685c7f89826468898a087c7f826487898764858975648a8968558282825d8180815c7f5c7f7d8164817c7c82825d816c87797f0f697d818600556e01787377588c557f748873778968097c097573876c066f88756673056104556e6d825881808c557f6d667d778903556e6c6367028601795a8c1b70001b1b29503a502f4f2f54295029502c522f5229503950294f2f54375050504b4f4e4f2b442b502f492f49094429502c522f522344505029492f4f444450504b4f38493a3a3940203f3e54373a0a402c3f3b543a3a3950293f4e54373a39503b4f4e541d440836203f3e54084408222c5238021d44395029495149373a3847510142002b2b21502f302f54282b2f502c522f302b2b3950294f2f4f282b282b294f2c4f1d272f312f302f302c272f222c302f52232b234429302930282b0353294f4800202b2131203f2f54372b214a2c522f522b2b393a294f2054372b392e293f2f041d36213120302f541d4a222e200345021d2b2150293f4201233d541b34001b1b0916091c171b1a1b0a190a19171b1a1b0916091c141b141b13161316171b171b0812081c101b1a1b0819081c101b1a1b09120916141b1a1b0e16031c171b0100090d090d0b1b0b1b0a190a0d171b0b1b0916090d141b0b1b09160916171b17070812080d101b0b1b080d08190b1b10060916090d141b05040a1611031002010001070107051b1a1b0a190a1c171b171b0907091c141b1a1b04160f09171b1a0802120212051b051b04120307051b1a060e120f1c051b05040e121503170201000107010d051b0b1b0a190a12171b0b11090d09070b1b14100907060f170e0d0c08120812051b050b0819180a05090807011215061405040309021b1b01001b00 | false => 0x2c2c20202c2c2cd22c2c2cd22cd289d22c2c2cd12ccfced12c85ced0a6cfcece646473cd64a4a3cd0a7f89d0a0a0a0d20a7c2ccda0cdcdcd79c6d0d07dcfced1202020782c2cc0c0737374c0c0c0c0c0203a39bfc0d1d1d16f3774d073cfc0d1736e6db999cdcdcd737f74b973d2c0cd09bfbfbfc0cdcdcd6fc674d073ad51b7646464af64af2faf2c2c2cd264d264d2012b299fa6a6a6afa628a6d0a6a6a6ce64a4a3a5a0a4a3a3a05ca0a5a0a0a0a3239f9f9f29a4a3cda6c6a6c6a6a0a0d220202199999999992c73c0c0c0c0c0c0202b21bf20af99d13737c084a69dc0931d5521b920a499cd55559935a0c499b41d9f21a520ad67bd5cc4748aad1a0b1b73737378738989760a7f7474738a89890a857482738789876f858985738a898a737f6d827d5d89807d7f747f7d7d8989797c82827d87898c7979797c7d8a898a736e747873767676737f7474737373766f6f09787370768c6f6f7474738a7389086e6d6d7377808c737f746d737d73896f6e6d82737767866f79747f73777a5d73735582645d64685c5c647f646464895c7c55826461646864856475648a6468555582825d5d80815c5c5c82645d647d7c7c82825d816c7a5c7c0f5e647d8676555501787358587655557484730b8968016e017573736c7d6f7175107300611055555582585d5880555555657d777314557c6c5b678970835c56051b701a1b1a202020402c2f2f3e202037502c4b2c52202b3950294b2f4e373750504b4b4e4f012721502c492f49284437502c452c522344505029492f4f444450504b4f3842203a2140203e3e3e37370a402c3b3b3e093a3939203f4e54373737503b4b3b4e1d1d084020343e540a3a0a222c2c38291d3a3950203f514837443841512f3425012b21212c302f2f28282c2b2c2c2c2f292b212b29292f2f282828502c4b2c291d272f272c302f302c272c222c302c5223232344293029302844034c2c29483e202b21212020203e373721262c172f52202b21392029202f3737372d293f2c101d1d21212030202f1d352214200045141d23212b203f424b2833171b341a1b1a0a090a1c17171a1a0a130a1817171a170913091c1414141a13131316171717170802081c10101a1a0a190a1910171a1a090e091614101a1b0e160315171701000a0d0a0d0b0b0b0b0a0a0a0d17050b1b0909090d140b0b0b0a130a09171b17050808080d100b0b0b0a080a190b0510040909090d141403020a091102100100050102010605051a050a040a0a170b170b0107010714051a1a04130f08171b1a04020202120505050504020309051b1a030e120f1105050201040e180c170b000b0101010d05170b1b0a170a09171b0b08010901070b171407090706101706051001020108051b0517081918140504031401081513140201170a1a1b14001a1b00)) | false => (match Nat.blt i 31 with | true => (match Nat.blt i 30 with | true => 0x787878783e783ed2747876d274d2c0d2393940bf3ed1d1d109d0d0d0cecfced26d7878b976cdcdcd747fd2d07dd2a3d2097c78bfa4cdcdcd79c6d0d07dcfced0787878783e783e787474c0c0c0c0c0c039bfbfbf39bfbfbf6f37bfbf6fcfc0d26db9b9b96db9b9b9746e74b973d2c0d209bfbfbf39bfbfbf6fc6bfd06fad3cb521403eaf3eaf99af0acf3ed264d2c0d2392bd1a529d1ced1282bced0a6cfcece08a5a3a5a3a4a3cd5c7fa3a5a0a4a3a3239fa5a529a4a3a579c6c5cca6cfcad221219999999999990a74c0c0c0c0c0c0393a39bf20d199d13737c071a6c8ce94555599b91da499cd55559935a0c8a3b51d9fb9a51dad599479c4bf89a818501a746d7878747f7678747f74787385898b0a857882748589866f85898b6f8589846d6e6d827d5d76807f7f748b7d7f808b797c82827d7c8082797f7b887d85898b746e787873787678746e7478737374766f6f71786f6f76786f6f74786f8589746d6e6d78736e7678746e746d737f74786f6e6d826f0d67866f7f74786f777b06086d76825d5d89695c7f898b64648989797c78826487898c64858978648a8967555582825d5d805e5c7f65827d5d67807c7c82825d817688797c7e5e647f8476555559785555767655557488730b8969096e7174736f6d7e6f7178696482881155556d82555d766d55556d657d777615557c76675989861879568c1a56111c1839393e4021293e3e09393e504b4b2f53393a3950294b3e4e373750504b4b4e4c0127405021272f4823443e502c522f542344505029444e50444450504b4f3e4a393a3e40203e3e3e37373c4037373e3e393a3939203a3e4037373950374b3e391d1d35401d1d3e40083a3c212037392a1d3a39501d0d514837443e513c2f4806212b214020272f31282b2f312c2c2f2f2b2b3931292b4e4e282b2d50294b514e1d272f311d272f262c272f402c302f51232b434a29272f3128442a4c2c2b2640213a214020203e3e3737214a200b2f53393a39392029213e3737392d293f3e111d1d21401d272f211d3540532c504a151d2b21401d3f43182333541a33151c1509091c1c0a091a1c0a13181c131318180913151513131a1513131515131318150802111c02021a110819181c100f1a18090e151c0e081a0c0e16151513170c0c090d1c0c0b0d0c1c0a0a0c0c0a010c1c09090c0c09080c1a09130c0c13120c0508080c0c08090c1a080818180a03110409090c0c161403020a091101100600060102061c02021a060a04181c040a1a0c0907151c14031a150413180c1716180c02021111020206060402060c0512060c0e12111102050c0c0e0e150c040a0c0c01010c0c010a0c1c0a170c0a0a190c0909091506010f1508090706070a11061108020c0c02170c0508191804011503150108150214180118091a001a1c151c00 | false => 0x90909090ad20ad20a850ad00acf89d2090909504bcfced10985d0d04bcfced0080808825da4a3cd087f89c67d7fa0d27c7c7c7cc6cdcdcd79c6c6c679c6ced0097809783e783e780a7874c073c0c0c0093a39bf3ebfbfbf6f376fbf6fcfc0d2086e6db976b9b9b9086e74b9737fc0d209bfbfbf09bfbfbf6fc66fbf6fa23cb6012701a501a42faf64a664d264d264d2092b509f292ba6d12828a6d0a6a6a6ce0827a3a55da4a3a35c5ca0a5a0a0a0a3239f9f9f239fa3a579c6c6c6a6c6a0d201402199209999990a0ac0c0c0c0c0c0093a39bf202b99d137373771a69dc093555555b91da499cd55555535a0c499b41d9f1db91da8599579c46f0da8150b6b086e7478737f76780a7f7474738589896f856f7c6f8589866f8589856f858984086e6d827d5d6d82797f747f7d7f7d7f797c7c7c797c7d827979797c79858985086e7478737876780a6e7474737373766f6f09786f6f76786f6f6f6f6f858989086e6d6e736e6d78086e746e737f73746f6e6d826f0d5e866f796f6e6f777b09555555825d5d64695c5c647f64646489797c6f7c646164876485647564606466555582825d5d5d5e5c5c5c825c5d645d7c7c7c7c5d5b6c7a797c0f5e6479846d555501785555767655557484730b8969096e0975736f6c7e6f7175106402605f55555582555d5582555555655c777301557c6c5b591319837956161b56181b19093a394020293e3e373737504b4b2c53093a3950294b3950373750504b4b4b4c1d271d441d272f48234437442c472c522344444423442950444444444b413842093a3940203e3e3e37370a4037373e3e093a393a203a394037373750374b37501d1d08401d1d3e40083a08222037382a1d3a39501d0d4c48374438413c020725012b212120272f2f28282c2b2c2c2c2f282b392b292b292928282850284b2c4b1d272f271d272f262c272c222c242c2e2323234423272f272844034c2c282639013a21212020203e37372126200b2f53093a393a202920393737372d283f200a1d1d1d1d1d272f2f1d3522142c13244d1d231d3a1d3f43082333171b33151b140909091c0a091a1c0a130a1813131a180913091c1313151513131316131317150802081c0202111108190819100f1019090e09160e08090d0e1603151317010c090d090d0b0d0b1c0a0a0a0d0a010b0d0909090d09080b0b09130909131b0a120808080d08090b0b080808190a0310030909090d161400040a091102100607030102010602021a060a040a0a040a170b090709071403141404130f081716180c0202021202020506040203090512060c0e120f1102050a0c0e0e150c040a0c090101010d010a0b0d0a170a000a190b0e09090907010f140f090706100a11020f08020808021b01170819181401151303010815131418190f091a1b141c151900) | false => (match Nat.blt i 32 with | true => 0x2f2b2faf2faf2faf28cfced22cd2ced22b2b5050a6cfced128cfd0d0a6cfcecf2727a5a5a4a4a3cd5c7f7dc6a0a4a0cd9f9f9f9fa6cdcdcdc6c6c6c67dcfced1214021403e3e3e3e0a6f74c0c0c0c0c0393a39bf4bbfbfbf373739bf6fcfced1556e6db955cdcdcd556e6db97dcdc0cd08bfbfbfa6cdcdcd6fc6bfbf7dad4cb52f272faf29a42faf2ca42faf2caf2faf292b2f9f2929a6af282ba6a7a6a6a6a92727a3a5a4a4a3a4a05ca0a5a0a4a0af239f9f9f29a4a3a5239fa09fa0a4a6af1d272199209999992c27999999999999292b2194292999af282b9494a69da9931d551da51da4a3af5555a326a09d99961d9f1da529ad5e94239d1d30a2062b1e027c768264cd8976287f89d264cf89d21385bf7ca6cfced11385ced0a6cfcecf027c82825da4a3cd5c7f6d827d7d7dcd7c7c7c7c7d7ccdcd79c679c67d797dcf01787678767676760a6e74787373c0c0093a39bf6fbf76bf6f6f6fbf6f6f73ce556e6d6d7d6e76b9556e6d6d7d7d73766f7c6db97d1667876f796f7c7d77c5a30227a3a55da464af5c5c64ae646464ad029f2f9fa6a4a630a663a6aea6a6a6680227a5a55da4a3a55c5c5ca2a05c64a49f9f9f9f5d9f8f5b5c5b24a1645ca9230155215a205d999955559769640596680195219520298f26925692946424931e555555915d55a3a5555555a15c91642055918f8d67282e1e5c8d051e561e1e302b2b2150292b2f3e282b39502c4b2f52292b3950294b2950282b50504b4b4b4f1d27214429272f49284421442c492f492344444429442950444444444b4f3842213a2140203e3e3e37370a4020373e3e393a3939293a394037373950374b39501d1d08401d1d3e40083a0822201d382a1d3a3950290d4c49374438413c2f07252f2b2f2f29272f2f282b2f2f2c2c2f2f292b212b2929292f282b282b28282c291d272f2729272f302c272f222c302f2e232b232b29272f27232b032d2c2926211d2b212120202f2f282b212620052f2e292b212a292b2121282b2a2d282229271d1d1d271d272f2f1d26222e2c0124031d2b212b29202304281f00051d060706013a2140012b3e3e13130a534b4b1a53091339504b4b392a1313134c4b4b4b1502270811022748480847081c4545104923440944233229221341031513421f25014021403e3e3e3e0a0a0a3c0a1f0b3d093a394009323e0b37130a39134f0a2008080835083235340808083d0a033425093a0840162d2c250a1335234525252a0227212702272f2a28282c2f2c1f2c1e012b2130292a3006282824252807061d02270227022726060202031e242e061e232724060205001f28232d202c01222201012121201f2107010501252c2e202301222107010003241f072d25282602260202011d02301d2b012e2d29022a282a011d2a2f292d2e2e012c3030312d2e00 | false => (match Nat.blt i 33 with | true => 0x29503e502fd12fd14bd0ced04bcfced2502b50504bcfd1d137d0d0d04bcfced02727b9b9a4a4a3cd79c6d2d0a0cfa0d244445050a6d1d1d1c6c6d0d079cfced13e4039403e3e3e3e0a6f74c0c0c0c0c0393a39bf4bbfbfbf373739bf6fcfced108b96db955b9b9b9086e74b973d2c0d208bfbfbf4bbfbfbf6fc6bfbf6fad4cb62f272faf29a42faf2c9f2faf2caf2faf2b2b509f292ba6d1282ba6d0a6a6a6ce1d27a3a5a4a4a3a4a05ca0a5a0a4a0af239f9f9f299fa3a5289f9f9fa6a6a6d121272199209999990a279999999999992b2b39bf292b99d1372b3971a69dce941d5521b91da499af55559935a0c899b41d9f21a529a85994289d390da81a4f1e097c787873827678138574d0738589d21385bf7c4b85ced11385ced04b85cece087c6d825da476cd797f74827d7f89d27c7c7c7c797ccd827985797c797989d009787878767876780a6e7478737374c0093a39bf6fbf76bf6f6f6fbf6f6f73ce086e6d78736e76b9086e746e737f73786f7c6db96f1667866f796f7c6fc17b3a022799a55da464af5c5c64d2646464d2139f509fa6a6a64fa685a6c2a6a6a6660227a5a55da4a3a55c5c5c7fa05c64a49f9f9f9f5d9fb77a797c41ae6479c728015521782099999955557488730bc069093a39bc202b8f4c6f71bc48733c931e5555556e555599b9555555655cb87321556e8f955941531e798d161e561e1e53292b395029292f3e372b39504b4b2f53292b3950294b2950372b50504b4b4b4c1d27215029272f49234439502c522f522344505029442950444450504b4f3842373a3940203e3e3e37370a4037373e3e393a3939293a394037373950374b39501d1d08401d1d3e40083a08222037382a1d3a3950290d4c49374438413c2f07252b2b212b29272f2f282b2f2b2c2c2f2f2b2b392b292b2929282b2850294b2c4b1d272f2729272f302c272f222c302f2e232b234429272f272844034c2c2b2639212b21212020213e372b2126200b2f522b2b393929292139372b392d293f29271d1d21211d272f2f1d3522142c50244d1d2b212b293f434b2333541b33151b14093a394020293e3e13130a534b4b1853091339504b4b392a1313134c4b4b4b150827081c02271a480819081c45471a5309440944233229221316031513421f0c094039403e3e3e3e0a0a0a3c0a1f3c3d093a394009323e0b37130a39134f0a200808080d083235340808083d0a03344d093a0840162d2c250a1335234525252a0127212102272f2a2828012b2c1f2c38092b3930292a4f332813243e4b16180c022702270227260602020332242e064d232741110205400c23443f0c2c090c3801012140201f3e0d01050a4420433e4d093a39072051144637072d34374650431d0208080230213a08193c4d024d282a1d1d432f14463d2d09401b3f44433f00 | false => 0xd282d2d2d2d2cdd289d0d2d2d2d2d2d22bd1d1d1cfd1d1d1d0d0d0d0cfcfced27fcdcdcda4cdcdcd7f7fd2d07dd2a0d2c6c6cdcda4cdcdcdc6c6d0d07dcfced174bfbfbfc0d2c0d274d074d2c0d2c0d239bfbfbfced1d1d16f37d0d06fcfced26db96db9a3cdcdcd7f7f74b97dd2c0d23abfbfbfa4cdcdcd6fc6d0d07dad4cb529a4afafafafafafa6cfd2d2a6d2d2d22b2b2b9f29d1a6d1a62ba6d0a6cfa6d29fa4a3a5a4a4a3cda07fa0a5a0a4a0af9f9f9f9f29a4a3cdc6c6c6c6a6cfa0d221a599af99af99af73d0c0d2c0d2c0d22b2b39bf29d199d1372bce84a6c8ce945555a3b91da4a3cd557fa335a0c8a3b51d9fb9a529ad5e9479c4d08aa818816b7f82788289828978897f89d2898589d285857882898589d1858589d0898589cf828282827da4cdcd7f7f74827d7f89d27c7c82827d7ccd82797f79c67d8589d07878787876787678747f7478737389c06fbf39bf6fbf76786f8574d06f8589d26d6e6d827d6e76787f7f746d7d7f74786f7c6d827d1667876f7f74827d77c5a35d8276825da489af5c7f89d2646489d2289f2b82a6cf894fa68589c2a6cf89685d8282825da4a3a45c7f5c7f7d5da0a49f9f82825da4b787797f41a17d7fc5765555217899999976557f7488730b8968097c39bc73d18f4c6f88c24973cc935f55556d825d5d76cd557f6da17d7789d0556eb79567ca5383798d8cac56c3c95329503e502fd12f3e4b503e504bcf2fd25050505029cfd1d14b5050504bcfced0272740502fa42fcd79c6d250a0cf2f8a444450502944d1d1c6c650504bcfbd493e403e403e3e3e3e37377440c0c0c03e393a3950293a3ebf373739504b4bced11db96db91db93e40084474912cd2ba841d44395029125149373abdb651a968252f2b2faf2fa42faf282b2faf2c2c2faf2b2b3950292b2fd1282b282b294ba6cf27272fa52fa42fa4a0272f9ba0a42f52232b239f292729a4282b60a7292b9e40212b214020202f3e372b214a2c172f522b2b39392929213e372b39a7293f2fa51d2721a51d272faf1d4a9b8720abb44d1d2b2150293f9ece23b054ac33c3c987097c78782c823e78138574d04b8589cc098539504b85cea9138513d04b85ce1508276d825da476ca087f748c7dcc8c947c7c7c7c796acd7579855b157942c20c097878783e783e780a0a74747396743d093a393909b339866f3709396fc1747c086e6d7808b36d34086e743d7388344d097c09bf16aebc836f857bd245c3c9ae022721a55da42fab282864d264572cc8092b395429ab54b62828249da666185f022702a55da4a3065c5c60c4a02e064d239f4111237aa88379c6c1aca6d1c9c10101212120963e690a170aba2cc7c04d093a395a2051708337072dac4bc3d1c75555086d1db82164551965ac5dc3cd861d2743af61c3c9ae09b9c98744c55200))))))
def routeByte (i : ℕ) := Nat.land (Nat.shiftRight (routeByteBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
def routeRefBlock (i : ℕ) : ℕ := (match Nat.blt i 6 with | true => (match Nat.blt i 3 with | true => (match Nat.blt i 1 with | true => 0xb700b100b700b803630363031603e7006701c8031603790363036302ef036500670068031603170369036902020122020201fa01990199013502a20135012801350213007c007c02f9008a04d7012e04d702040036027204be02a304d0010104d00108036903690369036901cb01c6020202030135019c013501a400ba016d013501360014019f02f9036d04c301ce04d702050036016f04be01a604b8007004d702b1037e037e02820282037e037e037e037e037e037e0395039501d501d500bf00bf031300c703250325035a035a02e502e5035f035f031303e9004901da03130380038c038c0370037001dd00be01f201ec038c038c038c038c038c038c037003700370037001dd01d801dd01de02950295010e010e00eb01ed009b009b031000a304c700c904d301f3023e023e03250325032701130327038e003001b00310037304c701e004c701e302a802a80041004100ca00c100ca00c2028202820282028202820282035f035f00ca018600ca00c100ca00cb026802680049004900eb00eb035f035f02e8004600490044031300ce035f035f02e502e50049004902e502e5035f035f02e803610049004a03130314029502950115010f0115010f01ab01ab011c029800d100c5011c020901150115011501150115011001150116011c01ad011c01b500d1018b00d100d2026802680295029500eb00e200eb00ec0017026904c1029a04cd00ed04cd00f400140014032503250327011a032703280017018e04c101b904b1005004c702ab038d038d0022002201d301d3010602af037f037f037f037f037f037f0358035800a40157010601d6010601dc0378037803780378039503950358035802d2002d006d028b04c702b0023e023e030f030f035a035a04c702880358035802d2035b006d015a04c701e200a400a401e801e800a901eb00a4009d00a4009e010600fc01060200023e023e00a400a400a9024200a901f100a4009d00a400a500a9015801060107021e021e008c008c009002210090020100300027031000a804d7013104d70137023e023e030f030f04d3024804d301f4003000310310031104ae003804d002a6000a000a01bf01bf00f202a90170005704b80066006d006104c700cd034b034b02c50012004e028304c302aa018f018504b10191004e01db04c700d4034b034b008c014600f201c200f201ca0170016a04b80172006d01c904c300bb034b034b02c50350004e014a04c301d00170017104b80174006d006e04b80260008c007f008c008300f200e600f201f00036002b04c100a704c704d30014000f02f9008f04d3011904d3011e003601b204c100ab04c704c7008c007f008c008e0090014800f200f3001701a104be009204c304d70014001502f902fa04a6001804cd029c0036003704ae024d04b804c7 | false => (match Nat.blt i 2 with | true => 0x4b07140714071607160c570c0a0c660287053f04e80718018d053f05c305dd004f0151015101510151051a050d051a0151015109f70151015100070007000700070154015406a30154015404dd06a201540154015401540154001f001f001f001f0143014306990143001f001f0a54001f053d05c405de02eb0231023108400840035a052c084b035a06a704f9085e0357053d04df07240159002600260026002601f507e401f501f50026065104a70026065507ea04c000a0000e000e000e000e065507e105ef0241015301530024015306550656055e02750026002600260026064c07ed05e4021f0026002600260026053606fe04ad0032068b068b023d023d05360247055a024706a7056706a802cf053d05c005d9015c0517050a0517013e013e09f1013e013e053f017c0056017c0538065b04b50060000700070a4f0007053c05c105da02df053f04e606ad0183053f066406b0025d014304d9069801430143014301430143053e04e206b30168053e065e06b60255069d04f70854034a053c04db07210149053f04e9018f01900538052f006d025f000e064904a3000e064c07de04bc00850536065404ab002a0538006a04b7006b000e000e000e000e053506fa04a50016053d065706a90246053f0192052601e101410141000b0141064c064d055d026d053c064e069f0224053e0173052401cf069d0565069e02c0053c05be05d1014d0536052d0036024b053f04ea04b8037e037e02ae02ae0312031203440344025902590312031203840384038c038c02a002a00384038403840384039403940382038200f700f7012f0212030f030f01e901e9032703ea0360036003310331034500fd0345038600b700b702a802a8037203720259025900ca00ca03760376036b036b0251025100b700b7033c033c0251025103150315025102510315031502510251031503150381038103850385020d020d00d102110385038500de00de01150208037203720385038500d1025b00d10214029502950381038103810381036b036b0382038200ba025300ba020a0364036403250325033d00ea033d03830364036404d002a504d0025e04d0021502ae02ae038d038d0271027100fe00fe00fe00fe02ae02ae028a028a028a028a02ae02ae03310331034e034e034403440363036302ee02ee00670067034403440394039402a002a000fe00f900fe00f902a002a00124012400fe01fb0271027102a002a000fe00fa00fe00ff039403940394039403940394012f012f012f012f012f0126012f0130021e021e033103310334012b033403960030003003310331034501020345034603760376005a005a00b700b100b700b201c101c100b000b0031600b50363036302ef00620067005e031600b90376037603760376037603760363036300b7016b | false => 0x2d80055005500550055005d005d005d005d0143014300430143003d003d003d003d00430043004300430ea70ea70ea70ea7024f024f085a085a06900690025002500162016201620162020c07f9020c020c02d802d8026402d802d807f102d807f10181018106ac0181066207fe05f5025a02640264026402640e420e420e420e420166016606b20166065c07f505f6025202640264085108510c65026a02e302e30364052e0862036405380256055b0256015101510151015102c902c9028902c9005500550055005501540154005d01540289028902890289001f001f001f001f01650165005c01650289028908410841071a071a071907190722072207230723016201620162016206fc06fb06fc06fb02c902c902c902c902c907e802c907e8015301530024015306f306f406f306f401660166002601660e4e0e4e0e4e0e4e016601660026016606fc06fd06fc06fd0e9f0e9f0e9f0e9f0c5f028c02ce02ce071a071a071c071c0c6b0c1b0c6c028e013e013e013e013e051c0513051c0162005d065804b2005d0055005500550055005d0659005d005d005500550a480055005d005d005d005d01660166016601660143014301430143016604e106b1016601650165005c016503e003e0083e03e006b4060b085701c706b404fd0844036206b4056c06b502ed016201620162016201c007e701c007e7016209e901620162065c07fc04c200b3000e064a000e000e00b607ef052300b6053e05bf05d502cc053806f504b60069016601660166016606bd01c306bd01c30166016601660166065c065d0563028d069d06050848019e053e054f01cc01cc053e04e4071d016e053e05c505df006f0151015101510151027b027b027b027b0181018101810181015401540154015402b702b7027b02b7003d003d003d003d0043066000430043027b027b0832083203de03de082d03de06ae060d085f01d9017a017a017a017a01d407d901d407d901810181000e01810e490e490e490e49018101810181018106c101d706c101d702b702b702b702b702b707db02b707db002606520026002600c807e2052500c80e960e960e960e960c57028402be02be06a70607083801af053f055001df01df013e013e013e013e051e0510051e017a0043065f04af004300070007000700070180018000420180018104e506ab01810180018000420180003d003d003d003d0143014300430143003d003d0a41003d0043004300430043071f071f071e071e071f071f0720072006ae04fc0835035e06ae056a06af02e4017a017a017a017a06f706f606f706f6017a09dd017a017a066207f304c600c401810181000e018106f706f806f706f80181018101810181066206630562028501410141000b014106ef06f006ef06f0053f05bc05cc02bc053706f204b0)) | false => (match Nat.blt i 4 with | true => 0xc210c210c210c2102190219021902190e930dd20a510dd60e9303580e97034903df03df03df03df03df03df0e940e94035809a40a510c22082e0358083a03e60a6b0a6b0a1a03c10c6d059d0a65009a0c6d00930c89009a0a1a0a1a0a1a0a1a0a1a02fd0a1a03c40a6505b00a6505b10a6101a80a6603b90b870b8709860bbf05e002f002f202f2057d05a0057d0bc305e302f30c8d02f60e9a0b8b0e9a0a1b0e9502b60eb103cd057d05b3057d05b5083901ae0a6803bb00080008000800080040004000400dd30040004000400dd30c4f0c4f0c4f0c4f0be00c4f0be00c4f015601560dd70dd8015601560dd70dd80c620c620c620c620c620c620c620c620145078b0a0307950a4001450c640254034b034b0e980e98034b034b0e990e99083307920a510a04083603a40a5203a80a6b0a6b0a6b0a6b0a6b00750a6b03190dda0dd50dda0df20c7001aa0a6c03230c710b880c710b8c0c6f03030c7203c80b9001ac0b900b910a6701ac0b9003d0098609830986098705c802b505ca0296056e0794056e098905cd02bd05d0029b0c7309880c730c7302bb02bb0c740326057d0798057d0b94083d018c0c7703d202320232002102320021002100210e1300210021002100210232023202320232023202320eb702320358067205f109a706a103580a4a03590219021902190219021902190eb9021903580be5057a0be60c5b03580c5e022205310531057d04f3083003580244024403580675057006770a4903580ea5035b0c860c8605f10bbd0bc7022a0c91023305a3059f05a30bcc04a8001e0c96029e05f104ef05f10bc205e9022d0c8b03b505f1067305f105a406a4023505f2030e05e504ee05e50bcd05e102170c9503ae057a0548057a0b9e0552021d0c830333057d04f1057d0bc6023e023e030f030f0570054a057005a5003002d1031002d30008000800080e110008000800080008051b079b0570002f051b015604ac002f034b0be1057d0be20c51034b0c550243015609a6057d0ddb06a6015606aa015b034b066c05e509a20697034b0a44034c014509a1057a0dd1069c014506a0014b034b066f056e06710a43034b0e9b0350083c0797057d0806084c03aa086403ac059a0594059a0bc104a400040c8c029105700029057000a604aa00290c9a00a6057d0544057d0b93055702370c7603d1057d0245057d00aa055901b405f401b805e5066d05e5059b069a021a05e6008d057a0223057a0091055401a305e701a5056e0546056e059c001402c302f902c6057d024a057d04f4003604ae01540154005d015402e902e902e902e90ea90ea90ea90ea9026f026f026f026f0e460e460e460e4602e902e9026f02e902e907fa02e907fa0c570e660eb3026f026f085b085b0c6b027302ec02ec005d005d005d005d02d802d802d8 | false => (match Nat.blt i 5 with | true => 0x5470d3a021c055100250fd504f0057c04f0068b068b023d023d0fce06db062c054906a7056805d702d0050f00200fd50f0b075e080906cd04de06a501550fd40f09075f080406cc04da069b01440fcd06c90761066e0f2004f70853034a0fd508b2083c080508b30505086303aa09d802910fce0653056f002804a9065304a900280fd50d30057b05430d380236055602360fd50676062a05b406e4054d055801b306dd06d506d3067c06de036706b803670fd40670062905ae06e3054c055301a20fcd06da062b0545069d056605cf02c20fd50541057d024a053604fa00360c680c680c210c680c5a0c5a0be40c5a080708070ea20ea2080708070ea20ea2029d029d029d029d03b303b303b303b30868086808680868082803710828037103ad03ad03ad03ad0a580a580c7e0df6098a036a0eaa036a0ead0ead0ea406c40ead02740eae02740c81098d0c810829085c02740eb202740c4f0c4f0be00c4f085908590dd70dd7085908590dd70dd70c620c620c1e0c62084f084f0dce0dce084f084f0dce0dce080208020e980e98080208020e980e98085908590ea80ea8080708590e1d0ea8028f028f028f028f0df40df40dda0df50df4037106c203710a600a600c710df0098203710eaf03710b9008080b900df80a6403710869037108660866086608660826036a0826036a0b9c08030b9c0df30a5b036a0867036a0c7309850c7308270852026b0eac026b057d080b057d0374086103a6027603dd002100210021002102320232023202320c680c680c680c680c680c680c680c6802190219021902190c5a0c5a0c5a0c5a0be40c5a0be40c5a03e103e103e103e103e103e10e9d0e9d035803580ea20ea2035803580ea30ea30a6e0a6e0a1d03d30a6e0a6e0a6e0a6e0a6e00960a6e03290b950b95098e0bca05e802fb03000300098e098b098e098f05d202c705d302a10a1d0a1d0a1d0a1d0a1d02f10a1d03d40c7e0b960c7e0b990c7a02f40c7f03d70ea40b980ea40a1e0e9e02c80eab03d80c8109900c810c8102cb02cb0c82033200080008000800080059005900590dc90059005900590dc90e9c0dc80a560dcd0e9c034b0ea10356015607990a0607a30a4701560c6a025c0c1e0c1e0c1e0c1e0c1e0c1e0c1e0c1e014501450dce0dcf014501450dce0dcf034b09a00a560c20083f034b084a03e4084207a00a560a07084503a90a5703ab0c7905920a5c007a0c7900710c93007a0dd00dcb0dd00df70c7c01980a6f0330057a0597057a0bcf05ec03020c98030c057007a20570099105d602cd05d802a40a5c05a90a5c05aa0a5901950a5d03b00b9c019b0b9c0b9d0a5e019b0b9c03da057a05ac057a05af0849019d0a5f03b2057a07a6057a0b9f084d03a00c840335002100210021002102320232023202320c210c210c210c21 | false => 0x6b701960d4d060906be01c406310a840953019e063108ec0d08099a0f5c0605084601a00d49060c06c001cd02b702b702b702b702b708e402b708e40d5202b202b702b205c907da05c902b80e960e96093b0bb3062d0cac0bb70bb70f7b03980e9603980f770c3d02be01140b730b730a9a0a9a0b740b740b740b740ccd02b30a3e01420b740c1302b903bc0b0a0a90093a093a0b0a0b0a0b0b070f0f1d0502071303a20b0a056902dd02de0ba30a890ba30a890ae809260a8009260cc009d60262000c0f1706ee04d1010d0ba70ba70ba70ba70ae80ae90ae807080ba702660c4c04080ae8027f056002800141062206230623063107290c9c0729014105ba05c702b4055c06f1055c00e1062d0ca1073007300631073407390b7805640564071703990c570c180c5802e6097809780db30db3014208eb0ef2080c0d47014205e201420d48014206990142083108310b560b56034d04f80f380de30f1e0529083103e2052a0534083b039f097a0cd70a7a0a7a01e707d701e701e70d51050b0a7a01e70f7607d701e701e709790979097909790cda0cdb0ee70e05097906860979000c0cda030a05ee030a097a097a097a097a062d094c0a7c021f0682068205e202180f5607ec05e40220093409340935080f062d0cde08ef097d0d54068c05ed023f0d5a068f05f30249014105a6058d05a60142090f0ec10dc40cce050a0517013a0cc40c150519013d000c0ecc09330ddf06310aea0b0c02df0cc8050c0c5000060cc905c205db02e20141062006d10141014209120d0701420ab104d8069601420d4e054e06bf0142063106210a4205a806310ee10dc60bdc0ab305010856039b0ccf0503085803a7000b06d00617000b062d09de061805900aa9064504a2000c0aaa07df04cb00e7000c0cdc0936000c062d0de40ee00bb90d55068e0555000c0cc207e304d2011801410141000b0141063105bd062806780141068306b90366064c014706ba026e062d062705ce067b06310581057e014c069d0685001402c1053c04dc04a60fd5080a08d2080a0860060808600de50b020bd30d390d390cbc0a050b08072f071b070e07620ab00901079f0ab50504084303a90ae40b6f0fce0b2205d407a1063d09ec05d40de80d310aee0cb007000d31072a0a5507020fd4063a05ab05ab0b250a2b08470e160fd40cbf0adc0bd40ccc0c0f0b7203a00b030bd70fd5063b05b205b20b260a3508370e1707600aaf090007910ab404fb083403a40ae30b6b0d2f0aef0caf07010d2f072b0a5007030fcd0b2105cb0793063c09e205cb0de60d370d370cba0a010b07072e0715070d0fd50cbe0adb0bd90cca0c3e0b6e039c052b02310fce06ca076306740f2104f9085d035709e5029e0a2f03b506df06d606d4067e06e0036f06bb02700a2803ae0fd40d320579))) | false => (match Nat.blt i 9 with | true => (match Nat.blt i 7 with | true => 0xe000ecb0a78022e03fe09f3056b02e002e7097b073c0af10eea08e5074008df08e00cea09e10bef0e3808e509e307b10e390742074d0bb50e6c074007440ded05890cb10e2706e8045b0ac2057506e904fe0cd90cdd0af1097c08e608e700e3054b064608900080008807dd0e4400e500f10cab0ad7070607070de4058101170506023607280237045c06fa04fa01190bba0a7104470a5304000c2e0a850a9607120a080a0809930d0c0db403b10d09099f09930a2a01c503b10be809fe02de09ce02800a0b097e0d690cf8097e02970a8a0a9b070c0a0b0d1703ed09db0a3f02970c4809e6029f0a140a140a880cf209b509750d780d1804020a9d0710097502400a5a04020c28099b0d0b0a93099b0a1f09fb09fb0a830d0409990db8039b06ff0169039b09c409c409a80cdf0d9a00e70cd90a7b097b09a80a810984002c06ec00e70feb0fe30fe206d70fe0036706dc03670fdd021b019a05ad06e10606019a036c0fe106d902ba02ba014105bd05ce026c06dd021b05e502f70141034f008c0b480e870c4009500c400dfb0c1f0c1f09540e520b4e0de7092b090e07110fe10d5d0dbd0ce00dbe0d0d0ef10e150d5e0cc50d0a09a30d020a2b0dc204030ad60f5003980b040bd80ea609fe0a4c02de02a70bde0c3902800a0b097e02b40ae2097e02970fe10d3b07820d340f280ca50b14070c0f1f0d460cbb0a020b070c080c54043f08b0082008b105320533082f039f0e010a170a3003b70679067904ed068102180fe10d2109450aa00d5308d008ee08100d5c06cb062504f20d59068d05ed02400acb0b11022f0f520c280695066b04f6069503470fdc0d5b0d3e0d44094606260903060e0d2e06ce08d106c30ab205010855039b09c409c409a80af7000300e70fdc0f0c0f220af307810cab0ae10bb60d3c0d420c9f0b8d0d350a3406e701b10fe106d906e506d806e6026706d2026706dd021b007e067d06e2064b007e03680fe10fd60637067a062d058105ce02bf0fcd0540056e0225069d035100140e180f5b03e5020f02640264026402640e4209270e420bda0d4c0264026102610f780e4200dd00dd026402640902090206310bdb0cad0bdb05bb05bb085002650f7e026a0c8503a509980998097a0998094a094b094a094b01410141000b01410f550c3f0f550c3f09510951095209520db50d7a0db60e1a0f5a0f5a0c7b0c7b0f7c0c410c80012a09980a820d030a8209970997099709970d4b0a82051803e30997099706bc014203e303e3084e03e30d050ee90d060e190f7d03e3084e03e30d05060a0377037709960d6e09960d6e07f00b3207f00b320d570604000c000c0f1807f0051f01fd000c0eef08ed080e008b0f2f04bd0dc50d58064a000c000c052007f60528012c0998099809980998091009110910080d06b70604 | false => (match Nat.blt i 8 with | true => 0x2d704070e430e6702d9049102fc0b5c0b490b4a0fa80f970b4c0f970d880b5d0d880b5d0da00fa80b4c089d0a2e0b5c02fc086a0e020f980e020e890a2e089502fc04870e4f0e850123047e0f9d0f920f9b0e580f9d0f9d0dfc0f9e0fb40b6303530e580d930f9d0e3c0e770fa70dba013b0e880b530f920dfc0e8d0fa70b63039e04890b53089e00af041400740fb50b270b290b310fb90b280fb909d70e3300740e330b310fba07ce0e3e0742074d0b4b0b4d074007440b2a0fa00ef70b5f0e340e710efd0fbc07d004150d6d0d790d6d0b290b330fb50b3307ac09d70e840074045f07e60e51012101fe0ef00f040e03086b0b350fc70ddc04800a3108990301048b07ee03f3012d04620c350a750c350d0e0c240c450ecd0daf0c350b1d0c350b1a0c240b1f0ecd0b1f0c240d120277043308fc0db1027804100c240b1d0277043308fc0c45027804110bee0bb00bee0bb00bee074d0bee0ed90bb009080bb009080ed40bf10ed40bf10a750a750ca20d100744074d0ece0d110ca70b1e0ca70b1e0ed50eed0ece0a760bee0edb0bee0edb08e30bb408e30bb40456045704560457010b0472010b04720ad40d130baf06c60deb0a180deb08250c340c36040504090e480e64027a040d0c000ba40c000ed709800c140cd10d660ba40905043004310cfb0da50279046409ef0a770ace0d0f09ef08fd0cd208fd0ca60b1b0c230c250cfd0906068008800c000ba40c000ed70afc0afe0ae50afe0ba40905043004310afc0c14027904650ca00d140ba206c50ae608fe0ba508240ca00b1b02d503fa0ae603fc02dd03fd0980074c0ca30ed8098007400cd30cd50abe0e690bed0e690cfc09c8066508810744074c0cb60cb7074407440ca90ad00cb20c2a0c2607250cb30e4c027d07260ca40edc0ca40ed80afd0eeb0afd09810bff0e7b00d804340c020e4a00e000e90cb80cb90ba6043b0bac0e7f070a070b0c37072702da043c06f90440027e02860e6b0c350c4208f80dae074407440c290f9f0c350b1c08f80c420ed60b200c290c430dec0e7e0eca0db2022703ee0c3c0fa9037d0e8e0eca0b1c022703ef0c3c0c46037d03f2097b0bf80af00af20b7f074d0ae00af50ce90d890af00bf80d8b0fbb0ae00bf909ab09090adf08fa0742074d0ee308fb0ceb090a0adf040a0cee090b09af056d0cd60d700ade0af20d6f0f990b7f0b81022904760229047801f50e8601f7047d0cd809090bb108220a320a360e070e080687088f0305040b07e00e650309040e0c00074c08dd0bab0b76074c0d650f930ecf0c060001044d0da60fb601bc0e780742074c0dde0a12074407440a250a130ed00eec0e210e5b0cff090707b30e5c0c000ede08dd0bab0ae70b000b760b770ecf0c060001044d0ae70c1601be04690ecb0d150dde08230ee508ff0dff | false => 0xaf7000300e70fdf0f49074f0af30f4507420ae10bb50fdf0238063205b90d350c2c06e701b109d902930647061a0596064804ba00110fdc0d3306370704000c0bae059102bf0fd5023a057d0245000e039d00140df10eb003dc03b402ff03b40f5d0e5f0f510e570dcc0ea0029007510f640f6c0b060f6a0ad10e350f7a0c2f007902900f660f6f0e040add0bec0b190bce048a0c9703ba0387093c060f093f0610036e03c303cc03c5031a03c5092e05c607520f250f2a0588073b0930035d0b1003ca09380318026305f8032207380b1703a3093e032103f90c7103c902db03f9032003cb0de20eb603c0039207510f24092c073a092d0f29058605b70b0e03b7042003d60216032d042007370b16093102fe0c8a03b60940030705ea0308030603b80e2407520f630f690acf0f6b0b01022f0f790c2b0e10049c0f650f6e00050b150bad0ada0be3022f0c5603ce07500736091d0f270920091407320bc000760aec0292074f07350752063907310bb5063305890f260917063205870ae102390c8e045d0f230af8058f057f02930595093900810086008202940f220af306370bc50936000d0580011d057b023a057d00aa000e023b02f90c9b0e0908f1081208f008110b2f0b420f4809620fd80f860fe40f00052807d00b4507a90fd90f850c990ddd0c7d0dfa052207ee04d6010001e409370bb203980f570c3b0a6303cc03c502dc02de075906660f48074307800ca80c270f1b0cfe0d3602800c1204c800dc07330aff072d07090c380c6e03f8055f0c07056102810a69039f01e701e70f480d1a09470ee20d600a97063f05b801e7052701f60cda0d720ee80e06030403070f580a3305f0030b013c013c0f450d190cd40d670f530c280d5f0a950f540a26013a013c052101bd09320ba809480ee40ee60dfe0a4d039b063e05c205dc02e10f4808e50943091f07550bf6075a07dc0f1309c60f45074107310af40f48074006300bb80f0d0ced05550bf20fd00575053a01b609440929057200e3064704b900780f1909df04cc00e807810caa072c0705062d0bae057301170d38023a0557023c0535019204d30fb704040fb70dad0fa80f970f9c0db90f9a0b5b0fb70dad0fb80b5e0f9c0b5e0ad30a160a150a160fa60e6201e50e8c0a2d040404040404037b0e6203be04900fa503f40acd0a0f02d40b500a220b500fa50b600a2003f40da40b610a22088a0fb20db00a0d0a0f0b4f0b5102d4086c0fa50db002d403f40da40b5102d4048f0f950fb50f950f9100d70fb90d640d750abd0fb309c2047009c30e4109c30e760744074c0ad20f01074407440eee0f020abf0b6204060e590efc0b640a24088d0f900f960f950f910b300b340d640b3409d5044b00d7049a00d70e4100d704820ad50f0300da0a110b520b540dfd086d03f70e63)) | false => (match Nat.blt i 11 with | true => (match Nat.blt i 10 with | true => 0x4b3066104b400450fe8076d0d22091e0fe50764075308e10fe7076c0fd307d5075a08e50aa509c70d2609160aa109ae0fd207ff053901030d2a092804c906690d2709190aa209b80fd107f7053b00ee061902ba0aaa09e004ca00e404a9065304aa00290538004c04c700f5042d077007700ab90aba0e2f00f808cc0d9509bb04850e2b00df08ce0d9709be048300d604260e45005b010907f8089c020b04860efe0efe0d7e0efe00f60da100f6087b01200dab01200884011f042100f60129012001290efa0efa00ad0d8600540d9400ad00b40daa0efa00ad088e00ac040f005203ff0054089b00ad00b40773077308ac0bfd0768076808ba0d810773077308bb0ce807e50e5007cd0e3d08bf0da307c5087d07fb09f907bd09d408af0bf508af06150ac30ac409cb046008cf0d01066801330072040107e50e50020601fc09e804480197044907fd09fa0127013400bc0413076c076c08ad0bfe08ae0bf308ad061607d20e4007d20e40010a04190094040907d80e4b020e01ee0efb0efb00bd0d840da70efb00bd088b003c0d9600bd00c6003a03fa003c089a00bd00c60eff0eff0d830eff0769076908bc0d7d076c076c08bd0ce7010c0da8010c08820ac00ac109c5045908cd0d000643011b00db0d9b00db087608c20d9d07c8087807f209f407c309d1010c0112010c011209dc043d01a9043e07f409f500c300d0076c076c08b70d870e3b00c00ac90aca09d2046d0e28012508c60dac07d108850e4d002300d5001903f109f6045401d20455077107710ab70ab80ef90ef900980d7f0770077008b80ce608ca0d8e09ac04740d9f0ef90098088808cb0cfa066a010408c80d9209b6047b001d0d91009800a107e909ed07b809cd07d6089801e6047c001d0896009800a107eb09ee00fb0105076a076a08b50d850767076707ba0e310767076707d309c008c40da907cc088c08a80c1a07ba0e3108c50cf607cf09bd0ac60ac709cf046708aa0c1707c00e2d08c70cf507d409c1000003ec09f0044f01bb046808a80613017e0187065a004d005f006c0ef80ef800760d7b076e076e08b60ce40765076507c909b9076c076c07d5057800030d8d0076008707dc09e307b209c908c00cef07c709b007ff057700cf04ec0d9a0ef80076088608c90cf9066900ef08c30cf407cb09ba07f70576013204eb000308910076008707df09e400e400f00653003400290035006a04ea0d8c0de70d710e150edf0301068a007b03a004180a8c0b120bd80a8b0a9c03fb038a0bde0c3903ca0afb0a7d0b6d0c030c4d03210bd60cae0bdf0b6a0c3a0c4e043f0a4503520a170a170a3003b70216001c0979022c0b0d040c062404f50688068905eb02400f620b11022f0f520c28099d013a0f610f4e00050b090baa0ad909ff022f0a4e039b09c409c409a8 | false => 0x44c0a74044c000901890f6d0f4b077a0ce20777073d0ef80e360f4a0639073c091c0e6c0cec09130e720e2606eb02990fe30fd70636067f063406cf058206060640036c0fd602ba054206d00581058e02c40684059402f80649034f007f0fc90b820a7f0442005800580d20094d0d9e0f750b710dc10dc10d7707ab0ec50b700cc30c0d0c5c01270d7607aa003f003f0d1f094e0dc30dc30d990f740b6d0a7e04360ec70b6c0cc10c050c5201110ec3045109ca09ca09e6029f0cf10f1409770c9d0b7e061b03040aab09e704bf009f0f080b2c0b670b3a07870f1107870b680b3f07840f0f07840ec2044c08a50786003e051d004509c409c40fe507780f4608e10fe50765075307c90cea0f12097b0fde0916062f09ad0fd0002c0642002c09d902930fdd0919062e09b70fcf001106410011061902f50aa909da04bb00840fce065305700029053600330036009c007d0f590e9102580097046c04210e81032f0442015e079d005104000778077809590dc00d1e095e0bf40d8000730e6f08be0da20d6b0d6c01600fb007b9087c0f600f68090d0b9a0abc0cb50aed0460040100730e82019304610f4d0f710dca0b9b0c0c0c0e0161044900950e730419040900950e7d01a7045a0176078f003903fb07770777095a0dbf0d1d095d0bf00d7c0f5f0f67090c0b8e0abb0cb40aeb045908c10d9c0d680d6a01780fb107bf08770e7c031f04360f4c0f700dd40b8f0c040c090179043e014f06c80612014f045109b2077809b20d1c09b20ef90e290ce50d8a0e7009b20dbc09b205a1064f095809a908890d900e7409b20cf309180afa075709eb06ed0e3a08930228040c09b20b24059e05a206500897009900a2077807780b2e0fab0f070fcc0b2e0fad0b650fda0b3b0b3c08a904e707bb0e320b660fdb0b400b4108ab04e307c10e2e013906c706110139044c0f0a07a4078c07a5051405120169018909a8077709a80d1b09a80ef80e200ce30778077808e1073e0764076508e109b909a80cec09140af9075509e106ea0e370d41063509ad05830756057507c6024c09a80dbb09a805980644095609b308870d43063409b705820758057407ca022609a80b230593059906450892007700890653054100290507065404e0002b0ec90b82061f0343061c02ea0fea07720d2509220f150b44075d08ea0aa809d30d2d092504d406680f1c0b4708a607a70ebd0b970aae09f804d501270f160b430f1a0b4608a707a8061d02dc0fe7076b0d2409230d2c092404c40667075c08e90aa709d0061e033b0ebe0b890aad09f204c501110ebf0b840fe9076f0d2309210d2b092a04ce066a075b08e80aa609cc0ec80b7e061b02ca0aac09ea04cf00fb0fe60766075408e20f100b3a0d29091a0aa309bc0f0e0b3f0d28091b0aa409bf0ec00b7508a5079a) | false => (match Nat.blt i 12 with | true => 0x17d04b8042908a108a30424042b046e024e042c04950441033e042a0970096a0fc30f39096808da086f0f33081708190fa30f40049b0e92044407bc042e0f44088308a40870046303970498079e03410499015f04450342042f086e049f04920872046a038f0493096f0969096708d90fc40f3a0f32081408160fa40f3f0f43087f08a20e90043807c2042704320336042507900339049401770439033a042809720fa209660f420fc20e61041e0f310789032b04a0096c0f3e08a008d4087a087e089f0f3c045207b70423048c03c2041f081d087301500453032c04a109710fa1096e096d09700fac0960074e0fc00e6009630f87074a0f340f2b058c09650f4109640f88074b0f350f2c058b0f300785031d049d08b40dd9058a078a00640508096b0f3d0fab096107460e3108b905780f3b044d07af041b0f370f2d0587018807be04ff08d3087508790f360f2e0585016c07c40500081a0871013a044e031e049e0796002f0509017c018a00660faf0ba10f8f0c1c04880df900ae0c1d0ce10d1603fb0a9403c60ba00a8f031b0cbd0ad809940cc60bd50a0c0a450352035503550b58082a0a4603f00d4a0355081f077c0c28022f09490c28099d013a077e094f00050baa0baa0775039b022f0184039b0b2d07c007420ba902380e2309a50e270e230182013f013f0d45099e07b6013f01bf0de10de1000c0de40a42039a0230034b015600070230034b03f602d603dc04960e56035c0f5e0e5d02ac0f4f03a10e1f0e14048a0eba032e060f03e8037a03e8082b0813082c05c6092f0a210a23044a033803380a0e093d0a1009fd0eb40e0f0a4b03f50eb503c60e540e1c0e5508f9035503b7041d0b5708210904030705ea0355086503cf0e0a095f077f077d0776077c074908000db70a730dc70e0b077e0d630783074709920775099c080109fc00d308de0b5507b0075206380dde063005890915063205840e220c75045d013f0293059508f5081c013f0082032406370b9209330de0057e011d0a00057d01b70a4f023002c50b710d7707ab0c78045e0194007b0a3803ca0cf70d4f0b6d0c4904360c9e0b6c097f0a3f0a3003b70cf009770c9d0b7a0c8f04790d560b7b0a5a0b830d73013a0c60044c078c000909c409c409a809840ef800e7097b0ae1097b09a80aec0984002c06ec00e709d9029309b4007e09b700860082001102ba02ba000b09de05910084023a059a0010000e0086008c04810d61044204880b590e5e045e045e0d3f0f060a7208dc045e0e83007b01fe046f041904090458045a0d620466095b095509410e6a08d508d60d98051608740edd00d904360f730b850b8a043500d903ed0451095c094209570e7008d70f720eda0d8f047708d80b7c0b80001b0479050e0894001b04020b5a0e5a0f050e6e0d3d044c08db | false => 0xc100c4a0c600c000fcb0f940391041d07480a0a03d50a6d07460a3703890a19031c041d0a1c032a03c70a6a02320ac80ac50f820b8403910f800b7e03550de9037c03750f840b750def0ab60e3f03890e4701d30e4d01f803480dea0151041c046b0fbe0fae0e7503900fc60e8b0e800f8b0fc50e8a041203880fbd0e7904160e7a0f810a3d0c440a270f7f0a3b03f00a2c0de904460fbf0a390fc10a3a0f830a3c0e8f0c470def04840faa09c00a130e6809e301d3027c0bdd0e6d09ed01f802ad03eb0a360dea043a0354015102340c780b8609e6029f097709b50a620b7e0c8f047909760b7b0a5a098c0bfb097b097b09aa0bbb09840bf801e80a2903af09b40bc7098c0bfc01f80c860471097a0b7f0a62023a0c8600260a8e0a9f04220a990b0502100c2e0a920393048d0bea0b180bc90c920b130a8d048e0be80a980a91038b02070c320a9e041a0b0f0bbe0c880c310be90270029f0be70bfa0af60b79061407480beb0c90047a0a790b7b0c94047f0c2d07460c330bf70af00b7d05b60a860bbc0bc00bf801ea01ef036703af0a870bc80bcb0bfc01f901ff0c8704730a7a0b7f0c8a0475023a05f1030d002600a40f8c0ba00b690fca0c28013a013a0c60044c078c0009000207c00c00031c00020140013f013f09b1099e079c013f01bf0008000801410c010c610230000805170a70034002ac09950e1e04970eb80d8203c6044a0d50033805f7053008f4033905fe041703910acc0a09002109740fa10dee0f880e530747031d0e1b000903db029107450c3008dd031c031c0bc00140031c00480d4002930d7400800bd0013f0082032400080008058d05a7057e031e0230000804500517000a0fc8005800580ed30340016401640f8e0ec404430ccb0c190c590f8d003f003f017f017f0ed203380ec604370cc70c110c4b0ec30451015201520ed1032a0fcb002100210cd00c0b0c6707790b2c077c0b38078707bb07bb077b0b3d078407c107c10ec2044c0774079a003e051d004507780b2e076707b40ecf031c078d07ae078d0511017b0182013f013f079c07b6079c051501630167000800080cce0c010c610020051b0029053f004c0170025703dc0601033f08f308180ef6005306020e30015d069401ba0ebb03bd0c5d0e12051c015d0603034201d10ebc03bf08f208150ef501750693003b05ff0e2c05fd03370c530e0e051e01750600033a0c690e0d0ef4014e0692001a05fb0e2a022b03d908f7081e051a014e05fc032c0973096d0b2b0f47073f077c0f8a0b3600470bd2077b0f890b3700630bd10c630e0c07740dd90788057100cc0ef30b2e0f46073e07ba0fd30578000105f90e250b39002e0bc407ad00480048013806910b3e00130bd007b50065006508f6081b0517013805fa031e078e057000a60056))))
def routeRef (i : ℕ) := Nat.land (Nat.shiftRight (routeRefBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def routeRankBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0x19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fc19fc19fc19fb19fa19fa19fa19fa19fa19fa19fa19fa19fa19fa19fa19fa19fa19fa19f919f919f819f819f819f819f819f819f819f819f819f819f819f819f819f819f219f219e719e719e719e719e719e719e719e719e619e619e619e619e519e319de19d919cf19cf19cf19cf19cf19cf19ce19cd19c619c619c319c219bd19bb19b319a91996199619961996199619961996199619951995199519951994199419891989197119711971197119711971196e196e19631963195f195f195519551944194419241924192419241924192419241924192319231923192319211921192019191904190419041904190319031903190318fd18fd18fd18fd18f318f318ed18e418c718c718c718c718c618c618c618c418ba18ba18b918b718ae18ac18a2188f1870187018701870186e186e186c186a185b185b18581856184818461838182217fe17fe17fd17fd17f617f617f217e817d317d217cc17c317b017a51791176f17481748174817481748174817481748174117411740173d173217301727171616f916f916f916f916f616f616f516f416e916e916e516e216d116ce16c216ac168a168a168a168a168a168a168a168a168316831683168316781678166d16661643164316431643164216421640163f16331633162e162c161a1619160715fb15d115d115d115d115cf15cf15cd15cb15bc15bc15ba15b815a915a715981585155915591559155915521552154e154a15231523151b151714f414ef14c814a31464146414641464146214621460145e144614461440143e142a1428141413fc13cb13cb13c913c913b013b0139e138a1358135613421330130012e712b7128512471247124712471247124712471247123e123e123a1237122612241214120311d611d611d611d611d311d311d011ca11b411b411ac11a9118d118a116e1158112311231123112311211121111f111d1107110710ff10fc10e310e110ca10ae107a107a105a103a0ffa0ffa0fda0fba0f7a0f5a0f1a0eda0e9a0e770e370df70db80db80db80db80db70db70db50db30da30da30da20da00d8f0d8e0d7d0d6d0d3f0d3f0d3f0d3f0d3d0d3d0d390d350d200d200d1b0d170cfd0cf60cdd0cc30c8e0c8e0c8a0c8a0c6a0c6a0c4a0c2a0bea0bea0bca0baa0b6a0b4a0b0a0aca0a8b0a8b0a8b0a8b0a830a830a790a710a4f0a4f0a450a3d0a1b0a1109eb09c9099009800954092c08f008c40888084c080c07e007a40768072806ec06ac066c062e0622060705df05a7057f0547050b04cb04a3046b042f03ef03b30373033302f402e802c802a802740254022001ec01ae018e015a012600e800b40076003800000000000000000000000000000000000000000000000000000000000000000000 | false => 0x19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe19fe)
def routeRank (i : ℕ) := Nat.land (Nat.shiftRight (routeRankBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def routeFlagBlock (i : ℕ) : ℕ := (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x10000000000000000000000000000010100000000000000030000000100153f3f000000000000000000000000000000010000000000000011000100010077077700000000000000010000000505150f3f000000010037373705550777fffffffe0000000000000000000000000000000000000000000000000000000000000011000000000000000000000000000005050000000000000033000000050015ffff000000000000000000000000000005150000000000000033000100150077ffff0000000000000537000005050515ffff000000370037ffff0555fffffffffffe0000000000000000000000000000010e000000000000000000000000ffffffff000000000000000000000000ffffffff00000000ffffffffffffffffffffffff000000000000000000000000ffffffff00000000ffffffffffffffffffffffff00000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000005ff00000000000000ff000500ff00ffffff000000000000000000000000000005ff00000000000000ff000500ff00ffffff00000000000005ff000505ff05ffffff000500ff00ffffff05fffffffffffffe00000033003300ff003333ff33ffffff000033ff33ffffff33ffffffffffffff003333ff33ffffff33ffffffffffffff33ffffffffffffffffffffffffffffff003333ff33ffffff33ffffffffffffff33ffffffffffffffffffffffffffffff33fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0000000f000f000f000000ff00ff0eff000f0fff0fff0fff00ffffffffffffff000f0fff0fff0fff00ffffffffffffff0fffffffffffffffffffffffffffffff000f0fff0fff0fff00ffffffffffffff0fffffffffffffffffffffffffffffff0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000030003033f0003033f033f3fff0003033f033f3fff033f3fff3fffffff0003033f033f3fff033f3fff3fffffff033f3fff3fffffff3fffffffffffffff0003033f033f3fff033f3fff3fffffff033f3fff3fffffff3fffffffffffffff033f3fff3fffffff3fffffffffffffff3ffffffffffffffffffafffafffafffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => 0x3000000000000000000000000000000030000000000000003000500070005053f000000000000000000000000000000050000000000000003000500050007033f0000000000000003000500050007033f000500370037033705ff07ff05ff3ffe000000000000000000000000000000000000000000000000000000010001005700000000000000000000000000000107000000000000003300ff03ff00ff1fff0000000000000000000000000003011f000000000000003300ff00ff00ff07ff000000000000003700ff05ff05ff07ff00ff00ff00ff37fffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000030000000000000003000f030f000f0f3f0000000000000000000000000003000f0000000000000003000f000f000f033f0000000000000003000f000f000f033f000f003f003f033f0fff0fff0fff3ffe000000000000000000000000000000030000000000000000000f003f003f03ef0000000000000000000f000f000f030f000f000f000f033f0fff0fff0fff3fff0000000000000003000f000f000f033f000f000f000f003f0fff0fff0fff0fff000f030f030f0e3f0fff0fff0fff0fff0fff0fff0fff3ffffffffffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000537000000000000000000000000000001150000000000000013000100150007077f00000000000000030000050500050f3f00000037001137370555ffff0577fffe00000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000010300000003000011120001333700113737000000000000000000000000000103370000000000000013001133370037377f00000000000001030001373701173f3f00013337001137373777ffff3777fffe000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000003000000000000000300050f0f00050f3f0000000000000000000000000001031f000000000000001300050f1f00070f7f000000000000000300050f0f00070f3f00050f3f00173f3f0f5fffff0f7ffffe00000000000000000000ffff0000ffff0000ffff0000ffffffffffffffffffff00000000000000000000ffff0000ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffff0001ffff0104fffffffffffffffffffffffffffffffffffffffffffffffffffe) | false => (match Nat.blt i 3 with | true => 0x2000000000000000000000000000000000000000000000000000000010001051200000000000000000000000000000000000000000000000000010001000703320000000000000000000000010001031200010001001103130111071705773f7a0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000003000000050005043e000000000000000000000000000000040000000000000003000000050005003e0000000000000003000000050005023e00050037003703370055057705773e7e0000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000030000000000000003000100070005073f000000000000000000000000000000070000000000000003000100050007033f0000000000000003000100050007033f00370037003703370177077705773f7e0000000000000000000000000000000100000000000000000000000100010117000000000000000000000000000001070011001100110113001101170015177f000000000000000100000000000101170011001100110013001100150017077f0011001100110117001101150117073f11771177117717771177177715773f7e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000516000000000000000000000000000000040000000000000013000000050004057e0000000000000003000000050000033e00000037001137370011057705763f7e00000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000100000000000000010000000700011517000000000000000000000000000001150000000000000013000100150007077f0000000000000103000001050001033f00013337001137370111377705773f7e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000053600000000000000000000000000000000000000000000000000010001000703360000000000000000000000050005033e00000001001103120555077705773f7e0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000001010000000000000001000001010011153700000000000000000000000000010115000000000000001100110011005707770000000000000001000005050515073f00000011001117175555577755777f7e | false => (match Nat.blt i 4 with | true => 0x400200000000000000000000000000000000000000000000002000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100010312000000000000000000110112011212200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000400000000000000000003000000000001030600000001000103020011010600060608000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000105000105040000000000000000000000000001000500000000000000010000000100050104000000000000000300000001000103170000001100110317001101170117174c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000200000000000000000000000050005033e00000000000000000011057605763e680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001030000000000000000000101030011113200000000000000000000000000010111000000000000000000010011000303320000000000000000000101050117033f00000000000000000111177705773f7a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000400200000000000000000000000000000020000000001001103120011051405763e68 | false => 0x0)))
def routeFlag (i : ℕ) := Nat.land (Nat.shiftRight (routeFlagBlock (Nat.shiftRight i 7)) (Nat.shiftLeft (Nat.land i 127) 6)) 18446744073709551615
def smallCodeBlock (i : ℕ) : ℕ := 0x3f003e803e403e203e103d803d403d203d103cc03ca03c903c603c503c303b803b403b203b103ac03aa03a903a603a503a3039c039a0399039603950393038e038d038b03870378037403720371036c036a0369036603650363035c035a0359035603550353034e034d034b0347033c033a0339033603350333032e032d032b0327031e031d031b0317030f02f802f402f202f102ec02ea02e902e602e502e302dc02da02d902d602d502d302ce02cd02cb02c702bc02ba02b902b602b502b302ae02ad02ab02a7029e029d029b0297028f027c027a0279027602750273026e026d026b0267025e025d025b0257024f023e023d023b0237022f021f01f801f401f201f101ec01ea01e901e601e501e301dc01da01d901d601d501d301ce01cd01cb01c701bc01ba01b901b601b501b301ae01ad01ab01a7019e019d019b0197018f017c017a0179017601750173016e016d016b0167015e015d015b0157014f013e013d013b0137012f011f00fc00fa00f900f600f500f300ee00ed00eb00e700de00dd00db00d700cf00be00bd00bb00b700af009f007e007d007b0077006f005f003f0000
def smallCode (i : ℕ) := Nat.land (Nat.shiftRight (smallCodeBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def largeCodeBlock (i : ℕ) : ℕ := (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x79b00000797000007900000078600000783000007810000077a00000777000007730000076300000759000007510000074e0000074d0000074a000007480000074700000745000007410000073c00000738000007310000072b000007290000072800000727000007260000072400000723000007220000071f0000071e000007180000071400000709000007060000070400000703000006fe000006fd000006fc000006fa000006f7000006f2000006f0000006ef000006ee000006e9000006e6000006e4000006e2000006df000006dd000006d9000006d8000006d7000006d2000006cb000006c8000006c6000006c5000006c3000006bc000006b9000006b5000006b0000006a50000069b000006930000068f000006850000067e0000067a00000678000006730000066c00000667000006640000065d000006560000065400000653000006460000063c0000063400000632000006300000062600000624000006210000061f0000061b00000614000006120000060d000006080000060700000605000005fe000005fb000005f7000005ed000005e8000005e7000005e5000005e1000005de000005dd000005dc000005d5000005d3000005d1000005c7000005c0000005be000005bc000005b8000005b5000005b3000005af000005ae000005ac000005a9000005a8000005a6000005a4000005a3000005a20000059f0000059e0000059c00000598000005970000058e0000058d0000058a000005890000058800000582000005800000057f0000057e0000057d000005760000057500000573000005720000056d0000056b0000056a00000564000005610000055d0000055c0000055b0000055a00000559000005560000054c0000054b0000054900000547000005450000053f0000053d00000539000005380000053600000534000005330000053100000529000005200000051f0000051e0000051700000516000005130000050d0000050b0000050500000502000004fe000004fc000004fa000004f7000004ea000004e8000004e6000004e0000004da000004d9000004d7000004d3000004d2000004ca000004c1000004c0000004bf000004b8000004b5000004b4000004af000004ae000004ac000004a6000004a30000049f0000049c0000049b000004980000048f0000048e0000048d0000048b0000048a000004890000048700000483000004810000047f0000047b0000047800000474000004730000046c0000046b0000046700000465000004620000046100000459000004550000044700000444000004400000043c00000439000004300000042c0000042a000004280000042700000426000004220000041c0000041b000004190000041400000413000004110000040d0000040c000004040000040300000402 | false => 0xc0b00000c0900000c0700000c0600000c0000000bfc00000bf300000bdf00000bde00000bdd00000bdc00000bc600000bbe00000bb900000bb400000baf00000bac00000ba700000ba100000b9d00000b9500000b9400000b8c00000b8000000b7d00000b7c00000b7600000b7000000b6800000b6700000b6300000b5f00000b5c00000b5b00000b5a00000b5500000b5000000b4200000b4100000b3e00000b3800000b3600000b2d00000b2200000b2100000b1d00000b1100000b0800000b0400000b0000000aff00000afd00000afb00000af600000af100000ae300000ae200000adf00000ade00000adb00000ad900000ad700000ace00000ac300000ac200000ac100000ac000000abf00000abe00000ab200000aa900000aa800000aa600000aa400000a9700000a9400000a9300000a9200000a8f00000a8400000a8300000a8200000a7800000a7600000a6300000a6200000a5f00000a5d00000a5100000a4a00000a4900000a3800000a3500000a3400000a3300000a2600000a2500000a2400000a2300000a1900000a1700000a1200000a0400000a0300000a00000009ff000009fe000009f4000009f2000009e6000009e3000009df000009de000009d9000009d8000009d7000009d4000009d0000009cf000009ce000009cc000009c6000009c2000009c1000009bf000009bd000009b9000009b3000009aa000009a9000009a8000009a7000009a6000009a5000009a4000009a20000099500000994000009920000098d0000098700000984000009800000097f0000097a00000979000009750000096f000009670000096300000962000009600000095e0000095a000009540000094b000009470000094600000945000009430000093600000935000009330000092b000009240000091b0000091a00000916000009080000090300000900000008fb000008f5000008ec000008e7000008d7000008d6000008d4000008cc000008cb000008c5000008bc000008bb000008b7000008b4000008a9000008a4000008a10000089c0000089a000008960000088f0000088d0000088800000887000008850000087e0000087800000877000008750000086e0000086b0000086a0000086500000864000008620000085e00000859000008550000085400000852000008510000084e0000084d0000084700000844000008410000083f00000835000008310000082f0000082c0000082a00000821000008170000080f0000080d0000080b0000080500000801000007ff000007fe000007fc000007fa000007f6000007f0000007ef000007e8000007e2000007e0000007d9000007d2000007c5000007c2000007b9000007b8000007b5000007b0000007ad000007ac000007a7000007a6000007a4000007a2000007a00000079d) | false => (match Nat.blt i 3 with | true => 0x1348000013430000133d0000133b00001338000013300000132f0000132d0000131800001312000012fa000012f5000012f4000012ea000012de000012d9000012d0000012bf000012ba000012b1000012ab0000129b00001292000012710000126c00001265000012600000125b00001252000012500000124f0000124d0000124c00001242000012400000123c0000123900001238000012350000123300001225000012240000121f0000121e000012140000121200001200000011ff000011fc000011f3000011ee000011ed000011e2000011dd000011d4000011ce000011c9000011b5000011b3000011b1000011a1000011a00000119f0000119d0000119c000011940000118f0000118e000011830000117e0000117b00001176000011750000116f0000116a00001168000011620000115d000011590000114d00001134000011290000111d00001111000010fa000010ee000010d5000010ca000010c00000109b00001093000010900000108f000010760000106c0000106b0000106700001065000010430000103c00001031000010300000102600001017000010100000100d0000100c0000100900001008000010070000100600000ff100000fe400000fcb00000fc200000fb900000fb800000fad00000f9a00000f7600000f6c00000f6b00000f6300000f5a00000f5900000f4e00000f4c00000f4a00000f4800000f4700000f4600000f4200000f3b00000f3200000f2900000f2500000f2200000f1600000f0400000eff00000efb00000efa00000eef00000ee500000edc00000ea700000ea500000ea400000ea000000e9c00000e9b00000e9000000e8600000e8300000e7e00000e7d00000e6b00000e6a00000e6500000e6100000e5b00000e5500000e4700000e3f00000e3c00000e3900000e3100000e2500000e1000000df500000de800000de000000ddd00000dda00000dd200000dd100000dbb00000db100000da300000d9e00000d9d00000d9c00000d9800000d9700000d9600000d8900000d8700000d8400000d8000000d7e00000d7b00000d7700000d7400000d7300000d7200000d7100000d7000000d6f00000d6e00000d6d00000d6c00000d6b00000d6800000d6700000d6600000d6000000d5c00000d5b00000d5800000d5700000d5400000d5300000d5200000d5000000d4e00000d4c00000d4a00000d3f00000d3d00000d2a00000d2800000d2100000d1f00000d1e00000d1c00000d1400000d0d00000d0c00000d0a00000d0900000d0100000cf700000cf500000cef00000ce300000cd100000ccc00000cbe00000cb200000cab00000ca900000ca100000c9d00000c9a00000c9900000c7200000c6d00000c5f00000c4c00000c4200000c2600000c1d00000c1900000c1800000c1300000c0e | false => 0x246f0000241d000024180000241500002412000024100000240900002407000023f5000023f4000023f3000023ee000023de000023c5000023b10000239f0000239e0000239c0000235c000023520000234000002307000020cd000020ac0000206e0000200f00001ff500001fb000001f8700001f5300001f3200001f2800001ed300001ec900001eac00001e9500001e4000001de200001dd700001dd100001dbf00001dba00001db400001daa00001da300001d9600001d8800001d8300001d7a00001d7600001d7200001d6c00001d6500001d6400001d6300001d6000001d5500001d5000001d4d00001d4b00001d4800001d4700001d4400001d1900001d0d00001ce700001cae00001c9d00001c7000001c5900001c4c00001c4800001c4700001c4600001c4500001c3000001c2300001c1100001bf000001bed00001be800001be600001bc400001bbc00001bb000001baf00001b8c00001b5100001b4a00001b3d00001b3c00001b2d00001b2100001b1100001b0c00001ae900001adf00001aad00001a9900001a8a00001a7400001a7000001a6b00001a5500001a4300001a3600001a2300001a1500001a0d00001a04000019fe000019f9000019e4000019d7000019c4000019b6000019ae000019a80000199f0000199a0000198d0000197800001965000019570000191900001906000018f8000018ba000018a700001899000018840000188200001873000018690000185b000018480000183e0000183a00001823000017fe000017fc000017e9000017e7000017db000017cd000017b20000179d0000178c0000178a000017880000177c0000176f0000176e0000176d0000173e0000172b0000171d0000171a000016df000016cc000016be000016bb000016ad00001698000016800000166d000016650000165f0000165c0000164f000016480000164300001639000016330000162500001621000016100000160e0000160c0000160600001600000015fd000015f0000015e9000015df000015c9000015c8000015b7000015930000158d0000158c0000158a00001585000015750000156900001558000015340000152e0000152d0000152b00001526000015160000150d0000150a000014ff000014fa000014f9000014e9000014d9000014d3000014d2000014cf000014ce000014cc000014c2000014ac000014ab0000149b0000149a000014920000148a000014840000147c0000147b0000147a000014700000146f0000146d000014680000146500001463000014600000144d0000144c0000143b000013ee000013ed000013dc0000138f0000138e0000137d0000137900001377000013710000136c0000136b0000136a000013670000135f0000135e0000135d0000135900001354000013530000135200001349)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0x466b0000454e000043c600004367000043650000431400004308000042ab000042a90000428e00003ff400003a2c00003a2300003a2000003a1f00003a1e00003a06000039a7000039a60000396e0000390f0000367600003674000036730000366c0000366b0000364e000036140000360d0000360c000035ef000035b8000035b5000035ac0000359000003559000035560000354d000035310000352f000034fa000034f1000034ed000034ec0000349b00003498000034740000343c0000342f0000342e000033dd000033d2000033d1000033d0000033cf000033b30000337e0000337200003371000033700000331f00003313000032c0000032b40000329a0000326100003257000032550000323b00003239000032370000320200003200000031ff000031f7000031f5000031f4000031da000031a3000031a00000317b00003144000031410000313b0000313900003137000031360000311e0000311c000030e5000030e2000030bf000030bd000030bb00003068000030660000304400003009000030070000300600002fe500002fd400002fa800002f8700002f8400002f7f00002f6f00002f4900002f2800002f1000002eea00002ec700002ec200002e1100002db200002cd100002cb000002caf00002c8d00002c8c00002c8800002bee00002bed00002bd500002b8e00002b7000002b6f00002b4a00002b3700002b3500002b3100002b3000002b2f00002b1f00002b0b00002b0a00002b0900002b0800002ad800002ad000002ac000002ab300002aac00002aa200002a9c00002a9700002a7100002a5900002a4d00002a4400002a1400002a1300002a12000029ee000029ed000029eb000029e5000029cf000029b7000029b300002995000029940000297300002965000029620000295800002954000029200000291f0000291c000028f6000028f5000028d9000028d8000028d60000289c000028960000287a0000287900002877000028680000285e0000283800002837000028270000281f0000281b0000281a000028180000281300002803000027e6000027e0000027d9000027d8000027c5000027c4000027c0000027bc000027bb000027b9000027b4000027b2000027b0000027a7000027a4000027a3000027a0000027800000277e000027670000275d0000275c0000275700002745000027210000271f00002708000026f8000026e6000026c0000026ab000026a9000026a20000269f0000269e0000269c00002697000026610000264c0000264a000026460000263d000026380000261800002603000025eb000025d9000025d8000025d60000258c000025590000253a0000253700002535000025320000252d0000252600002522000025120000250c0000250b000024ee000024d8000024ce00002471 | false => 0x1798f00017969000179680001793200017930000178d3000178d1000178c4000178aa0001788600017827000177d3000177d2000177cd000177cc000177c9000177c8000177c6000177c5000177b6000177a8000177a7000177a60001778e000177740001776e0001776d000177690001775700017748000177470001772f0001771500017709000176b6000176ac000176ab000176aa0001765700017656000176510001764d0001764b0001764a000176490001762c000175f8000175f7000175f2000175f1000175ee000175ec000175eb000175ea000175d9000175cd000175c8000174500001741d00017411000173be000173b3000173b20001735f0001735300017300000172f9000172f4000172e1000172d0000171dc000171d8000171b70001700100016eea00016ee500016ee100016ede00016edd00016ec000016e8b00016e8600016e8500016e8200016e7f00016e7e00016e6100016d0200016ccb00016cca00016a7700016a7100016a7000016a6b00016a6a00016a5a00016a4a00016a4700016a3200016a1800016a1200016a1100016a0c00016a0b000169fb000169ed000169ec000169eb000169e8000169d3000168950001688e000168700001686f00016856000104ca0001046b0000feda0000fc410000fc3e0000fb240000fb210000fac50000f6b00000f23c0000f1dd0000f0610000eee50000eee20000ed690000ec4c0000ec4a0000ec490000ebed0000ebea0000eb8e0000ea120000e9b30000e9540000e8f50000e5fd0000e5fb0000e4220000e3640000e3620000e3050000d7820000c4f10000c4950000c4920000c4810000c4340000c4330000c3d50000c3d40000c3c20000c1f90000c19a0000c18b0000c1890000c1880000c13b0000c0dc0000c0ca0000c0210000bfc20000bfc00000bfbf0000bfb00000bfae0000bfad0000bf610000bf600000bf510000bf4f0000bd880000bd290000bd140000bcc80000bc690000b9730000b6d80000b6d70000b6c80000b6c60000b6790000b6780000b6690000b6670000b08d0000933c000092dd00008f8600008f2700008ec800008e6900008e0a00008dab00008c8e00008b1200008ab300008a54000089f50000787a00007863000073ef00006f7d00006e3e000067710000670a000066b3000066ab000066940000664b000066340000652e0000651500006479000064710000641a0000641200006411000063f8000063530000633c000062bd000062800000625e00006221000061ff000061be000061a1000061a00000602500005e6b00005e6a00005e4900005e2200005e0c00005dea00005dac00005d8c00005d8b00005d4a00005d2d00005d2c000059580000571e00005660000055430000484400004838000047e4000047c00000471d000046ca) | false => (match Nat.blt i 7 with | true => 0x599b40005996e0005995900059955000599380005990f000598fb000598fa000598f6000598d9000598b00005989b00059897000598510005983d0005983c0005983800059819000596fc000596bc0005969f0005969d00059559000595450005954000049d7800048ea0000444c70004446800044462000444610004404d0004404c00043fee00043fed00043e7100043bdf00043b8000043b790004370600043705000432f100043292000392a300039244000390c8000390b90003806500037ee90003106400030b9100030b32000308990002fe350002fdd60002f1760002f1170002edad0002ec900002eac90002e3ca0002e1e10002e12f0002e0e40002e0d60002e0d10002e0d00002e0ae0002e06c0002e0250002e0110002e00d0002dff30002dfc60002dfc30002dfc20002dfb60002dfa60002df970002df670002df640002df630002df570002df470002df380002df090002df080002df050002df040002def70002def60002def20002dee80002ded90002ded80002deaa0002dea90002dea60002dea50002de980002de970002de930002de890002de7a0002de790002de750002de740002de2a0002ddcb0002dd6c0002dd0d0002dcbb0002dc110002dc030002dbff0002dbfe0002dbfd0002dbf10002dbe00002dbde0002dbdd0002dbdb0002dbb10002dbad0002db9d0002db7f0002db7e0002dac00002da310002d7840002d7270002d7250002d5be0002d5bd0002d58c0002d2c60002d1ad0002d1a80002d19b0002d19a0002d1960002d17c0002d14e0002d1490002d13c0002d13b0002d1370002d11d0002d11a0002d0db0002d07c0002d01d0002cfbe0002cf9f0002cf9e0002cf720002cf6f0002cf6e0002cf5f0002cf520002cf430002cf130002cf100002cf0f0002cf030002cf000002cef30002cee40002ceb40002ceb10002ceb00002cea40002cea10002ce940002ce850002ce800002ce7f0002ce550002ce520002ce510002ce3f0002ce350002ce260002ce250002ce230002ce220002ce210002ce200002cd840002cd340002ccd50002ccaa000229f2000228d500022876000228170002210a000220ab000214cd000213510001fb910001f8990001f77c0001f71d0001f5a10001f4840001f2a90001f1eb0001f0100001efb10001ee350001cf670001cf080001c7fb0001c79c0001c6200001c1ac0001ac250001a45a0001a4510001a27400019f7c000199970001998e0001992d000198ce000197b100019752000196f30001969600019694000195230001951a0001904800018fe900018f8c00018d5000018d3a00018cdb000181ac0001808f00017f9000017cfa00017ca500017c9b00017c9900017c9800017c3e00017c3c00017be100017bdd00017bbc000179f0000179ee000179c700017991 | false => 0xb2ede000b2ed1000b2ece000b2ecc000b2ec9000b2ebe000b2eb2000b2eae000b2e7f000b2e7b000b2e72000b2e6f000b2e6d000b2e6a000b2e5f000b2e5a000b2e1d000b2e1c000b2e13000b2e11000b2e10000b2e0e000b2e0b000b2e00000b2dfc000b2df8000b2df7000b2df4000b2dc5000b2dbe000b2db4000b2db2000b2db1000b2daf000b2dae000b2dac000b2da1000b2d9f000b2d9d000b2d98000b2d93000b2d91000b2d62000b2d52000b2d4d000b2d39000b2d32000b2cff000b2cf3000b2cdb000b2cda000b2cd3000b2c94000b2c92000b2c8f000b2c74000b2c35000b2c33000b2c15000b2be3000b2bd6000b2bc4000b2bc1000b2bbd000b2bb8000b2b84000b2b77000b2b65000b2b62000b2b5e000b2b59000b2b18000b2b06000b2b03000b2b02000b2aff000b2aba000b2ab9000b2ab6000b2aab000b2aa7000b2aa4000b2aa3000b2a64000b2a41000b29e2000b2929000b28c5000b2866000b2776000b276d000b276c000b2768000b2766000b2764000b2761000b275e000b2750000b274f000b274d000b274c000b2749000b2747000b2717000b2714000b2710000b2709000b2707000b2705000b2702000b26ff000b26f1000b26f0000b26ef000b26ee000b26ea000b26e8000b26b1000b2692000b2690000b268f000b268b000b2633000b2630000b26270009d91e0009d1530009d03600098cad00097f510009742f00096e9e00096e3f00096a8900096a2a0009696c0009690d0008d3800008c91c0008bc7e0008bb020008bb010008baa30008ba440008ba430008b9e50008b9e40008b9860008b9850008b9270008b8c80008b8690008b80a0008b8090008b74c0008b74b0008753a00087536000874db000874d7000870c600087067000861ea0008618b0008612c000860cd000860bd00085fb400085fa000085f5500085f4100085e9300085e340007f1810007f0640007e4250007e18c00077a62000777c90007764d000772f60007729700076f4000076acc000763bf00075eec00075e8d00075dcf00075dce00075bf400075bf300075663000755460007548800075429000752ad000712d1000711b40007109e000709e9000708cc00070575000702dc0006fd520006fd4b0006fb110006f99500065dbd00065534000654d50006529b000650c000064dc800064d6900064a710005ba750005ba610005b8f90005b8e50005acba0005aca50005aca10005ac5b0005ac460005ac420005ac250005abfc0005abe70005abe40005abe30005abc60005ab9d0005ab890005ab880005ab850005ab840005ab650005a88c0005a86f0005a4180005a35b0005a2ff0005a2a00005a29c0005a07b0005a0670005a0660005a06300059ea000059e8c00059e8b00059e8700059b9300059b3400059ad200059a73))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0xc9f05000c9eff000c9efe000c9ed8000c9ccb000c9cc5000c9cbf000c9c9e000c9c03000c9ba4000c9ba2000c9b81000c9b45000c9ae6000c99c9000c98ac000c9857000c9851000c984b000c961d000c9611000c931e000c92bf000c9260000c9208000c9202000c9201000c91fe000c91db000c91a2000c90e4000c8f10000c8f0a000c8f04000c8ee3000c8beb000c8a6f000c04a4000c0445000bff60000bff5d000bfc09000bfc06000bfbbc000bfb5d000bf450000bf3ef000be634000be102000be0f2000be0a3000be093000be044000be034000bdfe5000bdfd5000bdf86000bdf76000bdf27000bdf17000bdec8000bdeb8000bdeb5000bde69000bde59000bde56000bde0a000bddfa000bddab000bdd9b000bdd4e000bdd4c000bdd3c000bdced000bdcdd000bd998000b9b41000b8912000b6d91000b6508000b5aa3000b5a44000b59e5000b5986000b586a000b5869000b580b000b580a000b562f000b55d0000b5396000b527b000b525c000b521c000b51fd000b519e000b513f000b50fc000b4ec2000b4e01000b4dfc000b4d9d000b4d48000b4d43000b4d40000b4d3e000b4d24000b4d21000b4d1c000b4ce1000b4cdf000b4cde000b4cda000b4c80000b4c2b000b4c26000b4c21000b4c07000b4bc3000b4bc2000b4b64000b4b63000b4b09000b4b04000b4af0000b4aa5000b4aa4000b4aa0000b4a91000b4a51000b4a4b000b4a4a000b4a46000b4a32000b49f2000b49ec000b49eb000b49e7000b49d3000b49ca000b4993000b4974000b4934000b4915000b48b6000b4857000b4816000b47f2000b45dc000b45b8000b4460000b443f000b4401000b43e0000b42ca000b4231000b422b000b4227000b4225000b4224000b421d000b4218000b4217000b420c000b420a000b4206000b4201000b41cf000b41be000b41bb000b41ba000b41b9000b41b8000b41ad000b41ab000b41a9000b41a2000b419d000b4170000b416d000b4169000b4162000b4160000b415f000b415e000b415d000b415b000b415a000b4158000b4157000b414c000b4148000b4141000b4140000b4111000b410d000b4109000b4103000b4101000b4100000b40ff000b40fc000b40fb000b40f9000b40f8000b40ed000b40e8000b40e7000b40e5000b40e2000b40e1000b3f65000b3f63000b3c70000b3b78000b3b57000b3b19000b3af8000b3aaf000b3aab000b3875000b3871000b3866000b385c000b3800000b37a6000b37a4000b3749000b3747000b3745000b3705000b36e8000b36e6000b36a6000b3689000b3687000b367b000b356c000b344f000b33ff000b33fc000b33ed000b31c2000b31b3000b3055000b3054000b3047000b303c000b3031000b3002000b2ffc000b2fe8000b2fdd000b2fd2000b2f70000b2f6e | false => 0x16564f0016564200165627001655b30016557e0016555600165554001655410016553400165530001654f7001654f5001654ef001654e2001654d5001654d1001654ce00165498001654960016549000165485001654830016547600165472001654690016546700165465001654390016543700165431001654260016542400165423001654200016541700165413001654100016540a0016540800165406001653f2001653ed001653e1001653da001653c5001653b40016537b00165366001653550016534a0016531c00165307001652f6001652e5001652bd001652aa001652a8001652a7001652970016528600165276001652650016525e0016525c0016524900165238001651ff001651ea001651d9001651a00016519e0016518b001651870016517a001651770016516f0016516d001651690016515b00165141001651390016512c001651280016511b00165118001651100016510e0016510a00164f5500164f5000164f4d00164f4200164eff00164ef600164ef100164ee300164ede00164ec200164ec000164ea600164e1200164d8a00164d6200164d5a00164d5400164d4600164d3300164d0300164c9600164c0d00164bb000164ba200164b9b00164b9700164b9000164b8700164b8100164b7300164b5100164b4300164b3c00164b3800164b3100164b2800164b2200164b1400164aea00164ac9001649ac0016499e001648b7001648b00016488f0016488700164881001648730016483000164828001648220016481c00145fa200145e2600145dc70014553e001454df0014378e0014331a0013ac050013aba60013a3db0013a37c0013a31d0013a2be0013908f001390300013856d0013850e001383f10013809a0013803b0013138100124117001240b80011907000118d1900116f0a00116eab0010de500010de3b0010ddf10010dae40010d2ba0010cdfc0010cde70010cde30010c4ff0010c0870010bd8f0010bd300010bb6e0010bb590010bb550010b740000f6785000f654b000e62a4000e5a1b000e5016000e4ddc000e1443000e1326000e0ce8000e0cd4000e0b6c000e0b5c000e0b58000e0980000e097b000e03a1000e038d000e032f000e0108000e0105000e0104000e00f8000e00f5000e00f4000dffeb000dffdb000dffd7000dfc94000dfc80000df927000df75e000df700000df6ff000df6f2000df6ed000df6a0000df641000df5e2000df583000df524000df4c9000df4c6000df4c5000df4b5000df4b3000df466000df407000df3a8000df398000df34d000df349000df33d000df339000df337000df113000df110000df10f000df103000df03f000defe3000def84000cb134000cb12e000cb12d000cb107000caefa000caef4000caecd000ca723000ca60c000ca608000ca5ac000ca54d) | false => (match Nat.blt i 11 with | true => 0x191d7400191d6600191d6100191d4700191c8900191b9c00191b3d00191b3900191b27001919f0001919c2001919be001919bd001919b0001919ab00191991001915a8001915490019141d001913cd001913be001913720019136f0019136e001913610019135c00191342001912a1001912420019123f001911340019112700191122001911080017cf1e0017cce50017cc860017cc850017cc7c0017cc590017c4bb0017c4b00017c49e0017c48e0017c4760017c3810017c2800017bf2a0017bf290017befd0017bee50017bd320017baab0017b9980017b98f0017b9540017b9390017b9300017b8f50017b8da0017b8d10017b87c0017b87b0017b8720017b85f0017b84f0017b8370017b7540017b6f50017b6a00017b6970017b5e20017b5d90017b59e00171ac100171a62001719a5001719a400171995001708f1001708920017077600170717001706b8001706a80017065900170649001705fa0017059b0017053c001704dd0017047e0017041f001703c0001703610016fad700169740001696e100169581001694a700169405001693eb00168e5800168df900168d0100168c9900168be400168bc100168b1d00168aa200168a43001687670016874d0016857000168511001683f4001682d7001680b90016809f00167e2000167e0400167da500167b8700167a1400167a0b001679ef001677d1001677720016769a0016763b0016763900167541001675380016751c001674bd0016735d0016733c001670650016704400166e1300166d7300166c3800166c2700166ae300166ad400166ab300166a9f00166a7500166a5400166a40001669ff00166960001669520016694b00166947001669400016693a00166937001669310016692300166901001668f3001668ec001668e8001668e1001668d8001668d2001668c4001668a1001668a0001668930016688000166871001668420016684100166834001668210016681f0016681d0016680c001667f7001667d3001667ce001667c2001667c00016679f0016679d001667740016676f0016676c00166763001667610016675c0016673900166607001665a80016642c001662b000166251001661640016615800166076001660700016606a00166067001660650016605900166047001660450016603100166020001660170016601100165ff000165fe800165fe600165fb800165f4a00165f4800165f3c00165f3900165f1400165f0f00165f0300165e7400165e3600165e1500165e0100165dd700165db600165da200165bf100165bcd00165bbd00165bac00165b6e00165ae500165ad400165ac800165ac500165aa000165a9b00165a8f00165a00001659f2001658cf00165870001656fa001656d1001656d0001656c30016567200165671001656650016566400165651 | false => 0x2c9c61002c9c48002c9be9002c9b67002c9b63002c9b5f002c9b29002c9b08002c9b00002c9af9002c9a0e002c99ef002c99af002c999f002c9999002c9990002c997d002c9975002c9969002c9890002c987f002c986f002c9867002c9810002c9808002c97d1002c97b8002c97ad002c9773002c9772002c9759002c974e002c974c002c974a002c95fd002c95fc002c95f5002c95da002c959c002c9577002c9572002c956f002c955b002c953d002c9513002c94de002c947f002c9420002c941d002c941c002c9413002c940e002c940b002c9400002c93fb002c93f3002c93df002c93c6002c93c3002c93c1002c93be002c93b4002c93af002c93ac002c93a1002c939c002c9395002c9394002c9380002c92de002c92a5002c92a4002c929e002c9293002c928f002c928c002c9283002c927a002c9270002c9268002c925c002c91e6002c91e2002c91d1002c91ce002c91c1002c91bd002c91bc002c91b9002c91b6002c91b2002c91aa002c91a5002c919e002c90ff002c908d002c9071002c906e002c906b002c906a002c9065002c9064002c9059002c904e002c9041002c903f002c9031002c9012002c900f002c900d002c900c002c900b002c9006002c9005002c8ffe002c8ffa002c8fef002c8fed002c8fe2002c8fe0002c8fd2002c8fcf002c8fc3002c8f83002c8f28002c8e66002c8e2c002c8e12002c8e0b002c8e07002c8e03002c8de8002c8dac002c8da8002c8da4002c8d16002c8d0f002c8cee002c8cea002c8ce6002c8cd2002c8cb4002c8c8f002c8c8b002c8c8a002c8c55002c8c30002c8c2c002c8c2b002c8c28002c8c190022267e0022261f00222386002223270021962300219615002196130021960e002195f4002193e9002193db002193d4002193d0002193ba0021902500218e4a002189b50021879a0021861800218443002183360021832800218326002183210021831d002183070021826a002180fc002180ee002180ec002180e7002180cd0021786500217741002176e200217623002175c500217566002174a70021745e0021744a002174490021744800217445002173ff002173eb002173ea002173e9002173e60021738a0021732b002172e2002172d4002172cd002172cc002172c9002172b3002171ac0021714d002170d80021708f0021703000216f8b00216f7d00216f7600216f5c001bfa60001bfa01001be598001be539001bdcb0001bdc5100193be600193bd400193bcf00193bb5001938dc001938d7001938bd0019335d0019332c001932f9001931dc001930c400193001001929e5001928c8001927ca0019265b0019262f001924800019246e0019236700192364001923630019235600192304001922a50019218d0019215c00191fff00191ffd00191f9e00191ef400191d78)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0x2f65ec002f65eb002f65da002f65d5002f65bb002f658f002f6530002f651c002f64fd002f64d1002f6472002f6413002f640c002f63ff002f63fa002f63e0002f63b4002f63b2002f63b1002f63ad002f63a0002f639b002f6381002f6355002f62f6002f6297002f6291002f6238002f6232002f6231002f5fcc002f5dbd002f587e002f56b7002f56b5002f56b4002f56b1002f56b0002f56a3002f569e002f5685002f5684002f5598002f5593002f5586002f5581002f5567002e153c002e14fa002e14dd002e14cd002e149b002e147e002e143c002e143b002e1432002e141f002e140f002e0a36002e01a4002e0145002e00f0002e00e6002e00c3002dfc1d002dfbbe002dfb91002d6277002d6219002d6218002d57b5002d57a5002d54bd002d54ad002d4f2e002d4ecf002d4ecd002d4ebd002d4bd5002d49f9002d499a002d498b002d4821002d44ca002d44c8002d44c7002d440a002d4409002cd1fb002ccf03002cc936002cc913002cc61b002cbf0e002cbe73002cbe50002cbc98002cbc75002cba9a002cb9a0002cb393002cb351002cb34a002cb349002cb348002cb33f002cb33a002cb337002cb32c002cb327002cb320002cb31f002cb30b002cb2ef002cb2ea002cb2e0002cb2db002cb2d8002cb2cd002cb2c8002cb2c0002cb2ac002cb22b002cb1d7002cb1d4002cb1d1002cb1d0002cb1ca002cb1bf002cb1bb002cb1b8002cb1b4002cb1a6002cb1a5002cb197002cb194002cb178002cb175002cb173002cb172002cb171002cb160002cb15c002cb155002cb146002cb141002cb138002cb115002cb114002cb10e002cb0fa002cb0ed002cb0d9002cb0b6002cb0b5002cb0af002cb09b002cb08e002cb07a002cb077002cb056002cb04f002cb03c002cb038002cb036002cb02b002cb01b002caff9002caff7002caff1002caff0002cafe4002cafdd002cafd9002cafd7002cafd3002cafcc002cafca002cafc8002cafc7002cafbc002cafb9002cafb4002cacd8002ca9a8002ca8e4002ca8c3002ca82c002ca709002ca6e8002ca5ea002ca5cf002ca5c6002ca596002ca58d002ca579002ca56c002ca565002ca564002ca563002ca561002ca55d002ca555002ca549002ca45f002ca44f002ca447002ca415002ca411002ca3f0002ca3e8002ca299002ca295002ca284002ca281002ca274002ca26b002ca269002ca265002ca25d002ca251002ca0ba002ca099002ca05b002ca03e002ca03a002c9e48002c9dfc002c9dc9002c9dc4002c9d8d002c9d6b002c9d65002c9d63002c9d45002c9d42002c9d39002c9d33002c9d2e002c9d2b002c9d0d002c9d05002c9ce8002c9ce6002c9ccf002c9cac002c9ca6002c9c9c002c9c97002c9c91002c9c89002c9c87002c9c7c002c9c75002c9c70002c9c6d | false => 0x591e4a00591e4900591e3800591e2c00591d7700591d7100591d5b00591cd100591ccc00591cbe00591cb200591c9d00591c7200591c6d00591c6000591c5f00591bdf00591bac00591b6200591b4600591b3900591b2100591ac200591a9300591a8f00591a3400591978005919280059191a00591909005919030059190200591901005918ff005917fc0059179d005916f2005916ee005916df005916dd005916d9005916d2005916c8005916c5005916c3005916b5005916930059168f0059167e0059167a005916730059167200591669005916660059166400591656005915a300591572005915640059154b0059148f00591440005914300045b03d0045afde0044589b004454e500444e3700444dd80042fc7a0042f9820042f6250042f5730042f4570042f4560042f44a0042f0800042ed990042ed940042ed860042ec1d0042ec180042ec0a0042eab20042eaaf0042eaa40042ea530042ea500042ea450042ea420042ea3d0042ea2f0042e9f40042e9f20042e9f10042e9ec0042e9e60042e9e30042e9950042e9930042e9920042e9870042e9840042e97f0042e9360042e9330042e8d70042e8d40042e8cf0042e8780042e8750042e8640042e8620042e8190042e8160042e8110042e8080042e8050042e8030042e7f50042e7ba0042e7b70042e75b0042e7580042e74d0042e7390042e6fc0042e6fb0042e6f90042e6ee0042e69d0042e69c0042e69a0042e10b0042e1040042e0fe0042e0e80042e0890042e0460042de510042de4f0042dc950042dc900042dc870042dc820042dc760042dc740042dbda0042dbc60042db7b0042db6d0042db670042d9fc0042d9ee0042d9e90042d9db0042d40d0042d3ed0042d21200393934003936fa00392ed000391e1d00382e63003811120037d5530037d54d0037d5470037d52e0037d5210037d4f10037d4ee0037d4ed0037d4c70037d4c20037d1cf0037d1ca0037cb4b0037cb480037cb210037cb1c0037caca0037ca900037ca840037ca6b0037bf6b0037bf490037b7fc0037b6200037b5c50037b5c10037b3c00037b2650037af130037af0e00339ad800338552003242d4003242d00032427500324271003240f9003233990032269c003222e60032216e0032216a0032210f0032210b0030dd7a0030ca8d0030ca2e0030c9cf0030c9700030c9110030c8b20030c8530030c7f40030c7950030c7360030c6d70030c6780030baf7003017ad0030174e003014b500301456002fbba7002fbb48002fafc7002faeaa002f7a43002f7926002f784a002f716d002f715b002f7156002f713c002f6f92002f6f80002f6f7b002f6f61002f6e75002f6e63002f6bca002f68e4002f68d2002f67c9002f67c6002f67c3002f67c2002f67b5002f6797002f66a5002f664d002f65ee) | false => (match Nat.blt i 15 with | true => 0x5a8e1b005a8dbc005a8d63005a8d5a005a8cfe005a8c9f005a8c40005a8be1005a8bde005a8b7d005a8b1e005a8abf005a8a60005a8709005a85f1005a8355005a8353005a82970059e89d0059e5a50059dbff0059d8490059d4f10059d13c0059d13b0059d07e0059cd860059cd850059cb4c0059cb4b00597771005974790059694f00596300005962fe005962fc005962e3005961e1005960080059600400595feb005956620059565e00595645005953ac0059534d005952ee005952a80059528f005947e5005947cc005945ad005945ab00594592005944ed005943d0005943710059435800594312005942f90059429a0059423b005941f7005941f50059419600594137005940d80059404500593fe600593fa400593fa200593f8700593f4300593f4200593f3b00593f3800593e8800593e3700593e3200593e2500593e2400593e1800593e0300593dd800593dd300593dc500593d6100593d1800593d0200593cf400593ccc00593cc800593cb700593cb300593cac00593cab00593ca300593ca200593c9d00593c8f00593c6d00593c6900593c5800593c5400593c4d00593c4400593c4300593c3e00593c3000593bfb00593bee00593b9c00593b0b00593a8500593a8000593a6f00593a4d005939ee00593904005938f3005937e0005936cf005936ca005936b9005936b8005936b6005936b100593697005936790059365d00593657005936520059365000593638005935d9005935b2005935ad0059359c0059357a005935370059352e005934fd005934ee005934d8005934cf0059341f0059339f00593381005933650059335c005933580059334000593313005933070059326800593254005932420059323600593197005931380059312a005930740059306d00592fcf00592fbb00592fb600592fa900592f9d00592e9100592c5900592c4800592c4600592c1500592a7400592a2c00592a2b00592a1b00592a1500592a01005929db005929cc005929cb005929b6005929b2005929a2005929570059294300592921005928fb005928f8005928ef005928af0059288500592851005928500059284000592826005927ee005927a5005927910059278f0059278c005927820059277f0059277300592735005927330059272400592709005926d6005926d4005926c5005926aa00592666005926510059264b0059262500592610005926070059260600592600005925ff005925fc005925f2005925aa0059258d0059243b0059235e00592318005922c3005922ba005922b1005921ff005921a00059219c005921360059213400592127005920d5005920d4005920cd005920c8005920690059200a005920090059200700591f4c00591f1c00591f0800591f0700591f0400591ef900591ef600591eea00591ee500591e5e | false => 0xb20b2100b1fbea00b1fb2c00b1facd00b1fa6e00b1f8f200b1f8340090dcca008ddca1008dd82d008dd6b1008dd3b9008dd29c008dcfa4008dcf45008dc95500871505008714a60087120d00870f150086e2ed0086e1710086dd5c0086dcfd0086dc9e0086db220086dac30086da640086da050086d4740086d415008611410085c0d90085c07a0085c0380085c01b0085bf9d0085bf700085bf110085be1a0085bdbb0085bd5c0085bd360085bcfd0085bcd70085bc780085bafc0085baca0085ba090085ba060085ba050085b9e90085b9cc0085b94b0085b9470085b92b0085b9210085b90e0085b8ec0085b88d0085b86d0085b8630085b82b0085b82a0085b76c0085b7460085b6b20085b6ae0085b6920085b6880085b6750085b5320085b4d30085b4740085b4150085b3bd0085b3ba0085b3b70085b3b60085b39a0085b3900085b37d0085b1800085b17d0085b17c0085b1600085b1430085b0850085af460085af420085af260085af090085adaa0085ad8d0085ad2e0085ac700085aa490085a4de0085a47f0085a4200085a3c10085a2a40085a1e600859fac00859f8600859f4d00859f2700859d1300859ced006f8423006f8415006f83c3006f834f006f81e8006f806c006f7b25006f7a7d006f7a6f006f7894006f7835006f6dc9006f6bee006f6556006f64f7006f60e1006f5af1006f00c90065c6070065c36e0065b6d00065b6120065afc30065af640065ac0d0065aa320065a7990065a4a1006503ef0064f27e0064f1020064f0a3006461b6006461b500645fe900645fdb00645fd400645e01006454680064545400645409006453f4006451cf006451bb006451ba006447bb006443ff006443480064404900643ece00643e6f0060b5cd0060b4510060987c006092eb006091ce0060911000608f35005ecd0e005eccaf005ecc50005ecbf1005ec5a2005ec543005ec4e4005ec485005ec2aa005ec24b005ec1ec005ec18d005ebcba005eb846005eb7e7005eb788005eb729005eb256005eb1f7005eb198005eb139005ea8b0005ea7f2005ea793005ea734005ea6d5005c60f8005c5fdb005c5e00005c4938005c47bc005c428a005c40af005c3e16005c3abf005c054c005c04ed005c04e9005c04dc005c04d7005bf2ab005bf25b005bf24c005bf1a1005bf190005bf18b005bf12f005bf0d0005bf06e005bf025005bf00f005befb5005befb3005bef56005bef54005beea5005be1a8005bdf72005bdf5f005bdf13005ab810005ab752005a9b15005a987c005a96aa005a96a1005a9411005a9408005a8e80))))
def largeCode (i : ℕ) := Nat.land (Nat.shiftRight (largeCodeBlock (Nat.shiftRight i 8)) (Nat.shiftLeft (Nat.land i 255) 5)) 4294967295
def routeCode (i : ℕ) : ℕ :=
  let j := Nat.shiftRight i 6
  let x := routeByte i
  match Nat.beq (Nat.land (Nat.shiftRight (routeFlag j) (Nat.land i 63)) 1) 0 with
  | true => smallCode x
  | false => largeCode (routeRef (Nat.add (routeRank j) x))
def routeEnvBlock (i : ℕ) : ℕ := 0xc8c7c6c3c0bdbcbbb8b7b4b3b1b0aeada7a6a1a09e9c9b9a989392908f8e8a85848382817f7e7d77767574716f6a6968676662605c5b5a585756555251504c4a4948464544433e3b37363332312e2c2524221e18161211100d0c0a09070601
def routeEnv (i : ℕ) := Nat.land (Nat.shiftRight (routeEnvBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
abbrev RouteId := Fin 95
def mappedEnv (c : RouteId) : EnvelopeId := ⟨routeEnv c.val % 201,by omega⟩
def routeBlock (c a b t : ℕ) : Bool :=
  let e := routeEnv c % 201
  bitSub (negativeSig t) (coldMask a b) &&
    (if e = 199 then bitSub (positiveSig a &&& positiveSig b) (positiveSig t)
     else validEnv e (eraseMask a t) (eraseMask b t))
def checkedRoute (r b : ℕ) : Bool :=
  let a := repNum r
  let code := routeCode (r*1024+b)
  if code == 0 then coldMask a b == 0 else
  if code < 1024 then validClique a b code else
  let u := code-1024
  let pi := (u / 95) % 120
  routeBlock (u % 95) (permuteBits (permNum pi) a) (permuteBits (permNum pi) b) (u / 95 / 120)
lemma dispatchSelected (checked : ∀ r : Fin 34, ∀ b : Fin 1024, checkedRoute r.val b.val = true)
    (allEnv : ∀ c : RouteId, rejectsEnvelope (mappedEnv c)) (A B : Finset V) (P : Feature → Slot → Prop)
    (dirty : ∃ r, present A B (rows r) none) (cp : capacity A B P) (lh : layout A B P) : False := by
  let X := fsWord A
  let Y := fsWord B
  let p := chooseP X
  let r := chooseRow X
  let b : Fin 1024 := ⟨permuteBits (permNum p.val) Y.val,permute_bound p Y.val⟩
  let Q := vertexMark (vEquiv p) P
  have cx : capacity (fsCode X.val) (fsCode Y.val) P := by simpa only [X,Y,fsRound] using cp
  have lx : layout (fsCode X.val) (fsCode Y.val) P := by simpa only [X,Y,fsRound] using lh
  have hx : ∃ z, present (fsCode X.val) (fsCode Y.val) (rows z) none := by simpa only [X,Y,fsRound] using dirty
  have both : capacity (fsCode (repNum r.val)) (fsCode b.val) Q ∧ layout (fsCode (repNum r.val)) (fsCode b.val) Q := by
    simpa only [Q,b,p,r,canonical_row] using transfer_layout cx lx p
  have hot : ∃ z, present (fsCode (repNum r.val)) (fsCode b.val) (rows z) none := by
    simpa only [b,p,r,canonical_row] using dirty_moves p hx
  let code := routeCode (r.val*1024+b.val)
  have chk := checked r b
  change (if code == 0 then coldMask (repNum r.val) b.val == 0 else
    if code < 1024 then validClique (repNum r.val) b.val code else _) = true at chk
  split at chk
  · obtain ⟨z,za,zb⟩ := hot
    have inc := (negative_has _ z).mpr za
    have inc' := (negative_has _ z).mpr zb
    have bit : (coldMask (repNum r.val) b.val).testBit z.val = true := by
      simp [coldMask,Nat.testBit_and,inc,inc']
    rw [beq_iff_eq.mp chk] at bit
    simp at bit
  · split at chk
    · exact clique_check_sound chk both.1 both.2
    · let u := code-1024
      let c : RouteId := ⟨u % 95,by omega⟩
      let q : PIndex := ⟨(u/95) % 120,by omega⟩
      obtain ⟨cap,model⟩ := transfer_layout both.1 both.2 q
      have ok : routeBlock c.val _ _ (u/95/120) = true := chk
      obtain ⟨good,test⟩ := Bool.and_eq_true_iff.mp ok
      change (if (mappedEnv c).val=199 then _ else _) = true at test
      split at test
      · rename_i idx
        obtain ⟨Q',cq,lq⟩ := strippedLinear good test cap model
        exact allEnv c 1 1 Q' (by simpa only [idx] using diagonal_limit) cq lq
      · obtain ⟨Q',cq,lq⟩ := strippedOrdinary good cap model
        exact allEnv c _ _ Q' test cq lq
lemma permitted_moves {e A B m} (h : permittedWorld e A B m) (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) :
    permittedWorld e A B (moved m π sw) := by
  unfold permittedWorld at h ⊢
  by_cases eq : e=199 <;> simp only [eq,↓reduceIte] at h ⊢
  · exact ⟨move_world π sw h.1,silent_move h.2 π sw⟩
  · exact move_world π sw h
lemma permitted_exists {e a b : ℕ} {P} (en : validEnv e a b = true)
    (cap : capacity (fsCode a) (fsCode b) P) (lh : layout (fsCode a) (fsCode b) P) :
    ∃ m, permittedWorld e (fsCode a) (fsCode b) m := by
  by_cases eq : e=199
  · subst e
    obtain ⟨m,hm⟩ := diagonal_world en cap lh
    exact ⟨m,hm⟩
  · obtain ⟨O,R,M,root⟩ := lh
    exact ⟨marksFor P M,by
      rw [permittedWorld,if_neg eq]
      exact ⟨P,O,R,M,cap,root,rfl⟩⟩
lemma permitted_frame {e a b : ℕ} {m : Marks} (en : validEnv e a b = true)
    (w : permittedWorld e (fsCode a) (fsCode b) m) :
    ∃ O R, encLayout (modelNeg e) (modelPos e) (represented m) O R := by
  by_cases eq : e=199
  · subst e
    rw [permittedWorld,if_pos rfl] at w
    exact numeric_world _ _ (compatible_neg diagonal_limit) (compatible_pos diagonal_limit) w.1
  · rw [permittedWorld,if_neg eq] at w
    exact numeric_world _ _ (compatible_neg en) (compatible_pos en) w
set_option maxRecDepth 10000 in
lemma permitted_start {e a b : ℕ} {m : Marks} (en : validEnv e a b = true)
    (w : permittedWorld e (fsCode a) (fsCode b) m) : insidePacked (actualStart e) (represented m) := by
  by_cases eq : e=199
  · subst e
    rw [permittedWorld,if_pos rfl] at w
    have old := start_preserved _ _ (compatible_support diagonal_limit) (compatible_hot diagonal_limit) w.1
    have step := replacePacked_sound old (0 : Id)
    rw [silent_value w.2] at step
    change insidePacked (replacePacked _ 0 1) _
    exact step
  · rw [permittedWorld,if_neg eq] at w
    simpa only [actualStart,if_neg eq] using start_preserved _ _ (compatible_support en) (compatible_hot en) w
def rowHintsBlock (i : ℕ) : ℕ := (match Nat.blt i 6 with | true => (match Nat.blt i 3 with | true => (match Nat.blt i 1 with | true => 0x1fffbcd003ffcd0003ffc00003ffc4001dffddb01effdf601f7fe6d01fbfe5401fdfec101feef0501ff7f3601ffbf7501ffdf8b01fee70001ffe79001fffbcd006ffc40006ffcf001bffdd501dffddb006ffc0001f7fe6001fbfe7e01fdfeeb01fef72201ff7f3601ffbf7501ffdf8b01ffef9701fef70001fffbc0005dfcc0005dfc4001bffdd5005cdc0001effdf601f7fe6d01fbfe44005cdc0001dcdc0001ff7f3601ffbf7501dcd40001ffef9701ffd78001fffbcd00fffcfa017ffcf001bffdd501cddc0001cffd4001f5fe6001fbfe7e01d5dc0001feff2201ff7f3601ffbf7501dddc8201ffef9701fff7ba01fffbc000fffcfa01682c0001bffdd501cfbd4001482c0001f7fe6d01680c0001680c0001680c0001680c0001480c0001f80e0001680c0001fff7ba01fffbcd00687c00007dfce801aff9c001dffddb00a8780001f0fa0800e078000060780000e0780000e87c2201ffbf6001ffdf8b01ffef8201fff7ba01a0f80000fffcfa015ddc89019fdd81010cdc0001cfdd8201f4de0901f8de0a0150dc0001d01c0001fe5f0201fe9f0101001c0001ffef9701fff7ba01fffbcd007dfcc0007dfc8801bffd8001dffddb01effdf601f0fe0801f3fe440074fc0001f4bc0001ff7f3601febf0001ffdf8b01ffef9701fff78001fffbcd00fffcfa017ffc8801bffdd501dffdd001effdf601f7fe6d01fbfe7e01fdfee001febf2401ff7f3601febf0001ffdf8001ffef9701fff7ba01fffbcd007ff488007ff4b001bffdd501dffddb01effdc001f3fe2001f3fe4801fdfeeb01feff2f01ff770001ffbf7501ffdf8b01ffef97007f700001fff380005ddc88007ffcf001bffdd500cddc0001cfdd8001f1fe6001f1fe0800d1dc0001feff2201ff7f3601ffbf7500cddc8201ffef9701fff7ba01fffbc0005ddc80007ffcf001bffdd500dddc0001effdf601f1fe6001f1fe0000d1dc0001feff2201ff7f3601ffbf7500dddc8201ffef9701fff7ba01fffbc000fffcfa014ddc8001bffdd50149dc0001497c0001f7fe6d01c97c000149dc0001feff2801eb7c3001ffbf75015ddc8801ffef9001fff7ba01fffbcd006ffcd0006ffc8001bffdd501dffddb006f7c0001f7fe6d01fbfe5401fdfec101feff0501ef7d1401ffbf7501ffdf8b01ffef9701fff79001fffbcd00fffcfa017ffc8001bffdd501dffdd001effdf601f7fe6d01fbfc0001fdfee001feff2401ff7f3601ffbf7501ffdf8001ffef9701fff7ba01fffbcd00bffcd0017ffcfd00bffc8001dffddb01effdf601f7fe6d01fbbe5401fdfec101febf0501ff7f3601fabe0001ffdf8b01ffef9701fff79001fffbcd00fffcfa017dfcc901bffdd501cffd0001cffdc201f7fe6d01f9fe4a0179fc0001feff2f01ff7f0201ffbf4101ffdf8b01ffef9701fff7ba01fffbcd | false => (match Nat.blt i 2 with | true => 0x1ffe78001fffbc8007ffce8007ffcd001bffdd501dffdc901effde401f3fe4001f3fe6c01fdfeeb01fe7f0201fe7f2401ffbf7501ffdf8b01ffef8501fff7a801fffbcd00fffcc2017ffcc501bffdd501dffddb01effdf601f7fe6d01fbfe4601fdfeeb01fefc0001ff7f3601ffbf7501ffdf8b01ffe78001ffe78201fffbcd00cffcc0017ffcfd01bffdd500cefc0000ce7c0001f7fe6d01fbfe4401fdfeeb01ce7c0001ee7d2401ffbf7501ffdf8b01ffe78001ffe78001fffbcd007ff8c80077f80001bffdd501dffddb01eff9c40173f84001f3fa4c01fdfeeb01fe7b0001fe7b0401ffbf7501ffdf8b01ffef9701fff38800627000007ffcc00077bc0001bffdd501dffddb01effdf60173bc4001f3be4401fdfeeb01febf0001ff7f360172bc0001ffdf8b01ffef9701fff78001fffbcd00fffcfa017ffcf801bffdd001dffddb01effdf601f3fe6801f3fe4001fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffcd001bffdd501dffddb01effde001f3fe4001f3fe6801fdfeeb01fe7f0201fe7f2001ffbf7501ffdf8b01ffef8101fff7ba01fffbcd00fffcfa017efc0001bffdd501dffddb01effde001f7fe6d01fbfe6801fdfeeb017e7c0001fe7f2001ffbf7501ffdf8b01ffef8101fff7ba01fffbcd00fffcfa0167b80001bffdd501dffddb016f38000173b84001f3ba4001fdfeeb01fe3b0001ee39000162380001ffdf8b01ffef9701fff7ba0162380000fffcfa017ffcf901bffdd501cdfc0001cffdc201f7fe6d01f9fe4a01d9fc0001feff2f01ff7f0201ffbb4101ffdf8b01ffef9701fff7ba01ffbb0000cdcc02017ffcfd018fad10008d8c00008d8c0001f5be6001fbfe7e00c58c0001feff2201ff7f360185ac0000cdcc82008d8c0001fff7ba01fffbc000fbfc72017bfc3401bffd1401dffd1201effdf601f3fe240071fc0001f9fe2201feff2f01ff7f3601ffbf7501ffdf8b01ffef9701fff70001fffb0400effc32016ffcb401bffdd501cffd92004efc0001f6fe2401fbfe7e01fdfea201e6dc0001ff7f3601ffbf7501fedf0201ffef9701fff7ba01fffb84006ffcf0006eec0001bffdd501dffdc1006e6c0001f7fe6d01fbfe6401fcce00016c4c0001ee6d0401ffbf7501fcce01016c4c0001fff7a001fffbcd007ffc30007ffc0001bffdd501dffdd801effdf601f7fe6d01fbfe7e01fdfee801feff2c01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd007ffc40007ffcf801bffdd001dffddb01effdf601f7fe6801fbfe7e01fdfeeb01fef72a01ff7f3601ffbf7001ffdf8b01ffe79201fee70001fffbc800fffcd2017ffcd501bffdd501dffddb01effdf601f7fe4501fbfe5601fdfec301feef0701ff7f3601ffbf7501ffdf8b01fee70001ffe792 | false => 0x1ffef94006b540001fffbcd006bf430007ff49801bffdd501cffdd000cbf40001f3fe4c00e3f40001fdfee001feff2401ff7f3601ffb71001ffd78001ffef97006b940001fffbcd00fffcfa016ffcf401bffdd501cffdd2014ffc0001f7fe6501fbfe1001fdfee201feff2601ff7f3601ffbf7501ffdf8201ffef9701fff7ba01fffbc4006bf4300063f40001bffdd501cffdd00043f4000163fc440063f40001fdfee001feff2401ff7f3601ffbf7501ffd78001ffef97006bd40001fffbcd00ebfc32016ffcb401afbd1401cffd92000abc0001f2be2400e2bc0001fdfea201e2bc0001ff7f3601a2bc0001ffdf8b01ffef9701fff7ba01fffb84006bbc300062bc0001bffdd501cffd900042bc000162bc040062bc0001fdfea00162bc0001ff7f360062bc0001ffdf8b01ffef9701fff7ba01fffbcd00fffcfa017ffc9901bff98101dffddb01effd9201f7fa4d01fbfe1a01fdfac001fefb0401ff7f3601ffbf1101ffdf8b01ffef9701fff7ba01b4f800007fe490007ff4b801bfe59001dffddb01effdf601f6fe2d01fbee1401fdee8101f6e40001ff7f3601ffb73001ffdf8b00b8e400003ea00001fff38800fffcfa017ffc9801bfe98001dffddb01effdf601f4fa0801fbfe7e01f4e80001f4e80001ff7f3601ffaf1001ffdf8b01bca80001fff7ba01b4e800006ff490006ff49001bffdd501dffddb006ef00001f6fa0501fbfe1401fdfa8101e6f00001ff7f3601ffbf7501ffdf8b01ffef97006ef00001e4f00000fffcfa017ffcb001bffdd501dffddb01effdf601f2fe2401f2fc0001fdfe8001f2fc0001ff7f3601ffbf7501ffdf8b01ffef9701fff7ba01fffb8000fffcfa016ffcb001bffdd501dffddb016afc0001f2fe2001e2fc0001fdfeeb01e2fc0001ff7f3601ffbf7501ffdf8b01ffef9701fff7ba01fffb8000fffcfa017ffcfc01bffdd401dffdda01effdf601f3fe6c01f3fe4001fdfeea01feff2e01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc006b7430006b740001bffdd501dffdd8006b740001f7fe6d006b740001fdfee801feff2c006b743001ffbf7501ffd78801ffef94006b540001fffbcd006b74100063740001bffdd501dffddb006374000163fc440063740001fdfec001fe7f04006a742001ffbf7501ffdf8b01ffe780006b640001fffbcd004ffcd0004ffcc001bffdd5004f9c00004f3c0001f7fe6d01fbbe5401fdfec101febf0501ef3d1401ca3c0001dfdd8101ffef9701fff79001fffbcd00fffcfa01433c0001bffdd5014b1c0001431c000163bc4401433c0001fdfec001fe3f04014a3c0001423c0001cfdd8001ffef9701fff7ba01fffbcd007ffcc0007ffcf801bffdd001dffddb01effdf601f3fe6801f3fe4401fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffe792)) | false => (match Nat.blt i 4 with | true => 0x1ffdf8b01ffef9701fff7ba01fffb80007bec00007ffcf001bfad1001dffddb01effdf601f3be6000f3ac0001fdfeeb01feff2201ff7f3601b3ac0001ffdf8b00bbac0001fff7ba01fffbc000fff4aa017ffced01bfed8501cfe58201cffdc201f6fe0901fbfe4a01fdfeeb01f6640001fe670201ffbf4101ffdf8b019e640000de640001fffbcd00fffcaa017ffcbd01bffd8501dffd8b01effda601f6fe0901fafe2e01fdfeeb01f2bc0001ff7f3601febf2501ffdf8b01ffef9701fff7ba01fffbcd00fffcfa017ffc9901bfed8101dffddb01efed8201f4fe0901f8fe0a01f0ec0001f02c0001fe6f0201feaf0101ffdf8b01ac2c0001fff7ba01fffbcd0059fc00007dfce8019ffdc00099fc0001effdf601f1fe0800d1fc000051fc0001feff2f01ff7f3601ffbf6001ffdf8b01ffef8201fff7ba01fffbcd007ffcc8007ffcb801affd9001dffddb01affdc401f3fe2801f3fe4c01fdfeeb01feff2f01ff3f0401ff3f3001ffdf8b01ffef9701fff38801fff388007ffc88007ffcf801affdd001dffddb01affd8401f3fe6801f3fe0c01fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc8007df488007df4a801afed8001dffddb01afed8401f7fe6d01fbfe0c007de40001feff2f01ff270001ff372001ffdf8b01ad6400007d240001fffbcd00fffcfa017ffcfc01affdd401dffdda01affd8001f3fe6c01f3fe0801fdfeea01feff2e01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017ffce801affdc001dffddb01ab7c0001f7fe6d01eb7c0001fdfe8801feff2f01eb7c2201ffbf6001ffdf8b01ffef8201fff7ba01fffbcd00fffcfa017ffcf801affdd001dffddb01affd8001f3fe6801f3fe0801fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffca801afed8001dffddb01afed8001f7fe6d01fbfe0801fdfeeb01feff2f01ff2f0001ff3f2001ffdf8b01af6c0001fff7ba01fffbcd00fffcfa017ffc8801bffdd501dffdd801ebfc0001f7fe6d01ebfc0001fdfee801feff2c01ff7f3601ffbf0001ffdf8801ffef9401fff7ba01fffbcd007ffc88007fbc0001bffdd501dffddb01effd8001f7fe6d01fbfe0801fdfeeb01feff2801ff3f30017f3c0001ffdf8b01ffef9001fff7ba01fffbcd006b6400007ff48801bffdd501dffddb00eb640001f3f60800e3640001fdfeeb01feff2f00eb240001ff270001ffdf8b00eb24000063240001fffbcd00fffcfa017ffcfc01bffdd401dffdda01effdf601f7fe6d01fbfe1001fdfeea01feff2e01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc006b74300063740001bffdd501dffdd8006374000163fc440063740001fdfee801feff2c006b743001ffbf7501ffd788 | false => (match Nat.blt i 5 with | true => 0x1ffbf7501ffdf8b01ffe79001ffe79001fffbcd00fffcfa0135b8000135b84001dffddb01effdf60135b84001fbfe7e0135b80001feff2801ff7f360135b80001ffdf8b01ffef9001fff7ba0135b8000071f0000071f00001bffdd501dffddb01effdf60071f8400071f0000071f00001fef30001ff7f3601ffbf7501ffdf8b01ffef970078f0000070f00000fffcfa017ffce8019ff9c0019ffdd001effdf601f3fa4c01f3f80001fdfee001feff2401ff7f3601ffbf6001ffcb8001ffcf8201fff7ba01b3d80000fffcfa017bec0001bffdd501dffdd001effdf601f7fe6d017bec0001fdfee001feff2401ff7f3601ffbf7501ffcf80017bcc0001fff7ba01fffbcd007ffce0007ffcf8019ffdd0019ffdc101effdf601f3fe6801f3fe6401fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7a001fffbc800fffcfa017ffcf8019ffdd0019ffdc001effdf601f7fe6801fbfe7e01fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffce001bffdd501dffc0001effdf601f7fe6d01fbfe7e01fdfeeb01feff2801ff7f3601ffbf7501ffdf8b01ffef9001fff7ba01fffbcd00dae400017ffcfd01bffdd500dae40001effdf601f7fe6d00dae40001fdfeeb00dae40001ff7f3601ffbf7501ffdf8b00dae40000dae40001fffbcd007ffcf8007eec0001bffdd501decd0101ee6d0401f7fe6d01fbfe4401fcce01014c4c0001ee6d0401ffbf7501dcc400014c440001ffc78001fffbcd00fdfce2017ffc0501bffdd501dffd0101effdf601f7fe6d01fbfe0400fdfc0001feff2f01ff7f3601ffbf7501ffdf8b01ffef9701fff70001fffbcd00effc42017ffcf501afad1001dffddb00afac0001f7be6001fbfe7e01fdfeeb01fef72201ff7f3601a7ac0001ffdf8b01afa40001fee70201fffbc000fffcfa017ffcfd01bffdd501cffd5201cffdc201f7fe6d01f9fe4a01f9fe6201feff2f01ff5f0201ffbb4101ff5f0201ffef9701fff7ba01ffbb4400fffcfa017ffcfd01bffdd501cffdd201cffd4201f7fe6401fbfe7e01fdfee201feff2601ff7f3601ffbf7501ffdf8201ffef9701fff7ba01fffbc400fffcfa017ffcf901bffdd501dffddb01effd4201f23e2001f23c0001fdfeeb01f23c0001f23e0001f2380001ffdf8b01ffef9701fff7ba01ffbb4000fffcfa017ffcfc01afed9401cffdd2018bec0001f3fe6c01e3ec0001fdfee201feff2601ff7f3601ffaf0001ffcf8201ab8c0001fff7ba01fffbc400fffcfa017ffcbc01affd9401cffd92018b7c0001f3fe2c01e37c0001fdfea201feff2f01eb3c0001ff3f0001ffdf8b01ffef9701fff7ba01fffb8400fffc8a017ffcb901bffdd501dffddb01effd8201f6fe2901fafe0a01fdfeeb01f23c0001fe7f0201febf01 | false => 0x1ff3f3001373c0001ffdf8b01ffef8401fff7ba01fffbcd00fffcfa013fbc00012fbc4401dffdc801affdc001f7fe6d01fbfe4801fdfeeb01feff2f01ff3f20013f3c0001ffdf8b01ffef8401fff7ba01fffbcd00fffcfa017ffcc801bffdd501dffdd801effdf601f7fe6d01fbfe7e01fdfee801feff2c01ff7f3601ffbf4001ffdf8801ffef9401fff7ba01fffbcd00fffcfa0136bc000137bc4401dffdc801effdf60136bc0001fbfe7e01fdfeeb0176bc0001ff7f360136bc0001ffdf8b01ffef8401fff7ba01fffbcd007ff488007ffcf801affdd001dffddb01affdc001f3fe6801f3fe4801fdfeeb01fef72a01ff773201ffbf7001ffdf8b01ffe79200fe640001fffbc800fffcfa017ffce801affdc001dffddb01ab7c0001f7fe6d01eb7c0001fdfeeb01feff0801eb7c3201ffbf6001ffdf8b01ffef8201fff7ba01fffbcd006b7400007ffcc801bffdd501dffddb00eb740001f7fe6d00eb740001fdfeeb01fef72800eb743201ffbf4001ffdf8b01ffe79000ea640001fffbcd00eb7400017ffcfd01bffdd501dffddb00eb740001f7fe6d00eb740001fdfeeb01fef70800eb743001ffbf7501ffdf8b01ffe78000ea640001fffbcd007ffcc8003fac00012fac0001dffddb01affdc401f7fe6d01fbfe4c01fdfeeb01feff2f01ff2f04013f2c0001ffdf8b013f2c0001fff78801fffbcd00fffcfa012b2c00012b2c0001dffddb012b2c0001f7fe6d012b2c0001fdfeeb01feff2f012b2c00012b2c0001ffdf8b012b2c0001fff7ba01fffbcd00fffcfa017ffcfc01bffdd401dffdda01effdf601f7fe6d01fbfe5001fdfeea01feff2f01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc007ffcf8007ffcd001bffdd501dffdd901effdf401f7fe4501fbfe7c01fdfee901feff2f01ff7f3401ffbf7501ffdf8901ffef9501fff7b801fffbcd00fffcfa0173fc0001bffdd501dffdd801effdf60173fc440173fc0001fdfee801feff2c01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd00fffcfa016ffcf401bffdd501cffdd2014f7c0001f7fe6501fbfe5001fdfee201feff2701ef7d1001ffbf7501ffdf8201ffef9701fff7ba01fffbc4007ffcf0007ffcd001bffdd501dffdd101effdf601f7be4501fbbe7401fdfee101feff2701ff7f3601f3bc0001ffdf8101ffef9701fff7b001fffbcd00fffcfa01633c0001bffdd501cffdd001433c000163bc4401633c0001fdfee001fe3f24016a3c0001623c0001ffdf8001ffef9701fff7ba01fffbcd007ffcd0007ffcf801bffdd001dffddb01effdf601f7fe6d01fbfe5401fdfec101feff2f01ff7f3601ffbf7001ffdf8b01ffe79201ffe79001fffbc8007ffcd00077fc0001bffdd501dffddb01effdf60177fc4501fbfe5401fdfec101feff2d01ff7f36))) | false => (match Nat.blt i 9 with | true => (match Nat.blt i 7 with | true => 0x1feff2b01ff7f3601ffbf7101ffdf8b01ffef9301fff78001fffbc900ddf48a015ffcd101bffdd5005df40001effde001f5fe4101fbfe7a00d5f40001feff0301ff773001ffbf7501ffdf8b01ffef8100dd740001fffbcd00fffcfa017ffcc101bffdd501dffdd901effdf401f7fe6d01fbfe7e01fdfee901feff2d01ff7f3401ffbf7501ffdf8901ffef9501fff7b801fffbcd00fffcca017ffcc501bffdd501dffddb01effde001f7fe6d01fbfe6e01fdfeeb01fe7c0001fe7f2401ffbf7501ffdf8b01ffef8101fff78201fffbcd00fffcfa017ffcc101bffdd501dffddb01effde001f7fe6d01fbfe6a01fdfeeb01fe7c0001fe7f2001ffbf7501ffdf8b01ffef8101fff7ba01fffbcd00ddf488017ffcfd01bffdd500dcf40001effde001f7fe6d01f9fe6800d8f40001dc740001fe772001ffbf7501ffdf8b01ffef8100dc740001fffbcd00effcf2017ffcc101bffdd501dffdd100ef3c0001f7fe6d01fbfe7601fdfee101febf2501ef3d1401ee3c0001ffdf8101ffef9701fff7b001fffbcd00effcd2017ffcc101bffdd501dffddb00ef3c0001f7fe6d01fbfe5601fdfec101febf0501ef3d1401ee3c0001ffdf8b01ffef9701fff79001fffbcd00fffcca017ff8c101bffdd501dffddb01eff9c001f7ba4101fbfe5e01fdfeeb01febb0101ff3f1401f6380001ffdf8b01ffef9701fff3800166b00000fffcfa017ff8c101bffdd501dffddb01ef780001f7fa4101fbfe5201fdfeeb01fefb0101ef7d1001ffbf7501ffdf8b01ffef9701fff7ba0166f80000dffcd8017ffcfd01bffdd500cfdc0001cffdc001f7fe6d01fbfe5c01fdfec101feff0501ff7f1401ffbf7501dfdd8101ffef9701fff79001fffbcd00effcc0017ffcfd01bffdd501dffddb00ee7c0001f7fe6d01fbfe4401fdfeeb01ee7c0001ee7d0401ffbf7501ffdf8b01ffef9701fff78001fffbcd00fffcfa017ffcfd01bffdd501dffddb01ee7c0001f7fe6d01fbfe4001fdfeeb01ee7c0001ee7d0001ffbf7501ffdf8b01ffef9701fff7ba01fffbcd007ffcf8007ffcc801bffdd501dffdd901effdf401f7fe6d01fbfe7c01fdfee901feff2d01ff7f3601ffbf4001ffdf8901ffef9501fff7b801fffbcd007ffce80036bc000137bc4501dffdc901effde40132bc0001f3fe6c01fdfeeb01763c0001fe3f2401363c0001ffdf8b01ffef8501fff7a801fffbcd00fffcfa017ffcfc01affdd401dffdda01affdc001f3fe6c01f3fe4801fdfeea01feff2e01ff7f3201ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017fbc0001bffdd501dffdd801effdc001f7fe6d01fbfe4801fdfee801feff2c01ff3f30017f3c0001ffdf8801ffef9401fff7ba01fffbcd00fffcfa0137bc000127bc4401dffdc801affdd00137bc4101fbfe5801fdfeeb01feff09 | false => (match Nat.blt i 8 with | true => 0x1fdfeeb01feff2a01ff7f3601ffbf7501ffdf8b01ffef9001fff7ba01fffbc000fffcfa017ffcf001bffdd501dffdd001effdf601f7fe6401fbfe7e01fdfee001feff2601ff7f3601ffbf7501ffdf8201ffef9701fff7ba01fffbc000fffcfa017ffcfd01bffdd501ddcc0001effdf601f7fe6d01fbfe7e01ddcc0001feff2001ff7f3601ffbf7501ddcc8001ddcc0001fff7ba01fffbcd00fffcfa017ffcfd01bffdd501dffdda01effd8201f7fe6d01fbfe0a01fdfeea01feff2e01ff7f3601ffbf7501ffdf8a01ffef9601fff7ba01fffbcc00eb7422017ffcec01affdc401dffdca00ab740001f3f60800e3740001fdfeeb01feff2f00eb742201ffbf6401ffdf8b01ffef8600e3740001fffbcd00fffc8a017ffcf901bffdd101dffddb01effd8201f7fe6901fbfe0a01fdfeeb01feff2a01ff7f3601ffbf7101ffdf8b01ffef9201fff7ba01fffbc800697c00007dfce801affdc001dffddb00a97c0001f1fe0800e17c0000617c0001feff2f00e97c2201ffbf6001ffdf8b01ffef8201fff7ba01fffbcd00fff48a017ffce901bff98101dffddb01effdc201f7fa0901fbfe4a01fdfeeb01feff2f01ff770201ffbf6101ffdf8b01ffef9700ff700001b7f00000fffcfa017ff88801aff98001dffddb01abf80001f3fa0801e3f80001fdfeeb01feff2f01ff7f3601ffbb0001ffdf8b01ffef9701fff7ba0123b80000dffc9a017ffcfd019ffd91008fdc0001cffd9201f7fe6d01fbfe1a01fdde8201fedf0201ff7f3601ffbf1101dcd80001ffef9701fff7ba01ffdb8000dffc92017ffcfd019ffdd0009fdc0001effdf601f7fe6d01fbfe1201fdde8201feff2a01ff7f3601ffbf7001dddc8a01ffef9201fff7ba01fffbc800fffc92017ffcf501bffdd501dffddb01effdf601f7be6501fbfe1201fdfe8201feff2201ff7f3601f7bc0001ffdf8b01ffef9701fff7ba01fffbc000fffcfa017ffcf101bffdd501dffddb01efbc0001f7be6101fbfe1201fdfeeb01feff0201ff7f3601e7bc0001ffdf8b01ffef9701fff7ba01fffb8000cdfc82017ffcb1018fbd10008dbc00008dbc0001f5be2101fbfe1200c5bc0001feff2f01ff7f360185bc0001ffdf8b01ffef9701fff7ba01fffb8000fffcfa017ffcb8019fed90019cec0001effdf601f4fe2801fbfe7e01d4ec0001d4ec0001ff7f3601ffbf3001ffdf8b019cec0001fff7ba01fffb8800fffcfa017ffcb801bffdd501dcdc0001effdf601f4fe2801fbfe7e01d4dc0001d4dc0001ff7f3601ffbf1001dcd80001ffef9701fff7ba01ffdb8000fffcfa015ffc9001bffdd5015cf80001effdf601f4fa0001fbfe7e01d4f80001d4f80001ff7f3601ffbf7501ffdf8b01ffef9701fff7ba01d4f80000fffcca017ffcf901bffdd101dffddb01effdf201f7fe6901fbfe7e01fdfeeb | false => 0x1fbfe7e01fdfeea01feff2e01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd00effcf2016ffcf401bffdd501cffdd2004f7c0001f7fe6501fbfe5401fdfee301feff2701ef7d1401ffbf7501ffdf8301ffef9701fff79001fffbc400fbf432017ffcd401bffdd501dffdd001effdf601f3fe4400f3f40001fdfee201feff2601ff7f3601ffbf7501ffd78001ffef9700fbd40001fffbcd00fffcf8017ffcfd01bffdd501dffdd001effdd401f7fe6d01fbfe5c01fdfee901feff2d01ff7f1401ffbf7501ffdf8101ffef9701fff79801fffbcd00fffcf0017ffcfd01bffdd501dffdd001effdf601f7fe6d01fbfe5401fdfee101feff2501ff7f3601ffbf7501ffdf8101ffef9701fff79001fffbcd00fffcfa017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe7e01fdfec001feff0401ff7f3601ffbf7501ffdf8b01ffef9701fff7ba01fffbcd007ffcf0007ffcf8019ffdd0019ffdd101effdf601f7fe6d01fbfe7401fdfee101feff2f01ff7f3601ffbf7001ffdf8b01ffef9201fff7b001fffbc800fffcfa017ffcfc01bffdd401dffdda01effdf601f7fe6d01fbfe7001fdfeea01feff2f01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017ffcf801bffdd001dffddb01effdf601f7fe6901fbfe7001fdfeeb01feff2b01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc8007ffcf8007ffcf001bffdd501dffdd901effdf401f7fe6501fbfe7c01fdfee901feff2f01ff7f3401ffbf7501ffdf8b01ffef9501fff7b801fffbc000fffcfa017ffcf401bffdd501dffdd201effdf001f7fe6501fbfe7801fdfee201feff2f01ff7f3001ffbf7501ffdf8a01ffef9101fff7ba01fffbc400fffcfa017ffcf101bffdd501dffdd801effdf601f7fe6501fbfe7201fdfee801feff2f01ff7f3601ffbf7501ffdf8a01ffef9401fff7ba01fffbc100fffcfa017ffcfd01bffdd501dffdd001effdf001f7fe6d01fbfe7801fdfee001feff2d01ff7f3001ffbf7501ffdf8801ffef9101fff7ba01fffbcd00fffcfa017ffcfd01bffdd501dffdd801effdf601f7fe6d01fbfe7001fdfee801feff2d01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd00fffcfa017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe7001fdfeeb01feff2901ff7f3601ffbf7501ffdf8b01ffef9001fff7ba01fffbcd00fffcfa017ffcf8019ffdd0019ffdd001effdf601f7fe6c01fbfe7e01fdfee001feff2e01ff7f3601ffbf7001ffdf8a01ffef9201fff7ba01fffbc800fffcfa017ffcf001bffdd501dffdd001effdf601f7fe6401fbfe7e01fdfee001feff2e01ff7f3601ffbf7501ffdf8a01ffef9001fff7ba01fffbc000fffcfa017ffcf001bffdd501dffddb01effdf601f7fe6001fbfe7e)) | false => (match Nat.blt i 10 with | true => 0x1f7fe6d01fbfe6c01fdfeeb01feff2f01ff7f2401ffbf7501ffdf8b01ffef8101fff78801fffbcd00fffcca017ffcc901bffdd501dffddb01effdc601f7fe6d01fbfe4e01fdfeeb01feff2f01ff7f0601ffbf4101ffdf8b01ffef9701fff78801fffbcd00fffcfa017fac0001bffdd501dffddb01effdc001f7fe6d01fbfe4801fdfeeb01feff2f01ff2f00017f2c0001ffdf8b017f2c0001fff7ba01fffbcd00fffcfa017ffccc01bffdd501dffdd801effdc401f7fe6d01fbfe4c01fdfee801feff2c01ff7f3601ffbf4401ffd78801ffef9401ffd78801fffbcd00fffcf8017ffcfd01bffdd501dffdd801effdc401f7fe6d01fbfe4c01fdfee801feff2c01ff7f3401ffbf7501ffd78801ffef9401ffd78801fffbcd00fffcfa017ffccc01bffdd501dffdd801effdf601f7fe6d01fbfe7e01fdfee801feff2c01ff7f3601ffbf4401ffdf8801ffef9401fff7ba01fffbcd00fffcf8017ffcfd01bffdd501dffdc901effde401f7fe6d01fbfe6c01fdfec801feff0c01ff7f3401ffbf7501ffdf8b01ffef8501fff7a801fffbcd00fffce8017ffcfd01bffdd501dffdc801effdc401f7fe6d01fbfe4c01fdfeeb01feff2f01ff7f2401ffbf7501ffdf8b01ffef8401fff78801fffbcd00fffcfa017ffcfd01bffdd501dcec0001effdf601f7fe6d01fbfe7e01dcec0001dcec0001ff7f3601ffbf7501ffdf8b01dcec0001fff7ba01fffbcd00fffcd2017ffcfd01bffdd001dffddb01effdf601f7fe6d01fbfe5601fdfec301feff2f01ff7f3601ffbf7001ffdf8b01ffe79201ffe79201fffbc800fffcfa017ffcfd01bffdd401dffdda01effdf601f7fe6d01fbfe5201fdfeea01feff2f01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017ffcfc01bffdd001dffddb01effdf601f7fe6c01fbfe7e01fdfec201feff2e01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe7201fdfeca01feff2f01ff7f3601ffbf5401ffdf8b01ffef9701fff7ba01fffbc100fffcfa017ffcd001bffdd501dffddb01effdf601f3ba4001f3b80001fdfeeb01feff0201ff7f3601f3b80001ffdf8b01ffef9701fff7ba01f3b80000fffcf2017ffcfc01bffdd401dffdda01effdf601f7fe6d01fbfe5401fdfeeb01feff2f01ff7f3601ffbf7401ffdf8b01ffef9601fff79001fffbcc00fffcfa017ffcd401bffdd501dffdd901effdf401f7fe4501fbfe7c01fdfeeb01feff2f01ff7f3401ffbf7501ffdf8901ffef9501fff7b801fffbcd007ffcf00077fc0001bffdd501dffdd801effdf60177fc4501fbfe5401fdfee901feff2d01ff7f3601ffbf7501ffdf8901ffef9401fff79001fffbcd00fffcfa017ffcd401bffdd501dffdd801effdf601f7fe44 | false => (match Nat.blt i 11 with | true => 0x1effdf601f7fe6501fbfe7401fdfee301feff2701ff7f3601ffbf7501ffdf8301ffef9701fff7b001fffbc400fffcfa017ffcf401bffdd501dffdda01effdf601f7fe6401fbfe7e01fdfeea01feff2e01ff7f3601ffbf7501ffdf8a01ffef9401fff7ba01fffbc400fffcfa017ffcfd01bffdd501dffdd001effdf601f7fe6d01fbfe7e01fdfee001feff2401ff7f3601ffbf7501ffdf8001ffef9701fff7ba01fffbcd00fffcfa017ffcfc01bffdd501dffdda01effdf001f7fe6d01fbfe7801fdfeea01feff2f01ff7f3201ffbf7401ffdf8a01ffef9701fff7ba01fffbcc00fffcfa017ffcf801bffdd401dffdd801effdf601f7fe6c01fbfe7e01fdfee801feff2e01ff7f3601ffbf7001ffdf8a01ffef9601fff7ba01fffbc800fffcfa017ffcfd01bffdd501dffdd801effdf001f7fe6d01fbfe7801fdfee801feff2d01ff7f3001ffbf7501ffdf8801ffef9501fff7ba01fffbcd00fffcfa017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe7e01fdfeeb01feff2801ff7f3601ffbf7501ffdf8b01ffef9001fff7ba01fffbcd00fffc8a017ffcfd01bffdd101dffddb01effdf601f7fe6901fbfe7e01fdfeeb01feff2b01ff7f3201ffbf7501ffdf8b01ffef9301fff7ba01fffbc900fdfc8a017ffcf901bffdc101dffddb01effdf201f5fe0901fbfe7a00f5fc0001feff2f01ff7f2201ffbf7101ffdf8b01ffef8301fff7ba01fffbcd00fffcfa017ffc8901bffd8101dffddb01effd8201f7fe6d01fbfe0a01fdfeeb01feff2f01ff7f0201ffbf0101ffdf8b01ffef9701fff7ba01fffbcd00fffcfa017ffcc901bffdd501dffdd901effdf601f7fe6d01fbfe7e01fdfee901feff2d01ff7f3601ffbf4101ffdf8901ffef9501fff7b801fffbcd00fffcea017ffcc901bffdc501dffdc901effdf601f7fe4901fbfe7e01fdfeeb01feff0901ff7f3601ffbf4101ffdf8b01ffef8501fff7a801fffbcd00fffce8017ffcfd01bffdd501dffdc901effdf401f7fe6d01fbfe7c01fdfeeb01feff0901ff7f3401ffbf7501ffdf8b01ffef8501fff7a801fffbcd00fffcca017ffcf901bffdd101dffddb01effdf601f7fe6901fbfe7e01fdfeeb01feff2b01ff7f3601ffbf7101ffdf8b01ffef9301fff78801fffbc9007ffcc8007fbc0001bffdd501dffddb01effdf401f7fe6d01fbfe7c01fdfeeb01feff2901ff3f34017f3c0001ffdf8b01ffef9101fff78801fffbcd00fffcfa013fbc00013fbc4101dffddb01effdf001f7fe6d01fbfe7801fdfeeb01feff0901ff3f30013f3c0001ffdf8b01ffef8101fff7ba01fffbcd00dffcca015ffcc9019ffdc1001ffc0001effde601f7fe6d01fbfe6e01fdfeeb01feff2f01ff7f2601ffbf4101ffdf8b01ffef8101fff78801fffbcd00fffcc8017ffcfd01bffdd501dffddb01effde4 | false => 0xfffcfa017ffc3401bffdd501dffd1201effdc401f7fe6d01fbfe4c01fdfe2201feff2f01ff7b0401ffbf7501ffdf8b01ffef9701fff78801ff7b0400fffcfa017ffcfc01bffdd401dffdda01effdf601f7fe6c01fbfe7e01fdfeea01feff2e01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017ffcfd01bffdd501dffdda01effdf201f7fe6d01fbfe7a01fdfeea01feff2f01ff7f3201ffbf7501ffdf8a01ffef9701fff7ba01fffbcd00fffcfa017ffcf801bffdd001dffddb01effdf601f7fe6801fbfe7e01fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffcfd01bffdd501dffdd801effdf601f7fe6d01fbfe7e01fdfee801feff2c01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd00fffcfa017ffccd01bffdd501dffdd901effdf601f7fe6d01fbfe7e01fdfee901feff2d01ff7f3601ffbf4501ffdf8901ffef9501fff7ba01fffbcd00fffcf8017ffcfd01bffdd501dffdc901effdf401f7fe6d01fbfe7c01fdfec901feff0d01ff7f3401ffbf7501ffdf8b01ffef8501fff7b801fffbcd00fffcc8017ffcfd01bffdd501dffddb01effdc401f7fe6d01fbfe4c01fdfeeb01feff2f01ff7f0401ffbf7501ffdf8b01ffef9701fff78801fffbcd00fffcfa017ffcd501bffdd501dffdd901effdf401f7fe4501fbfe7e01fdfeeb01feff2f01ff7f3401ffbf7501ffdf8901ffef9501fff7ba01fffbcd00fffcf8017ffcfd01bffdd501dffdd101effdd401f7fe6d01fbfe7c01fdfee901feff2d01ff7f1401ffbf7501ffdf8101ffef9701fff7b801fffbcd00fffcd0017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe5401fdfec101feff0501ff7f3601ffbf7501ffdf8b01ffef9701fff79001fffbcd00fffcf2017ffcfc01bffdd401dffddb01effdf601f7fe6d01fbfe7401fdfeeb01feff2f01ff7f3601ffbf7401ffdf8b01ffef9601fff7b001fffbcc00fffcf2017ffcf501bffdd501dffddb01effdf601f7fe6501fbfe7601fdfeeb01feff2f01ff7f3601ffbf7501ffdf8b01ffef9401fff7b201fffbc500fffcf2017ffcf401bffdd501dffdd3))))
def rowHints (i : ℕ) := Nat.land (Nat.shiftRight (rowHintsBlock (Nat.shiftRight i 8)) (Nat.shiftLeft (Nat.land i 255) 5)) 4294967295
def primitiveHintsBlock (i : ℕ) : ℕ := (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x101102fd187d388d1a8140e07834220112650024100503ff187f788f7a9162f279364002327548ee121400fd187d188d1a9140f05834000112750024101502af182f288f000062a27826000a322548ae000c00af182f188f100140a25826000b1225002e100d03fe1c7e7c8e4a8040226d366b0a02644d2e3a1c03b91c397c890c0026307d302a0907200c280a88033a1c3a7c0a4d0045226d326b0a05204d2a080803bc183c788c18100030793408081334082c1a9c02bf1c3f7c8f5c1066327c36480a16344c2e181c02bf183f788f589062b27836488a103448ae189c03ff1c7f7c8f7f9166f27c366acb36754cee000002dd185d188d1a9142f058340ac912550000121100dd185d188d1a9100305810080912510808181903c7106f708f73810200512602011365000412cd00c7104f508f528140025006400312454006100503ff1c7f7c8f7f9126f03c342ac905200cec088803ff1c7f7c8f7f9145b23010498b153500c8189d03bf1c3f7c8f7f9106b01c300a8937314daa3a99039f103f708f739122b03010228933310088329901fe1c7e5c8e5f9000901814498a1534088c189c01ef1c6f5c8f5f8104a01c24088915250cac188d03ff1c7f7c8f7f9166f27c366acb04204cee088803ff1c7f7c8f7f9145b27812498b101148ca189d03bf1c3f5c8f5f9147b258124b8b1211488a1a9d01ce186e588e5b8040825806488a1004488e188c037f147f740e771062427006634a1244456e325c03631063200b23012362312221022120416a200002ff1c7f040c441066f07c34004836754cec005c03bf183f3887111063b279360102333549ae1014039b183358035b11431250100201133100001a1903ff1c7f1c8f1f9147f25d360bcb17750522121103ff1c7f3c8d7f9127f03d342bc905200dec088803ff1c7f7c8b7f9104307d32080937714dea3ad903ff0c7f4c8b5f9106304d320a0907710c280ad903ff187f388d7b9123f039340988113409ec189c033714375407771106301434020117350424121503771477700f77116372713641021134416e1014020b180350035a01420250024203120140021201021e181e380e3810203208022a0a0000082e08080337143774074001400240066303000545263215033f1c3f7c0f4d0104200c242a0905250c2c080d03ff1c7f7c8f5f8147e25d26630317654526120503fd1c7d7c8d1d9022d0381449c8105408cc18dc03771477740f32112272303641021034006e101403771477740f36112672343600021434046e101402571057700f521142725036424b12114002121103df187f788f5b91021059360a091375080c1add02ff1c7f7c8f5e9146f25c36420316754426121503ff0c6f7c8f6f8126206d262a0927650c2c2acd037f1c7f740f771142425006634b1245456e325d | false => 0x49cb1005408a02c903ef0c6f4c8f5f8142e240024bcb124540ca02c903ff1c7f7c8f7f9147e25d266bcb17654522120101af0c2f4c8f5d8145a24522498b152545aa008903fd1c7d7c8d3f9122f038346bc9000008ec088802df185f788f7a9162b248226acb020148ae0a8902dd185d388d3a9102e018242ac9120108a81a8902dd185d388d3a9122b038302ac9321108883a9903eb0c6b4c8b4f8102c008004bcb076108c80ac902cb084b488b4a8142c248024acb024148ca0ac903ff1c7f7c8f7f9166f27d366acb36754cee024003ff1c7f7c8f7f9145f27d3649cb177500401add00ff1c7f5c8f5e9144f25c3648cb16754422101103df187f788f7b9162d279364002325548ce125403ef1c6f7c8f7f8145e27d260001176504641acd00cf184f588f5a8140c25806400312454006100503ff1c7f7c8f7f9126707d362a4907600c6c0ac801ff1c7f5c8f5f9104705d36084917710c281ad9016e0c6e4c0e5f0045624d26494a05204d2a0808007c1c7c1c0c1e1004301c34080814340c2c181c02fe1c7e7c8e7e9064f24c22620206604426000002fb1c7b5c8b5e9146f25c32420316714422121103ff1c7f7c8f7f9167f2343422c9052004ec088803ff1c7f7c8f7f9167f2753663cb052045ee008803ff147f748f779167f2553643cb173145aa129902b914393489369126b034302289363104a8329903931c3350035311421050104201173100001a91037f1c7f540d56114670143402493775446c3a5d03eb186b28896b8123e039200988212049ea288803ff1c7f74067f9162c27806634232454dee325403ff1c7f788f7f9163f27936610233754dee301402af1c0f788e7c8162827806688a10044c8e388c02fb187b788b6a8162e278226202326148ea000002df185f788f400062c27806624a324548ce004c03bf1c3f7c8f1880228238066b8a10044dae3a9c02eb1c6b2c8b2e8126e23c22088a04200cea088803b91c397c89259160800000638930014da8329903bf1c3f7c8f008165b220266b8b35354dae3a9d033b1c3b7c0b4801400268026b0b00014d2a3a19027f147f340f341124720422224b0461046e004903ff1c7f7c8f4d8022d038146bcb056408cc08cc03ff1c7f7c8f3a9122f238366bcb052008ee088803791c797c090a01225008006b49074108480a4903ff1c7f7c8f7a9162f278366bcb327548ee000002df185f788f7a11627248026acb0241486e0a4903ff1c7f7c8f7a9162f278366bcb002048ee088803fb1c7b7c8b4a8162d248026bcb024148ca0ac902ff187f788f5a8142e258266acb12654022120103ef1c6f5c8f1a8102e218264bcb1201088a1a8902d918593889188100c018002ac9104108c818c903ff1c7f7c8f7e9166f27d366acb36754cee020000dd185d188d1a9140f0583408c91255) | false => (match Nat.blt i 3 with | true => 0x45f27d3649cb377545e2101103df187f788f7b9162d079360000337548cc12dc02fd1c7d3c8d3e9144f07c340001367544e4101503ff1c7f7c8f7f9162d07d3663c33775000432dd03ff1c7f7c8f7f9166f07d3622013775042432dd03ff1c7f7c8f7f9167327d366b0b37754d2e3a1d03ff1c7f7c8f7f9167f27d3622490760046c0ac803ff1c7f7c8f7f9167f27d366acb36754cee024003ff1c7f7c8f7f9167f27d366acb04204cee0ac803ff1c7f7c8f7f9167f27d3649ca177400481adc03ff1c7f7c8f7f9167f27d36414a325148ca125403ff1c7f7c8f7f9167f27d3648ca1674456a325103ff1c7f7c8f7f9167f27d36634b32514002325503ff1c7f7c8f7f9167f27d366acb36754422325103ff1c7f7c8f7f9167f27d366acb36314caa3ad903ff1c7f7c8f7f9167f27d36634b0760456e000003ff1c7f7c8f7f9167f27d36414a1770456a101003ff1c7f7c8f7f9167f27d3649ca15304dea189803ff1c7f7c8f7f9167f27d3641021774456e101403731473740b771167727532630337314522321103ff1c7f7c8f7a9162f278366bcb32754dee321002dd185d388d389160f000002ac9305548ec00c903ff1c7f7c8f3a9122f238366bcb00204dee3a98025f185f380f3811207208022a4b0041086e084903fc1c7c7c8c2d9020d008046bc800444dec3adc02fe187e788e488040e248266aca006448ee08cc03f7147774872200222275366302222445e6321403f71477748f361126727536224b262045ee220003ef1c6f7c8f3e0126627d26080a36244dee3a0c03ef186f788f7a8062a27926488a102449ee3a8c036f106f600f000022623126004a0064416e224c033b143b740b450067327532630b0520452a00080337143774075500672275366302152445261004033e143e740e551045327536410a1534452e101c03ff1c7f7c8f7f9127f03d346bc901204dec3add037d147d740d371105303130410910114148325d03ff1c7f7c8f7f9147f25d364bcb177541003add03bf1c3f7c8f7f9107b018104b893331498a3a9d03bf1c3f7c8f7f9147b258124b8b1211498a3a9d033d143d740d371127303010630932110008321d03cf186f788f7b8143c259260201136541043acd03cf186f788f7b81020059260a091365490c3acd03ee1c6e7c8e7f800080192449881124498c3acc03de187e788e7b9040925936488a1014498e3adc03f7147f748f77912210713663013375000432dd039f183f788f7b91229038142a893335088c3a9d039f183f788f7b91629278166a8b3215488e3a9d03ff1c7f7c8f7f9147e25d266bcb176500201acd01af0c2f4c8f5d8145a20000498b15250088188d03ff1c7f7c8f7f9162f278366bcb325548ee000003ef1c6f5c8f5f8142e258264bcb12454002120101ef0c6f4c8f5f8140a24522 | false => 0x3ff1c7f540e571062d07814434a377548cc125c03ff1c7f7c8f7f9167f27d366bcb37754dee000003ff1c7f7c8f7f9167f27d366bcb32554dee325503ff1c7f7c8f7f9167f27d366bcb05204dee088803ff1c7f7c8f7f9167f27d366bcb37754522321103ff1c7f7c8f7f9147e25d266bcb377545223add03ff1c7f7c8f7f91673275326bcb377500083add03ff1c7f7c8f7f9122d038146bcb377508cc3add03ff1c7f7c8f7f9145f27d3649cb377541c23add03ff1c7f7c8f7f9163d27d3663c3377500043add03ff1c7f7c8f7f9126307d362a0937750c2c3add03ff1c7f7c8f7f9167f27d362ac937754cec0ac803ff1c7f7c8f7f9167f27d3608c837754dea3ad903ff1c7f7c8f7f9167f27d36000037754cec1adc03ff1c7f7c8f7f9167f27d3649ca37754dea101003ff1c7f7c8f7f9167f27d36630337754526321503ff1c7f7c8f7f9167f27d366bcb325548ee124403ff1c7f7c8f7f9167f27d366bcb1764456e000003ff1c7f7c8f7f9167f27d366bcb32554002325503ff1c7f7c8f7f9167f27d366bcb37314daa3a9903ff1c7f7c8f3f9127f23d366bcb25104dee3add037f1c7f7c0f3d1125722d126b4b00414d6e3a5d03ff1c7f7c8f4a8142c248066bcb02454dee3add03ff1c7f7c8f7f9147e25d266bcb176545203add03ff1c7f7c8f7f9145a205206bcb152545a83add03ff1c7f7c8f7f9167b235306bcb373500883add03ff1c7f7c8f7f9127f03d346bcb05204dec3add03ef1c6f5c8f5f8107e01d244bcb172108881acd03ef0c6f4c8f5f8147a24d224bcb0201488a1acd03ff147f748f779107e0000063cb076145e832dd03ff1c7f7c8f7f9127f038106bcb377108c83add03ff1c7f7c8f7f9102c018046bcb17654dec3add03eb1c6b5c8b5f8142c258024bcb124148ca1ac903ff1c7f7c8f7f9142e058246bcb37754020120103ff1c7f7c8f7f9162f078346bcb37750000321103ff1c7f7c8f7f9147e25d266bcb37754522120103ff1c7f7c8f7f91673270306bcb377500083a1d03ff1c7f7c8f7f9162f030106bcb377500c832d9033b143b740b771167327532630b3731452a321903ff1c7f7c8f7f9126707d362a4927604dee2ac803ff1c7f7c8f7f9166f27d366acb36754dee224003ff1c7f7c8f7f9167727d366b4b27604dee080803ff1c7f7c8f7f9167627d366aca36744dee3a4d02ee1c6e7c8e7e8044a27c26488a14244cee188c03ff1c7f7c8f7f9166f07d362ac937754cec02c803ff1c7f7c8f7f9145f27d3649cb377540c01add01ff1c7f5c8f5f9144f05d3608c91775042012d903ff1c7f7c8f7f91))
def primitiveHints (i : ℕ) := Nat.land (Nat.shiftRight (primitiveHintsBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def unitCandidatesBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0x80000000000000000000000000000000400000000000000000000000000000002000000000000000000000000000000010000000000000000008840000000000000000000000000000000000060100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000080000000000000000000000000190000000000000000000000000000000000000000000000000000000000000000900010000000000000000000000000006080000000000000000000000000000000000000000000000010000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000400000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000048800000000000000000000000000000000000002a0000000000000000000000000000000018400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006200000000000000000000000000000000000000000000000000000000000000140200000000000000000000000000000860000000000000010000000000000000000000000000000000000001000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000100000000000000000000000000000000800000000000000020000000000000000000000000000000000000004000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000040000000000000000000000000000000000000010000000000000000000000000000000000008000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001 | false => (match Nat.blt i 2 with | true => 0x500000000000000400000000000000000300000000000000010000000000000000000000000000000000000000000000001400000000000000040000000000000000000000000000000000000000000000032000000000000000000000000000000000000000000000000000000000000000c20000000000000000000000000000000000000000000000000000000800000000000000000000000000000000002000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000008000000000000000000000000000000004000000000000000000000000000000000400000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000000000000000000000000000a008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180000002000000000000000000000000100010000800000000000000000000000000000000000000000000000000000004200000020000000000000000000000030004000000000000000000000000000000000000000000000000000000000000c400000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000008000000000000000000000000000000004000000000000000000000000000000010000000000000000000000000000000080000000000000000000000000000000400000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000008000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000200000000000000000001000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000 | false => 0x5000000000000080000000000000000008000002000000040000000000000000018000000100000000000000000000000030000000000000200000000000000000050000004000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000004000000000000000000000000000000004000000000000000000000000000000008000000000000000000000000000000020000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000242000000000000000000000))
def unitCandidates (i : ℕ) := Nat.land (Nat.shiftRight (unitCandidatesBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def crossCandidatesBlock (i : ℕ) : ℕ := (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x1ae2f77060000000000000000000000002024010000000000000000000000000000f18018000000000000000000000000000e0004000000009b0004a8100002e200000860000000004d84048c200002b400001402000000000000079f20000000000077060000000000000488000000000000000000000000000005e95c00000000006af00000000000000000019302b586081402000000000000000000a94ae3851008600000000000000000000002a00000000000000000000000000000000184000000000000000000000000000001fd906af0000000000000000000000001ae2f77060000000000000000000000000000000000000000000000000000000000006200000000000000000000000000000008600000000000000000000000000000140200000000985001e154000140000002d000000000642003000000010000000100000000000000030000000000000001000000000000000181000000000000020000000000000001404000000000000080000000000000000001942110aa2e2504000000000000000000681100600000800000000000000000000003a800006200000000000000000000000000a800200000000000000000000000000060000080000000000000000000000000202401000000000000000000000000000000620000000000000000000000000000000000000000000000000000000000000002d0000000000000000000000000000025040000000080000020000000400000000000000000c00e0020000000400000000800000000000003e3f6000000000003d800000000000000a0100000000000004000000000000000600400000000000010000000000000000001a3ccc607100028000000000000000000200840001000000000000000000000000000c200000020000000000000000000000000051000200000000000000000000000000090001000000000000000000000000000f1801800000000000000000000000000000860000000000000000000000000000002d00000000000000000000000000000000000000000000000000000000000001c6b000000001f8e000c30000036000000030000000004800004000000100000000000000000000000140000000000000004000000000000000c20000000000000020000000000000014ca000000000000050000000000000000001000100008000000000000000000000018c410000800010000000000000000000000340000000200000000000000000000000082080400000000000000000000000000fb6ea585000000000000000000000000000e0004000000000000000000000000000014020000000000000000000000000000250400000000000000000000000000001c6b00000000000000000000000000000000 | false => 0x1480200000000000000000000000000a04000010000000000000000000000006010000000000000000000000000000000340000008000000000000000000000a94ae385100860000000000000000000681100600000800000000000000000002008400010000000000000000000000018c410000800010000000003000000000000020000000000000000018400000000000400000000000000002da4001f2000003c000000060000000009000008000000200000000000000000035000000c00000a0000000000000000000000000003000400000000000000000000000000014802000000000000000000000000000000000000000000000000000000000081008004000000000000000000000000e158ca1d90003000000000000000000007200c000300000000000000000000000002a0000000000000000000000000000003a8000062000000000000000000000000c20000002000000000000000000000003400000002000000058301002000a148c2051000200000000a408100000180000002000000000000000001531400000000aa2e2504000000000001248800000001840000000000000000018840080000001900000000000000000000000180000002000000000000000000000000a04000010000000000000000000000008100800400000000000000000000000000000000000000000000000000000000000000190000000000000000000000000000000a22000000000000000000000000000184000000000000000000000000000000a800200000000000000000000000000005100020000000000000000000000000820804000000000580508860046018400090001000000003403298400260340000608000000000000000db40c200000060648180000000000000a9e154000000609002d000000000000088400000000000000000000000000000000001e4f4001b62800000000000000000000060100000000000000000000000000000e158ca1d900030000000000000000000000000190000000000000000000000000000000000000000000000000000000000000000608000000000000000000000000001fd906af00000000000000000000000006000008000000000000000000000000000900010000000000000000000000000fb6ea58500000007007e180006003c000001800000000002002010000000200000000000000000000000500000000000000400000000000000007003200000000005000000000000000018000200000000008000000000000000000000042000000200000000000000000000000034000000800000000000000000000007200c000300000000000000000000000000000a2200000000000000000000000000000060800000000000000000000000000000000000) | false => (match Nat.blt i 3 with | true => 0x320000000000000000000000000000000c2000000000000000000000a24a0501400142010000e00040000000324325800c208340000048000000000002da4001f2000003c00000006000000000001531400000000aa2e2504000000000000db40c20000006064818000000000000050000000000000040000000000000000079f20000000000077060000000000000300000000000000010000000000000003e3f6000000000003d80000000000000014000000000000000400000000180000001000000000000000000000000c04000020000000000000000000000000000003200000000000000000000000000000000000000000000000000000000000000154000000000000000000000a0d84200c2013003400080002000000051800200010080800000000000000000009000008000000200000000000000000000124880000000184000000000000000000a9e154000000609002d000000000000070032000000000050000000000000000048800000000000000000000000000000181000000000000020000000000000000a01000000000000040000000000000000c200000000000000200000000005000000400000000000000000000000032000002000000000000000000000000000000c20000000000000000000000000000015400000000000000000000000000000000000000000000000000000b00b218000a04f400000280000000000100100800000010000000000000000000035000000c00000a0000000000000000000188400800000019000000000000000000884000000000000000000000000000001800020000000000800000000000000005e95c00000000006af000000000000001404000000000000080000000000000006004000000000000100000000000000014ca000000000000050000000f038e00000003cc06000000000000000a0080000000000000000000000000000a24a0501400142010000e00040000000a0d84200c20130034000800020000000b00b218000a04f400000280000000000000000000000000000000000000000000000000000000c400000000000000000000000000000300040000000000000000000000000180000002000000000000000000000001e4f4001b628000000000000000000000042000000200000000000000000000019302b586081402000000000000000001942110aa2e2504000000000000000001a3ccc6071000280000000000000000001000100008000000000005000000000000080000000000000000030002000000000400000000000000000324325800c208340000048000000000051800200010080800000000000000000100100800000010000000000000000000000000000000c4000000000000000000000000000000000000000000 | false => 0xe00000000000000000000000000003c7e0003f60000000000000000000000180000001000000000000000000000000050000004000000000000000000000f038e00000003cc06000000000000000500000000000008000000000000000000030000000000000200000000000000058301002000a148c2051000200000000580508860046018400090001000000007007e180006003c0000018000000000009b0004a8100002e20000086000000000985001e154000140000002d000000000800000200000004000000000000000001f8e000c300000360000000300000000000e000000000000000000000000000000000000000000000000000000000000242000000000000000000000000000000c0400002000000000000000000000000032000002000000000000000000000a00800000000000000000000000000003000200000000040000000000000000000184000000000004000000000000000a4081000001800000020000000000000340329840026034000060800000000002002010000000200000000000000000004d84048c200002b4000014020000000064200300000001000000010000000000c00e0020000000400000000800000000048000040000001000000000000000003c7e0003f6000000000000000000000024200000000000000000000000000000000000000000000000000000))
def crossCandidates (i : ℕ) := Nat.land (Nat.shiftRight (crossCandidatesBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def pickPoint (x : ℕ) : PositiveId :=
  let j := 0
  let j := if x >>> (j+64) == 0 then j else j+64
  let j := if x >>> (j+32) == 0 then j else j+32
  let j := if x >>> (j+16) == 0 then j else j+16
  let j := if x >>> (j+8) == 0 then j else j+8
  let j := if x >>> (j+4) == 0 then j else j+4
  let j := if x >>> (j+2) == 0 then j else j+2
  let j := if x >>> (j+1) == 0 then j else j+1
  ⟨j % 100,by omega⟩
def rawGroups (e : ℕ) (i : Id) : ℕ × ℕ × ℕ :=
  if i.val < 11 then
    let zer := if i.val < 10 then incidence i.val else hotNum e
    let hit := if i.val < 10 then primitiveHints (10*e+i.val) else 0
    (zer <<< 11,hit <<< 11,0)
  else
    let r := i.val-11
    let record := rowHints (15*e+r)
    let neg := negNumber r ||| (if (hotNum e).testBit r then 1024 else 0)
    (neg,record &&& 1023,(record >>> 10) <<< 11)
def groupWord (e : ℕ) (i : Id) (mode : Fin 3) := if mode.val=0 then (rawGroups e i).1
  else if mode.val=1 then (rawGroups e i).2.1 else (rawGroups e i).2.2
def hinted (e : ℕ) : Link := fun mode i j => (groupWord e i mode).testBit j.val
def unitPoint (e : ℕ) (r : Fin 15) (z : FeatureId) : PositiveId :=
  let mask := if (hotNum e).testBit r.val then 1267650600228229401496703205375 else
    1267650600228229401496703205375 ^^^ pointNum e
  pickPoint (unitCandidates (10*r.val+z.val) &&& mask)
def crossPoint (e : ℕ) (r s : Fin 15) : PositiveId :=
  let mask := if (hotNum e).testBit r.val || (hotNum e).testBit s.val then 1267650600228229401496703205375 else
    1267650600228229401496703205375 ^^^ pointNum e
  pickPoint (crossCandidates (15*r.val+s.val) &&& mask)
def testLink (e : ℕ) (mode : Fin 3) (i j : Id) : Bool :=
  if !(hinted e mode i j) then true else
  match decodeId i,decodeId j with
  | .inl _,.inl _ => false
  | .inl z,.inr r | .inr r,.inl z =>
    if mode.val=0 then (modelNeg e r).testBit z.val else
    mode.val=1 && delta (modelPos e (unitPoint e r z)) (modelNeg e r) == 1 <<< z.val
  | .inr r,.inr s =>
    mode.val=2 && r != s && let u := crossPoint e r s
      bitSub (modelPos e u) (modelNeg e r ||| modelNeg e s)
lemma link_meaning {e : ℕ} {mode : Fin 3} {i j : Id} (ok : testLink e mode i j = true)
    (edge : hinted e mode i j = true) : generatedNet (modelNeg e) (modelPos e) mode i j = true := by
  simp only [testLink,edge,Bool.not_true,Bool.false_eq_true,↓reduceIte] at ok
  unfold generatedNet
  rcases ei : decodeId i with z | r <;> rcases ej : decodeId j with w | s <;>
    simp only [ei,ej] at ok ⊢
  · contradiction
  · split at ok
    · rename_i zer
      simpa only [zer,↓reduceIte] using ok
    · rename_i nz
      obtain ⟨one,rw⟩ := Bool.and_eq_true_iff.mp ok
      have one' := of_decide_eq_true one
      simp only [nz,one',↓reduceIte]
      exact List.any_eq_true.mpr ⟨unitPoint e s z,List.mem_finRange _,rw⟩
  · split at ok
    · rename_i zer
      simpa only [zer,↓reduceIte] using ok
    · rename_i nz
      obtain ⟨one,rw⟩ := Bool.and_eq_true_iff.mp ok
      have one' := of_decide_eq_true one
      simp only [nz,one',↓reduceIte]
      exact List.any_eq_true.mpr ⟨unitPoint e r w,List.mem_finRange _,rw⟩
  · obtain ⟨both,sub⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨two,ne⟩ := Bool.and_eq_true_iff.mp both
    apply Bool.and_eq_true_iff.mpr
    refine ⟨two,Bool.and_eq_true_iff.mpr ⟨ne,?_⟩⟩
    exact List.any_eq_true.mpr ⟨crossPoint e r s,List.mem_finRange _,sub⟩
lemma hint_valid {e : ℕ} {w O R} (ok : ∀ m i j, testLink e m i j = true)
    (h : encLayout (modelNeg e) (modelPos e) w O R) : linkValid (hinted e) w := by
  obtain ⟨z,u,c⟩ := generated_valid h
  exact ⟨fun i j a => z i j (link_meaning (ok _ _ _) a),fun i j a => u i j (link_meaning (ok _ _ _) a),
    fun i j a => c i j (link_meaning (ok _ _ _) a)⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn0 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((0*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn1 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((1*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn2 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((2*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn3 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((3*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn4 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((4*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn5 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((5*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn6 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((6*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn7 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((7*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn8 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((8*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn9 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((9*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn10 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((10*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn11 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((11*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn12 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((12*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn13 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((13*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn14 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((14*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn15 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((15*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn16 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((16*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn17 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((17*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn18 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((18*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn19 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((19*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn20 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((20*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn21 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((21*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn22 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((22*4+v.val) % 95) % 201) m i k = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma rn23 : ∀ v : Fin 4, ∀ m i k, testLink (routeEnv ((23*4+v.val) % 95) % 201) m i k = true := by decide +kernel
lemma chosenNet (c : RouteId) (m : Fin 3) (i j : Id) : testLink (mappedEnv c).val m i j = true := by
  have groups (g : Fin 24) : ∀ v : Fin 4, ∀ s k l, testLink (routeEnv ((g.val*4+v.val) % 95) % 201) s k l = true := by
    fin_cases g
    · exact rn0
    · exact rn1
    · exact rn2
    · exact rn3
    · exact rn4
    · exact rn5
    · exact rn6
    · exact rn7
    · exact rn8
    · exact rn9
    · exact rn10
    · exact rn11
    · exact rn12
    · exact rn13
    · exact rn14
    · exact rn15
    · exact rn16
    · exact rn17
    · exact rn18
    · exact rn19
    · exact rn20
    · exact rn21
    · exact rn22
    · exact rn23
  let g : Fin 24 := ⟨c.val/4,by omega⟩
  let v : Fin 4 := ⟨c.val % 4,by omega⟩
  have id : (g.val*4+v.val) % 95 = c.val := by dsimp [g,v]; omega
  simpa only [mappedEnv,id] using groups g v m i j
def col0 : ℕ := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def ncol0 : ℕ := 0x5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555
def col1 : ℕ := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def ncol1 : ℕ := 0x3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333
def col2 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def ncol2 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def col3 : ℕ := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def ncol3 : ℕ := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def col4 : ℕ := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def ncol4 : ℕ := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def col5 : ℕ := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def ncol5 : ℕ := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def col6 : ℕ := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def ncol6 : ℕ := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff
def col7 : ℕ := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
def ncol7 : ℕ := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff
def col8 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
def ncol8 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def col9 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def ncol9 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def growUp (d : ℕ) : ℕ :=
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol0) 1)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol1) 2)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol2) 4)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol3) 8)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol4) 16)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol5) 32)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol6) 64)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol7) 128)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol8) 256)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol9) 512)
  d
def growDown (d : ℕ) : ℕ :=
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col0) 1)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col1) 2)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col2) 4)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col3) 8)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col4) 16)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col5) 32)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col6) 64)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col7) 128)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col8) 256)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col9) 512)
  d
def bitMap00 (i : ℕ) : ℕ := Nat.mul (match Nat.blt i 16 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => 0x55555555) | false => (match Nat.blt i 3 with | true => 0x33333333 | false => 0x77777777)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0xf0f0f0f | false => 0x5f5f5f5f) | false => (match Nat.blt i 7 with | true => 0x3f3f3f3f | false => 0x7f7f7f7f))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0xff00ff | false => 0x55ff55ff) | false => (match Nat.blt i 11 with | true => 0x33ff33ff | false => 0x77ff77ff)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xfff0fff | false => 0x5fff5fff) | false => (match Nat.blt i 15 with | true => 0x3fff3fff | false => 0x7fff7fff)))) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 20 with | true => (match Nat.blt i 18 with | true => (match Nat.blt i 17 with | true => 0xffff | false => 0x5555ffff) | false => (match Nat.blt i 19 with | true => 0x3333ffff | false => 0x7777ffff)) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 21 with | true => 0xf0fffff | false => 0x5f5fffff) | false => (match Nat.blt i 23 with | true => 0x3f3fffff | false => 0x7f7fffff))) | false => (match Nat.blt i 28 with | true => (match Nat.blt i 26 with | true => (match Nat.blt i 25 with | true => 0xffffff | false => 0x55ffffff) | false => (match Nat.blt i 27 with | true => 0x33ffffff | false => 0x77ffffff)) | false => (match Nat.blt i 30 with | true => (match Nat.blt i 29 with | true => 0xfffffff | false => 0x5fffffff) | false => (match Nat.blt i 31 with | true => 0x3fffffff | false => 0x7fffffff))))) 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001
def bitMap05 (i : ℕ) : ℕ := (match Nat.blt i 16 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff) | false => (match Nat.blt i 3 with | true => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 7 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 11 with | true => 0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 15 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 20 with | true => (match Nat.blt i 18 with | true => (match Nat.blt i 17 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 19 with | true => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 21 with | true => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 23 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) | false => (match Nat.blt i 28 with | true => (match Nat.blt i 26 with | true => (match Nat.blt i 25 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 27 with | true => 0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) | false => (match Nat.blt i 30 with | true => (match Nat.blt i 29 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 31 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))))
def bitMap10 (i : ℕ) : ℕ := Nat.mul (match Nat.blt i 16 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => 0xaaaaaaaa) | false => (match Nat.blt i 3 with | true => 0xcccccccc | false => 0xeeeeeeee)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0xf0f0f0f0 | false => 0xfafafafa) | false => (match Nat.blt i 7 with | true => 0xfcfcfcfc | false => 0xfefefefe))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0xff00ff00 | false => 0xffaaffaa) | false => (match Nat.blt i 11 with | true => 0xffccffcc | false => 0xffeeffee)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xfff0fff0 | false => 0xfffafffa) | false => (match Nat.blt i 15 with | true => 0xfffcfffc | false => 0xfffefffe)))) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 20 with | true => (match Nat.blt i 18 with | true => (match Nat.blt i 17 with | true => 0xffff0000 | false => 0xffffaaaa) | false => (match Nat.blt i 19 with | true => 0xffffcccc | false => 0xffffeeee)) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 21 with | true => 0xfffff0f0 | false => 0xfffffafa) | false => (match Nat.blt i 23 with | true => 0xfffffcfc | false => 0xfffffefe))) | false => (match Nat.blt i 28 with | true => (match Nat.blt i 26 with | true => (match Nat.blt i 25 with | true => 0xffffff00 | false => 0xffffffaa) | false => (match Nat.blt i 27 with | true => 0xffffffcc | false => 0xffffffee)) | false => (match Nat.blt i 30 with | true => (match Nat.blt i 29 with | true => 0xfffffff0 | false => 0xfffffffa) | false => (match Nat.blt i 31 with | true => 0xfffffffc | false => 0xfffffffe))))) 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001
def bitMap15 (i : ℕ) : ℕ := (match Nat.blt i 16 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) | false => (match Nat.blt i 3 with | true => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) | false => (match Nat.blt i 7 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) | false => (match Nat.blt i 11 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) | false => (match Nat.blt i 15 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000)))) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 20 with | true => (match Nat.blt i 18 with | true => (match Nat.blt i 17 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) | false => (match Nat.blt i 19 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000)) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 21 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) | false => (match Nat.blt i 23 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000))) | false => (match Nat.blt i 28 with | true => (match Nat.blt i 26 with | true => (match Nat.blt i 25 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) | false => (match Nat.blt i 27 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000)) | false => (match Nat.blt i 30 with | true => (match Nat.blt i 29 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) | false => (match Nat.blt i 31 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000)))))
def signTableUp (m : ℕ) : ℕ := Nat.lor (bitMap10 (Nat.land m 31)) (bitMap15 (Nat.shiftRight m 5))
def signTableDn (m : ℕ) : ℕ := Nat.lor (bitMap00 (Nat.land m 31)) (bitMap05 (Nat.shiftRight m 5))
def hiBit (x : ℕ) : ℕ :=
  let j := match Nat.beq (Nat.shiftRight x 512) 0 with | true => 0 | false => 512
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 256)) 0 with | true => j | false => Nat.add j 256
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 128)) 0 with | true => j | false => Nat.add j 128
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 64)) 0 with | true => j | false => Nat.add j 64
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 32)) 0 with | true => j | false => Nat.add j 32
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 16)) 0 with | true => j | false => Nat.add j 16
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 8)) 0 with | true => j | false => Nat.add j 8
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 4)) 0 with | true => j | false => Nat.add j 4
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 2)) 0 with | true => j | false => Nat.add j 2
  match Nat.beq (Nat.shiftRight x (Nat.add j 1)) 0 with | true => j | false => Nat.add j 1
def spanUp (d : ℕ) := Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (if overlaps d col0 then 1 else 0)) (if overlaps d col1 then 2 else 0)) (if overlaps d col2 then 4 else 0)) (if overlaps d col3 then 8 else 0)) (if overlaps d col4 then 16 else 0)) (if overlaps d col5 then 32 else 0)) (if overlaps d col6 then 64 else 0)) (if overlaps d col7 then 128 else 0)) (if overlaps d col8 then 256 else 0)) (if overlaps d col9 then 512 else 0)
def spanDown (d : ℕ) := Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (if overlaps d ncol0 then 1 else 0)) (if overlaps d ncol1 then 2 else 0)) (if overlaps d ncol2 then 4 else 0)) (if overlaps d ncol3 then 8 else 0)) (if overlaps d ncol4 then 16 else 0)) (if overlaps d ncol5 then 32 else 0)) (if overlaps d ncol6 then 64 else 0)) (if overlaps d ncol7 then 128 else 0)) (if overlaps d ncol8 then 256 else 0)) (if overlaps d ncol9 then 512 else 0)
def rapidGrow (b : Bool) (d : ℕ) := if b then growUp d else growDown d
def rapidSpan (b : Bool) (d : ℕ) := if b then spanUp d else spanDown d
def rapidSign (b : Bool) (x : ℕ) := if b then signTableUp x else signTableDn x
lemma rapidGrow_eq (b : Bool) (d : ℕ) : rapidGrow b d = grow b d := by cases b <;> rfl
lemma rapidSpan_eq (b : Bool) (d : ℕ) : rapidSpan b d = spanBits d b := by cases b <;> rfl
set_option maxRecDepth 10000 in
lemma rapidSign_eq : ∀ b (x : Fin 1024), rapidSign b x.val = someBits x.val b := by decide +kernel
def simpleParts (d : ℕ) (b : Bool) : ℕ × ℕ :=
  let item := hiBit d
  if item < 1024 && d == 1 <<< item then
    let z := if b then item else 1023-item
    (allWords ^^^ rapidSign (!b) z,z)
  else (rapidGrow b d,rapidSpan b d)
def fastParts (d : ℕ) (b : Bool) :=
  match Nat.beq (Nat.land d (d-1)) 0 with
  | true => simpleParts d b
  | false => (rapidGrow b d,rapidSpan b d)
def singleCorrect (b : Bool) (x : ℕ) : Prop :=
  let z := if b then x else 1023-x
  (allWords ^^^ rapidSign (!b) z,z) = (upperSet x b,spanBits (1 <<< x) b)
set_option maxRecDepth 10000 in
private lemma single0 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (0*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single1 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (1*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single2 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (2*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single3 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (3*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single4 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (4*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single5 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (5*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single6 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (6*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single7 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (7*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single8 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (8*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single9 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (9*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single10 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (10*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single11 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (11*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single12 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (12*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single13 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (13*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single14 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (14*64+x.val) := by unfold singleCorrect; decide +kernel
set_option maxRecDepth 10000 in
private lemma single15 : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (15*64+x.val) := by unfold singleCorrect; decide +kernel
lemma singletonParts : ∀ b : Bool, ∀ x : Fin 1024,
    let z := if b then x.val else 1023-x.val
    (allWords ^^^ rapidSign (!b) z,z) = (grow b (1 <<< x.val),spanBits (1 <<< x.val) b) := by
  intro b x
  rw [Nat.one_shiftLeft,grow_one]
  have every (k : Fin 16) : ∀ b : Bool, ∀ x : Fin 64, singleCorrect b (k.val*64+x.val) := by
    fin_cases k
    · exact single0
    · exact single1
    · exact single2
    · exact single3
    · exact single4
    · exact single5
    · exact single6
    · exact single7
    · exact single8
    · exact single9
    · exact single10
    · exact single11
    · exact single12
    · exact single13
    · exact single14
    · exact single15
  let k : Fin 16 := ⟨x.val/64,by omega⟩
  let v : Fin 64 := ⟨x.val % 64,by omega⟩
  have val : k.val*64+v.val=x.val := by dsimp [k,v]; omega
  have good := every k b v
  rw [val] at good
  simpa only [singleCorrect,Nat.one_shiftLeft] using good
lemma swapped_bounded : ∀ v : Fin 1024, swapWord v.val < 1024 := by
  decide +kernel
lemma boundedSign (b : Bool) (x : ℕ) (bd : x<1024) :
    rapidSign b x = someBits x b := rapidSign_eq b ⟨x,bd⟩
def quickCross (x : ℕ) := rapidSign false (swapWord (rapidSpan false x))
lemma quickCross_eq (x : ℕ) : quickCross x = someBits (swapWord (spanBits x false)) false := by
  unfold quickCross
  rw [rapidSpan_eq]
  apply boundedSign
  exact swapped_bounded ⟨spanBits x false,vectorBits_lt _ 10⟩
lemma simpleParts_eq (d : ℕ) (b : Bool) : simpleParts d b = (grow b d,spanBits d b) := by
  by_cases ex : (decide (hiBit d < 1024) && (d == 1 <<< hiBit d)) = true
  · obtain ⟨bd,eq⟩ := Bool.and_eq_true_iff.mp ex
    let v : Fin 1024 := ⟨hiBit d,of_decide_eq_true bd⟩
    simp only [simpleParts,ex,↓reduceIte]
    exact (singletonParts b v).trans (congrArg (fun n => (grow b n,spanBits n b)) (beq_iff_eq.mp eq).symm)
  · simp only [simpleParts,ex,Bool.false_eq_true,↓reduceIte,rapidGrow_eq,rapidSpan_eq]
lemma fastParts_eq (d : ℕ) (b : Bool) : fastParts d b = (grow b d,spanBits d b) := by
  unfold fastParts
  split
  · exact simpleParts_eq d b
  · exact Prod.ext (rapidGrow_eq b d) (rapidSpan_eq b d)
def reuseCross (x : ℕ) : Bool → ℕ → ℕ
  | true,_ => quickCross x
  | false,z => rapidSign false (swapWord z)
lemma reuseCross_ok (x : ℕ) : ∀ b z, z = rapidSpan b x → reuseCross x b z = quickCross x
  | true,_,_ => Eq.refl (quickCross x)
  | false,_,h => congrArg (fun z => rapidSign false (swapWord z)) h
lemma reuseCross_eq (x : ℕ) (b : Bool) :
    reuseCross x b (fastParts x b).2 = someBits (swapWord (spanBits x false)) false := by
  have h : (fastParts x b).2 = rapidSpan b x :=
    (congrArg Prod.snd (fastParts_eq x b)).trans (rapidSpan_eq b x).symm
  exact (reuseCross_ok x b _ h).trans (quickCross_eq x)
def trimWord (w : ℕ) := Nat.land fieldMask (Nat.xor fieldMask w)
abbrev Chart := Id → ℕ × ℕ × ℕ
def lanesFor (net : Link) (i : Id) (mode : Fin 3) := strideFlags (List.ofFn (net mode i))
def chartOf (net : Link) : Chart := fun i => (lanesFor net i 0,lanesFor net i 1,lanesFor net i 2)
def quickCut (table : Chart) (d : ℕ) (i : Id) : ℕ :=
  let fields := table i
  let x := laneRead d i.val
  let b := orientation i
  let p := fastParts x b
  let one := if fields.1 == 0 then 0 else Nat.mul (trimWord p.1) fields.1
  let two := if fields.2.1 == 0 then 0 else Nat.mul (trimWord (rapidSign (!b) p.2)) fields.2.1
  let three := if fields.2.2 == 0 then 0 else
    Nat.mul (trimWord (reuseCross x b p.2)) fields.2.2
  Nat.lor (Nat.lor one two) three
lemma mul_empty (a b : ℕ) : (if b == 0 then 0 else Nat.mul a b) = a*b := by
  by_cases eq : b=0 <;> simp [eq]
lemma fastJoin_direct (d : ℕ) (b : Bool) :
    rapidSign (!b) (fastParts d b).2 = someBits (spanBits d b) (!b) := by
  have ok := congrArg Prod.snd (fastParts_eq d b)
  exact (congrArg (rapidSign (!b)) ok).trans (rapidSign_eq (!b) ⟨_,vectorBits_lt _ 10⟩)
lemma quickCut_eq (net : Link) (d : ℕ) (i : Id) :
    quickCut (chartOf net) d i = sourceCut net d i := by
  let x := laneRead d i.val
  let b := orientation i
  let f := chartOf net i
  let u := fastParts x b
  let g := grow b x
  have fst : u.1 = g := congrArg Prod.fst (fastParts_eq x b)
  have one : (if f.1 == 0 then 0 else Nat.mul (trimWord u.1) f.1) =
      trimWord g * f.1 :=
    (mul_empty _ _).trans (congrArg (fun z => trimWord z * f.1) fst)
  have two : (if f.2.1 == 0 then 0 else Nat.mul (trimWord (rapidSign (!b) u.2)) f.2.1) =
      trimWord (someBits (spanBits x b) (!b)) * f.2.1 :=
    (mul_empty _ _).trans (congrArg (fun z => trimWord z * f.2.1) (fastJoin_direct x b))
  have three : (if f.2.2 == 0 then 0 else Nat.mul (trimWord (reuseCross x b u.2)) f.2.2) =
      trimWord (someBits (swapWord (spanBits x false)) false) * f.2.2 :=
    (mul_empty _ _).trans (congrArg (fun z => trimWord z * f.2.2) (reuseCross_eq x b))
  exact congrArg₂ Nat.lor (congrArg₂ Nat.lor one two) three
def laneBase : ℕ := 1 <<< 1025
def spacedFlags (x : ℕ) := Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (0)) (x.testBit 25).toNat)) (x.testBit 24).toNat)) (x.testBit 23).toNat)) (x.testBit 22).toNat)) (x.testBit 21).toNat)) (x.testBit 20).toNat)) (x.testBit 19).toNat)) (x.testBit 18).toNat)) (x.testBit 17).toNat)) (x.testBit 16).toNat)) (x.testBit 15).toNat)) (x.testBit 14).toNat)) (x.testBit 13).toNat)) (x.testBit 12).toNat)) (x.testBit 11).toNat)) (x.testBit 10).toNat)) (x.testBit 9).toNat)) (x.testBit 8).toNat)) (x.testBit 7).toNat)) (x.testBit 6).toNat)) (x.testBit 5).toNat)) (x.testBit 4).toNat)) (x.testBit 3).toNat)) (x.testBit 2).toNat)) (x.testBit 1).toNat)) (x.testBit 0).toNat
set_option maxRecDepth 10000 in
lemma spacedFlags_eq (x : ℕ) : spacedFlags x = strideFlags (List.ofFn fun j : Id => x.testBit j.val) := by rfl
def directId {α : Type} (f : Id → α) (j : Id) : α :=
  let i := j.val
  (match Nat.blt i 13 with | true => (match Nat.blt i 6 with | true => (match Nat.blt i 3 with | true => (match Nat.blt i 1 with | true => f 0 | false => (match Nat.blt i 2 with | true => f 1 | false => f 2)) | false => (match Nat.blt i 4 with | true => f 3 | false => (match Nat.blt i 5 with | true => f 4 | false => f 5))) | false => (match Nat.blt i 9 with | true => (match Nat.blt i 7 with | true => f 6 | false => (match Nat.blt i 8 with | true => f 7 | false => f 8)) | false => (match Nat.blt i 11 with | true => (match Nat.blt i 10 with | true => f 9 | false => f 10) | false => (match Nat.blt i 12 with | true => f 11 | false => f 12)))) | false => (match Nat.blt i 19 with | true => (match Nat.blt i 16 with | true => (match Nat.blt i 14 with | true => f 13 | false => (match Nat.blt i 15 with | true => f 14 | false => f 15)) | false => (match Nat.blt i 17 with | true => f 16 | false => (match Nat.blt i 18 with | true => f 17 | false => f 18))) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 20 with | true => f 19 | false => (match Nat.blt i 21 with | true => f 20 | false => f 21)) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 23 with | true => f 22 | false => f 23) | false => (match Nat.blt i 25 with | true => f 24 | false => f 25)))))
lemma directId_eq {α : Type} (f : Id → α) (j : Id) : directId f j = f j := by fin_cases j <;> rfl
def readyChart (e : ℕ) : Chart := directId fun i =>
  let groups := rawGroups e i
  (spacedFlags groups.1,spacedFlags groups.2.1,spacedFlags groups.2.2)
lemma readyChart_eq (e : ℕ) : readyChart e = chartOf (hinted e) := by
  funext i
  rw [readyChart,directId_eq]
  simp only [spacedFlags_eq]
  rfl
def allLanes : ℕ := spacedFlags 67108863
def guardBits : ℕ := allLanes <<< 1024
def lowBits : ℕ := Nat.mul allWords allLanes
def dirtyBits (x : ℕ) := Nat.land (Nat.add x lowBits) guardBits
def chooseSource (q : ℕ) : Id :=
  (match Nat.blt q (Nat.shiftLeft 1 14349) with | true => (match Nat.blt q (Nat.shiftLeft 1 7174) with | true => (match Nat.blt q (Nat.shiftLeft 1 4099) with | true => (match Nat.blt q (Nat.shiftLeft 1 2049) with | true => 0 | false => (match Nat.blt q (Nat.shiftLeft 1 3074) with | true => 1 | false => 2)) | false => (match Nat.blt q (Nat.shiftLeft 1 5124) with | true => 3 | false => (match Nat.blt q (Nat.shiftLeft 1 6149) with | true => 4 | false => 5))) | false => (match Nat.blt q (Nat.shiftLeft 1 10249) with | true => (match Nat.blt q (Nat.shiftLeft 1 8199) with | true => 6 | false => (match Nat.blt q (Nat.shiftLeft 1 9224) with | true => 7 | false => 8)) | false => (match Nat.blt q (Nat.shiftLeft 1 12299) with | true => (match Nat.blt q (Nat.shiftLeft 1 11274) with | true => 9 | false => 10) | false => (match Nat.blt q (Nat.shiftLeft 1 13324) with | true => 11 | false => 12)))) | false => (match Nat.blt q (Nat.shiftLeft 1 20499) with | true => (match Nat.blt q (Nat.shiftLeft 1 17424) with | true => (match Nat.blt q (Nat.shiftLeft 1 15374) with | true => 13 | false => (match Nat.blt q (Nat.shiftLeft 1 16399) with | true => 14 | false => 15)) | false => (match Nat.blt q (Nat.shiftLeft 1 18449) with | true => 16 | false => (match Nat.blt q (Nat.shiftLeft 1 19474) with | true => 17 | false => 18))) | false => (match Nat.blt q (Nat.shiftLeft 1 23574) with | true => (match Nat.blt q (Nat.shiftLeft 1 21524) with | true => 19 | false => (match Nat.blt q (Nat.shiftLeft 1 22549) with | true => 20 | false => 21)) | false => (match Nat.blt q (Nat.shiftLeft 1 25624) with | true => (match Nat.blt q (Nat.shiftLeft 1 24599) with | true => 22 | false => 23) | false => (match Nat.blt q (Nat.shiftLeft 1 26649) with | true => 24 | false => 25)))))
def repeatWord (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => Nat.lor 1 (Nat.shiftLeft (repeatWord k n) k)
def denseSpread (x : ℕ) := Nat.land (Nat.mul (Nat.land x 67108863) (repeatWord 1024 26)) allLanes
def denseChart (e : ℕ) : Chart := directId fun i =>
  let g := rawGroups e i
  (denseSpread g.1,denseSpread g.2.1,denseSpread g.2.2)
def sameChart (e : ℕ) : Bool := (List.finRange 26).all fun i => denseChart e i == readyChart e i
lemma chartCert {e : ℕ} (h : sameChart e = true) : denseChart e = chartOf (hinted e) := by
  rw [←readyChart_eq]
  funext i
  exact beq_iff_eq.mp (List.all_eq_true.mp h i (List.mem_finRange i))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc0 : ∀ v : Fin 16, sameChart ((0*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc1 : ∀ v : Fin 16, sameChart ((1*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc2 : ∀ v : Fin 16, sameChart ((2*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc3 : ∀ v : Fin 16, sameChart ((3*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc4 : ∀ v : Fin 16, sameChart ((4*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc5 : ∀ v : Fin 16, sameChart ((5*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc6 : ∀ v : Fin 16, sameChart ((6*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc7 : ∀ v : Fin 16, sameChart ((7*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc8 : ∀ v : Fin 16, sameChart ((8*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc9 : ∀ v : Fin 16, sameChart ((9*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc10 : ∀ v : Fin 16, sameChart ((10*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc11 : ∀ v : Fin 16, sameChart ((11*16+v.val) % 201)=true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma sc12 : ∀ v : Fin 16, sameChart ((12*16+v.val) % 201)=true := by decide +kernel
lemma correctChart (e : Fin 201) : denseChart e.val = chartOf (hinted e.val) := by
  apply chartCert
  let k : Fin 13 := ⟨e.val/16,by omega⟩
  let v : Fin 16 := ⟨e.val % 16,by omega⟩
  have eq : (k.val*16+v.val) % 201=e.val := by dsimp [k,v]; omega
  have group (j : Fin 13) : ∀ x : Fin 16, sameChart ((j.val*16+x.val) % 201)=true := by
    fin_cases j
    · exact sc0
    · exact sc1
    · exact sc2
    · exact sc3
    · exact sc4
    · exact sc5
    · exact sc6
    · exact sc7
    · exact sc8
    · exact sc9
    · exact sc10
    · exact sc11
    · exact sc12
  exact eq ▸ group k v
def maskFlag (x m weight : ℕ) :=
  match Nat.beq (Nat.land x m) 0 with | true => 0 | false => weight
lemma maskFlag_eq (x m weight : ℕ) : maskFlag x m weight = (if overlaps x m then weight else 0) := by
  change (match ((x &&& m) == 0) with | true => 0 | false => weight) = (if !((x &&& m) == 0) then weight else 0)
  cases h : ((x &&& m) == 0) <;> rfl
def projectionPositive (x : ℕ) : ℕ := Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (maskFlag x col0 1)) (maskFlag x col1 2)) (maskFlag x col2 4)) (maskFlag x col3 8)) (maskFlag x col4 16)) (maskFlag x col5 32)) (maskFlag x col6 64)) (maskFlag x col7 128)) (maskFlag x col8 256)) (maskFlag x col9 512)
lemma projectionPositive_eq (x : ℕ) : projectionPositive x = spanUp x := by simp only [projectionPositive,spanUp,maskFlag_eq]
def projectionNegative (x : ℕ) : ℕ := Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (maskFlag x ncol0 1)) (maskFlag x ncol1 2)) (maskFlag x ncol2 4)) (maskFlag x ncol3 8)) (maskFlag x ncol4 16)) (maskFlag x ncol5 32)) (maskFlag x ncol6 64)) (maskFlag x ncol7 128)) (maskFlag x ncol8 256)) (maskFlag x ncol9 512)
lemma projectionNegative_eq (x : ℕ) : projectionNegative x = spanDown x := by simp only [projectionNegative,spanDown,maskFlag_eq]
def tightParts (x : ℕ) (b : Bool) : ℕ × ℕ :=
  match Nat.beq (Nat.land x (x-1)) 0 with
  | true => simpleParts x b
  | false =>
    match b with
    | true => (growUp x,projectionPositive x)
    | false => (growDown x,projectionNegative x)
lemma tightParts_eq (x : ℕ) (b : Bool) : tightParts x b = fastParts x b := by
  cases c : Nat.beq (Nat.land x (x-1)) 0
  · cases b <;> simp only [tightParts,fastParts,c,rapidGrow,rapidSpan,projectionPositive_eq,projectionNegative_eq,Bool.false_eq_true,↓reduceIte]
  · simp only [tightParts,fastParts,c]
def weighted (m f : ℕ) := match Nat.beq f 0 with | true => 0 | false => Nat.mul m f
lemma weighted_eq (x f : ℕ) : weighted x f = Nat.mul x f := by
  by_cases h : f=0
  · subst f; simp [weighted]
  · have hf : Nat.beq f 0=false := beq_eq_false_iff_ne.mpr h
    simp only [weighted,hf]
lemma weighted_if (m f : ℕ) : weighted m f = (if f == 0 then 0 else Nat.mul m f) :=
  (weighted_eq m f).trans (mul_empty m f).symm
def tightCut (net : Chart) (d : ℕ) (i : Id) : ℕ :=
  let f := net i
  let x := laneRead d i.val
  let b := orientation i
  let p := tightParts x b
  Nat.lor (Nat.lor (weighted (trimWord p.1) f.1)
    (weighted (trimWord (rapidSign (!b) p.2)) f.2.1))
    (weighted (trimWord (reuseCross x b p.2)) f.2.2)
lemma tightCut_eq (net : Chart) (d : ℕ) (i : Id) : tightCut net d i = quickCut net d i := by
  simp only [tightCut,quickCut,tightParts_eq,weighted_if]
def laneReadRaw (d i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight d (Nat.mul 1025 i)) fieldMask
def rawLoop (step : ℕ → Id → ℕ) (source : ℕ → Id) (changed : ℕ → ℕ) (high : ℕ) :
    ℕ → ℕ → ℕ → ℕ
  | 0,d,_ => d
  | fuel+1,d,q =>
    match Nat.beq q 0 with
    | true => d
    | false =>
      let i := source q
      let flag := Nat.shiftLeft 1 (Nat.add (Nat.mul 1025 i.val) 1024)
      let pending := Nat.xor q flag
      let del := Nat.land d (step d i)
      match Nat.beq del 0 with
      | true => rawLoop step source changed high fuel d pending
      | false =>
        let next := Nat.xor d del
        let empty := Nat.xor high (changed next)
        let stop := !(Nat.beq empty 0) && Nat.beq (laneRead next (source empty).val) 0
        match stop with
        | true => 0
        | false => rawLoop step source changed high fuel next (Nat.lor pending (changed del))
lemma rawLoop_keeps {w : Valuation} {step : ℕ → Id → ℕ} {source : ℕ → Id} {changed : ℕ → ℕ} {high : ℕ}
    (pres : ∀ d, insidePacked d w → ∀ i, insidePacked (restrictPacked d (step d i)) w)
    (fuel d q : ℕ) (ok : insidePacked d w) : insidePacked (rawLoop step source changed high fuel d q) w := by
  induction fuel generalizing d q with
  | zero => exact ok
  | succ fuel ih =>
    simp only [rawLoop]
    split
    · exact ok
    · try dsimp only
      split
      · exact ih _ _ ok
      · try dsimp only
        have now := pres d ok (source q)
        split
        · rename_i stop
          obtain ⟨_,empty⟩ := Bool.and_eq_true_iff.mp stop
          have hit := heldLane now (source (high ^^^ changed (restrictPacked d (step d (source q)))))
          change (laneRead _ _).testBit _ = true at hit
          change (laneRead _ _ == 0) = true at empty
          simp only [beq_iff_eq] at empty
          change laneRead (restrictPacked d (step d (source q))) _ = 0 at empty
          change laneRead (restrictPacked d (step d (source q)))
            (source (high ^^^ changed (restrictPacked d (step d (source q))))).val = 0 at empty
          rw [empty] at hit
          simp at hit
        · exact ih _ _ now
def directSettle (e : ℕ) := rawLoop (tightCut (denseChart e)) chooseSource dirtyBits guardBits 400
lemma directSettle_ok {e : Fin 201} {w O R} (h : encLayout (modelNeg e) (modelPos e) w O R)
    (tested : ∀ m i j, testLink e m i j=true) (d q : ℕ) (ok : insidePacked d w) :
    insidePacked (directSettle e d q) w := by
  apply rawLoop_keeps _ _ _ _ ok
  intro val hv i
  rw [tightCut_eq,correctChart e,quickCut_eq]
  exact sourceCut_keep hv (hint_valid tested h) i
def colByIdx (s : ℕ) : ℕ :=
  match Nat.blt s 5 with
  | true =>
    match Nat.blt s 2 with
    | true => (match Nat.beq s 0 with | true => col0 | false => col1)
    | false => (match Nat.blt s 4 with | true => (match Nat.beq s 2 with | true => col2 | false => col3) | false => col4)
  | false =>
    match Nat.blt s 7 with
    | true => (match Nat.beq s 5 with | true => col5 | false => col6)
    | false => (match Nat.blt s 9 with | true => (match Nat.beq s 7 with | true => col7 | false => col8) | false => col9)
def pairNeg0 : ℕ := Nat.lor ncol0 ncol1
def pairNeg1 : ℕ := Nat.lor ncol2 ncol3
def pairNeg2 : ℕ := Nat.lor ncol4 ncol5
def pairNeg3 : ℕ := Nat.lor ncol6 ncol7
def pairNeg4 : ℕ := Nat.lor ncol8 ncol9
def pairNegByIdx (k : ℕ) : ℕ :=
  match Nat.blt k 2 with
  | true => match Nat.beq k 0 with | true => pairNeg0 | false => pairNeg1
  | false => match Nat.blt k 4 with
    | true => match Nat.beq k 2 with | true => pairNeg2 | false => pairNeg3
    | false => pairNeg4
set_option maxRecDepth 20000 in
lemma colByIdx_ok : ∀ s : Slot, colByIdx (slotNum s) = column (slotNum s) := by decide +kernel
set_option maxRecDepth 20000 in
lemma pairNegByIdx_ok : ∀ k : Fin 5, pairNegByIdx k.val = someBits (pairBits k) false := by decide +kernel
def popBelow5 (on k : ℕ) : ℕ :=
  let m := Nat.land on (Nat.sub (Nat.shiftLeft 1 k) 1)
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.land m 1) (Nat.land (Nat.shiftRight m 1) 1))
    (Nat.land (Nat.shiftRight m 2) 1)) (Nat.land (Nat.shiftRight m 3) 1))
    (Nat.land (Nat.shiftRight m 4) 1)
def witnessRowFast (byte : ℕ → ℕ) (t on count k j : ℕ) : ℕ :=
  let before := popBelow5 on k
  let off := match Nat.testBit on k with | true => 0 | false => popBelow5 on j
  let idx := Nat.add (Nat.add before (Nat.mul (Nat.sub k before) count)) off
  let nib := Nat.land (Nat.shiftRight (byte (Nat.add (Nat.add t 3) (Nat.shiftRight idx 1))) (Nat.shiftLeft (Nat.land idx 1) 2)) 15
  Nat.mod nib 15
def scanDown (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => match f n with | true => scanDown f n | false => false
lemma scanDown_at {f : ℕ → Bool} {n : ℕ} (ok : scanDown f n = true) {k : ℕ} (lt : k < n) : f k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases e : f n
    · simp [scanDown,e] at ok
    · by_cases eq : k=n
      · simpa only [eq] using e
      · exact ih (by simpa only [scanDown,e] using ok) (by omega)
def checkRawLoop (d u colMask : ℕ) := scanDown fun z =>
  match Nat.testBit u z with
  | false => true
  | true => Nat.beq (Nat.land (laneReadRaw d z) colMask) 0
def checkArcLoop (byte : ℕ → ℕ) (t on count d colMask k : ℕ) := scanDown fun j =>
  match Nat.testBit on j with
  | false => true
  | true =>
    let r := witnessRowFast byte t on count k j
    Nat.beq (Nat.land (laneReadRaw d (Nat.add 11 r)) (Nat.lor colMask (pairNegByIdx j))) 0
def checkGraphLoop (byte : ℕ → ℕ) (t on sw count d u : ℕ) := scanDown fun k =>
  match Nat.testBit on k with
  | true =>
    let r := witnessRowFast byte t on count k 0
    Nat.beq (Nat.land (laneReadRaw d (Nat.add 11 r)) (pairNegByIdx k)) 0
  | false =>
    let s := Nat.add (Nat.shiftLeft k 1) (sw.testBit k).toNat
    let colMask := colByIdx s
    checkRawLoop d u colMask 11 && checkArcLoop byte t on count d colMask k 5
def readLeafFast (pos : PositiveId → ℕ) (byte : ℕ → ℕ) (d tag t : ℕ) : ℕ :=
  let uIdx := Nat.sub tag 26
  if h : uIdx < 100 then
    let on := byte (Nat.add t 1)
    let sw := byte (Nat.add t 2)
    let count := popBelow5 on 5
    match checkGraphLoop byte t on sw count d (pos ⟨uIdx, h⟩) 5 with
    | true => Nat.add (Nat.add t 3) (Nat.shiftRight (Nat.add (Nat.add count (Nat.mul (Nat.sub 5 count) count)) 1) 1)
    | false => 0
  else 0
def sideMaskFast (neg : Bool) (k : ℕ) : ℕ :=
  match neg with
  | true =>
    match k with
    | 0 => sideMask true 0 | 1 => sideMask true 1 | 2 => sideMask true 2 | 3 => sideMask true 3 | _ => sideMask true 4
  | false =>
    match k with
    | 0 => sideMask false 0 | 1 => sideMask false 1 | 2 => sideMask false 2 | 3 => sideMask false 3 | _ => sideMask false 4
def orderMaskFast (neg : Bool) (k : ℕ) : ℕ :=
  match neg with
  | true =>
    match k with
    | 0 => orderMask true 0 | 1 => orderMask true 1 | 2 => orderMask true 2 | 3 => orderMask true 3 | _ => orderMask true 4
  | false =>
    match k with
    | 0 => orderMask false 0 | 1 => orderMask false 1 | 2 => orderMask false 2 | 3 => orderMask false 3 | _ => orderMask false 4
def canonDomainFast (eq fl : ℕ) (neg : Bool) : ℕ :=
  let a := fieldMask
  let a := match Nat.testBit fl 0 with | true => Nat.land a (sideMaskFast neg 0) | false => a
  let a := match Nat.testBit fl 1 with | true => Nat.land a (sideMaskFast neg 1) | false => a
  let a := match Nat.testBit eq 1 with | true => Nat.land a (orderMaskFast neg 1) | false => a
  let a := match Nat.testBit fl 2 with | true => Nat.land a (sideMaskFast neg 2) | false => a
  let a := match Nat.testBit eq 2 with | true => Nat.land a (orderMaskFast neg 2) | false => a
  let a := match Nat.testBit fl 3 with | true => Nat.land a (sideMaskFast neg 3) | false => a
  let a := match Nat.testBit eq 3 with | true => Nat.land a (orderMaskFast neg 3) | false => a
  let a := match Nat.testBit fl 4 with | true => Nat.land a (sideMaskFast neg 4) | false => a
  match Nat.testBit eq 4 with | true => Nat.land a (orderMaskFast neg 4) | false => a
lemma maskNo {x y : ℕ} (h : Nat.beq (Nat.land x y) 0 = true) : !overlaps x y = true := by
  change (x &&& y == 0) = true at h
  simp [overlaps,beq_iff_eq.mp h]
lemma checkGraph_sound (byte : ℕ → ℕ) (t on sw count d u : ℕ)
    (h : checkGraphLoop byte t on sw count d u 5 = true) :
    ∃ rr, graphLeaf d u on sw rr = true := by
  let rr (k j : Fin 5) : Fin 15 := ⟨witnessRowFast byte t on count k.val j.val,Nat.mod_lt _ (by decide)⟩
  refine ⟨rr,List.all_eq_true.mpr ?_⟩
  intro k _
  have hk := @scanDown_at _ 5 h k.val k.isLt
  cases e : on.testBit k.val with
  | true =>
    simp only [e,↓reduceIte] at hk ⊢
    change barredRoot d (rr k 0) k = true
    unfold barredRoot
    rw [←pairNegByIdx_ok]
    exact maskNo hk
  | false =>
    simp only [e,Bool.false_eq_true,↓reduceIte] at hk ⊢
    let s : Slot := (k,sw.testBit k.val)
    have index : Nat.add (Nat.shiftLeft k.val 1) (sw.testBit k.val).toNat = slotNum s := by
      simp [s,slotNum,Nat.shiftLeft_eq,Nat.mul_comm]
    rw [index] at hk
    obtain ⟨hraw,harc⟩ := Bool.and_eq_true_iff.mp hk
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply List.all_eq_true.mpr
      intro z _
      have hz := @scanDown_at _ 11 hraw z.val z.isLt
      cases hit : u.testBit z.val with
      | false => simp [hit]
      | true =>
        simp only [hit,Bool.not_true,Bool.false_or] at hz ⊢
        rw [←colByIdx_ok]
        exact maskNo hz
    · apply List.all_eq_true.mpr
      intro j _
      have hj := @scanDown_at _ 5 harc j.val j.isLt
      cases hit : on.testBit j.val with
      | false => simp [hit]
      | true =>
        simp only [hit,Bool.not_true,Bool.false_or] at hj ⊢
        unfold barredArc
        rw [←colByIdx_ok,←pairNegByIdx_ok]
        exact maskNo hj
lemma fastLeaf_safe {n p w O R d} (h : encLayout n p w O R) (ok : insidePacked d w)
    (byte : ℕ → ℕ) (tag t : ℕ) : readLeafFast p byte d tag t = 0 := by
  unfold readLeafFast
  dsimp only
  split
  · split
    · rename_i test
      obtain ⟨rr,good⟩ := checkGraph_sound _ _ _ _ _ _ _ test
      exact (graphLeaf_impossible h ok _ _ _ rr good).elim
    · rfl
  · rfl
lemma fastCanon_ok (m : Marks) (i : Id) (eq fl : ℕ) (ok : acceptMark eq fl (rawNumber m i).val) :
    (canonDomainFast eq fl (!(orientation i))).testBit (represented m i).val = true := by
  let neg := !(orientation i)
  let v := represented m i
  have word : admissibleTable neg v = (rawNumber m i).val := by
    change (if !(orientation i) then 1023-v.val else v.val) = _
    by_cases lt : i.val < 11
    · simp [v,orientation,represented,lt]
    · have := (rawNumber m i).isLt
      simp [v,orientation,represented,lt]
      omega
  have side (k : Fin 5) (h : fl.testBit k.val=true) :
      (sideMaskFast neg k.val).testBit v.val = true := by
    have masks (b : Bool) (g : Fin 5) : sideMaskFast b g.val = sideMask b g := by
      fin_cases g <;> cases b <;> rfl
    rw [masks]
    exact sideMask_ok neg k v (word ▸ (ok k).1 h)
  have order (k : Fin 5) (h : eq.testBit k.val=true) :
      (orderMaskFast neg k.val).testBit v.val = true := by
    have masks (b : Bool) (g : Fin 5) : orderMaskFast b g.val = orderMask b g := by
      fin_cases g <;> cases b <;> rfl
    rw [masks]
    exact orderMask_ok neg k v (word ▸ (ok k).2 h)
  have add (b : Bool) (m a : ℕ) (hm : b = true → m.testBit v.val=true) (ha : a.testBit v.val=true) :
      (match b with | true => Nat.land a m | false => a).testBit v.val=true := by
    cases b <;> simp_all [Nat.testBit_and]
  unfold canonDomainFast
  change (match eq.testBit 4 with | true => Nat.land _ _ | false => _).testBit v.val=true
  apply add _ _ _ (order 4)
  apply add _ _ _ (side 4)
  apply add _ _ _ (order 3)
  apply add _ _ _ (side 3)
  apply add _ _ _ (order 2)
  apply add _ _ _ (side 2)
  apply add _ _ _ (order 1)
  apply add _ _ _ (side 1)
  apply add _ _ _ (side 0)
  rw [show fieldMask = allWords by decide +kernel]
  exact allWords_bit v
def pop10 (c : ℕ) : ℕ :=
  Nat.add (Nat.land c 1)
  (Nat.add (Nat.land (Nat.shiftRight c 1) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 2) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 3) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 4) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 5) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 6) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 7) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 8) 1)
           (Nat.land (Nat.shiftRight c 9) 1)))))))))
def bothSigns (a b r : ℕ) := let s := 32767; (s ^^^ (a &&& b)) ||| r
def chosenSig (a b tt tf ft ff v : ℕ) :=
  let s := if a.testBit v then (if b.testBit v then tt else tf) else (if b.testBit v then ft else ff)
  Nat.land (Nat.xor 32767 (incidence v)) s
lemma chosenSig_eq (a b na nb v : ℕ) :
    chosenSig a b (bothSigns 32767 32767 (na &&& nb)) (bothSigns 32767 nb (na &&& nb))
      (bothSigns na 32767 (na &&& nb)) (bothSigns na nb (na &&& nb)) v = stableSig a b na nb v := by
  cases ha : a.testBit v <;> cases hb : b.testBit v <;> simp only [chosenSig,stableSig,bothSigns,ha,hb] <;> rfl
def cliqueRun (c : ℕ) (sig : ℕ → ℕ) := scanDown fun v =>
  !c.testBit v || scanDown (fun w => !c.testBit w ||
    (sig v &&& sig w != 0 && sig v &&& incidence w != 0 && sig w &&& incidence v != 0)) v
def quickClique (a b c : ℕ) :=
  bitSub c (a ||| b) && (pop10 c == 6) &&
    let na := negativeSig a
    let nb := negativeSig b
    let r := na &&& nb
    cliqueRun c (chosenSig a b (bothSigns 32767 32767 r) (bothSigns 32767 nb r)
      (bothSigns na 32767 r) (bothSigns na nb r)) 10
lemma countBits10 : ∀ c : Fin 1024, pop10 c.val = ((List.range 10).filter (fun i => c.val.testBit i)).length := by
  decide +kernel
lemma quickClique_sound {a b c : ℕ} (ct : c<1024) (ok : quickClique a b c = true) : validClique a b c = true := by
  let sig := stableSig a b (negativeSig a) (negativeSig b)
  obtain ⟨base,ck⟩ := Bool.and_eq_true_iff.mp ok
  have all : cliqueRun c sig 10 = true := by
    have sigEq := funext (chosenSig_eq a b (negativeSig a) (negativeSig b))
    simpa only [sigEq] using ck
  have pair {v w : ℕ} (bd : v<10) (lt : w<v) (hv : c.testBit v=true) (hw : c.testBit w=true) :
      (sig v &&& sig w != 0) = true ∧ (sig v &&& incidence w != 0) = true ∧ (sig w &&& incidence v != 0) = true := by
    have up := @scanDown_at _ 10 all v bd
    simp only [hv,Bool.not_true,Bool.false_or] at up
    have down := @scanDown_at _ v up w lt
    simpa only [hw,Bool.not_true,Bool.false_or,Bool.and_eq_true,and_assoc] using down
  apply Bool.and_eq_true_iff.mpr
  constructor
  · simpa only [←countBits10 (⟨c,ct⟩ : Fin 1024)] using base
  · apply List.all_eq_true.mpr
    rintro _ hv
    obtain ⟨v,mv,rfl⟩ := List.mem_map.mp hv
    apply List.all_eq_true.mpr
    rintro _ hw
    obtain ⟨w,mw,rfl⟩ := List.mem_map.mp hw
    obtain ⟨vr,cv⟩ := List.mem_filter.mp mv
    obtain ⟨wr,cw⟩ := List.mem_filter.mp mw
    rcases lt_trichotomy v w with lt | eq | gt
    · obtain ⟨cross,_,inc⟩ := pair (List.mem_range.mp wr) lt cw cv
      exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr ⟨by simpa only [Nat.and_comm] using cross,inc⟩))
    · exact Bool.or_eq_true_iff.mpr (Or.inl (beq_iff_eq.mpr eq))
    · obtain ⟨cross,inc,_⟩ := pair (List.mem_range.mp vr) gt cv cw
      exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr ⟨cross,inc⟩))
def permuteStraight (pw x : ℕ) : ℕ :=
  let z := 0
  let z := if x.testBit 0 then z ||| (1 <<< ((pw >>> 0) &&& 15)) else z
  let z := if x.testBit 1 then z ||| (1 <<< ((pw >>> 4) &&& 15)) else z
  let z := if x.testBit 2 then z ||| (1 <<< ((pw >>> 8) &&& 15)) else z
  let z := if x.testBit 3 then z ||| (1 <<< ((pw >>> 12) &&& 15)) else z
  let z := if x.testBit 4 then z ||| (1 <<< ((pw >>> 16) &&& 15)) else z
  let z := if x.testBit 5 then z ||| (1 <<< ((pw >>> 20) &&& 15)) else z
  let z := if x.testBit 6 then z ||| (1 <<< ((pw >>> 24) &&& 15)) else z
  let z := if x.testBit 7 then z ||| (1 <<< ((pw >>> 28) &&& 15)) else z
  let z := if x.testBit 8 then z ||| (1 <<< ((pw >>> 32) &&& 15)) else z
  let z := if x.testBit 9 then z ||| (1 <<< ((pw >>> 36) &&& 15)) else z
  z
lemma permuteStraight_eq (pw x : ℕ) : permuteStraight pw x = permuteBits pw x := by rfl
def rowTest (r b : ℕ) : Bool :=
  let a := repNum r
  let code := routeCode (r*1024+b)
  if code == 0 then coldMask a b == 0 else
  if code < 1024 then quickClique a b code else
  let u := code-1024
  let pi := (u / 95) % 120
  routeBlock (u % 95) (permuteStraight (permNum pi) a) (permuteStraight (permNum pi) b) (u / 95 / 120)
lemma rowTest_ok {r b : ℕ} (h : rowTest r b = true) : checkedRoute r b = true := by
  unfold checkedRoute rowTest at *
  dsimp only at h ⊢
  by_cases off : (routeCode (r*1024+b) == 0) = true
  · simpa only [off,↓reduceIte] using h
  · simp only [off,↓reduceIte] at h ⊢
    by_cases sm : routeCode (r*1024+b) < 1024
    · simp only [sm,↓reduceIte] at h ⊢
      exact quickClique_sound sm h
    · simpa only [sm,↓reduceIte,permuteStraight_eq] using h
def positiveLowBlock (i : ℕ) : ℕ := 0xfffffffffffffffffffffffff0000000effffffffffd7ffffffffffff0000000dbbffffffffffffffffffffff0000000cbbfdffffffd7fbffffffffff0000000ff7ffdf7fffffffffffffffff0000000a67ffdf5fefd7f7bfffefffbf0000000db3fbdf7fdfffffffffffffff0000000823f1df5fcfd7f3bfffefffb70000000ffffffefffffffeffdfffffff0000000effef76bfbf97eeff9fffff7f0000000d9bdfacffffffdeffdfdbfeff0000000c9bcd24bf3d97caff9f9b7e7f0000000ff7ffde7efffffeffdffffdff0000000a67af561eab97e6bf9f6ffd2f0000000d93db8c7cdfffdeffdfdafcff000000080381041c0997c2bf9f0a7c270000000ffffeffffff7fffff7fffffff0000000efffeffffff57bfff7effffff00000005bb7efffbfe6fffef7df7fbff00000004bb7cfffbfe473bef7cf7fbfe0000000ff6fedb77ff7efd5e7bffffff0000000a64fedb57ef56b51c7aeff79f00000005b27adb73de6cfd4a79f7ebfd000000002070db53ce44310878e7e3940000000ffffefeffff7ffeff57ffdfff0000000effee76bfb717aeff06ffdf7f000000059b5eacebfe6bdeef55d1dafb000000049b4c24ab34030aef04915a7a0000000ff6feda76ff7efc5653ff9dff0000000a64ae5216a316a414026f950f00000005925a8860de68dc4251d088f900000000000000000000000000000000
def positiveLow (i : ℕ) := Nat.land (Nat.shiftRight (positiveLowBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def positiveHighBlock (i : ℕ) : ℕ := 0xfffffffffffffffffffffffff0000000ffffffffffffffffffffffff80000000fffffffffffffffffffffffc70000000fffffffffffffffffffff80000000000ffffffffffffffffffffc7fff0000000ffffffffffffffffffff07ff80000000fffffffffffffffffe00c7fc70000000ffffffffffffffffe000000000000000ffffffffffffffff1ffffffff0000000fffffffffffffffc1fffffff80000000fffffffffffffff31ffffffc70000000ffffffffffffffc01ffff80000000000ffffffffffff803f1fffc7fff0000000fffffffffffe003c1fff07ff80000000ffffffffffe180331e00c7fc70000000ffffffffffe000000000000000000000ffffffffff1ffffffffffffff0000000fffffffe001fffffffffffff80000000fffffff9ff1ffffffffffffc70000000ffffff80001ffffffffff80000000000fffffe7fff1fffffffffc7fff0000000fffff87e001fffffffff07ff80000000ffffe679ff1ffffffe00c7fc70000000ffffe000001fffffe000000000000000ffc01fffff1fffff1ffffffff0000000fc001ffe001ffffc1fffffff80000000f3c01ff9ff1ffff31ffffffc70000000f0001f80001fffc01ffff800000000000fc01e7fff1f803f1fffc7fff00000000c00187e001e003c1fff07ff8000000003c00679ff0180331e00c7fc700000000000000000000000000000000
def positiveHigh (i : ℕ) := Nat.land (Nat.shiftRight (positiveHighBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def positiveHalves (x : ℕ) := Nat.lor (positiveLow (Nat.land x 31)) (positiveHigh (Nat.shiftRight x 5))
set_option maxRecDepth 10000 in
lemma positiveHalves_good : ∀ x : Fin 1024, positiveHalves x.val = positiveSig x.val := by decide +kernel
def positiveMemo (x : ℕ) := if x<1024 then positiveHalves x else positiveSig x
lemma positiveMemo_eq (x : ℕ) : positiveMemo x = positiveSig x := by
  unfold positiveMemo
  split
  · rename_i lt
    exact positiveHalves_good ⟨x,lt⟩
  · rfl
def negativeLowBlock (i : ℕ) : ℕ := 0x7fff7eff5fff5eff77ff36fd57ff16fd7ffb7adb4feb4acb77fb32d947eb02c97fbf7ebf5dbe5cbe77373635553614347fbb7a9b4daa488a7733321145220000
def negativeLow (i : ℕ) := Nat.land (Nat.shiftRight (negativeLowBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def negativeHighBlock (i : ℕ) : ℕ := 0x7fff7ffe7ffd7ff07fef7fee7f8d7f807f7f7f7e7f7d7f707c6f7c6e7c0d7c007bff63fe7bfd63f07bef63ee7b8d63801b7f037e1b7d0370186f006e180d0000
def negativeHigh (i : ℕ) := Nat.land (Nat.shiftRight (negativeHighBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def negativeHalves (x : ℕ) := Nat.lor (negativeLow (Nat.land x 31)) (negativeHigh (Nat.shiftRight x 5))
set_option maxRecDepth 10000 in
lemma negativeHalves_good : ∀ x : Fin 1024, negativeHalves x.val = negativeSig x.val := by decide +kernel
def negativeMemo (x : ℕ) := if x<1024 then negativeHalves x else negativeSig x
lemma negativeMemo_eq (x : ℕ) : negativeMemo x = negativeSig x := by
  unfold negativeMemo
  split
  · rename_i lt
    exact negativeHalves_good ⟨x,lt⟩
  · rfl
def memoCold (a b : ℕ) := Nat.land (negativeMemo a) (negativeMemo b)
def memoEnv (e a b : ℕ) :=
  bitSub (suppNum e) (Nat.lor a b) && bitSub (hotNum e) (memoCold a b) &&
    bitSub (Nat.land (positiveMemo a) (positiveMemo b)) (pointNum e)
def memoRouteBlock (c a b t : ℕ) :=
  let e := routeEnv c % 201
  bitSub (negativeMemo t) (memoCold a b) &&
    (if e=199 then bitSub (Nat.land (positiveMemo a) (positiveMemo b)) (positiveMemo t)
     else memoEnv e (eraseMask a t) (eraseMask b t))
def memoClique (a b c : ℕ) :=
  bitSub c (a ||| b) && (pop10 c == 6) &&
    let na := negativeMemo a
    let nb := negativeMemo b
    let r := na &&& nb
    cliqueRun c (chosenSig a b (bothSigns 32767 32767 r) (bothSigns 32767 nb r)
      (bothSigns na 32767 r) (bothSigns na nb r)) 10
def memoRow (r b : ℕ) : Bool :=
  let a := repNum r
  let code := routeCode (r*1024+b)
  if code == 0 then memoCold a b == 0 else
  if code < 1024 then memoClique a b code else
  let u := code-1024
  let pi := (u / 95) % 120
  memoRouteBlock (u % 95) (permuteStraight (permNum pi) a) (permuteStraight (permNum pi) b) (u / 95 / 120)
lemma memoRow_eq (r b : ℕ) : memoRow r b = rowTest r b := by
  simp only [memoRow,rowTest,memoClique,quickClique,memoRouteBlock,routeBlock,memoEnv,validEnv,
    memoCold,coldMask,negativeMemo_eq,positiveMemo_eq]
  rfl
def rowRun (r base : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => match memoRow r (Nat.add base n) with
    | true => rowRun r base n
    | false => false
lemma rowSound {r a n : ℕ} (h : rowRun r a n = true) {b : ℕ} (lt : b < n) : memoRow r (a+b) = true := by
  induction n generalizing b with
  | zero => omega
  | succ n ih =>
    change (match memoRow r (a+n) with | true => rowRun r a n | false => false) = true at h
    cases e : memoRow r (a+n)
    · simp [e] at h
    · simp only [e] at h
      rcases Nat.lt_or_ge b n with less | more
      · exact ih h less
      · have eq : b=n := by omega
        simpa only [eq] using e
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr0 : rowRun 0 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr1 : rowRun 1 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr2 : rowRun 2 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr3 : rowRun 3 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr4 : rowRun 4 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr5 : rowRun 5 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr6 : rowRun 6 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr7 : rowRun 7 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr8 : rowRun 8 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr9 : rowRun 9 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr10 : rowRun 10 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr11 : rowRun 11 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr12 : rowRun 12 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr13 : rowRun 13 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr14 : rowRun 14 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr15 : rowRun 15 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr16 : rowRun 16 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr17 : rowRun 17 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr18 : rowRun 18 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr19 : rowRun 19 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr20 : rowRun 20 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr21 : rowRun 21 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr22 : rowRun 22 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr23 : rowRun 23 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr24 : rowRun 24 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr25 : rowRun 25 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr26 : rowRun 26 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr27 : rowRun 27 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr28 : rowRun 28 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr29 : rowRun 29 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr30 : rowRun 30 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr31 : rowRun 31 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr32 : rowRun 32 0 1024 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma rr33 : rowRun 33 0 1024 = true := by decide +kernel
lemma routeChecks (r : Fin 34) (b : Fin 1024) : checkedRoute r.val b.val = true := by
  have all : rowRun r.val 0 1024 = true := by
    fin_cases r
    · exact rr0
    · exact rr1
    · exact rr2
    · exact rr3
    · exact rr4
    · exact rr5
    · exact rr6
    · exact rr7
    · exact rr8
    · exact rr9
    · exact rr10
    · exact rr11
    · exact rr12
    · exact rr13
    · exact rr14
    · exact rr15
    · exact rr16
    · exact rr17
    · exact rr18
    · exact rr19
    · exact rr20
    · exact rr21
    · exact rr22
    · exact rr23
    · exact rr24
    · exact rr25
    · exact rr26
    · exact rr27
    · exact rr28
    · exact rr29
    · exact rr30
    · exact rr31
    · exact rr32
    · exact rr33
  apply rowTest_ok
  rw [←memoRow_eq]
  simpa only [Nat.zero_add] using rowSound all b.isLt
def tapeByteBlock (i : ℕ) : ℕ := (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x1040b040b02040e040403020100010140001f1a040b040b02040e07100201040b040b02040e040403020100050d010004001f1a070f02030d011320102200151e030d0201070d0f0d07051135204200171e011521424200131e040315214200171e425242420003370207050d01001201c000001d1a0125554155011a6110010c01201a0550001c1a05070b100c0501d1110b1020121c155502181e050117041109004000171a050b119415e901143b01151104101f110500ec05121a07010c0403669904091106480600d019041a11001d0906049909062d0600d019041a10001d11001d1906000019041a06000019041a0a0103000012041a0c09204404000e1c07000012041a46462046100f610c09204c66000e1c0245255545100b61c9255455000a2c0c09204565010e2b0245255545140b6144255455140a610c09204565010e2b101103000012041a09051419002001c020c0c9000c1c0000900b042d14071701e31706103b0c9c2444cc000d1c08194d2ccccc10096101242c001f1a06c9245555030c2b050c9c2444cc000d1c08c0220cc004091c16001f0514001f044c2455c1000d1c16001f0cc0240a0004091c011601524000131dc0220cb004091cc022022004091cc0220cb004091c0d0514001f16001f0c070c021a0020042a4504081c0c180056180056180056090e001b021c001a11001d11001d11001d0901121cbcec0018530c2d4c04081c0121551d9402191d0454255554140b61442555541409610c2c5c02086f100c25ac04081c0907020c25cc04081c0109945909042d1800561a001d011c001a1100200714001a10005615001f1800560c25cc04081c190c05170410001f00300008041c0600b00008041c0114040b071400200c040503000f0b0c15080f10101010e000181a0c0185ee07106e190b030c100c0d0112110101001320060c0301080d140f00040006081c0900040006081c02020242020c1c00009900082400040007081c00040406081c0d0b14030f02422208041c1305222210041e07100d0c1e00291e002913060301000010001002040e010d040203010b0b13bb04085d0016040115a020202000031c010b00020612155555001d2d020121a22522021c210d151001284aaaaa00195c161506020202041110847b7b001b1a12050216060304110432046202000b1c050d02030d030d020100010e000000000000191b0800023500550419210d02002903002910010b06000d000022cc04102200170604101104449400012900000010081b030f06039904085106039904085100009010083e00009010083e08140600100902000029100f1e002401060405040b040b02017102001f1a060d17580202001b1a050d020107230723000f1b0023002323000b1b0810001f0e10001f040510001f0e010000 | false => 0xe53e02186b030516041304002000171b040b0c422413041c05040c442215021c0501373305101b0316010000036000040939110504020c04000c1c1704026406020c2b110f0b0909990c020c1c0c0c9c0c020c1c0c0c9c0c020c1c1406060666000c1c00060604081c11140b16005a0c00333300092416005a170000330008240e0b09090939020c1c00090306081c14010301e445444400132904b4004400052c0b030155545554021934155555550218340222420c011c94e43d540205371545455402111e94e47d540205371545455402111d0e0309229309042d94e4774400052c060155555454081334155555550812341e4545440011291e454544001129155545540a11340155550a10341005555554140813345555515508123454e4541400032954e454140003290555555414100b3455555155100a34065554541410031e165554541410031e01030d001c645454140003290c001c170222120c021a030f0024065555541418033405551518023410042c420c011c0d001c0300050e1ec2aeee02145301e5550010290e02e3001f1a01e5aa02105301e55500102901eeae06105610e0508005181ae3ee1e131003540ee11e1002540ee11e110254190000330408240ee11e110254190000330608240000330708240e08002b06669600082b0c22c209041c1408002b0708002b66626666010c1c06669601082b06696605082466666666040a24666666660409240656660408240666660508241108002b08002b08002b070a08002b0b00020002081c07000000030608240e0e0a001c0a001c0a059c969295000f1c1c001b09929908041c6c991299000f1a08002b09e99700014708002b1c001b1422091207000f1a08002b08002b08002b0609001c0501030f04020b120e070e0110110380021c1a0819070d0c04060e1112013221222200132213212322001123132123220011230e013133001023190131770010230131330010230131110010230c120d04000636066608052b110350108010000c1a50108050000c1a0000600a042710120c0b0605051ee501087a1907081406051118020821051115020821051115020829051181000844011907080605118500082917100d1304031406030117040002030b000e010318001601040314031101031875b5351500031e1c001c10010405011202001f1a040104050d0c13120310100d0c011a110e101e011a550f101e0115510e101e10130302041205050d02030d05050302010012012311001d1a060c061704060c1163140100171a060c040332421242000f1b060d040e03060d2626360600032404110302000b0410061005050d0715060103070f110f0405050d0711030100030b000e01011700160304041403100100121c002d18040705010140001f1a040b040b02040e071002) | false => (match Nat.blt i 3 with | true => 0x7700113c0b1757947900124a1757947900124a07176e663604123401b77308101b0104031c7cbc7c0218571bc7c7cc08115701b7b70a1057171612060550021002000f1a06030d170222cc0b042217030b06100502c02c01c000071c0e00531702001c1403375321330c121f17040cc4440304220306010b0002010e000d02030c00100205001700140503190000050201060511115e1102141e11115e1102141e05030c010500100000191a01111807101e0410131013001e1a1050101000181a01111507101e0c100b02050e01115104101e0310020101313310041f0601311310042003050e0900c0100853050023040500230500230e03170201131310021f0e05c2221804290d02011b1114021e0d001c1513131310031f1c00291513131310031f1e00291f0029100b01111311021f0e0c1500210d0503733309021b0006000c011c16001e0b001b061561561510071e111c00291d0029101c00291c0053057131313110031f03733308021b05c2221804290b16001e16001e0a0c17001e0d002203733708021b1b001d0a1c00530506020301000402a5aa06106002a5aa071060150b161506170d100e09020222222206191c2053ab2200185a2053ab220118580d1506160104100f140602222531220912210224440e102c2153ab4b0118540f161422e4dadd0c111c22e4dadd0c111c080714090011153ab10811542c1274310e111c0016249530580012320206150105070e0b14060022033102110a2302000016081c1053aba00118540b1514097d097d000f1b02030012081e080414090211035ba1100954c103505112091e021509035437000a34000616010440d01104531a001e0e070903030d3308051b00000d0a041b0e0b1805331318021e0e0908140916141b001e0777770c023e0e003e120e003e0f003e081a001e071a001e1a001e1e001d1e001d0a07777709041b1500470f003e08071a001e0715121a001e05b5551a011e1a001e101a001e08090e1a001e05333319021e1a001e05333319021e1e001d0a1a001e1a001e1a001e10160e0787770b041b041002070877870a041b040e020006010503011300703002141b010b061770333308143f12171700303308141b1330307001141b01030e11becbcb001b290e001c1713030b0004111b1e001c0040001e011c011e001c1f001c0b1e001c0911beeebe021856010c42241c021c0f013b2e03106201733b0c101b1300621c00240111111111031c1a111111110718340c0111152112011a37130062061e001c0901b33e05101b11be3d3a001856091500241135111105181a1111111102184201bb3701105706190103130300bc04121b1f002b0d001c0d001c1711be113e0218540cc22c0c021c0cc22c0c021c0cc22c0c021c11be3eea0118560f11bee5ba0218541711be | false => 0x1d00036c02180704050f0124126155001c1e100c0117150701141301a1110a101e0c01511109101e01188e06103b1918070306140f05222212081e0802242404081c02244c04081c1817070300631a041e0900006008041c00000908041c181403022213081e0600000004081c00000c04081c18171b001e0604444408041c04444908041c18140119d1cd9d00131d0c001c9d9dcd9d00037802c9910c011c0d001c0c001c0a0400900c011c16001f1600321a001e1a00210226190d021c0d001c0f001c09c9990c011c0d001c0a0400900c011c1d00291c00290400900c011c1d001b010c001c0ecccc18015418005409c9990c021c09c9990d021c1702c9910c011c0c001c0d001c0c001c0a0f002716003b0c001c1b001e17001f110c0c003e0c003e080c001c0717e114013b0d001b021c00291c002901180444490c021c14180054180700000c0c021c1714003b18050403000e051405140202001300100504041600170203190018020507041604160605111108041e0410041806020612031904031403180402050311110308200c050e02121223220019230006022522041027050d041a005717011411080228c2ec8c0013212145aa2a06181b0805170d0402040e0019050c0d040ddddd00016b04180502030706022c5c120822049c20c777100d1b1717020503707710044103707710044103707710044103707710044108011506121212db7b001b1d121212aa02181e16091704040320331b04270e16180c0503020d0222cc0408220917060416271717170003330412050300000e03000c04001600cbbb08106100cbbb0810610c16040616511021000f1d12000c00100403121a7a1a1a0003290015040605020e02110512b42102001722050d1001050d02040312190516008858188800054803040851880004481113050400460504000206050b060c04050b06100402060c060c04032500500500072106101c001b1c001b16040201040d010c05041601190506040d011005001759e9191900032914001b011405060205021402000c900208470101c1191102191d0004400208470605170405060c0617081e00240a0c0206050401040b0414020516050b00220506040100060f22222122050a220d09061205060b01eb330f10230133b706101b01337704101b01337304101b0e120503060b060f05060bbb3b21b504121a0222150c02220222120d0222161e0023060503020e16160e10121070b07000181b120b0606212219041c017551333300151e017551335500151e17513333021441120e040651151004320006515510043206515510043201320172000a151b00040651531004321321337209141b1751333300141e0651531004321751b53300141e1751b23300141e04175133330314410e12101777070000113c177777)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0x112900c9d90a103b00c9d40a103b0d001e0d001e0099940010440c4ccc4c06185d0c4ccccc07181a0ce9edee0a113b0cc9eccc0a113b0ce9ecee0a113b00c94c09101d1700999400104419080d001e0700c9d90a103b0c0704070e001e100dd9d9dd0811720d19191108111d0033360d10220094d406106600d9d90a107204009949001044091814030209190c150610015e119e4e000b2e015e119e4e000b2e011b1106081e01131106081e0407011be104085401131e06081e06011bee04085409190302e559527500074602e55952750007460222aa0a04540802225508041e0706100030630e101a0036630a101d0c0069970010440f001e0f001e15006676011032033333330a1422033333330b141a033333330c1222033333330e11220033330e10220033330f10220e006669021032101405e55955750007460f00540222220c011e1c00220d1b00720905e5595575000746080c001e02225508041e0c001e0c001e063666666605122f03666605102f113655656a0114290c001e0c001e0c001e1514002f22222222020c1e02222202042101007a02222208041e1f005d0902225208041e0d14002f14002f060900450c0ccccc0f101a07445456550411291511815400092e0c001e0336c60b10721e005d332323200c1122050906555514012f15002f061506555514012f1511815400092e0ccccc0e101a0703666600103201121106081e1b0072060c001e0115110c011e0c001e0c001e0c0444460410290c001e0c001e0366660010321101121106081e0c001e14002f061c002c0710086666306604122f080639060802416666606610062f076666660614032f06660614022f110d00540c001e1004030201010120001f1a00000401081c040b010500100000191a040b0210020303020c010390091204480114052444100829120e020f050524441008290c020f040703000010041a14070b0110e14e0e00131d01190c0b02040300000030933308151b0e0f060b0714060d17040511140b0040000d101a0040990f102b0040000d101a14180403080d1506100502222201082106100407030006010434060e051c002b071e001c0d1c002b0710040301201c0100001d1a000201c01505001c1a0201c01505001c1a10070b050b06050f24ece4ee001153080244cc07102c17190704070b0e09e0ee00093b1000540700090900083b00009907082d14190509c404c901067400c0300204750f0b020c000c18041c0200450c000c18041c1917079e4e4e4e00034404005609444900024404944919022b14190eeeee00016b0008003b0f002d020045090200006b1d001c171907050403030000000002181b060e01080b0e07011013010e0200000b0a101b0309160704121301090800099716082d14120705755b541500071d03107dbd3d | false => 0x7700151e0601555500101e01555500101e01555500101e03339304013401555100101e000c9911087b01555500101e0f001b0e001b0a0f001b0f001b1401555500101e0e1135c59300111e01155500101e0301555500101e0f003e13005a08004703140f003e1135a59300111e018588588800191d1858588801181d1585858800111e0155580110451885858808112901555801101e130801555500101e0a0f001b105c59500018290f001b0a02120510040104120414020406002316058858585404111e0333930001340100340e8858585404111e0701004a140509001b0204120100002012001f1a0c0d100f05020b00140503030e03190505100011030201060e0510051903051011130302030e111205030b01110502000f000e0917070b0e031144520500171d000f100114e10e0e00131d121903050017001005005001001000071a0b20331b04230e0b000c01050302100c11060e041219050301100411100502070b0e06191205030d0b0711050200010202001f1a2202cccc030c2217060d01010e12ee00192001190312190c01201ccecc001c530c0c19170812081212e21202181e190d0c011177777704113b171217170131110c10200c06010c01021ccecc021c530c0c170c08061701113307101d1b22121209142308090119081010103001181a1301003009121b01b11709101b0b04190c0305010d0b080103040b0b0d170020001010000b24060101033103001a1a1119061a00201b00200c0b03060d0b170b0820202c20030c221703029222e272000b420400029222e272000b420801151106101d080c17006b1901151105101d08022c22040822022c22040822171800201800200b0601151114021d191c001b000d0200c202040a1c081c001b0e0024060402cc220c021c170b06696904022b06696904022b06696904022b1c001a140b1800561d001b00081200541c00571719030105020b0b170d040e0d0104100f0402225208101e11100105060e0b0702023010081e110e01060301091108051b111415004708686614014707080c003e08140777770c023e0777770d023e0c003e0d003e120777770a041b0777770a041b0c003e0e003e0777970c013e080402001c00220611010503020b070f060703100510100e015355050500132101515504101e0610020105030e050b020343353123000723013133100420060e050503020100170f14080f0f170f091900191e31ee00191d0704011b1114081e140c0819030095924499001547009d0406101a090cc2ca9c0a145d0952cccc031466170407140e001e0115110c021e0115110c021e0115110c021e00c9dc0b10720609991d110211440e001e0c0d9ddd9d0218720d9ddddd031872079ddddd0318720409d9dddd02116b18004a04070079d90a1072080954545504) | false => (match Nat.blt i 7 with | true => 0x1f030c0018001a055555020129010047101400561400560d001f140056171909c009000247140700460c001f1e001b0a0c0102040509170909170b0219080c040c03000304081b03000004081b03003004081b03003304081b0b03003304082406020e01031912060e1006020c03100c0405081201313310042005040e09cc0000001009530c000c1008530c090c1508651701313312042010051f004f0605040030002010000b2405060009300004091b160020040e0606061e0020061e00201f00200c120e0c04090710080b333312042003030903000c1b03039303020c1b0b33331204200803030b03000c1b0603039303020c1b0b33331204200909909904093c00090004083c00090004083c00090905083c0037037037000e1b00090004083c00090905083c1203039303020c1b140403039309020c1b0909909904093c00090004083c00099006083c140e0c0c022c9c011a1a03002202000a240033002221000b1c0300229c010a1c00c300c2c1000b1c0609cc00cc0c100a53c2002202100a21cc00c0cc1009530c00001008530033032c33010e1b0c000c1108530a03002203000a24030022c3010a240e17060c00901208550c009012084804050b0208060333007302053f0b90039003000f1b0b30021104200b300211042003060800000208042400300002043f080b0a003c0b021200003308042400003308041b0230331004200c303310042006020e020151e11a016508003510020072195e25eaee12095305255610081d02252210081d63232353010c1b030900330806485604081b03aa330c011c0e3e3310015f033ee3020172090322330804240c001b10020322330904240e05555518022905555518012910080333b302045d0705e55510012e0525a21a01461b004618001d0310025e25eaee1209295e25eaee12092918001d1400201400200c001c140020030602007205555518012911004502080035032222080424100333b302045d03007209190c90890097040a1b0000060d0224060122da0e101a0222da0e101a06190405010003140d0b000e01030f140653510900121f00120105060d172502510c000a1e001601064c490488000546100fd575757500031eb5d5b5a500031e0c33330802230393331002343632323218031f0716120f0d0600a232323208031e0393331002340305555500011e0353331201411200410eb5d5b5a500031e09d575757500031e080600470393331201340a00230e08161206030700100105040214100105c5595500191d160207105c595900182909090907083e0714051004031530535600141e0e15305057001432020512101555555500111e171601155100101e0301555100101e091402015373567700151e1500340977771401340155550010461500511418002f0701537356 | false => 0x5d0e0918aaaaaa021158018aaa021058150216040118b4b04b00171a24b40b4410052c1a002f0f0413090bb03303045d0e1504090718b01b1200145604021614002c0f010909030f0ddddd10016c18188888880411450188880410451813070e0e081802030ddddd02016c02006c070818080204120506020d02110504160118120506001708050c0c1914031529509500171a1551955504113204015250109502151a030e003c14159195990411320151550410320d0601155508101e140310020d12155959001b1d2925555500092b2925959900092b012155129500191d0c10051000481000480225cc00082b0f0517140e042902c29904091c292c029908051c170808050902180601041000480112006b0a006f070118061403000117110d07151706070b02040e0709060051140b060302100418150602140014060305060c060c03051001529a090900131a15140602051605160306142929191900032b0614050200040f040f05040d0210050105140518040511131e001c05040103090505010e05120e024c4404102c050e07010f05070f20404c4c001b1c02c44409102c072040a04000181c150f02c5cc0e105a0a204040c000181c100f02c44409102c07170f00030004081b00030004081b00030004081b0e0f0901050b02002200cccc08141c0209170813100504050e02050405040b0a00441300e83e80e800071f190a00441400230616003707130e0838c8080003200200001d021c000513040103030e131205031601190504040d041005051101130403020412041203041404140302040005011b770408451304120b0f050503030f040201000c0e001312050119011ce19e0e00131d13190504030b00191405010d08c8980800032919130504020209051717171706050617020e202cb818001b1d0400481713042233b10b00171e04051600228244240012210404070d0201000112160e120912010808020000000006181b0b0a020607141701120b0045131c00231c00230a1c0023091c00230a061c00230106020e0500081617010010130204030b050c050c040b05100510040205050404050d05090404050d0200010c031901060e010e0000510a0103141a06150603100300c0303300111c00000201101c0e160d06030100003002101c0000b002103e00000201101c0e160d030601170b00020312190b0311ee1708561912000610131c0020081c0020061d0020130310000205020b0211010217020d01040214021101020f021c001b0c010405030c0e030d140b02031716002ec09c7c001322002ec09c7c00132208002bcc0410560000200a101a000317020403141206e900c9a9000b2b06e900c9a9000b2b0906079904083b00006012081a00071402019e1ce10e00071d01717e08043b01711109041f14190f00))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0xf020c06100c0e11030100051717090201443cc3031c1c170904991008441410070f19020599409900192b09040714021f003e0c11061004111002011313133308051f0e0c0b08191307041402040e0c04041013020103020b020b06020d0017060402110014060619000f020405000e010f0d02011716030701170b020657113333000c4157113333020c340e0011120105d412d4d4000b290511320408341f00751801070f110201074d74d14d00072915002c1f00370f090818120ddddd0001711f0023031c00610918020605000e030f0b060021c133cc0015220017070f1706040619013399000d2a0014030f14061414134400052a000f030f18060405020c06020e0711030666120834111016131300181f1016131600181f0e08110b06020c05011b1010110015200602020b06011b101311001520011b101311001520090e09011b101011001520060b021611b01b13001420010116090e11b01b1000142016160b02010b11b0131b00142017090300001a041b010300001b041b010b16160e090b010b091602060c02060607100601070c0039015a770e101a08070606071104222405081b0181110810320f0704444408012b0f0132b5001f1a115151b500115f160d3ddd01083c01181151555502111e1151555502111e0a011211041020030701121104102004333304081b07031551515508113201511108103201511108103207156161660811320151110810320151510a103211101711b1d1ea00115f0f011a1104102011b1eb1b00125f161d1d1ded011878011a1104102004224206081c181711b1da1b00125f16180c001b0f11b1d1ea00115f09020131555555011a1e021800341c00391315155501181e12a2a41406181a08013c33133304191e01118503106f031315131300181f0e1315155501181e0a0702030c33cd06081b1151555501121e081151521200121e1151521200121e070c33cd16081b08090308071551551608123201511108103211011211041020011a1104102003015111081032030201511108103210060c0504020430303c0000051b14005616000d00040157000d00040157000d0004015718070602303c030000091b16606636000409390e06040907020604050908005709dc990801571319131307181e09020024010300390333c300081b03339800081b090710001a1a00200a10001a07003401001b07020605040b0002111183111106181f0c020911030d04033b102222100d23160222103333030c270e030d100c1155d6a6001b1d10020802120307011a22522204191e1155525202181e0216220308350d031666100834031666100834070e02162610083503021155525202181e1009020411050103707710043f03707710043f0812030118484a440611290f0314005d14005d0e14005d14 | false => 0x1110061112030501040c110610020c1005120902190110e14e0e00131d0c190503020e0d070b0e0302070f0646060600033301110305000c03331408230e11020c030314082307110e0101b55055041921101b50500418210c0b0014085a16100c000010081c0c000010081c040b020e0601010917020e0e0206060e160b00330f002b100710071009101510041703000010082417060e100407040407040e010b03154e50e500171d155ae5550411540c00750319110703101110015eaa0410530f021906100315010502161707110e0302070f060e1203050002190b090b09021917140f1808181419050416060d020e04060808021905010f140e02110f05020e0d0606666602013501391110022e1112050100190c0c040101191e9e001c3b090c19141314030311071002060e07061004131110020112141111040e0609094403082b09044403082b0f1141001191140a20070304140207111415143410061e06040e041110040904222222220412202222222204112002222204102022222222061120022222120420222222221403200222221402200222221401201400200222221601201600200d112222222205122002222211041e050222221402200222221502201400201500200d02212211041e18002f0610100903020100051609090517040b1702041605040e000190591900131a0b1402031905060e070c0e03040d10165616160003320011030201040d11061004121903041605060e07110e0300040d100419130304110f86767676000339080411030002050d012a222522041a210121a1151100191e1015012151121100191e0121a1121100191e1015100d040615121a151500181e1212151500181e1212151500181e1212151500181e070d0125221222041921125212120418210d100c011361360604131f0c003511061186e86e00171f010113060c00350606111181888804114501118804104502130111ee04101f0c1101aeee08105401aeee08105408118188880411450111880410451309190314003211496c096c000f1c0f140414003208041146046c6604092b0404cc04082b1411030f14000ccc100858140f0517bb76676600171f05096676676600073900663660660007390509667667660007391c0057160f042624626600093326046266000933262462660009330509050d063636060003390908041c006e06360606000339063606060003390808139676e676000351049676e676000351083e36360610031f020502967686760003511308081c006c093e36060610031f0808190704170f0e03097779000251097997000151141f00531704040704030c07081c002904070f06110100190c191903171f003f0f0f031002030c1165616600113210110201040b110404050b1405070c0035081411041403) | false => (match Nat.blt i 11 with | true => 0x41403141705050605030d020e0c0c19060c0e0c06060c050d07101010040815111100503010041c090579c50c011f0c001f1011030d0201000b110e000f0b06000f0d000f170604000f11010c1004000f141878181800032902130406050211001b1b33330019610e090c0e01021604020b001502091604060211011502000c040e0313071102010f150406050b0e0c11110c050d0d0c011c51950500131d0c1005040b110d1111100505c5095500052905100813100104020c0e170001007003001c1b120171331b0440190e0b0b1710020000b1333308141b10060e03502222001121035052550011210d03100201140037100c061400370906101a11a7aa040954011177040854040111ee07085419151111111104091f01111104081f13190c03177710083f0b010812130b031008131004020500140d0b000d1704000f1400100f0405000d0e00100d040010113575b51500031e0210040501010e000e1604001401170b0010170402000e120010140275b5103500061d0795bc510500071d07b13300041e100e0016120601081310020405020e0e0100e00500001c1a0e0e100b0310010714050310010317015c55950500131d1419100504030717140b1000c9065929000b2b0200c9065929000b2b00c9065929000b2b19031900009004082d00009904082d0b190b07140510009c25c04c00072c02009c25c04c00072c009c25c04c00072c190719190000c008041c0000cc08041c0b0b031785c5951510031e028ece9e1e10031e00002f1100460203191010071415c5911100111e08c9881201460208c9881201461001050400020e0e0100e00500001c1a0e0e100b08140f07100509170f031010100f0504030717140b18140f0518170f94c494840003471300460608180111220c101a01117e0e101a0ac98a1002468ece9e1e10034508c918100246190111220c101a08c98910024608c98811024608c98810024616110046100807030f050400100c101905011e33113300191f011e33113300191f0808081919100c0118eee3ee041954118ee3e3041856118e11e3061856041019040411535e5e03181e10191187838304183b1913060e13101313156865660011320313131007130713061102120e1212361763660009340412120e1204041206110101061109b99908013c1e00561604010801113318041e03399308013c1a001e1a001e0103339308013c1a00200e080408070804010999d9020133061801010108003c08003c111402000202255c5504192110180917040b1702120c0012061004100f0205010b0e0111120506110b19591919000332001405020317050c050c030301050503100205010303050e2626256600052b06263606000324030505031102000d0d170b020e0b0302100f0211140305020e0d07110e0302 | false => 0x80c0011041111000b1d0c110504111211090419111111000c0103040b101704171014101004100244449501182b141406002020040004191c0202040404181c050d0b070f0c00230e0b0b0c0023180b0e0b0b0c0020180b0e020b080c0023180b0e020018081804140314003c12101502100e022522040835110e02242204083511050d1c0047021c00470339930401341c0047141605080333730201340712180022180022180022120e0301020181550c104f0181550c104f081004030604070108d8844404194418010a44844400192909150707010104844400192908115181840e112e0c1080801007181a0b0c08130f005114100e0e0603141414111054548400182910100808131001010aa4aa0419531010a4a404185303091715070f0c001b0e0c0c0c001b13130e030606071001140b1404040f0b1000201000201000200f0f140e046656626600072344562444000535465624660005350f0503040e031101000201a1550c106001a1550c106009100406041906040707020101d554440419290401059554440419290105955444041929021f0075080b1401084454440019290b07010844544400192914050702150807010804544400192906040b0406141301555107101e190710171017015aaa0a106510a410a400182909171506084909949904092b4909949904092b0304015aaa09106510a9a4a4041829015aaa0d10651508010191141104191d1019141404181d1019191406181d0c140a08060105595545021c29101411108458840218291306666618043510548454001829111054588402182910545884021829158858880a144613101001010aa4aa0419531010a4a4041853170c0444100866090c04441008661715070f0c001b0e15190c001b15150e191506018555081029152125220411210151550410210d071001140f0717070f140f070f0411140056160d0202080e0d0d0d0411010003100c030903090408010199e99900193b0b010199e99900193b030808010109e99900193b09010199e99900193b0c08170208010109e99900193b090b030b02081f0062020919020200049914082f10040412190496006966040933090099040833110c0708140c00220d0c030c002207030d020c10100c018eee08106c100c081901920c202204091c1400210d10102222041b1a0202050314002192002c220609220905030d0807070704140707040962762762000727030404050e0403065531201200171e060307070704081207041106031119001b0e0e031f003c1406050d0100030b140f0f09070f1711110605140b14060614050b00141cc3330419220505170d050d0504180f361163660409340311330408341105051114060141c3c30418220c051917040e009220222200131a1c004a14030909292c22001122)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0x2222001321070501a221222200132101a221222200132111aa7a1a0a145411a127a20a11541501a221222200132101a221222200132111aa8a1a0a145411a128a20a115415070201a221222200131e100701522122220013211151215208111e100501a221222200132101a221222200132111aa7a1a0a145411a127a20a11541501a221222200132101a221222200132111aa8a1a0a145411a128a20a1154150f02060707011818222108134f070713150306061151a1520c111e03020307100c0219150f191310152a2a22001121111515252a22001121100408131121512204111e0c1121512204111e0c10020e030503030c0c100515131315100201a8810110211319030c1002030c0111125522001921112125220011211515161507182e0c021121512204111e0c15212522001121030215212522001121011115112204191e1121512204111e0c1013018a4aaa220815530f150f0201188501102113191519184828220811461513191303050503111525210011211115252100112111152521001121111525210011210715015a5aa2a1081360155a252108116015100519131913030619130e020f0f15061710170502130c110c191306030d060d1c00461403070603090303030109180306010909030909030603141c00581c00581e00210d1790990c0000093e030f0517111160303300000524071490990c0000093e0f1105170405180f0040000801220d040262c901041c070522221802210336661608321102922901021c030322221802210322221802210406030f06030d04140f0f0f149090770000053e110505606366000805391190990c0000093e0f05050405180f0040000801220d040411001ac2b2b2b208063711001a04050307060d01180d0f02929c00041c05080d0d0f050404180d0f110d10001a10001a0504010b0012020e0b06000625333300191e06b500535500092100000533550019210000053355001921000005335500192100000533550019210200000300530419240b020e03030e0b0610141114120712110800210800210800211111141005000000cccc100c5c03170c55095555000b1d0c15091515000b1d0ce509e5e5000b1d0ce509e5e5000b1d1c003f01e1510801460151e10201460c02191400270c88098888000b1d140027140027131005020c13030502081000350c0303031000351000350c100104040b0b0d0204044c4400192c0204044c4400192c20c020c006181c0b020d161702022222220419222022222204182217204322220318230e0d0202022222041922202022220418220e0d0d100d0d101006110202022222041922202022220418220e0e0d070f0c00200c10000c002009000c1007041010110f05000416110b0066046666000b1d0031045131000b1d0016041616000b1d | false => 0x1184409999d1108441303c3330e101b0b04080f110e1093497397100a3c03773718023c12d4d4d9d904187b039d44d9dd14097b09449914087b180484898984011844094994110844131204049d4d9d4d110c7b180404086e44e9ee04094506449904084519020d0c04101904838d393304093f088d9904083f0e0b680989880009480609990008481317080894054454110a2b09059511082b0f09055511082b08060803100944044644110e2994094464110a2b09099611082b0f94049404110c2b0f080806947944d4110a4709799d1108470f09333312081b0609333312081a09050393739696100c3300004018041c1108949944d4110a470f0404170d0d0dd9dd041971d0d0d9d904187108d4dcd4d906186f0b0409909d090014093e0b04c9cdcdc906186f179d00d9dd14097109009914087103c3330d101c1709180707070707070406002303c3330a101b0b0806002303c3330a101b03c3330a101b0b080343330b101c033c11160123033c111601230d4404c4800c11470f03c3330a101a0e0343330b101a0e050090939708112d0b0803c3330a101c0b080090939408112d03c3330a101c05070703c3330f101b050f449494660a112b0f03c3330f101c0b08070030353308111b0977b71a011a020979c71a013e0302064495949708112b0f08009090660a112d0b080808c90090c612091c090090c612091c0999c61a012d0b0b0f0999c21a011c17080900907712093e0999771a013e0b0900907712093e0bd9cc9d941009710dccdd11087118090700c05e09101b020800c0e008101b0208494484981409470f180b1807044440449004191c4944049014092b0990901c012b0f00c5e009101b030918070407002303c3330b101b0b0803c3330b101c0b080700c05e08101b03180704140818001b0e121c001b021c001b0206030d04040419001b0218001b080908041c001b1c001b020e03e2eae5e20803450318006c0300053012011c03081c006c1c006c02031508190115510801321161616561080332011551080132110115510801321103030318003c19021e003c091512030d0c0c0c0d120707a5a4aa5408056504555410012f1512070703011551080132116161656108033201155108013211011551080132110311002f11002f11002f11002f030211002f0c003b121906161216120622222222010c210222220104210d22222222010c210222220104210d06161216120603100107101510014122001f1a014122001f1a030615014122001f1a014122001f1a06020610150706015221111100132110031001522121210013211001a2212121001321151a32232100171a1a32232100171a0710011511212108131e1001a221212100132101522121210013211501522121210013211001a2212121001321150601a221) | false => (match Nat.blt i 15 with | true => 0x1b003303c301141b0e00000c01101c0317080307070f0503110502050500920c0900141c17070033933033021c1b0303930302181b0e00009002102d0106010600181b07140042202222081322042020220811220040000810220f17042420220c11220f03050f030d040b050d0400230e0b0b030d0d0606100f020d0d02060b020b170e0e170e0e020e0e0e1702050d0b050f050f050505170b170e10170b0b170b0f02170f050b0308044446696604193304444669660419330444466966041933044446696604193308040f0f11041013124090505003182d0b1003040f080f0804444e99ee041944444499990418441904030308030804000007797704193c0000797904183c120e000007977704193c0000979704183c12060b0b0f06050508060e034049434303182b0f0e0b0818180b0f0b080d0c47494d49021847060f0494944d4402194749494d49021847030f0408080804030090d0090004193e090d090904183e030808080d00900004193e80d0909004183e060505040b040908090d00900004193e90d0909004183e180517d09d090014093e181705170b07030f0f0f03170f03030f05050f050b9405454412092b0f080606031602120807070708120308030f110711330336930009340e110367066967000b51370696970009510e0e110e0f0f99098987100944189d077777130c3c18029907777712093c09077713083c02120e9900c09914091c17120f0f080b10100039030377120d1b0039030377120d1b1205040c09c0d902191c040c09c0d902191c18050b02050808120e07070b080f0586088986000b48560898960009481303060608110b030685098884000b4865098984000948131108101211120b0b080900709714093e030b0009000707140b3e0900709714093e050b0900505416092d0b1008070c08080f06100c1808070705070474d449440419471118070e17034944c49914094717004c44c99404192c030518947d49441409470400461307009099c99400192d0f0e0763796660000b51737969600009511109051707051703070f902303001209240b0e0e070806060511101008120f03050f030803034944849614094717030f49448497140947050f0b0e1117051790890d0012093e110b10868969660009510511050508031002060f06080e0e0900907712093e0f050f0b050b08180b17070705170494d4494404194718071718150803004c44c99404192c170317949d49441409471703009099c99400192d070f030f05030f070f040400499004192b0f05902303001409240e0507044440449004192b440404900c112b0f0b18171703171717030f040890333030110a2490330030110a2409339311082d0b092333110824080b08110e03040700230053730000181b00c5e008101b0f048989898d | false => 0x50d041403050d01e631634300131f040e0301050d43093c3300091b040e03050d040e030100050b040704020f0b0f0f0f041402050b0090c9001f1a0b0b050503020d0f030303030305050503031702080807080807070907000004494404192b0000494904182b0f04004040090004192d0f0f0504170949494d0118470f0b000199001f1a1705050b050040c09c9004191c0b11040b040b0990c0990c113e170b0b180404041717009090c20a111c0b0418050040c09c9004191c0b0b040707090f070f0414060c030d02001900001f1a0c070711020704081207030808080708080702060208080807140f003433030004191b0f0505001060030000192406060030600300001924020703333717083411020602020211110e07009330303008131b140211110e07180f030f0f1705003933030004191b140e1106110611050702003933030004191b0e003933030004191b003939030004191b0e0714050d0307050d0703050718030f170203004330303008131b0f06021700cc30c0c008131c170e1705060f170d04004222022208152204220202081422030f0420202208112200400008102216030f0d07030003333c330116))))
def tapeByte (i : ℕ) := Nat.land (Nat.shiftRight (tapeByteBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
def initialOffsetBlock (i : ℕ) : ℕ := 0x3d913483315b000000003097000000002fe5000000002f532e9a2d40000000002c5c2bc8000000002ba22b7300002b472aca00002aa42a6b0000000000000000000029ad293100000000000000002871284000002818000027f827c92726000026eb0000000000000000262125ef000025c5242e23f500000000000023a9000000000000000023922332230020921f7b00001ee21ebf1e99000000000000000000001e7f1ddb1dc41da3000000001d7a00001d0500000000000000001cea1c831c691bcb190a00000000000018700000171c00000000000016ff16e616ac0000168c154314cf149500000000118d113610e1000000000000103b00000ff70eab0e9200000e750e290dc00d8d00000000000000000d59000000000d350000000000000d140cd8000000000c8a0b860b6e000000000a69000008f2000000000000000000000000057804cd000004ad000000000000047600000000000000000000044300000429000000000000041003f203d4000000000391017a0000010700e20000009e0038000000000000000000010000
def initialOffset (i : ℕ) := Nat.land (Nat.shiftRight (initialOffsetBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def finalOffsetBlock (i : ℕ) : ℕ := 0x3db73d91348300000000315b000000003097000000002fe52f532e9a000000002d402c5c000000002bc82ba200002b732b4700002aca2aa4000000000000000000002a6b29ad000000000000000029312871000028400000281827f827c900002726000000000000000026eb2621000025ef25c5242e00000000000023f5000000000000000023a9239223322300209200001f7b1ee21ebf000000000000000000001e991e7f1ddb1dc4000000001da300001d7a00000000000000001d051cea1c831c691bcb000000000000190a00001870000000000000171c16ff16e6000016ac168c154314cf000000001495118d113600000000000010e10000103b0ff70eab00000e920e750e290dc000000000000000000d8d000000000d590000000000000d350d14000000000cd80c8a0b86000000000b6e00000a6900000000000000000000000008f20578000004cd00000000000004ad000000000000000000000476000004430000000000000429041003f20000000003d403910000017a0107000000e2009e000000000000000000380000
def finalOffset (i : ℕ) := Nat.land (Nat.shiftRight (finalOffsetBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
abbrev EvalState := ℕ × ℕ × ℕ × ℕ × ℕ
def layer (byte high : ℕ → ℕ) (settled : ℕ → ℕ → ℕ) (leaf : ℕ → ℕ → ℕ → ℕ)
    (allow : ℕ → ℕ → Bool → ℕ) (next : EvalState → ℕ) (state : EvalState) : ℕ :=
  let (t,D,eq,fl,q) := state
  let d := settled D q
  if d == 0 then t else
  let tag := byte t
  if lt : tag < 26 then
    let i : Id := ⟨tag,lt⟩
    let cand := laneRead d i.val &&& allow eq fl (!(orientation i))
    match optionsBy high 1024 cand with
    | none => 0
    | some vals => vals.reverse.foldl (fun loc val =>
      if loc == 0 then 0 else
      if bd : val < 1024 then
        let raw := rawFrom i ⟨val,bd⟩
        next (loc,replacePacked d i.val (1 <<< val),eq &&& sameMark raw,
          fl &&& freeMark raw,1 <<< (1025*i.val+1024))
      else 0) (t+1)
  else leaf d tag t
def play (f : (EvalState → ℕ) → EvalState → ℕ) : ℕ → EvalState → ℕ
  | 0,_ => 0
  | k+1,s => f (play f k) s
lemma play_spec (byte high : ℕ → ℕ) (settled : ℕ → ℕ → ℕ) (leaf : ℕ → ℕ → ℕ → ℕ)
    (allow : ℕ → ℕ → Bool → ℕ) (fuel : ℕ) :
    ∀ s : EvalState, play (layer byte high settled leaf allow) fuel s =
      searchTree byte high settled leaf allow fuel s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 := by
  induction fuel with
  | zero => intro s; rfl
  | succ k ih =>
    rintro ⟨t,d,eq,fl,q⟩
    rw [play,funext ih]
    rfl
def assisted (f : (EvalState → ℕ) → EvalState → ℕ) (tip : ℕ → EvalState → Option ℕ) : ℕ → EvalState → ℕ
  | 0,_ => 0
  | k+1,s => match tip (k+1) s with
    | none => f (assisted f tip k) s
    | some v => v
lemma assisted_eq (f : (EvalState → ℕ) → EvalState → ℕ) (tip : ℕ → EvalState → Option ℕ)
    (checked : ∀ k s v, tip (k+1) s = some v → f (assisted f tip k) s = v) (fuel : ℕ) :
    assisted f tip fuel = play f fuel := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
    funext s
    simp only [assisted,play]
    cases hit : tip (k+1) s with
    | none => simp only [ih]
    | some v => exact (ih ▸ checked k s v hit).symm
def workLayer (e : ℕ) := layer tapeByte hiBit (directSettle e) (readLeafFast (modelPos e) tapeByte) canonDomainFast
def workRoot (e : ℕ) : EvalState := (initialOffset e,actualStart e,30,31,guardBits)
def blockFieldBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0x20542e312ddebb0008532e9a2d5cbb0000532e9a2d40bb0018502d3d2cf9b800084f2d402cbdb800104d2c932c5eb800004d2d402c5cb800184a2c592c37b70008492c5c2bf4b70000492c5c2bc8b70000492bc82ba2b40000492ba22b73b30000492b732b47b10008482b102acbb00000482b472acab00000482aca2aa4ae0000482aa42a6bad0008472a4429aea70000472a6b29ada7000846298e2932a600004629ad2931a6000845293128d0a100004529312871a100004528712840a0000045284028189e000045281827f89c00004527f827c99b002041278327609a00103f27c9275e9a00003f27c927269a00003f272626eb9800103d26a726239300003d26eb26219300003d262125ef9200003d25ef25c59000083c25c525178f00203824a724578f00103624e724308f00003625c5242e8f000036242e23f58e00003623f523a98a00003623a92392850000362392233284000036233223008300203222b022748200282d225c21a18200182a2273210d820008292300210b82000029230020928200102720922025810018241fc01f8a8100002420921f7b810008231f3e1ee37f0000231f7b1ee27f0000231ee21ebf7e0000231ebf1e997d0000231e991e7f770008221e7f1e10760000221e7f1ddb760000221ddb1dc4750000221dc41da3740000221da31d7a710008211d481d066f0000211d7a1d056f0000211d051cea6a0000211cea1c83690000211c831c69680000211c691bcb6700201d1b4a1a406600181a19ef190d660008191b8e190b660000191bcb190a66000019190a1870620010171850174e600000171870171c60000017171c16ff5c00001716ff16e65b00001716e616ac5a00001716ac168c58001015167116055700181215cd154657000012168c154357000012154314cf5600001214cf149555001010147613775200180d131c11905200000d1495118d5200000d118d11365100000d113610e15000000d10e1103b4c00000d103b0ff74a00000d0ff70eab4900000d0eab0e924800000d0e920e754600000d0e750e294500000d0e290dc04400000d0dc00d8d4300000d0d8d0d593e00000d0d590d353b00000d0d350d143700000d0d140cd83600000d0cd80c8a3300080c0c8a0bc33200000c0c8a0b863200000c0b860b6e3100000c0b6e0a692e002807097b09012c00080609eb08f32c0000060a6908f22c0018030680057b2500080207d505792500000208f2057825000002057804cd2400000204cd04ad2200000204ad04761e000002047604431800000204430429160000020429041012000002041003f21100000203f203d41000000203d403910d001000033e01970c0000000391017a0c000000017a01070a000000010700e20900000000e2009e07000000009e0038060000000038000101 | false => 0x10b3db73d91c80011093d683d37c70011073d2d3cf7c70009063d843cf0c70011043ceb3ccbc70019013ccb3c9cc70018fe3c7c3c58c70018fb3c583c4bc70010f93ccb3c2bc70018f63c2b3be9c70018f33b863b71c70010f13b8c3b57c70018ee3b073aadc70018eb3aa93a82c70018e83a813a61c70010e63b573a60c70018e33a513a40c70018e03a1a39eac70018dd39ea39bbc70018da39ba3962c70018d739623958c70018d43958391fc70018d1390e3905c70020cd38fa38f6c70020c938f038ebc70020c538eb38dfc70020c138d438c7c70020bd38bd38b9c70020b938b838b3c70020b538b338a6c70018b238fa389fc70018af389f386fc70018ac386f3843c70018a93843383ac70010a73a513839c70018a438393816c70018a137743703c700189e370336c0c700109c383936bfc700189936b93653c7001896363935c9c700109436b9358cc70008933b95356dc700189035463526c700188d34f634e1c700108b354634adc700088a356d3484c700008a3d913483c7001887347f345ec600188434543403c60018813403335dc600107f3480333fc600187c333f3310c600187932f832b4c600187632b43291c6001074333f3258c6001072323b321ac600186f321a31f8c600186c31ed31bfc600106a321a317cc60008693242315cc60000693483315bc6000868315b30ffc3000068315b3097c300106630973031c000006630972fe5c00010642fe52fbbbd0008632fe52f96bd0000632fe52f53bd0018602f442f0ebc00085f2f532ecdbc00005f2f532e9abc00205b2e622e40bb0018582e8b2e31bb)
def blockField (i : ℕ) := Nat.land (Nat.shiftRight (blockFieldBlock (Nat.shiftRight i 7)) (Nat.shiftLeft (Nat.land i 127) 6)) 18446744073709551615
def blockMoveBlock (i : ℕ) : ℕ := 0x53ea0740536b074007402faf070011802fab070010812fab070010802fab07002fab070011802faa07000e1053eb054053eb05401e2053ea05401d2053ea05401c2053ea054053ea0540118051eb054010c051eb054010a051eb0540108151eb0540108051eb0540106051eb0540104151eb05401d80102151eb05401c88102151eb05401c82102151eb05401c48102151eb05401c22102151eb05401c0a102151eb05401c09102151eb0540102151eb0540102051eb0540100351eb0540100151eb054051eb05401d8051ea05401c2851ea05401c2051ea054051ea05401120516b05401021516b0540516b054005401a8042ab0500188042ab050042ab05000500337a36af0300336b36af0300336a36af030036af03001a8036ab0300188136ab0300188036ab030036ab03002eaf010006802eab010006012eab01002eab01000100130014c00f000cc0070007003eeb04c003000300439a3eeb04c003003eeb04c003001e403eea04c00300030052eb04c003000300044001003aeb08c00700070015000100010003002eea0c1014c0030014c003000440010003000c4046ab044001000440010033aa143010400300190033aa141010400300141010400300030018c0030014101840030001000f000d002eea081004c0010014100440010001000440030014400b00041014400900084007000c10084005000b0001001804041014400d000d003eaa1040090009000cc00100
def blockMove (i : ℕ) := Nat.land (Nat.shiftRight (blockMoveBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def blockFlagBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0x400080000000000000000000000000000000000000c0000000080000000020000008000000000000000000000000001000000000000080000100000000800000000040000000000000000000000000000600000040000000000000000000000000800000200000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000002c000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000004000000000001000000080000040000000000000100000001000000000000000000000000000000000200000000000000000000000000000000000000000000000480000000000000000000000000000800000000000002000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000120000000000000000000004000000000000000000002000000000000000000000000000000000000000008000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000800000400000020000000000000000002000000000000000000000000010000000000002000000000000200000000200000001000000000000001000000000000000000040000000000000000000000000000000000000000000000000800000000000000400000400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b00000000000000000000000000000000000000000020000000200000000000004000000000000800000200000100000004000000100000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000040000000000000000000000000000800000000400000000000000004000000000000000000000000100000000000002 | false => 0x20000000000000000000000800000000000000081000000000800000000001000000000000000010008000000080000000000000002000000000000000000000000000002000000800000000000000000000000000000000000000000200000000004000000030000000100000000000000000000040000000000080000000000000000000004010000000000000080000020004008008000008002080040800000000000800000000008060000000040000000000000000000000000000000000000000000000000000000000000000000080000000000000001800000000000000000000000000800000000000000000000000000000000020000000000000010000000200000000000000000400000000000000002000000000000200000000018000000004000000000000000000000080000000000000000000000000000000000000000200000008000000000010000000000000000000000100000000200000000000001000000000000000400000001000000000000008000000000000000100000001800000000000000000000008000000000000000000000000080000000000000000000000002000000000000000000200000000008000000004000000000000000080000000000000000400000000000000020000000000004000000000000000000000100020000000000000000000040000000000000000000000000000000100000010000000000000000020000000000000020000000000000000000000050000000008000000000000000100000000001000000000400000000000800000000008000000000000000000000000000000c000000001000000000000008000000000000000000000000000000000000000000000060000000000000000000000000000006000000000000000000000001000000000000000000000002000000000001000000000100000001000000000002000000000000000000000000014000000000000040000000000000080000000000000000000000000000000000000000000000000a00000000000080000000002000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000080000000014000000000000020000000000000000002000004000000000000000000000004000000000001000000000000000000000000000000000010000000000000000000000000000000000000000000000000000200000000000000000000000000000000000028000000000000000000000000000004000000000000000000000000002000000000)
def blockFlag (i : ℕ) := Nat.land (Nat.shiftRight (blockFlagBlock (Nat.shiftRight i 7)) (Nat.shiftLeft (Nat.land i 127) 6)) 18446744073709551615
def blockRankBlock (i : ℕ) : ℕ := 0xca00c900c900c800c500c400c200c100c000c000be00be00be00bc00b900b900b800b700b500b300af00ab00a900a600a600a600a600a500a400a300a200a200a100a0009f009e009d009a00990098009800980097009500950093009200910090008f008c008c008b008a008a008900880086008500840083008200810080007f007f007d007d007c007b00790078007600750073007300710070006f006f006f006d006d006b006a006a006800670065006500630062006100610061005f005d005d005d005c005c005c005b00590058005600560054005400540053005300530052005200500050004f004f004e004e004d004c004c004a0048004700460044004300420040003f003e003d003d003c003c003c003c003c003c003b003b003b003b003b003800380038003700370037003700360035003300310031003000300030002e002e002d002c002c002c002c002c002b002b002b002b002b002b002b0029002900280027002700270026002500250025002500250023002200210020001f001e001c001b001a001a001a0019001800170017001700170016001600160016001600150013001300130013001300130013001300130013001300130013001300100010000f000e000c000a0008000700070007000700070007000700070006000500040003000200020000
def blockRank (i : ℕ) := Nat.land (Nat.shiftRight (blockRankBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
abbrev BlockId := Fin 202
def blockCase (i : BlockId) := blockField i.val &&& 255
def blockPointer (i : BlockId) := (blockField i.val >>> 8) &&& 65535
def blockEnd (i : BlockId) := (blockField i.val >>> 24) &&& 65535
def blockBase (i : BlockId) := (blockField i.val >>> 40) &&& 2047
def blockLength (i : BlockId) := blockField i.val >>> 51
def blockFuel (i : BlockId) := 28-blockLength i
def rankPrefix (x : ℕ) : ℕ :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c * 0x0101010101010101) >>> 56) &&& 127
def selectRecord (t : ℕ) : Option BlockId :=
  let pg := t >>> 6
  let bs := blockFlag pg
  let bit := 1 <<< (t &&& 63)
  if Nat.land bs bit == 0 then none else
    let k := blockRank pg + rankPrefix (bs &&& (bit-1))
    some ⟨k % 202,Nat.mod_lt _ (by decide)⟩
abbrev TrailState := ℕ × ℕ × ℕ × ℕ
def replayMoves (e : ℕ) : ℕ → ℕ → TrailState → TrailState
  | 0,_,s => s
  | k+1,a,(D,eq,fl,q) =>
    let w := blockMove a
    let tag := w >>> 10
    let v := w &&& 1023
    let x := if tag < 11 then v else 1023-v
    let d := directSettle e D q
    replayMoves e k (a+1) (replacePacked d tag (1 <<< v),eq &&& sameMark x,
      fl &&& freeMark x,1 <<< (1025*tag+1024))
def blockState (i : BlockId) : EvalState :=
  (blockPointer i,replayMoves (blockCase i) (blockLength i) (blockBase i)
    (actualStart (blockCase i),30,31,guardBits))
def genericTip {ι : Type} (pick : ℕ → Option ι) (grp left stop : ι → ℕ)
    (input : ι → EvalState) (e fuel : ℕ) (s : EvalState) : Option ℕ :=
  match pick s.1 with
  | none => none
  | some i => if grp i == e && left i == fuel && input i == s then some (stop i) else none
def tipFor := genericTip selectRecord blockCase blockFuel blockEnd blockState
def checkBlock (i : BlockId) : Bool :=
  workLayer (blockCase i) (assisted (workLayer (blockCase i)) (tipFor (blockCase i)) (blockFuel i-1)) (blockState i) == blockEnd i
lemma tableHit {ι : Type} (pick : ℕ → Option ι) (grp left stop : ι → ℕ) (input : ι → EvalState)
    {e k v : ℕ} {s : EvalState}
    (hit : genericTip pick grp left stop input e k s = some v) :
    ∃ i, grp i=e ∧ left i=k ∧ input i=s ∧ stop i=v := by
  unfold genericTip at hit
  cases hp : pick s.1 with
  | none => simp [hp] at hit
  | some i =>
    simp only [hp] at hit
    split at hit
    · rename_i ans
      obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp ans
      obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp x
      exact ⟨i,beq_iff_eq.mp a,beq_iff_eq.mp b,beq_iff_eq.mp y,Option.some.inj hit⟩
    · contradiction
lemma normalizedTip (all : ∀ i, checkBlock i = true) (e : ℕ) {k s v}
    (hit : tipFor e (k+1) s = some v) :
    workLayer e (assisted (workLayer e) (tipFor e) k) s = v := by
  obtain ⟨i,he,hf,hs,hv⟩ := tableHit selectRecord blockCase blockFuel blockEnd blockState (e := e) (k := k+1) (v := v) (s := s) hit
  have good : workLayer (blockCase i) (assisted (workLayer (blockCase i)) (tipFor (blockCase i))
      (blockFuel i-1)) (blockState i) = blockEnd i := beq_iff_eq.mp (all i)
  rw [he,hf,hs,hv] at good
  exact good
def checkRoot (e : EnvelopeId) : Bool :=
  (tipFor e.val 28 (workRoot e.val) == some (finalOffset e.val)) && (!(finalOffset e.val == 0))
lemma assisted_hit (f : (EvalState → ℕ) → EvalState → ℕ) {tip k s v} (h : tip (k+1) s = some v) :
    assisted f tip (k+1) s = v := by simp only [assisted,h]
lemma completeRun (all : ∀ i, checkBlock i = true) {e : EnvelopeId} (ok : checkRoot e = true) :
    play (workLayer e.val) 28 (workRoot e.val) ≠ 0 := by
  obtain ⟨raw,nz⟩ := Bool.and_eq_true_iff.mp ok
  have hit : tipFor e.val (27+1) (workRoot e.val) = some (finalOffset e.val) := beq_iff_eq.mp raw
  rw [←assisted_eq (workLayer e.val) (tipFor e.val) (fun _ _ _ => normalizedTip all e.val)]
  rw [assisted_hit (workLayer e.val) hit]
  exact beq_eq_false_iff_ne.mp (Bool.not_eq_true' _ |>.mp nz)
lemma cannotModel (e : EnvelopeId) (scan : play (workLayer e.val) 28 (workRoot e.val) ≠ 0)
    (net : ∀ m i j, testLink e.val m i j = true) : rejectsEnvelope e := by
  intro a b P env cap lh
  obtain ⟨m,hm⟩ := permitted_exists env cap lh
  apply scan
  rw [workLayer,play_spec]
  apply tree_impossible (permittedWorld e.val (fsCode a) (fsCode b)) (fun _ π sw h => permitted_moves h π sw)
    tapeByte hiBit _ _ _ (fuel := 28) (hist := []) (m := m)
  · intro x hx d q ok
    obtain ⟨out,refs,model⟩ := permitted_frame env hx
    exact directSettle_ok model net d q ok
  · intro x hx d tag t ok
    obtain ⟨out,refs,model⟩ := permitted_frame env hx
    exact fastLeaf_safe model ok tapeByte tag t
  · exact fastCanon_ok
  · exact hm
  · simp [fixedHistory]
  · exact ⟨fun _ => le_rfl,fun _ _ _ => le_rfl⟩
  · exact flags_nil m
  · exact fun _ h _ => permitted_start env h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verifiedRoots : ∀ c : RouteId, checkRoot (mappedEnv c)=true := by decide +kernel
def indexedBlock (n : ℕ) := checkBlock ⟨n % 202,Nat.mod_lt _ (by decide)⟩
lemma eightChecks (f : ℕ → Bool) (a : ℕ)
    (h0 : f (a+0)=true)
    (h1 : f (a+1)=true)
    (h2 : f (a+2)=true)
    (h3 : f (a+3)=true)
    (h4 : f (a+4)=true)
    (h5 : f (a+5)=true)
    (h6 : f (a+6)=true)
    (h7 : f (a+7)=true)
    (k : Fin 8) : f (a+k.val)=true := by
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb0 : ∀ b : Fin 8, indexedBlock (0*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb1 : ∀ b : Fin 8, indexedBlock (1*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb2 : ∀ b : Fin 8, indexedBlock (2*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb3 : ∀ b : Fin 8, indexedBlock (3*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb4 : ∀ b : Fin 8, indexedBlock (4*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb5 : ∀ b : Fin 8, indexedBlock (5*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb6 : ∀ b : Fin 8, indexedBlock (6*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb7 : ∀ b : Fin 8, indexedBlock (7*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb8 : ∀ b : Fin 8, indexedBlock (8*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb9 : ∀ b : Fin 8, indexedBlock (9*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb10 : ∀ b : Fin 8, indexedBlock (10*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb11 : ∀ b : Fin 8, indexedBlock (11*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb12 : ∀ b : Fin 8, indexedBlock (12*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb13 : ∀ b : Fin 8, indexedBlock (13*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb14 : ∀ b : Fin 8, indexedBlock (14*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb15 : ∀ b : Fin 8, indexedBlock (15*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb16 : ∀ b : Fin 8, indexedBlock (16*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb17 : ∀ b : Fin 8, indexedBlock (17*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb18 : ∀ b : Fin 8, indexedBlock (18*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb19 : ∀ b : Fin 8, indexedBlock (19*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb20 : ∀ b : Fin 8, indexedBlock (20*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb21 : ∀ b : Fin 8, indexedBlock (21*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb22 : ∀ b : Fin 8, indexedBlock (22*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb23 : ∀ b : Fin 8, indexedBlock (23*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb24 : ∀ b : Fin 8, indexedBlock (24*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb25 : ∀ b : Fin 8, indexedBlock (25*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verifiedBlocks (i : BlockId) : checkBlock i=true := by
  have groups (g : Fin 26) : ∀ b : Fin 8, indexedBlock (g.val*8+b.val)=true := by
    fin_cases g
    · exact gb0
    · exact gb1
    · exact gb2
    · exact gb3
    · exact gb4
    · exact gb5
    · exact gb6
    · exact gb7
    · exact gb8
    · exact gb9
    · exact gb10
    · exact gb11
    · exact gb12
    · exact gb13
    · exact gb14
    · exact gb15
    · exact gb16
    · exact gb17
    · exact gb18
    · exact gb19
    · exact gb20
    · exact gb21
    · exact gb22
    · exact gb23
    · exact gb24
    · exact gb25
  let g : Fin 26 := ⟨i.val/8,by omega⟩
  let k : Fin 8 := ⟨i.val % 8,by omega⟩
  have eq : (g.val*8+k.val) % 202 = i.val := by dsimp [g,k]; omega
  have idEq : (⟨(g.val*8+k.val) % 202,Nat.mod_lt _ (by decide)⟩ : BlockId) = i := Fin.ext eq
  exact idEq ▸ groups g k
lemma noPossibleLayout (A B : Finset V) (P : Feature → Slot → Prop)
    (dirty : ∃ r, present A B (rows r) none) (cap : capacity A B P) (h : layout A B P) : False :=
  dispatchSelected routeChecks (fun c => cannotModel (mappedEnv c) (completeRun verifiedBlocks (verifiedRoots c)) (chosenNet c)) A B P dirty cap h
end PEqualNP.Outside.L_meta_905

theorem PEqualNP.Outside.L_meta_905 : ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
  ¬ (∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true)) := by
  rintro G rfl ⟨C,wf,small,bare,spec⟩
  exact PEqualNP.Outside.L_meta_905.reduce_problem PEqualNP.Outside.L_meta_905.noPossibleLayout C wf small bare spec
