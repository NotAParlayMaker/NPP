import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]


def wire {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def single {n : ℕ} (p : Fin n) (q : Fin n) : Bool := decide (q = p)

def support (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => wire C w (single p) = true)

def Owned {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  support n C w ⊆ S ∧ 2 ≤ (support n C w).card

def Pass {n : ℕ} (C : Circuit) (w : ℕ) (x y : Fin n → Bool) : Prop :=
  wire C w x = true → wire C w y = true

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (h : w < n) :
    wire C w x = x ⟨w,h⟩ := by
  rw [wire, wires_eq_foldl, foldl_step_getD_lt _ _ _ (by simpa), ofFn_getD_lt]

lemma bad_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (h : n + C.size ≤ w) :
    wire C w x = false := by
  rw [wire, wires_eq_foldl, foldl_step_getD_ge]
  simpa [Circuit.size] using h

lemma owned_bounds {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {w : ℕ}
    (h : Owned C S w) : n ≤ w ∧ w < n + C.size := by
  have hc := h.2
  constructor
  · by_contra! hl
    have eqn : support n C w = {⟨w,hl⟩} := by
      ext p
      simp [support, input_value C _ hl, single, eq_comm]
    simp [eqn] at hc
  · by_contra! hh
    have eqn : support n C w = ∅ := by ext p; simp [support, bad_value C _ hh]
    simp [eqn] at hc

def Binary (C : Circuit) : Prop := ∀ g ∈ C.gates,
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

lemma parents {n : ℕ} {C : Circuit} (bin : Binary C) {w : ℕ}
    (lo : n ≤ w) (hi : w < n + C.size) :
    ∃ a b : ℕ, (a < w ∨ a = n + C.size) ∧ (b < w ∨ b = n + C.size) ∧
      ∀ x y : Fin n → Bool, Pass C a x y → Pass C b x y → Pass C w x y := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j; unfold Circuit.size at hi; omega
  let g := C.gates[j]
  have hjg : C.gates[j]? = some g := by simp [g,hj]
  obtain ⟨hop,hlen⟩ := bin g (List.getElem_mem hj)
  obtain ⟨u,v,huv⟩ : ∃ u v, g.inputs = [u,v] := by
    rcases he : g.inputs with _ | ⟨u,tail⟩ <;> simp [he] at hlen
    rcases tail with _ | ⟨v,tail⟩ <;> simp_all
  let clip := fun z : ℕ => if z < w then z else n + C.size
  have hw : n + j = w := by unfold j; omega
  have val (x : Fin n → Bool) (z : ℕ) :
      wire C (clip z) x = (if z < w then wire C z x else false) := by
    by_cases hz : z < w <;> simp [clip,hz,bad_value]
  have gate (x : Fin n → Bool) : wire C w x =
      g.op.eval [wire C (clip u) x, wire C (clip v) x] := by
    have H := wires_gate_ofFn C x j g hjg
    rw [hw,huv] at H
    rw [val,val]
    exact H
  refine ⟨clip u,clip v,by simp [clip]; split <;> simp_all,
    by simp [clip]; split <;> simp_all, ?_⟩
  intro x y ha hb
  unfold Pass at *
  rw [gate x,gate y]
  rcases hop with ho | ho <;> simp [ho,GateOp.eval] <;> tauto

lemma pass_of_inputs {n : ℕ} {C : Circuit} (bin : Binary C)
    {x y : Fin n → Bool} (h : ∀ p, x p = true → y p = true) (w : ℕ) : Pass C w x y := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases lo : w < n
    · simpa only [Pass,input_value C _ lo] using h ⟨w,lo⟩
    by_cases hi : n + C.size ≤ w
    · simp [Pass,bad_value C _ hi]
    obtain ⟨a,b,ha,hb,hg⟩ := parents bin (Nat.le_of_not_gt lo) (Nat.lt_of_not_ge hi)
    apply hg x y
    · rcases ha with hl | rfl
      · exact ih _ hl
      · simp [Pass,bad_value]
    · rcases hb with hl | rfl
      · exact ih _ hl
      · simp [Pass,bad_value]


noncomputable def cost {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (t : ℕ) : ℕ := by
  classical exact ∑ j ∈ Finset.range t, if Owned C S (n+j) then 1 else 0

lemma frontier {n : ℕ} {C : Circuit} (bin : Binary C) (S : Finset (Fin n))
    (t : ℕ) (F : Finset ℕ) (bound : ∀ w ∈ F, Owned C S w → w < n+t) :
    ∃ B : Finset ℕ, (∀ w ∈ B, ¬ Owned C S w) ∧ B.card ≤ F.card + cost C S t ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, Pass C w x y) → ∀ w ∈ F, Pass C w x y := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F,?_,by simp [cost],fun _ _ h => h⟩
    intro w hw h
    have := bound w hw h
    have := (owned_bounds h).1
    omega
  | succ t ih =>
    by_cases expand : n+t ∈ F ∧ Owned C S (n+t)
    · obtain ⟨member,priv⟩ := expand
      obtain ⟨a,b,ha,hb,hgate⟩ := parents bin (owned_bounds priv).1 (owned_bounds priv).2
      let E := insert a (insert b (F.erase (n+t)))
      have parent_lt (v : ℕ) (hv : v < n+t ∨ v = n+C.size) (hp : Owned C S v) : v < n+t := by
        have := (owned_bounds hp).2
        omega
      have limits : ∀ w ∈ E, Owned C S w → w < n+t := by
        intro w hw hp
        simp only [E,Finset.mem_insert,Finset.mem_erase] at hw
        rcases hw with rfl | rfl | ⟨hne,hf⟩
        · exact parent_lt _ ha hp
        · exact parent_lt _ hb hp
        · have := bound w hf hp
          omega
      obtain ⟨B,hB,hsize,hpass⟩ := ih E limits
      refine ⟨B,hB,?_,?_⟩
      · have h1 := Finset.card_insert_le a (insert b (F.erase (n+t)))
        have h2 := Finset.card_insert_le b (F.erase (n+t))
        have h3 := Finset.card_erase_add_one member
        simp only [cost,Finset.sum_range_succ,priv,↓reduceIte] at hsize ⊢
        dsimp only [E] at hsize
        omega
      · intro x y h w hw
        have keep := hpass x y h
        by_cases he : w = n+t
        · subst w
          exact hgate x y (keep a (by simp [E])) (keep b (by simp [E]))
        · exact keep w (by simp [E,he,hw])
    · have limits : ∀ w ∈ F, Owned C S w → w < n+t := by
        intro w hw hp
        have := bound w hw hp
        have : w ≠ n+t := by rintro rfl; exact expand ⟨hw,hp⟩
        omega
      obtain ⟨B,hB,hsize,hpass⟩ := ih F limits
      refine ⟨B,hB,?_,hpass⟩
      simp only [cost,Finset.sum_range_succ] at hsize ⊢
      omega


lemma output_cost {n k : ℕ} {C : Circuit} (bin : Binary C) (S : Finset (Fin n))
    (o c : ℕ) (ck : c ≤ k) (large : c+1 ≤ (support n C o).card)
    (promise : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → wire C o x = false) : c ≤ cost C S C.size := by
  classical
  by_contra! cheap
  obtain ⟨B,hB,hsize,hpass⟩ := frontier bin S C.size {o} (fun _ _ h => (owned_bounds h).2)
  simp only [Finset.card_singleton] at hsize
  let rep (w : ℕ) : Finset (Fin n) :=
    if h : ∃ q ∈ support n C w, q ∉ S then {h.choose} else support n C w
  have small (w : ℕ) (hw : w ∈ B) : (rep w).card ≤ 1 := by
    dsimp only [rep]
    split
    · simp
    · rename_i h
      have sub : support n C w ⊆ S := by intro q hq; by_contra hn; exact h ⟨q,hq,hn⟩
      have denied := hB w hw
      have few : ¬ 2 ≤ (support n C w).card := fun h₂ => denied ⟨sub,h₂⟩
      omega
  let A := B.biUnion rep
  have limit : A.card ≤ B.card := calc
    A.card ≤ ∑ w ∈ B, (rep w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ B, 1 := Finset.sum_le_sum small
    _ = B.card := by simp
  obtain ⟨p,hp,hmiss⟩ : ∃ p ∈ support n C o, p ∉ A := by
    by_contra! contained
    have := Finset.card_le_card contained
    omega
  let test (q : Fin n) : Bool := decide (q ∈ A \ S)
  have test_on : Finset.univ.filter (fun q => test q = true) = A \ S := by
    ext q
    simp [test]
  have test_off : wire C o test = false := by
    apply promise
    · rw [test_on]
      have := Finset.card_le_card (Finset.sdiff_subset (s := A) (t := S))
      omega
    · intro q hq
      simp [test,hq]
  have compare (w : ℕ) (hw : w ∈ B) : Pass C w (single p) test := by
    intro accept
    have pmem : p ∈ support n C w := by simpa [support] using accept
    by_cases outside : ∃ q ∈ support n C w, q ∉ S
    · let q := outside.choose
      obtain ⟨hq,hqS⟩ := outside.choose_spec
      have hrep : q ∈ rep w := by simp [rep,outside,q]
      have hA : q ∈ A := Finset.mem_biUnion.mpr ⟨w,hw,hrep⟩
      apply pass_of_inputs bin (x := single q) (y := test) _ w
      · simpa [support,q] using hq
      · intro v hv
        have : v = q := by simpa [single] using hv
        simp [this,test,hA,hqS,q]
    · have hrep : p ∈ rep w := by simpa [rep,outside] using pmem
      exact (hmiss (Finset.mem_biUnion.mpr ⟨w,hw,hrep⟩)).elim
  have on := hpass (single p) test compare o (by simp) (by simpa [support] using hp)
  simp [test_off] at on

lemma total_cost {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (overlap : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∑ i, cost C (S i) C.size ≤ C.size := by
  classical
  have unique (w : ℕ) {i j : Fin m} (hi : Owned C (S i) w) (hj : Owned C (S j) w) : i = j := by
    by_contra h
    have sub : support n C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi.1 hp,hj.1 hp⟩
    have := Finset.card_le_card sub
    have := overlap i j h
    have := hi.2
    omega
  unfold cost
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j ∈ Finset.range C.size, 1 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : ∃ i, Owned C (S i) (n+j)
      · obtain ⟨i,hi⟩ := h
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro b _ hne
          have hn : ¬ Owned C (S b) (n+j) := fun hb => hne (unique _ hb hi)
          simp [hn]
        · simp
      · simp_all
    _ = C.size := by simp

end PEqualNP.Outside.L_meta_782

open PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c overlap _ bin _ promise ck large
  exact (Finset.sum_le_sum (fun i _ => output_cost bin (S i) (o i) (c i)
    (ck i) (large i) (promise i))).trans (total_cost C S overlap)
