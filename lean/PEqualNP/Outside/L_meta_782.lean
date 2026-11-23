import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782_aux

open PEqualNP.CircuitLowerBounds

-- Basic wire identities from L-meta-717.
def stepWires (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def runWires (m : ℕ) (gs : List Gate) (x : Fin m → Bool) : List Bool :=
  gs.foldl stepWires (List.ofFn x)

def wireVal (m : ℕ) (gs : List Gate) (x : Fin m → Bool) (i : ℕ) : Bool :=
  (runWires m gs x).getD i false

def wireAt (m : ℕ) (gs : List Gate) (bound i : ℕ) (x : Fin m → Bool) : Bool :=
  if i < bound then wireVal m gs x i else false

lemma foldl_stepWires_length (gs : List Gate) (ws : List Bool) :
    (gs.foldl stepWires ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, stepWires, List.length_append]
    simp only [List.length_nil]
    omega

lemma runWires_length (m : ℕ) (gs : List Gate) (x : Fin m → Bool) :
    (runWires m gs x).length = m + gs.length := by
  unfold runWires
  rw [foldl_stepWires_length, List.length_ofFn]

lemma foldl_stepWires_getD_lt (gs : List Gate) (ws : List Bool) {i : ℕ} (hi : i < ws.length) :
    (gs.foldl stepWires ws).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWires ws g).length := by
      simp only [stepWires, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (stepWires ws g) hlt, List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hi]
    simp only [stepWires, List.getElem_append_left hi]

lemma wireVal_input (m : ℕ) (gs : List Gate) (x : Fin m → Bool) (v : Fin m) :
    wireVal m gs x v.val = x v := by
  unfold wireVal runWires
  have hv : v.val < (List.ofFn x).length := by simp
  rw [foldl_stepWires_getD_lt gs (List.ofFn x) hv, List.getD_eq_getElem _ _ hv, List.getElem_ofFn]

lemma wireVal_of_ge (m : ℕ) (gs : List Gate) (x : Fin m → Bool) {i : ℕ} (hi : m + gs.length ≤ i) :
    wireVal m gs x i = false := by
  unfold wireVal
  rw [List.getD_eq_default]
  rw [runWires_length]
  exact hi

lemma wireVal_gate (m : ℕ) (gs : List Gate) (x : Fin m → Bool) {k : ℕ} (hk : k < gs.length) :
    wireVal m gs x (m + k) =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => wireAt m gs (m + k) i x) := by
  unfold wireVal runWires
  have hsplit : gs = gs.take k ++ (gs[k]'hk) :: gs.drop (k + 1) := by
    simp
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  set ws := (gs.take k).foldl stepWires (List.ofFn x)
  have hws_len : ws.length = m + k := by
    rw [foldl_stepWires_length, List.length_ofFn, List.length_take]
    omega
  have hstep_len : (stepWires ws (gs[k]'hk)).length = m + k + 1 := by
    simp [stepWires, hws_len]
  have hlt : m + k < (stepWires ws (gs[k]'hk)).length := by omega
  rw [foldl_stepWires_getD_lt (gs.drop (k + 1)) (stepWires ws (gs[k]'hk)) hlt]
  have hlast : (stepWires ws (gs[k]'hk)).getD (m + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => ws.getD i false) := by
    rw [List.getD_eq_getElem _ _ hlt]
    simp [stepWires, hws_len]
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i _
  unfold wireAt
  split_ifs with hi
  · have hi_ws : i < ws.length := by omega
    have hsplit2 : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    symm
    unfold wireVal runWires
    rw [hsplit2, List.foldl_append]
    exact foldl_stepWires_getD_lt (gs.drop k) ws hi_ws
  · rw [List.getD_eq_default]
    omega

def dominates {α : Type} (v : α → ℕ → Bool) (F : Finset ℕ) (x y : α) : Prop :=
  ∀ w ∈ F, v x w = true → v y w = true

-- Replace each private gate on the boundary by its two earlier operands.
-- This preserves comparisons at the output and adds at most one boundary wire per gate.
theorem cut {α : Type} (v : α → ℕ → Bool) (parents : ℕ → Finset ℕ)
    (P F : Finset ℕ)
    (spec : ∀ w ∈ P, (parents w).card ≤ 2 ∧ (∀ a ∈ parents w, a < w) ∧
      ∀ x y, dominates v (parents w) x y → v x w = true → v y w = true) :
    ∃ B : Finset ℕ, (∀ w ∈ B, w ∉ P) ∧ B.card ≤ F.card + P.card ∧
      (∀ w ∈ B, w ∈ F ∨ ∃ p ∈ P, w < p) ∧
      ∀ x y, dominates v B x y → dominates v F x y := by
  classical
  induction P using Finset.induction_on_max generalizing F with
  | empty => exact ⟨F, by simp, by simp, fun _ h => Or.inl h, fun _ _ h => h⟩
  | insert a P lt ih =>
    have ha := spec a (Finset.mem_insert_self ..)
    have hnot : a ∉ P := fun h => lt_irrefl _ (lt a h)
    let R := if a ∈ F then F.erase a ∪ parents a else F
    have har : a ∉ R := by
      by_cases h : a ∈ F
      · have notParent : a ∉ parents a := fun h' => lt_irrefl a (ha.2.1 a h')
        simp [R,h,notParent]
      · simp [R,h]
    have rc : R.card ≤ F.card + 1 := by
      by_cases h : a ∈ F
      · rw [show R = F.erase a ∪ parents a by simp [R,h]]
        have b := Finset.card_union_le (F.erase a) (parents a)
        have e := Finset.card_erase_add_one h
        omega
      · simp [R,h]
    have inlet (w : ℕ) (hw : w ∈ R) : w ∈ F ∨ w < a := by
      by_cases h : a ∈ F
      · simp only [R, ite_eq_left h, Finset.mem_union, Finset.mem_erase] at hw
        exact hw.elim (fun z => Or.inl z.2) (fun z => Or.inr (ha.2.1 w z))
      · exact Or.inl (by simpa [R,h] using hw)
    obtain ⟨B, outside, card, source, transfer⟩ :=
      ih R (fun w hw => spec w (Finset.mem_insert_of_mem hw))
    refine ⟨B, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rw [Finset.mem_insert]
      rintro (rfl | hp)
      · rcases source w hw with hr | ⟨z,hz,hl⟩
        · exact har hr
        · exact (lt_asymm hl) (lt z hz)
      · exact outside w hw hp
    · rw [Finset.card_insert_of_notMem hnot]
      omega
    · intro w hw
      rcases source w hw with hr | ⟨z,hz,hl⟩
      · exact (inlet w hr).elim Or.inl (fun hl => Or.inr ⟨a,Finset.mem_insert_self ..,hl⟩)
      · exact Or.inr ⟨z,Finset.mem_insert_of_mem hz,hl⟩
    · intro x y hxy w hw
      have h := transfer x y hxy
      by_cases haF : a ∈ F
      · rw [show R = F.erase a ∪ parents a by simp [R,haF]] at h
        by_cases he : w = a
        · subst w
          exact ha.2.2 x y (fun z hz => h z (Finset.mem_union_right _ hz))
        · exact h w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hw⟩))
      · rw [show R = F by simp [R,haF]] at h
        exact h w hw

def binary (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def parentsOf (n : ℕ) (gs : List Gate) (w : ℕ) : Finset ℕ :=
  (((gs[w-n]?).map Gate.inputs).getD []).toFinset.filter (fun a => a < w)

theorem gateRule (n : ℕ) (gs : List Gate) (hg : binary gs) (j : ℕ) (hj : j < gs.length) :
    (parentsOf n gs (n+j)).card ≤ 2 ∧ (∀ a ∈ parentsOf n gs (n+j), a < n+j) ∧
    ∀ x y, dominates (wireVal n gs) (parentsOf n gs (n+j)) x y →
      wireVal n gs x (n+j) = true → wireVal n gs y (n+j) = true := by
  obtain ⟨op, len⟩ := hg gs[j] (List.getElem_mem hj)
  obtain ⟨a,b,ab⟩ := List.length_eq_two.mp len
  have ps : parentsOf n gs (n+j) = ({a,b} : Finset ℕ).filter (fun w => w < n+j) := by
    simp [parentsOf, List.getElem?_eq_getElem hj, ab]
  refine ⟨?_, ?_, ?_⟩
  · rw [ps]
    have h := Finset.card_le_card (Finset.filter_subset (fun w => w < n+j) ({a,b} : Finset ℕ))
    have hh := Finset.card_insert_le a ({b} : Finset ℕ)
    simp only [Finset.card_singleton] at hh
    omega
  · intro w hw
    exact (Finset.mem_filter.mp hw).2
  · intro x y h
    have step {w : ℕ} (hw : w ∈ ({a,b} : Finset ℕ)) :
        wireAt n gs (n+j) w x = true → wireAt n gs (n+j) w y = true := by
      by_cases hl : w < n+j
      · simpa [wireAt,hl] using h w (ps ▸ Finset.mem_filter.mpr ⟨hw,hl⟩)
      · simp [wireAt,hl]
    have ha := step (w := a) (by simp)
    have hb := step (w := b) (by simp)
    rw [wireVal_gate n gs x hj,wireVal_gate n gs y hj,ab]
    rcases op with op | op
    · simp only [op,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id,
        Bool.and_true,Bool.and_eq_true]
      exact fun h => ⟨ha h.1,hb h.2⟩
    · simp only [op,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id,
        Bool.or_false,Bool.or_eq_true]
      exact Or.imp ha hb

theorem wire_mono {n : ℕ} (gs : List Gate) (hg : binary gs) (x y : Fin n → Bool)
    (incl : ∀ i, x i = true → y i = true) (w : ℕ) :
    wireVal n gs x w = true → wireVal n gs y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let i : Fin n := ⟨w,hw⟩
      exact (wireVal_input n gs x i) ▸ (wireVal_input n gs y i) ▸ incl i
    by_cases ht : n + gs.length ≤ w
    · simp [wireVal_of_ge n gs x ht]
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hw)
    have rule := gateRule n gs hg j (by omega)
    exact rule.2.2 x y (fun a ha => ih a (rule.2.1 a ha))

def singletonInput {n : ℕ} (p : Fin n) (q : Fin n) : Bool := decide (q = p)

def support (n : ℕ) (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => wireVal n gs (singletonInput a) w = true)

def privateGates (n : ℕ) (gs : List Gate) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n+gs.length)).filter (fun w => support n gs w ⊆ S ∧ 2 ≤ (support n gs w).card)

theorem private_of_support {n : ℕ} {gs : List Gate} {S : Finset (Fin n)} {w : ℕ}
    (sub : support n gs w ⊆ S) (many : 2 ≤ (support n gs w).card) :
    w ∈ privateGates n gs S := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ico.mpr ⟨?_,?_⟩,sub,many⟩
  · by_contra! hw
    let i : Fin n := ⟨w,hw⟩
    have eq : support n gs w = {i} := by
      ext a
      change a ∈ support n gs i.val ↔ _
      simp [support,wireVal_input,singletonInput,eq_comm]
    simp [eq] at many
  · by_contra! hw
    have eq : support n gs w = ∅ := by simp [support, fun x => wireVal_of_ge n gs x hw]
    simp [eq] at many

theorem union_bound {n : ℕ} (B : Finset ℕ) (t : ℕ → Finset (Fin n))
    (one : ∀ w ∈ B, (t w).card ≤ 1) : (B.biUnion t).card ≤ B.card := by
  calc
    _ ≤ ∑ w ∈ B, (t w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ B, 1 := Finset.sum_le_sum one
    _ = _ := by simp

theorem cost_one {n k c : ℕ} (gs : List Gate) (S : Finset (Fin n)) (o : ℕ)
    (hg : binary gs) (hc : c ≤ k) (large : c+1 ≤ (support n gs o).card)
    (promise : ∀ x : Fin n → Bool, (Finset.univ.filter (fun a => x a = true)).card ≤ k →
      (∀ a ∈ S, x a = false) → wireVal n gs x o = false) :
    c ≤ (privateGates n gs S).card := by
  classical
  by_contra! tooFew
  let P := privateGates n gs S
  have rule (w : ℕ) (hw : w ∈ P) :
      (parentsOf n gs w).card ≤ 2 ∧ (∀ a ∈ parentsOf n gs w, a < w) ∧
      ∀ x y, dominates (wireVal n gs) (parentsOf n gs w) x y →
        wireVal n gs x w = true → wireVal n gs y w = true := by
    have ⟨lo,hi⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le lo
    exact gateRule n gs hg j (by omega)
  obtain ⟨B,outside,bc,_,transfer⟩ := cut (wireVal n gs) (parentsOf n gs) P {o} rule
  have small : B.card ≤ c := by
    simp only [Finset.card_singleton] at bc
    change P.card < c at tooFew
    omega
  -- Each boundary wire supported inside S accepts at most one singleton.
  let smallSupport (w : ℕ) := if support n gs w ⊆ S then support n gs w else ∅
  have oneSmall (w : ℕ) (hw : w ∈ B) : (smallSupport w).card ≤ 1 := by
    by_cases sub : support n gs w ⊆ S
    · simp only [smallSupport, ite_eq_left sub]
      by_contra! big
      exact outside w hw (private_of_support sub (by omega))
    · simp [smallSupport,sub]
  let Y := B.biUnion smallSupport
  have hy : Y.card ≤ c := (union_bound B smallSupport oneSmall).trans small
  have notSub : ¬support n gs o ⊆ Y := fun h => by
    have := Finset.card_le_card h
    omega
  obtain ⟨a,hao,hay⟩ := Finset.not_subset.mp notSub
  -- Choose one outside point for every remaining boundary wire.
  let pick (w : ℕ) : Finset (Fin n) :=
    if h : ∃ b ∈ support n gs w, b ∉ S then {h.choose} else ∅
  have pick_size (w : ℕ) : (pick w).card ≤ 1 := by
    dsimp [pick]
    split <;> simp
  let X := B.biUnion pick
  let input (q : Fin n) := decide (q ∈ X)
  have hx : (Finset.univ.filter (fun q => input q = true)) = X := by ext b; simp [input]
  have zero (q : Fin n) (hqs : q ∈ S) : input q = false := by
    simp only [input, decide_eq_false_iff_not]
    intro hm
    obtain ⟨w,_,hp⟩ := Finset.mem_biUnion.mp hm
    unfold pick at hp
    split at hp
    · rename_i h
      have he := Finset.mem_singleton.mp hp
      exact h.choose_spec.2 (he ▸ hqs)
    · exact Finset.notMem_empty _ hp
  have evalFalse := promise input (hx ▸ (union_bound B pick (fun w _ => pick_size w)).trans
    (small.trans hc)) zero
  -- This outside input dominates the omitted singleton on the boundary.
  have dom : dominates (wireVal n gs) B (singletonInput a) input := by
    intro w hw hit
    by_cases sub : support n gs w ⊆ S
    · exfalso
      apply hay
      apply Finset.mem_biUnion.mpr
      refine ⟨w,hw,?_⟩
      rw [show smallSupport w = support n gs w by simp [smallSupport,sub]]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
    · have h : ∃ b ∈ support n gs w, b ∉ S := Finset.not_subset.mp sub
      have hmem : h.choose ∈ X := Finset.mem_biUnion.mpr ⟨w,hw,by simp [pick,h]⟩
      have hval := (Finset.mem_filter.mp h.choose_spec.1).2
      apply wire_mono gs hg (singletonInput h.choose) input _ w hval
      intro i hi
      have eq : i = h.choose := by simpa [singletonInput] using hi
      simpa [input,eq] using hmem
  have evalTrue := transfer _ _ dom o (Finset.mem_singleton_self _) (Finset.mem_filter.mp hao).2
  simp_all

end PEqualNP.Outside.L_meta_782_aux

open PEqualNP.Outside.L_meta_782_aux
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c overlap _ hg _ promise hk large
  classical
  let P (i : Fin m) := privateGates n C.gates (S i)
  have budget (i : Fin m) : c i ≤ (P i).card :=
    cost_one C.gates (S i) (o i) hg (hk i) (large i) (promise i)
  -- A gate private to two outputs would put two points in their intersection.
  have disj : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have ai := (Finset.mem_filter.mp hi).2
    have aj := (Finset.mem_filter.mp hj).2
    have sub : support n C.gates w ⊆ S i ∩ S j := Finset.subset_inter ai.1 aj.1
    have small := (Finset.card_le_card sub).trans (overlap i j hij)
    exact (by omega : False)
  calc
    ∑ i, c i ≤ ∑ i, (P i).card := Finset.sum_le_sum (fun i _ => budget i)
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion disj).symm
    _ ≤ (Finset.Ico n (n + C.gates.length)).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp [Circuit.size]
