import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_666

def line (w : Fin 7) : Finset (Fin 7) :=
  ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)

private theorem lineCard : ∀ w : Fin 7, (line w).card = 3 := by decide

private theorem lineInjective : ∀ w z : Fin 7, line w = line z → w = z := by decide

private def charge (w : Fin 7) (a : Finset (Fin 7)) : Nat :=
  if (a.card = 2 ∧ a ⊆ line w) ∨ (a.card = 4 ∧ line w ⊆ a) then 2
  else if a.card = 5 ∧ line w ⊆ a then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem eachSetCharge : ∀ a : Finset (Fin 7), (∑ w : Fin 7, charge w a) ≤ 2 := by
  decide +kernel

private theorem chargeOfPair {w : Fin 7} {a : Finset (Fin 7)} (h : a.card = 2)
    (s : a ⊆ line w) : charge w a = 2 := by simp [charge,h,s]

private theorem chargeOfFour {w : Fin 7} {a : Finset (Fin 7)} (h : a.card = 4)
    (s : line w ⊆ a) : charge w a = 2 := by simp [charge,h,s]

private theorem chargeOfFive {w : Fin 7} {a : Finset (Fin 7)} (h : a.card = 5)
    (s : line w ⊆ a) : charge w a = 1 := by simp [charge,h,s]

private theorem inSetsOfSize (S : Finset (Finset (Fin 7))) (a : Finset (Fin 7))
    (lo : 1 < a.card) (hi : a.card < 7)
    (h : a.card ≤ 1 ∨ a = Finset.univ ∨ a ∈ S) : a ∈ S := by
  rcases h with small | whole | inside
  · omega
  · have hcard : a.card = 7 := by simp [whole]
    omega
  · exact inside

private theorem lineCharge (S : Finset (Finset (Fin 7))) (w : Fin 7)
    (a b : Finset (Fin 7))
    (ha : a.card ≤ 1 ∨ a = Finset.univ ∨ a ∈ S)
    (hb : b.card ≤ 1 ∨ b = Finset.univ ∨ b ∈ S)
    (hneA : a ≠ line w) (hneB : b ≠ line w)
    (hprod : a ∪ b = line w ∨ a ∩ b = line w) :
    2 ≤ ∑ z ∈ S, charge w z := by
  have single (z : Finset (Fin 7)) (hm : z ∈ S) (hc : charge w z = 2) :
      2 ≤ ∑ c ∈ S, charge w c := by
    rw [← hc]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
  have hline := lineCard w
  rcases hprod with union | inter
  · have asub : a ⊆ line w := by rw [← union]; exact Finset.subset_union_left
    have bsub : b ⊆ line w := by rw [← union]; exact Finset.subset_union_right
    have al := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨asub,hneA⟩)
    have bl := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨bsub,hneB⟩)
    have sumCards := Finset.card_union_le a b
    rw [union,hline] at sumCards
    have sizes : a.card = 2 ∨ b.card = 2 := by omega
    rcases sizes with h | h
    · exact single a (inSetsOfSize S a (by omega) (by omega) ha) (chargeOfPair h asub)
    · exact single b (inSetsOfSize S b (by omega) (by omega) hb) (chargeOfPair h bsub)
  · have asub : line w ⊆ a := by rw [← inter]; exact Finset.inter_subset_left
    have bsub : line w ⊆ b := by rw [← inter]; exact Finset.inter_subset_right
    have al := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨asub,hneA.symm⟩)
    have bl := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨bsub,hneB.symm⟩)
    by_cases aFour : a.card = 4
    · exact single a (inSetsOfSize S a (by omega) (by omega) ha) (chargeOfFour aFour asub)
    by_cases bFour : b.card = 4
    · exact single b (inSetsOfSize S b (by omega) (by omega) hb) (chargeOfFour bFour bsub)
    have inclusion := Finset.card_le_card (Finset.subset_univ (a ∪ b))
    have hseven : (Finset.univ : Finset (Fin 7)).card = 7 := by simp
    rw [hseven] at inclusion
    have sumCard := Finset.card_union_add_card_inter a b
    rw [inter,hline] at sumCard
    have aFive : a.card = 5 := by omega
    have bFive : b.card = 5 := by omega
    have ain := inSetsOfSize S a (by omega) (by omega) ha
    have bin := inSetsOfSize S b (by omega) (by omega) hb
    have ne : a ≠ b := by
      intro he
      apply hneA
      simpa only [← he, Finset.inter_self] using inter
    have covered : ({a,b} : Finset (Finset (Fin 7))) ⊆ S := by
      intro c hc
      simp only [Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ain
      · exact bin
    calc
      2 = ∑ z ∈ ({a,b} : Finset (Finset (Fin 7))), charge w z := by
        simp [Finset.sum_insert,ne,chargeOfFive aFive asub,chargeOfFive bFive bsub]
      _ ≤ ∑ z ∈ S, charge w z :=
        Finset.sum_le_sum_of_subset_of_nonneg covered (fun _ _ _ => Nat.zero_le _)

theorem set_bound (S : Finset (Finset (Fin 7))) (hl : ∀ w : Fin 7, line w ∈ S)
    (hp : ∀ w : Fin 7, ∃ a b : Finset (Fin 7),
      (a.card ≤ 1 ∨ a = Finset.univ ∨ a ∈ S) ∧
      (b.card ≤ 1 ∨ b = Finset.univ ∨ b ∈ S) ∧
      a ≠ line w ∧ b ≠ line w ∧ (a ∪ b = line w ∨ a ∩ b = line w)) :
    14 ≤ S.card := by
  let other := S.filter (fun a => a.card ≠ 3)
  let lines := Finset.univ.image line
  have lineCount : lines.card = 7 := by
    change (Finset.univ.image line).card = 7
    rw [Finset.card_image_of_injective _ (fun _ _ h => lineInjective _ _ h)]
    simp
  have lineSub : lines ⊆ S := by
    intro a ha
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp ha
    exact hl w
  have otherSub : other ⊆ S := Finset.filter_subset _ _
  have apart : Disjoint lines other := by
    rw [Finset.disjoint_left]
    intro a ha ho
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp ho).2 (lineCard w)
  have count := Finset.card_le_card (Finset.union_subset lineSub otherSub)
  rw [Finset.card_union_of_disjoint apart,lineCount] at count
  have low : 14 ≤ ∑ w : Fin 7, ∑ a ∈ S, charge w a := by
    calc
      14 = ∑ _w : Fin 7, (2 : Nat) := by decide
      _ ≤ ∑ w : Fin 7, ∑ a ∈ S, charge w a := by
        apply Finset.sum_le_sum
        intro w _
        obtain ⟨a,b,ha,hb,na,nb,prod⟩ := hp w
        exact lineCharge S w a b ha hb na nb prod
  have hi : (∑ w : Fin 7, ∑ a ∈ S, charge w a) ≤ 2 * other.card := by
    rw [Finset.sum_comm]
    have zero (a : Finset (Fin 7)) (ha : a ∈ S) (hna : a ∉ other) :
        (∑ w : Fin 7, charge w a) = 0 := by
      have h : a.card = 3 := by
        by_contra hn
        exact hna (Finset.mem_filter.mpr ⟨ha,hn⟩)
      simp [charge,h]
    rw [← Finset.sum_subset otherSub zero]
    calc
      (∑ a ∈ other, ∑ w : Fin 7, charge w a) ≤ ∑ _a ∈ other, (2 : Nat) :=
        Finset.sum_le_sum (fun a _ => eachSetCharge a)
      _ = 2 * other.card := by simp [Nat.mul_comm]
  omega

open PEqualNP.CircuitLowerBounds

def inputSupports : List (Finset (Fin 7)) :=
  List.ofFn fun p : Fin 7 => {p}

def readSupports (W : List (Finset (Fin 7))) (p : Fin 7) : List Bool :=
  W.map fun s => decide (p ∈ s)

def gateSupport (W : List (Finset (Fin 7))) (g : Gate) : Finset (Fin 7) :=
  Finset.univ.filter fun p =>
    g.op.eval (g.inputs.map fun i => decide (p ∈ W.getD i ∅)) = true

def gateSupports (gates : List Gate) (S : List (Finset (Fin 7))) : List (Finset (Fin 7)) :=
  gates.foldl (fun W g => W ++ [gateSupport (inputSupports ++ W) g]) S

theorem readSupports_getD (W : List (Finset (Fin 7))) (p : Fin 7) (i : ℕ) :
    (readSupports W p).getD i false = decide (p ∈ W.getD i ∅) := by
  simp only [readSupports, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> simp

theorem decide_gateSupport (W : List (Finset (Fin 7))) (g : Gate) (p : Fin 7) :
    decide (p ∈ gateSupport W g) =
      g.op.eval (g.inputs.map fun i => (readSupports W p).getD i false) := by
  simp only [readSupports_getD, gateSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  simp

theorem readSupports_gateSupports (gates : List Gate) (S : List (Finset (Fin 7))) (p : Fin 7) :
    readSupports (inputSupports ++ gateSupports gates S) p =
      gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (readSupports (inputSupports ++ S) p) := by
  induction gates generalizing S with
  | nil => rfl
  | cons g gs ih =>
    simp only [gateSupports, List.foldl_cons] at ih ⊢
    rw [ih]
    rw [← List.append_assoc]
    simp only [readSupports, List.map_append, List.map_cons, List.map_nil, decide_gateSupport]

theorem readSupports_input (p : Fin 7) :
    readSupports inputSupports p = List.ofFn (fun i : Fin 7 => decide (i = p)) := by
  simp [readSupports, inputSupports, eq_comm]

theorem eval_eq (gates : List Gate) (out : ℕ) (p : Fin 7) :
    Circuit.eval ⟨gates, out⟩ (List.ofFn (fun i : Fin 7 => decide (i = p))) =
      decide (p ∈ (inputSupports ++ gateSupports gates []).getD out ∅) := by
  rw [← readSupports_getD, readSupports_gateSupports, List.append_nil, readSupports_input]
  rfl

theorem getD_mem_or_empty (W : List (Finset (Fin 7))) (i : ℕ) :
    W.getD i ∅ ∈ W ∨ W.getD i ∅ = ∅ := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : W[i]? with
  | none => simp
  | some a => exact Or.inl (List.mem_of_getElem? h)

theorem inputSupports_card (s : Finset (Fin 7)) (hs : s ∈ inputSupports) :
    s.card ≤ 1 := by
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hs
  simp

theorem line_mem_of_read (W : List (Finset (Fin 7))) (j : ℕ) (w : Fin 7)
    (h : W.getD j ∅ = line w) : line w ∈ W := by
  rcases getD_mem_or_empty W j with hm | he
  · exact h ▸ hm
  · have hc := lineCard w
    rw [← h, he, Finset.card_empty] at hc
    omega

def hasParents (W : List (Finset (Fin 7))) (w : Fin 7) : Prop :=
  ∃ a b : Finset (Fin 7), (a ∈ W ∨ a = ∅) ∧ (b ∈ W ∨ b = ∅) ∧
    a ≠ line w ∧ b ≠ line w ∧ (a ∪ b = line w ∨ a ∩ b = line w)

theorem hasParents_mono {W Z : List (Finset (Fin 7))} {w : Fin 7}
    (h : hasParents W w) (inc : ∀ s ∈ W, s ∈ Z) : hasParents Z w := by
  obtain ⟨a, b, ha, hb, hneA, hneB, hop⟩ := h
  exact ⟨a, b, ha.imp (inc a) id, hb.imp (inc b) id, hneA, hneB, hop⟩

theorem gate_parents (W : List (Finset (Fin 7))) (g : Gate) (w : Fin 7)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : gateSupport W g = line w) (hn : line w ∉ W) : hasParents W w := by
  have hu : (Finset.univ : Finset (Fin 7)) ≠ line w := by
    intro h
    have hc := lineCard w
    rw [← h] at hc
    simp at hc
  have hz : (∅ : Finset (Fin 7)) ≠ line w := by
    intro h
    have hc := lineCard w
    rw [← h] at hc
    simp at hc
  have read_ne (i : ℕ) : W.getD i ∅ ≠ line w := by
    intro h
    exact hn (line_mem_of_read W i w h)
  rcases g with ⟨op, inputs⟩
  change (op = GateOp.and ∨ op = GateOp.or) ∧ inputs.length ≤ 2 at hg
  obtain ⟨ho, hl⟩ := hg
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases ho with rfl | rfl
    · exact (hu (by simpa [gateSupport, GateOp.eval] using he)).elim
    · exact (hz (by simpa [gateSupport, GateOp.eval] using he)).elim
  · rcases ho with rfl | rfl
    · exact (read_ne a (by simpa [gateSupport, GateOp.eval] using he)).elim
    · exact (read_ne a (by simpa [gateSupport, GateOp.eval] using he)).elim
  · refine ⟨W.getD a ∅, W.getD b ∅, getD_mem_or_empty W a, getD_mem_or_empty W b,
      read_ne a, read_ne b, ?_⟩
    rcases ho with rfl | rfl
    · right
      have hs : gateSupport W ⟨GateOp.and, [a, b]⟩ = W.getD a ∅ ∩ W.getD b ∅ := by
        ext p
        simp [gateSupport, GateOp.eval]
      exact hs.symm.trans he
    · left
      have hs : gateSupport W ⟨GateOp.or, [a, b]⟩ = W.getD a ∅ ∪ W.getD b ∅ := by
        ext p
        simp [gateSupport, GateOp.eval]
      exact hs.symm.trans he
  · simp at hl

theorem gateSupports_parents (gates : List Gate) (S : List (Finset (Fin 7)))
    (h : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hS : ∀ w : Fin 7, line w ∈ inputSupports ++ S → hasParents (inputSupports ++ S) w) :
    ∀ w : Fin 7, line w ∈ inputSupports ++ gateSupports gates S →
      hasParents (inputSupports ++ gateSupports gates S) w := by
  induction gates generalizing S with
  | nil => exact hS
  | cons g gs ih =>
    simp only [gateSupports, List.foldl_cons] at ih ⊢
    apply ih _ (fun a ha => h a (List.mem_cons_of_mem g ha))
    intro w hw
    rw [← List.append_assoc, List.mem_append, List.mem_singleton] at hw
    have sub (s : Finset (Fin 7)) (hs : s ∈ inputSupports ++ S) :
        s ∈ inputSupports ++ (S ++ [gateSupport (inputSupports ++ S) g]) := by
      rw [← List.append_assoc]
      exact List.mem_append_left _ hs
    by_cases hp : line w ∈ inputSupports ++ S
    · exact hasParents_mono (hS w hp) sub
    · have he := (hw.resolve_left hp).symm
      exact hasParents_mono (gate_parents _ g w (h g (List.mem_cons_self)) he hp) sub

theorem gateSupports_length (gates : List Gate) (S : List (Finset (Fin 7))) :
    (gateSupports gates S).length = S.length + gates.length := by
  induction gates generalizing S with
  | nil => simp [gateSupports]
  | cons g gs ih =>
    simp only [gateSupports, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem line_not_input (w : Fin 7) : line w ∉ inputSupports := by
  intro h
  have hc := lineCard w
  have hm := inputSupports_card _ h
  omega

theorem circuit_bound (gates : List Gate) (out : Fin 7 → ℕ)
    (mono : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (correct : ∀ (w : Fin 7) (x : Fin 7 → Bool),
      (∀ i j : Fin 7, x i = true → x j = true → i = j) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ line w, x v = true)) :
    14 ≤ gates.length := by
  let supports := gateSupports gates []
  have eval_line (w : Fin 7) : (inputSupports ++ supports).getD (out w) ∅ = line w := by
    ext p
    have onehot (i j : Fin 7) (hi : decide (i = p) = true) (hj : decide (j = p) = true) : i = j :=
      (of_decide_eq_true hi).trans (of_decide_eq_true hj).symm
    have h := correct w (fun i => decide (i = p)) onehot
    rw [eval_eq] at h
    simpa [supports] using h
  have mem_line (w : Fin 7) : line w ∈ inputSupports ++ supports :=
    line_mem_of_read _ _ _ (eval_line w)
  have available (a : Finset (Fin 7)) (ha : a ∈ inputSupports ++ supports ∨ a = ∅) :
      a.card ≤ 1 ∨ a = Finset.univ ∨ a ∈ supports.toFinset := by
    rcases ha with hw | rfl
    · rw [List.mem_append] at hw
      rcases hw with hi | hg
      · exact Or.inl (inputSupports_card _ hi)
      · exact Or.inr (Or.inr (List.mem_toFinset.mpr hg))
    · simp
  have lower : 14 ≤ supports.toFinset.card := by
    apply set_bound
    · intro w
      exact List.mem_toFinset.mpr ((List.mem_append.mp (mem_line w)).resolve_left (line_not_input w))
    · intro w
      have hnil (v : Fin 7) (hv : line v ∈ inputSupports ++ []) :
          hasParents (inputSupports ++ []) v :=
        (line_not_input v (by simpa using hv)).elim
      obtain ⟨a, b, ha, hb, hneA, hneB, hp⟩ :=
        gateSupports_parents gates [] mono hnil w (mem_line w)
      exact ⟨a, b, available a ha, available b hb, hneA, hneB, hp⟩
  have upper := List.toFinset_card_le supports
  have size : supports.length = gates.length := by
    simpa [supports] using gateSupports_length gates []
  omega

end PEqualNP.Outside.L_meta_666

theorem PEqualNP.Outside.L_meta_666 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) → 14 ≤ gates.length := by
  exact PEqualNP.Outside.L_meta_666.circuit_bound
