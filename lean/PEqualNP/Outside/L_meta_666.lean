import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_666

abbrev Mask := BitVec 7

def pointMask (i : Fin 7) : Mask := (1 : Mask) <<< i.val

def lineMask (w : Fin 7) : Mask :=
  pointMask w ||| pointMask (1 + w) ||| pointMask (3 + w)

def weight (m : Mask) (w : Fin 7) : ℕ :=
  if m.cpop.toNat = 2 ∧ m &&& lineMask w = m then 2
  else if m.cpop.toNat = 4 ∧ m &&& lineMask w = lineMask w then 2
  else if m.cpop.toNat = 5 ∧ m &&& lineMask w = lineMask w then 1
  else 0

lemma lineMask_injective : Function.Injective lineMask := by
  intro a b
  exact (by decide +kernel : ∀ i j : Fin 7, lineMask i = lineMask j → i = j) a b

lemma lineMask_ne_zero (w : Fin 7) : lineMask w ≠ 0 := by
  exact (by decide +kernel : ∀ j, lineMask j ≠ 0) w

lemma lineMask_ne_top (w : Fin 7) : lineMask w ≠ BitVec.allOnes 7 := by
  exact (by decide +kernel : ∀ j, lineMask j ≠ BitVec.allOnes 7) w

lemma lineMask_ne_point (w i : Fin 7) : lineMask w ≠ pointMask i := by
  exact (by decide +kernel : ∀ j k, lineMask j ≠ pointMask k) w i

lemma weight_line (i w : Fin 7) : weight (lineMask i) w = 0 := by
  exact (by decide +kernel : ∀ j k, weight (lineMask j) k = 0) i w

lemma weight_point (i w : Fin 7) : weight (pointMask i) w = 0 := by
  exact (by decide +kernel : ∀ j k, weight (pointMask j) k = 0) i w

lemma weight_zero (w : Fin 7) : weight 0 w = 0 := by
  exact (by decide +kernel : ∀ j, weight 0 j = 0) w

lemma weight_top (w : Fin 7) : weight (BitVec.allOnes 7) w = 0 := by
  exact (by decide +kernel : ∀ j, weight (BitVec.allOnes 7) j = 0) w

lemma weight_sum_le (m : Mask) : (∑ w : Fin 7, weight m w) ≤ 2 := by
  exact (by decide +kernel : ∀ a : Mask, (∑ w : Fin 7, weight a w) ≤ 2) m

set_option maxRecDepth 8192 in
lemma weight_or (a b : Mask) (w : Fin 7) (h : a ||| b = lineMask w)
    (ha : a ≠ lineMask w) (hb : b ≠ lineMask w) : 2 ≤ weight a w + weight b w := by
  exact (by decide +kernel : ∀ (u v : Mask) (j : Fin 7),
    u ||| v = lineMask j → u ≠ lineMask j → v ≠ lineMask j → 2 ≤ weight u j + weight v j)
    a b w h ha hb

set_option maxRecDepth 8192 in
lemma weight_and (a b : Mask) (w : Fin 7) (h : a &&& b = lineMask w)
    (ha : a ≠ lineMask w) (hb : b ≠ lineMask w) : 2 ≤ weight a w + weight b w := by
  exact (by decide +kernel : ∀ (u v : Mask) (j : Fin 7),
    u &&& v = lineMask j → u ≠ lineMask j → v ≠ lineMask j → 2 ≤ weight u j + weight v j)
    a b w h ha hb

end PEqualNP.Outside.L_meta_666

open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_666

def semOp (op : GateOp) : List Mask → Mask
  | [] => if op matches .and then BitVec.allOnes 7 else 0
  | [a] => a
  | a :: b :: _ => if op matches .and then a &&& b else a ||| b

def semGate (ws : List Mask) (g : Gate) : Mask :=
  semOp g.op (g.inputs.map fun i => ws.getD i 0)

def semSeq (ws : List Mask) : List Gate → List Mask
  | [] => []
  | g :: gs => semGate ws g :: semSeq (ws ++ [semGate ws g]) gs

def semBit (i : Fin 7) (v : Mask) : Bool := v.getLsbD i.val

private lemma semGet (i : Fin 7) (ws : List Mask) (j : ℕ) :
    semBit i (ws.getD j 0) = (ws.map (semBit i)).getD j false := by
  induction ws generalizing j with
  | nil => simp [semBit]
  | cons w ws ih => cases j with
    | zero => rfl
    | succ j => exact ih j

private lemma semOp_ok (i : Fin 7) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) (ws : List Mask) :
    semBit i (semGate ws g) =
      g.op.eval (g.inputs.map fun j => (ws.map (semBit i)).getD j false) := by
  rcases g with ⟨op,l⟩
  rcases hg with ⟨ho,hl⟩
  rcases ho with h | h <;> change op = _ at h <;> subst op
  all_goals
    change l.length ≤ 2 at hl
    rcases l with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
    · first
      | exact (by decide +kernel : ∀ j : Fin 7, semBit j (BitVec.allOnes 7) = true) i
      | exact (by decide +kernel : ∀ j : Fin 7, semBit j 0 = false) i
    · cases h : ws[a]? <;> simp [semGate,semOp,GateOp.eval,semBit,h]
    · cases ha : ws[a]? <;> cases hb : ws[b]? <;> simp [semGate,semOp,GateOp.eval,semBit,ha,hb]
    · simp at hl

private lemma semFold (i : Fin 7) (gs : List Gate) (ws : List Mask)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    (ws ++ semSeq ws gs).map (semBit i) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
        (ws.map (semBit i)) := by
  induction gs generalizing ws with
  | nil => simp [semSeq]
  | cons g gs ih =>
    have he := ih (ws ++ [semGate ws g]) (fun a ha => hg a (by simp [ha]))
    simpa [semSeq,List.append_assoc,List.map_append,semOp_ok i g (hg g (by simp))] using he

def semAllowed (ws : List Mask) (z : Mask) : Prop :=
  z = 0 ∨ z = BitVec.allOnes 7 ∨ z ∈ ws ∨
    ∃ a ∈ (0 :: ws), ∃ b ∈ (0 :: ws), z = a &&& b ∨ z = a ||| b

private lemma semRead (ws : List Mask) (k : ℕ) : ws.getD k 0 ∈ (0 :: ws) := by
  induction ws generalizing k with
  | nil => simp
  | cons w ws ih =>
    cases k with
    | zero => simp
    | succ k =>
      have he := ih k
      simp only [List.mem_cons] at he ⊢
      change ws.getD k 0 = 0 ∨ ws.getD k 0 = w ∨ ws.getD k 0 ∈ ws
      tauto

private lemma semAllowed_gate (ws : List Mask) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) : semAllowed ws (semGate ws g) := by
  rcases g with ⟨op,l⟩
  rcases hg with ⟨ho,hl⟩
  rcases ho with h | h <;> change op = _ at h <;> subst op
  all_goals
    change l.length ≤ 2 at hl
    rcases l with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
    · simp [semAllowed,semGate,semOp]
    · have hr := semRead ws a
      simp only [List.mem_cons] at hr
      simp [semAllowed,semGate,semOp]; tauto
    · apply Or.inr; apply Or.inr; apply Or.inr
      refine ⟨_,semRead ws a,_,semRead ws b,?_⟩
      first | exact Or.inl rfl | exact Or.inr rfl
    · simp at hl

def semValid (ws : List Mask) : List Mask → Prop
  | [] => True
  | a :: l => semAllowed ws a ∧ semValid (ws ++ [a]) l

theorem semValid_at {base vs : List Mask} (h : semValid base vs) (i : Fin vs.length) :
    semAllowed (base ++ vs.take i.val) vs[i.val] := by
  induction vs generalizing base with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    rcases i with ⟨_ | i, hi⟩
    · simpa using h.1
    · have hi' : i < xs.length := by simpa using hi
      have := ih h.2 ⟨i,hi'⟩
      simpa [List.append_assoc] using this

private lemma semValid_run (ws : List Mask) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    semValid ws (semSeq ws gs) := by
  induction gs generalizing ws with
  | nil => trivial
  | cons g gs ih =>
    exact ⟨semAllowed_gate ws g (hg g (by simp)),ih _ (fun a ha => hg a (by simp [ha]))⟩

private lemma semLength (gs : List Gate) (ws : List Mask) : (semSeq ws gs).length = gs.length := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => simp [semSeq,ih]

private lemma semInput : ∀ i j : Fin 7, semBit i (pointMask j) = decide (i = j) := by decide +kernel

private lemma semLine : ∀ i w : Fin 7, semBit i (lineMask w) =
    decide (∃ v ∈ (({0,1,3} : Finset (Fin 7)).image (fun u => u + w)), decide (i = v) = true) := by
  decide +kernel

private lemma semDistinct : ∀ w : Fin 7, lineMask w ≠ 0 ∧ lineMask w ∉ List.ofFn pointMask := by
  decide +kernel

theorem semantics (gs : List Gate) (o : Fin 7 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hout : ∀ (w : Fin 7) (x : Fin 7 → Bool),
      (∀ i j : Fin 7, x i = true → x j = true → i = j) →
      Circuit.eval ⟨gs, o w⟩ (List.ofFn x) =
        decide (∃ v ∈ (({0,1,3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) :
    ∃ vs : List Mask, vs.length = gs.length ∧ semValid (List.ofFn pointMask) vs ∧
      ∀ w : Fin 7, lineMask w ∈ vs := by
  let init := List.ofFn pointMask
  let vs := semSeq init gs
  refine ⟨vs,semLength ..,semValid_run _ _ hg,?_⟩
  intro w
  have eq : (init ++ vs).getD (o w) 0 = lineMask w := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 7 := ⟨j,hj⟩
    change semBit i _ = semBit i _
    rw [semGet, semLine, semFold i gs init hg]
    have hinit : init.map (semBit i) = List.ofFn (fun j => decide (i=j)) := by
      simp [init,semInput]
    rw [hinit]
    exact hout w (fun j => decide (i=j)) (by simp +contextual)
  have hm := semRead (init ++ vs) (o w)
  rw [eq] at hm
  simp only [List.mem_cons,List.mem_append] at hm
  exact (hm.resolve_left (semDistinct w).1).resolve_left (semDistinct w).2

end PEqualNP.Outside.L_meta_666

namespace PEqualNP.Outside.L_meta_666

lemma count_from_charge {M : Type} (ws : List M) (charge : Fin 7 → M → ℕ)
    (cap : ∀ m, ∑ i, charge i m ≤ 2)
    (demand : ∀ i, 4 ≤ (ws.map (charge i)).sum) : 14 ≤ ws.length := by
  have upper (xs : List M) : ∑ i, (xs.map (charge i)).sum ≤ 2 * xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, List.length_cons]
      have hx := cap x
      omega
  have lo := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 7)))
    (fun i _ => demand i)
  have hi := upper ws
  simp at lo
  omega

lemma sum_of_subset_list {M : Type} [DecidableEq M] (f : M → ℕ) (ws : List M)
    (s : Finset M) (hs : ∀ x ∈ s, x ∈ ws) :
    ∑ x ∈ s, f x ≤ (ws.map f).sum := by
  induction ws generalizing s with
  | nil =>
    have hempty : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun x hx => List.not_mem_nil (hs x hx))
    simp [hempty]
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hy : y ∈ s
    · have he : ∀ x ∈ s.erase y, x ∈ ys := by
        intro x hx
        obtain ⟨hne, hxs⟩ := Finset.mem_erase.mp hx
        exact (List.mem_cons.mp (hs x hxs)).resolve_left hne
      have hu := ih (s.erase y) he
      have hsum := Finset.add_sum_erase s f hy
      omega
    · have he : ∀ x ∈ s, x ∈ ys := by
        intro x hx
        rcases List.mem_cons.mp (hs x hx) with h | h
        · exact (hy (h ▸ hx)).elim
        · exact h
      have hu := ih s he
      omega

lemma demand_from_parents {M : Type} [DecidableEq M] (ws : List M)
    (charge : M → ℕ) (l a b : M) (hl : l ∈ ws) (ha : a ∈ ws) (hb : b ∈ ws)
    (hla : a ≠ l) (hlb : b ≠ l) (hab : a ≠ b)
    (h : 4 ≤ charge l + charge a + charge b) : 4 ≤ (ws.map charge).sum := by
  have hs : ∀ x ∈ ({l,a,b} : Finset M), x ∈ ws := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hl
    · exact ha
    · exact hb
  have hu := sum_of_subset_list charge ws {l,a,b} hs
  simp [Ne.symm hla, Ne.symm hlb, hab] at hu
  omega

end PEqualNP.Outside.L_meta_666

namespace PEqualNP.Outside.L_meta_666

def credit (w : Fin 7) (m : Mask) : ℕ :=
  if m = lineMask w then 2 else weight m w

lemma credit_bound (m : Mask) : ∑ w, credit w m ≤ 2 := by
  by_cases hit : ∃ i, m = lineMask i
  · obtain ⟨i, rfl⟩ := hit
    simp [credit, weight_line, lineMask_injective.eq_iff]
  · simpa [credit, fun i => show m ≠ lineMask i from fun h => hit ⟨i, h⟩] using weight_sum_le m

def freeMasks : List Mask := 0 :: BitVec.allOnes 7 :: List.ofFn pointMask

lemma free_ne_line {a : Mask} (w : Fin 7) (ha : a ∈ freeMasks) : a ≠ lineMask w := by
  simp only [freeMasks, List.mem_cons, List.mem_ofFn] at ha
  rcases ha with rfl | rfl | ⟨i, rfl⟩
  · exact (lineMask_ne_zero w).symm
  · exact (lineMask_ne_top w).symm
  · exact (lineMask_ne_point w i).symm

lemma credit_free_sum (w : Fin 7) : (freeMasks.map (credit w)).sum = 0 := by
  have allZero : ∀ a ∈ freeMasks, credit w a = 0 := by
    intro a ha
    rw [credit, if_neg (free_ne_line w ha)]
    simp only [freeMasks, List.mem_cons, List.mem_ofFn] at ha
    rcases ha with rfl | rfl | ⟨i, rfl⟩
    · exact weight_zero w
    · exact weight_top w
    · exact weight_point i w
  have aux (xs : List Mask) (hz : ∀ a ∈ xs, credit w a = 0) :
      (xs.map (credit w)).sum = 0 := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp [hz a (by simp), ih (fun t ht => hz t (by simp [ht]))]
  exact aux _ allZero

lemma demand_for_line (vs : List Mask) (w : Fin 7) (hl : lineMask w ∈ vs)
    (a b : Mask) (ha : a ∈ freeMasks ++ vs) (hb : b ∈ freeMasks ++ vs)
    (hal : a ≠ lineMask w) (hbl : b ≠ lineMask w)
    (hop : a ||| b = lineMask w ∨ a &&& b = lineMask w) :
    4 ≤ (vs.map (credit w)).sum := by
  have hab : a ≠ b := by
    rintro rfl
    rcases hop with h | h <;> exact hal (by simpa using h)
  have hWeight : 2 ≤ weight a w + weight b w :=
    hop.elim (fun h => weight_or a b w h hal hbl) (fun h => weight_and a b w h hal hbl)
  have h := demand_from_parents (freeMasks ++ vs) (credit w) (lineMask w) a b
    (List.mem_append_right _ hl) ha hb hal hbl hab (by simp [credit, hal, hbl]; omega)
  simpa only [List.map_append, List.sum_append, credit_free_sum, zero_add] using h

end PEqualNP.Outside.L_meta_666

namespace PEqualNP.Outside.L_meta_666

lemma first_line_demand (vs : List Mask) (hv : semValid (List.ofFn pointMask) vs)
    (w : Fin 7) (hl : lineMask w ∈ vs) : 4 ≤ (vs.map (credit w)).sum := by
  let i : Fin vs.length := ⟨vs.idxOf (lineMask w), List.idxOf_lt_length_iff.mpr hl⟩
  have hi : vs[i.val] = lineMask w := List.getElem_idxOf _
  have prior : lineMask w ∉ vs.take i.val :=
    fun h => (Nat.lt_irrefl _) ((List.mem_take_iff_idxOf_lt hl).mp h)
  have newLine : lineMask w ∉ List.ofFn pointMask ++ vs.take i.val := by
    rw [List.mem_append]
    rintro (hp | hp)
    · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hp
      exact lineMask_ne_point w j hj.symm
    · exact prior hp
  have wrap {m : Mask} (hm : m ∈ 0 :: (List.ofFn pointMask ++ vs.take i.val)) :
      m ∈ freeMasks ++ vs := by
    rcases List.mem_cons.mp hm with rfl | hp
    · simp [freeMasks]
    · rcases List.mem_append.mp hp with hf | ht
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf))
      · exact List.mem_append_right _ (List.mem_of_mem_take ht)
  have fresh {m : Mask} (hm : m ∈ 0 :: (List.ofFn pointMask ++ vs.take i.val)) :
      m ≠ lineMask w := by
    rintro rfl
    exact (List.mem_cons.mp hm).elim (lineMask_ne_zero w) newLine
  have hs := semValid_at hv i
  rw [hi] at hs
  rcases hs with h | h | h | ⟨a, ha, b, hb, hab⟩
  · exact (lineMask_ne_zero w h).elim
  · exact (lineMask_ne_top w h).elim
  · exact (newLine h).elim
  · exact demand_for_line vs w hl a b (wrap ha) (wrap hb) (fresh ha) (fresh hb)
      (hab.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm))

end PEqualNP.Outside.L_meta_666

open PEqualNP.Outside.L_meta_666

theorem PEqualNP.Outside.L_meta_666 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) → 14 ≤ gates.length := by
  intro gs out hg hout
  obtain ⟨vs, hlen, hv, hlines⟩ := semantics gs out hg hout
  rw [← hlen]
  exact count_from_charge vs credit credit_bound (fun w => first_line_demand vs hv w (hlines w))
