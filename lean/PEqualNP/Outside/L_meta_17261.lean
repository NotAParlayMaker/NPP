import PEqualNP.Defs
import Mathlib.Data.Finset.Sort

namespace PEqualNP.Outside.L_meta_17261
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire evaluation, support counting, and input renaming adapted from the project's
-- Shannon, Support, and PermInputs helper modules.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]
variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

-- The support of a gate: the union of the supports of the wires it reads.
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

-- The supports of all wires, starting from the supports `L` of the wires present.
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

-- The supports of the input wires: input `i` has support `{i}`.
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
-- `y` agree on.
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

-- Any set `W` of wires has a joint support of size at most `t + |W|`.
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this
-- The renaming of wires: input wire `w < n` goes to `π w`, gate wire `w ≥ n` to
-- `w - n + m`.
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

-- A gate with its wires renamed.
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

-- A circuit with its wires renamed.
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

-- One gate evaluated on a wire list.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- The invariant: the wire lists match along the renaming.
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

-- Renaming inputs along any map keeps the circuit size.
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

lemma sources (n : ℕ) (C : Circuit) (shape : FanInTwo C) :
    ∃ T : Finset (Fin n), T.card ≤ C.size+1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) → circuitFun n C x = circuitFun n C y := by
  let T := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) shape cnt_inputs {C.output}
  refine ⟨T,by simpa only [T,Circuit.size,Finset.singleton_biUnion,Finset.card_singleton,zero_add] using hc,?_⟩
  intro x y same
  exact (agree_wiresFrom x y C.gates _ _ _ (agree_inputs _ _)).2.2 C.output same

theorem split (n k l : ℕ) (C : Circuit) (fan : FanInTwo C) (budget : C.size ≤ k+l) :
    ∃ (P : Circuit) (p : Fin (l+1) → Fin (n+k+1)) (h : (Fin (l+1) → Bool) → Bool),
      FanInTwo P ∧ P.size ≤ k ∧ HasCircuitSize (l+1) h l ∧
      (∀ i j, i<j → p i < p j ∨ p i = Fin.last (n+k) ∧ p j = Fin.last (n+k)) ∧
      ∀ w : List Bool, w.length = n → h (fun j => (P.wires w).getD (p j) false) = C.eval w := by
  classical
  let P : Circuit := ⟨C.gates.take k,0⟩
  let S : Circuit := ⟨C.gates.drop k,C.output⟩
  let m := n+P.size
  have pf : FanInTwo P := fun g hg => fan g (List.mem_of_mem_take hg)
  have sf : FanInTwo S := fun g hg => fan g (List.mem_of_mem_drop hg)
  have ps : P.size ≤ k := by simp [P,Circuit.size]
  have ss : S.size ≤ l := by
    change C.gates.length ≤ k+l at budget
    simp only [S,Circuit.size,List.length_drop]; omega
  obtain ⟨T,cap,dep⟩ := sources m S sf
  have bound : T.card ≤ l+1 := by omega
  let e := T.orderIsoOfFin (k := T.card) rfl
  let label (i : Fin m) : Fin (l+1) := if hi : i∈T then
      Fin.castLE bound (e.symm ⟨i,hi⟩) else 0
  have ml : m ≤ n+k := Nat.add_le_add_left ps n
  let p (j : Fin (l+1)) : Fin (n+k+1) := if hj : j.val<T.card then
      Fin.castLE (by omega : m≤n+k+1) (e ⟨j.val,hj⟩).val else Fin.last (n+k)
  have code (i : Fin m) (hi : i∈T) : (p (label i)).val = i.val := by simp [p,label,hi]
  have sorted (i j : Fin (l+1)) (ij : i<j) :
      p i < p j ∨ p i=Fin.last (n+k) ∧ p j=Fin.last (n+k) := by
    have lt : i.val<j.val := ij
    by_cases hj : j.val<T.card
    · have hi : i.val<T.card := by omega
      left
      simp only [p,dite_eq_left hi,dite_eq_left hj]
      change (e ⟨i.val,hi⟩).val.val < (e ⟨j.val,hj⟩).val.val
      exact (show (e ⟨i.val,hi⟩).val < (e ⟨j.val,hj⟩).val from
        e.strictMono (show (⟨i.val,hi⟩ : Fin T.card)<⟨j.val,hj⟩ from ij))
    · by_cases hi : i.val<T.card
      · left
        have hlt := (e ⟨i.val,hi⟩).val.isLt
        simp only [p,dite_eq_left hi,dite_eq_right hj]
        change (e ⟨i.val,hi⟩).val.val < n+k
        omega
      · right; simp [p,hi,hj]
  let h (y : Fin (l+1) → Bool) := circuitFun m S (y ∘ label)
  have hsize : HasCircuitSize (l+1) h l :=
    relabel_size label (circuitFun m S) l ⟨S,sf,ss,fun _ => rfl⟩
  refine ⟨P,p,h,pf,ps,hsize,sorted,?_⟩
  intro w hw
  let W := P.wires w
  have len : W.length=m := by
    change (wiresFrom P.gates w).length=n+P.gates.length
    rw [length_wiresFrom,hw]
  let original (i : Fin m) := W.getD i.val false
  have restore : List.ofFn original = W := by
    apply List.ext_getElem
    · simpa using len.symm
    · intro i h1 h2
      simp [original,List.getD_eq_getElem?_getD,h2]
  have compose : S.eval W = C.eval w := by
    change (wiresFrom (C.gates.drop k) (wiresFrom (C.gates.take k) w)).getD C.output false =
      (wiresFrom C.gates w).getD C.output false
    rw [← wiresFrom_append,List.take_append_drop]
  calc
    h (fun j => W.getD (p j) false) = circuitFun m S original := by
      apply dep
      intro i hi
      simp only [Function.comp_apply,code i hi,original]
    _ = S.eval W := by change S.eval (List.ofFn original) = _; rw [restore]
    _ = C.eval w := compose

theorem transfer (n k l : ℕ) (s t : List (Fin n → Bool)) (C : Circuit)
    (sub : s ⊆ t) (fan : FanInTwo C) (budget : C.size ≤ k+l) :
    ∃ (P : Circuit) (p : Fin (l+1) → Fin (t.length+k+1)) (h : (Fin (l+1) → Bool) → Bool),
      FanInTwo P ∧ P.size ≤ k ∧ HasCircuitSize (l+1) h l ∧
      (∀ i j, i<j → p i < p j ∨ p i = Fin.last (t.length+k) ∧ p j = Fin.last (t.length+k)) ∧ ∀ r : Fin n,
      h (fun j => (P.wires (t.map fun v => v r)).getD (p j) false) = C.eval (s.map fun v => v r) := by
  classical
  have witness (i : Fin s.length) : ∃ j : Fin t.length, t[j.val]=s[i.val] := by
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp (sub (List.getElem_mem i.isLt))
    exact ⟨⟨j,hj⟩,eq⟩
  choose ρ hρ using witness
  have hb : HasCircuitSize s.length (circuitFun s.length C) (k+l) := ⟨C,fan,budget,fun _ => rfl⟩
  obtain ⟨D,df,ds,de⟩ := relabel_size ρ _ _ hb
  obtain ⟨P,p,h,pf,ps,hs,sorted,he⟩ := split t.length k l D df ds
  refine ⟨P,p,h,pf,ps,hs,sorted,?_⟩
  intro r
  rw [he _ (by simp)]
  let x (i : Fin t.length) := t[i.val] r
  have tx : List.ofFn x = t.map (fun v => v r) := by
    apply List.ext_getElem <;> simp [x]
  have sx : List.ofFn (x ∘ ρ) = s.map (fun v => v r) := by
    apply List.ext_getElem <;> simp [x,Function.comp_apply,hρ]
  have e := de x
  change D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ ρ)) at e
  simpa only [tx,sx] using e
end PEqualNP.Outside.L_meta_17261

theorem PEqualNP.Outside.L_meta_17261 : ∀ (x1 x2 x3 : ℕ) (x4 x5 : List (Fin x1 → Bool)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x4 ⊆ x5 → PEqualNP.MetaComplexity.FanInTwo x6 → x6.size ≤ x2 + x3 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : Fin (x3 + (1 : ℕ)) → Fin (x5.length + x2 + (1 : ℕ))) (x12 : (Fin (x3 + (1 : ℕ)) → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x10.size ≤ x2 ∧ PEqualNP.MetaComplexity.HasCircuitSize (x3 + (1 : ℕ)) x12 x3 ∧ (∀ (x13 x14 : Fin (x3 + (1 : ℕ))), x13 < x14 → x11 x13 < x11 x14 ∨ x11 x13 = Fin.last (x5.length + x2) ∧ x11 x14 = Fin.last (x5.length + x2)) ∧ ∀ (x13 : Fin x1), (x12 fun (x14 : Fin (x3 + (1 : ℕ))) => (x10.wires (List.map (fun (x15 : Fin x1 → Bool) => x15 x13) x5)).getD (↑(x11 x14)) Bool.false) = x6.eval (List.map (fun (x14 : Fin x1 → Bool) => x14 x13) x4) :=
  PEqualNP.Outside.L_meta_17261.transfer
