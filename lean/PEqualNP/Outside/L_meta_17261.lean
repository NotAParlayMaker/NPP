import Mathlib.Data.Finset.Sort
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17261_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

abbrev run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl appendGate w

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (appendGate w g)).length = _
    rw [ih]
    simp [appendGate]
    omega

theorem get_old (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (appendGate w g).getD i false = w.getD i false := by
  simp [appendGate, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem get_new (w : List Bool) (g : Gate) :
    (appendGate w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [appendGate, List.getD_eq_getElem?_getD]

theorem get_missing (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default w false h

def move (k m : ℕ) (p : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < k then p i else m + (i - k)

def relabel (k m : ℕ) (p : ℕ → ℕ) (gs : List Gate) : List Gate :=
  gs.map fun g => ⟨g.op, g.inputs.map (move k m p)⟩

theorem good_relabel (k m : ℕ) (p : ℕ → ℕ) (gs : List Gate)
    (h : FanInTwo ⟨gs,0⟩) : FanInTwo ⟨relabel k m p gs,0⟩ := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  simpa using h a ha

theorem move_agree (gs : List Gate) (u v : List Bool) (p : ℕ → ℕ)
    (hp : ∀ i < u.length, p i < v.length ∨ v.length + gs.length ≤ p i)
    (base : ∀ i < u.length, v.getD (p i) false = u.getD i false) :
    ∀ i, (run (relabel u.length v.length p gs) v).getD (move u.length v.length p i) false =
      (run gs u).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    by_cases hi : i < u.length
    · simpa [run, relabel, move, hi] using base i hi
    · simp [run, relabel, move, hi]
  | append_singleton gs g ih =>
    intro i
    have hp' : ∀ j < u.length, p j < v.length ∨ v.length + gs.length ≤ p j := by
      intro j hj
      rcases hp j hj with h | h
      · exact Or.inl h
      · right
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        omega
    let K := u.length
    let M := v.length
    let a := run gs u
    let b := run (relabel K M p gs) v
    let g' : Gate := ⟨g.op, g.inputs.map (move K M p)⟩
    have hal : a.length = K + gs.length := run_length _ _
    have hbl : b.length = M + gs.length := by simp [b, run_length, relabel, M]
    have hrewrite : run (relabel K M p (gs ++ [g])) v = appendGate b g' := by
      simp [relabel, run, List.foldl_append, b, g']
    have hright : run (gs ++ [g]) u = appendGate a g := by simp [run, List.foldl_append, a]
    rw [hrewrite, hright]
    change (appendGate b g').getD (move K M p i) false = (appendGate a g).getD i false
    have prev (j : ℕ) : b.getD (move K M p j) false = a.getD j false := ih hp' j
    rcases lt_trichotomy i (K + gs.length) with hi | he | hi
    · rw [get_old a g i (by omega)]
      by_cases hsource : i < K
      · rw [move, ite_eq_left hsource]
        rcases hp i hsource with hl | hl
        · rw [get_old b g' _ (by omega)]
          have h := prev i
          rw [move, ite_eq_left hsource] at h
          exact h
        · have hlarge : b.length + 1 ≤ p i := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hl
            dsimp [M] at hbl
            omega
          rw [get_missing _ _ (by simp [appendGate]; omega)]
          have h := prev i
          rw [move, ite_eq_left hsource, get_missing b _ (by omega)] at h
          exact h
      · have hback : move K M p i < b.length := by unfold move; rw [ite_eq_right hsource]; omega
        rw [get_old b g' _ hback]
        exact prev i
    · have hout : move K M p i = b.length := by rw [move, ite_eq_right (by omega)]; omega
      have ei : i = a.length := he.trans hal.symm
      rw [hout, ei, get_new, get_new]
      change g.op.eval (List.map (fun j => b.getD j false) (g.inputs.map (move K M p))) =
        g.op.eval (List.map (fun j => a.getD j false) g.inputs)
      rw [List.map_map]
      apply congrArg (fun bits => g.op.eval bits)
      exact List.map_congr_left fun j _ => prev j
    · have ha : (appendGate a g).length ≤ i := by simp [appendGate]; omega
      have hb : (appendGate b g').length ≤ move K M p i := by
        simp [appendGate, move, show ¬ i < K by omega]
        omega
      rw [get_missing _ _ ha, get_missing _ _ hb]

def crossing (k : ℕ) (gs : List Gate) (T : Finset ℕ) : Finset ℕ :=
  match gs with
  | [] => T
  | g :: rest =>
    let U := crossing (k+1) rest T
    if k ∈ U then U.erase k ∪ g.inputs.toFinset.filter (· < k) else U

theorem crossing_count (k : ℕ) (gs : List Gate) (T : Finset ℕ)
    (hg : FanInTwo ⟨gs, 0⟩) (hT : ∀ i ∈ T, i < k + gs.length) :
    (crossing k gs T).card ≤ T.card + gs.length ∧ ∀ i ∈ crossing k gs T, i < k := by
  induction gs generalizing k with
  | nil => simpa [crossing] using hT
  | cons g gs ih =>
    have hrest : FanInTwo ⟨gs,0⟩ := fun a ha => hg a (List.mem_cons_of_mem _ ha)
    have hall : ∀ i ∈ T, i < (k+1)+gs.length := by
      intro i hi
      have h := hT i hi
      simp at h
      omega
    obtain ⟨hc, hb⟩ := ih (k+1) hrest hall
    let U := crossing (k + 1) gs T
    change U.card ≤ T.card + gs.length at hc
    change ∀ i ∈ U, i < k + 1 at hb
    change (if k ∈ U then U.erase k ∪ g.inputs.toFinset.filter (· < k) else U).card ≤
      T.card + (g :: gs).length ∧ ∀ i ∈ (if k ∈ U then U.erase k ∪ g.inputs.toFinset.filter (· < k) else U), i < k
    by_cases hm : k ∈ U
    · rw [ite_eq_left hm]
      constructor
      · have cd := Finset.card_erase_add_one hm
        have cb := Finset.card_union_le (U.erase k) (g.inputs.toFinset.filter (· < k))
        have cf := Finset.card_filter_le (s := g.inputs.toFinset) (p := (· < k))
        have cl := List.toFinset_card_le g.inputs
        have gg : g.inputs.length ≤ 2 := by
          exact (hg g List.mem_cons_self).2
        simp only [List.length_cons]
        omega
      · intro i hi
        rcases Finset.mem_union.mp hi with h | h
        · have ⟨hn, hu⟩ := Finset.mem_erase.mp h
          have hh := hb i hu
          omega
        · exact (Finset.mem_filter.mp h).2
    · rw [ite_eq_right hm]
      constructor
      · simp only [List.length_cons]; omega
      · intro i hi
        have h := hb i hi
        have ne : i ≠ k := fun eq => hm (eq ▸ hi)
        omega

theorem crossing_agree (gs : List Gate) (T : Finset ℕ) (u v : List Bool) (hl : u.length = v.length)
    (ha : ∀ i ∈ crossing u.length gs T, u.getD i false = v.getD i false) :
    ∀ i ∈ T, (run gs u).getD i false = (run gs v).getD i false := by
  induction gs generalizing u v with
  | nil => exact ha
  | cons g gs ih =>
    let k := u.length
    let U := crossing (k+1) gs T
    have al : (appendGate u g).length = k+1 := by simp [appendGate, k]
    have bl : (appendGate v g).length = k+1 := by simp [appendGate, k, hl]
    intro i hi
    apply ih (appendGate u g) (appendGate v g) (al.trans bl.symm) _ i hi
    rw [al]
    intro j hj
    change j ∈ U at hj
    change ∀ j ∈ (if k ∈ U then U.erase k ∪ g.inputs.toFinset.filter (· < k) else U), _ at ha
    by_cases hk : k ∈ U
    · rw [ite_eq_left hk] at ha
      by_cases h : j = k
      · subst j
        change (appendGate u g).getD u.length false = (appendGate v g).getD u.length false
        conv_rhs => rw [hl]
        rw [get_new, get_new]
        apply congrArg (fun x => g.op.eval x)
        apply List.map_congr_left
        intro l hmem
        by_cases hlt : l < k
        · exact ha l (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, hlt⟩))
        · rw [get_missing _ _ (by omega), get_missing _ _ (by omega)]
      · have hh := ha j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hj⟩))
        rcases lt_or_gt_of_ne h with lt | gt
        · rwa [get_old _ _ _ (by omega), get_old _ _ _ (by omega)]
        · rw [get_missing _ _ (by omega), get_missing _ _ (by omega)]
    · rw [ite_eq_right hk] at ha
      have ne : j ≠ k := fun h => hk (h ▸ hj)
      rcases lt_or_gt_of_ne ne with lt | gt
      · rw [get_old _ _ _ (by omega), get_old _ _ _ (by omega)]
        exact ha j hj
      · rw [get_missing _ _ (by omega), get_missing _ _ (by omega)]

end PEqualNP.Outside.L_meta_17261_aux

namespace PEqualNP.Outside.L_meta_17261_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem covers {α : Type} (a b : List α) (h : a ⊆ b) :
    ∃ p : ℕ → ℕ, ∀ i (hi : i < a.length), ∃ hj : p i < b.length, b[p i] = a[i] := by
  classical
  have e (i : ℕ) (hi : i < a.length) : ∃ j : Fin b.length, b[j.val] = a[i] := by
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (h (List.getElem_mem hi))
    exact ⟨⟨j,hj⟩,he⟩
  let p (i : ℕ) := if hi : i < a.length then (e i hi).choose.val else 0
  refine ⟨p, fun i hi => ?_⟩
  have eq : p i = (e i hi).choose.val := dite_eq_left hi
  refine ⟨by rw [eq]; exact (e i hi).choose.isLt, ?_⟩
  simp only [p, dite_eq_left hi]
  exact (e i hi).choose_spec

theorem sorted_pad (S : Finset ℕ) (m Q : ℕ) (hs : S.card ≤ m) (hQ : ∀ i ∈ S, i < Q) :
    ∃ E : Fin m → Fin (Q+1),
      (∀ i j, i < j → E i < E j ∨ E i = Fin.last Q ∧ E j = Fin.last Q) ∧
      ∀ x ∈ S, ∃ i, (E i).val = x := by
  classical
  let f := S.orderEmbOfFin rfl
  let E (i : Fin m) : Fin (Q+1) :=
    if h : i.val < S.card then ⟨f ⟨i.val,h⟩, Nat.lt_succ_of_lt (hQ _ (Finset.orderEmbOfFin_mem _ _ _))⟩
    else Fin.last Q
  refine ⟨E, ?_, ?_⟩
  · intro i j hij
    by_cases hj : j.val < S.card
    · have hi : i.val < S.card := by omega
      left
      change (E i).val < (E j).val
      simpa only [E, dite_eq_left hi, dite_eq_left hj] using f.strictMono (show (⟨i.val,hi⟩ : Fin S.card) < ⟨j.val,hj⟩ from hij)
    · by_cases hi : i.val < S.card
      · left
        change (E i).val < (E j).val
        simpa only [E, dite_eq_left hi, dite_eq_right hj, Fin.val_last] using hQ _ (Finset.orderEmbOfFin_mem S rfl ⟨i.val,hi⟩)
      · right
        simp [E, dite_eq_right hi, dite_eq_right hj]
  · intro x hx
    have r : x ∈ Set.range f := by rwa [Finset.range_orderEmbOfFin]
    obtain ⟨i, hi⟩ := r
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hs⟩, by simpa only [E, dite_eq_left i.isLt] using hi⟩

end PEqualNP.Outside.L_meta_17261_aux

open PEqualNP.Outside.L_meta_17261_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_17261 : (∀ (x1 x2 x3 : ℕ) (x4 x5 : List (Fin x1 → Bool)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x4 ⊆ x5 → PEqualNP.MetaComplexity.FanInTwo x6 → x6.size ≤ x2 + x3 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : Fin (x3 + (1 : ℕ)) → Fin (x5.length + x2 + (1 : ℕ))) (x12 : (Fin (x3 + (1 : ℕ)) → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x10.size ≤ x2 ∧ PEqualNP.MetaComplexity.HasCircuitSize (x3 + (1 : ℕ)) x12 x3 ∧ (∀ (x13 x14 : Fin (x3 + (1 : ℕ))), x13 < x14 → x11 x13 < x11 x14 ∨ x11 x13 = Fin.last (x5.length + x2) ∧ x11 x14 = Fin.last (x5.length + x2)) ∧ ∀ (x13 : Fin x1), (x12 fun (x14 : Fin (x3 + (1 : ℕ))) => (x10.wires (List.map (fun (x15 : Fin x1 → Bool) => x15 x13) x5)).getD (↑(x11 x14)) Bool.false) = x6.eval (List.map (fun (x14 : Fin x1 → Bool) => x14 x13) x4)) := by
  classical
  intro n k t a b C ha hg hsize
  obtain ⟨p, hp⟩ := covers a b ha
  let first := C.gates.take k
  let last := C.gates.drop k
  have hrebuild : first ++ last = C.gates := List.take_append_drop _ _
  have hf : first.length ≤ k := by simp [first]
  have hlast : last.length ≤ t := by
    change C.gates.length ≤ k+t at hsize
    simp [last]
    omega
  have hg1 : FanInTwo ⟨first,0⟩ := fun g h => hg g (List.mem_of_mem_take h)
  have hg2 : FanInTwo ⟨last,0⟩ := fun g h => hg g (List.mem_of_mem_drop h)
  let D : Circuit := ⟨relabel a.length b.length p first, 0⟩
  have hd : FanInTwo D := good_relabel _ _ _ _ hg1
  have hds : D.size ≤ k := by simpa [D, Circuit.size, relabel] using hf
  let A := a.length + first.length
  let B := b.length + first.length
  let Q := b.length + k
  let M := t+1
  by_cases hout : C.output < A + last.length
  · let S := crossing A last {C.output}
    have hs : S.card ≤ M ∧ ∀ i ∈ S, i < A := by
      have h := crossing_count A last {C.output} hg2 (by simpa using hout)
      refine ⟨?_,h.2⟩
      have hb : S.card ≤ 1 + last.length := by simpa only [Finset.card_singleton] using h.1
      dsimp [M]
      omega
    let r := move a.length b.length p
    have hr (i : ℕ) (hi : i < A) : r i < B := by
      dsimp [r, move]
      split_ifs with h
      · obtain ⟨hj, _⟩ := hp i h
        dsimp [B]; omega
      · dsimp [A] at hi
        dsimp [B]; omega
    let V := S.image r
    have hV : V.card ≤ M := (Finset.card_image_le (f := r)).trans hs.1
    have hQ (i : ℕ) (hi : i ∈ V) : i < Q := by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have h := hr j (hs.2 j hj)
      dsimp [B,Q] at *
      omega
    obtain ⟨E, hE, hsurj⟩ := sorted_pad V M Q hV hQ
    have inv (i : ℕ) (hi : i ∈ S) : ∃ j : Fin M, (E j).val = r i :=
      hsurj _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    let q (i : ℕ) := if h : i ∈ S then (inv i h).choose.val else M + last.length
    have qrange (i : ℕ) : q i < M ∨ M + last.length ≤ q i := by
      unfold q
      split_ifs with h
      · exact Or.inl (inv i h).choose.isLt
      · exact Or.inr le_rfl
    let F : Circuit := ⟨relabel A M q last, move A M q C.output⟩
    refine ⟨D, E, circuitFun M F, hd, hds, ⟨F, good_relabel _ _ _ _ hg2, ?_, fun _ => rfl⟩, hE, ?_⟩
    · simpa [F, Circuit.size, relabel] using hlast
    · intro x
      let u := a.map (fun j => j x)
      let v := b.map (fun j => j x)
      have ul : u.length = a.length := List.length_map _
      have vl : v.length = b.length := List.length_map _
      have eqin (i : ℕ) (hi : i < u.length) : v.getD (p i) false = u.getD i false := by
        have hi' : i < a.length := by simpa only [ul] using hi
        obtain ⟨hj, he⟩ := hp i hi'
        simp [u, v, List.getD_eq_getElem?_getD, hi', hj, he]
      let u' := run first u
      let v' := run D.gates v
      have u'l : u'.length = A := by rw [run_length, ul]
      have v'l : v'.length = B := by rw [run_length, vl]; simp [D, relabel, B]
      have eqpre (i : ℕ) : v'.getD (r i) false = u'.getD i false := by
        have e := move_agree first u v p (fun j hj => Or.inl (by
          rw [ul] at hj
          rw [vl]
          exact (hp j hj).choose)) eqin i
        simpa only [ul, vl] using e
      let w := List.ofFn (fun j : Fin M => v'.getD (E j).val false)
      let z := List.ofFn (fun j : Fin A => w.getD (q j.val) false)
      have wl : w.length = M := List.length_ofFn
      have zl : z.length = A := List.length_ofFn
      have eqz (i : ℕ) (hi : i < z.length) : w.getD (q i) false = z.getD i false := by
        let j : Fin A := ⟨i, by simpa only [zl] using hi⟩
        change w.getD (q j.val) false = z.getD j.val false
        simp [z, List.getD_eq_getElem?_getD]
      have eqs := move_agree last z w q (fun j _ => by simpa only [wl] using qrange j) eqz C.output
      have boundz (i : ℕ) (hi : i ∈ crossing z.length last {C.output}) :
          z.getD i false = u'.getD i false := by
        rw [zl] at hi
        change i ∈ S at hi
        have hiA := hs.2 i hi
        let ii : Fin A := ⟨i, hiA⟩
        let j := (inv i hi).choose
        have jval : q i = j.val := dite_eq_left hi
        have jgood : (E j).val = r i := (inv i hi).choose_spec
        rw [← eqpre i, ← jgood]
        change z.getD ii.val false = _
        rw [← eqz ii.val (by simpa only [zl] using hiA), jval]
        change (List.ofFn (fun j : Fin M => v'.getD (E j).val false)).getD j.val false = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left j.isLt]
        rfl
      have eqout := crossing_agree last {C.output} z u' (zl.trans u'l.symm) boundz C.output
        (Finset.mem_singleton_self _)
      change (run F.gates w).getD F.output false = (run C.gates u).getD C.output false
      have orig : run C.gates u = run last u' := by
        rw [← hrebuild]
        exact List.foldl_append
      rw [orig]
      rw [zl,wl] at eqs
      exact eqs.trans eqout
  · let F : Circuit := ⟨[],M⟩
    refine ⟨D, fun _ => Fin.last Q, circuitFun M F, hd, hds, ⟨F, ?_, by simp [F, Circuit.size], fun _ => rfl⟩,
      fun _ _ _ => Or.inr ⟨rfl,rfl⟩, ?_⟩
    · intro g h
      simp [F] at h
    · intro x
      rw [circuitFun]
      have hlen : A + last.length = a.length + C.gates.length := by
        rw [← hrebuild,List.length_append]
        dsimp [A]
        omega
      change (List.ofFn _).getD M false = (run C.gates (a.map (fun j => j x))).getD C.output false
      rw [get_missing _ _ (by rw [List.length_ofFn]), get_missing _ _ (by simp [run_length]; omega)]
