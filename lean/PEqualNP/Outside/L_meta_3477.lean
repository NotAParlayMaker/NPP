import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3477

-- The support-size argument follows L-meta-1660.

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Dep (n : ℕ) (D : Finset (Fin n)) (h : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i ∈ D, x i = y i) → h x = h y

def St (n : ℕ) (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n)) : Prop :=
  (∀ x, (W x).length = m) ∧ ∀ i, Dep n (Sup i) (fun x => (W x).getD i false)

def sup0 (n : ℕ) (i : ℕ) : Finset (Fin n) := if h : i < n then {⟨i, h⟩} else ∅

lemma st_step (n : ℕ) (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n))
    (h : St n W m Sup) (g : Gate) :
    St n (fun x => step (W x) g) (m + 1)
      (fun i => if i = m then g.inputs.toFinset.biUnion Sup else Sup i) := by
  obtain ⟨hm, hD⟩ := h
  refine ⟨fun x => by simp [step, hm x], fun i => ?_⟩
  intro x y hxy
  show (step (W x) g).getD i false = (step (W y) g).getD i false
  unfold step
  rcases lt_trichotomy i m with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by rw [hm x]; exact hi),
      List.getD_append _ _ _ _ (by rw [hm y]; exact hi)]
    refine hD i x y (fun j hj => hxy j ?_)
    simpa [hi.ne] using hj
  · rw [List.getD_append_right _ _ _ _ (by rw [hm x]; omega),
      List.getD_append_right _ _ _ _ (by rw [hm y]; omega), hm x, hm y]
    have e : (g.inputs.map fun k => (W x).getD k false) =
        (g.inputs.map fun k => (W y).getD k false) := by
      apply List.map_congr_left
      intro k hk
      refine hD k x y (fun j hj => hxy j ?_)
      have hmem : j ∈ g.inputs.toFinset.biUnion Sup :=
        Finset.mem_biUnion.mpr ⟨k, List.mem_toFinset.mpr hk, hj⟩
      simpa [hi] using hmem
    rw [e]
  · rw [List.getD_append_right _ _ _ _ (by rw [hm x]; omega),
      List.getD_append_right _ _ _ _ (by rw [hm y]; omega), hm x, hm y]
    obtain ⟨k, hk⟩ : ∃ k, i - m = k + 1 := ⟨i - m - 1, by omega⟩
    rw [hk]
    rfl

lemma st_init (n : ℕ) : St n (fun x : Fin n → Bool => List.ofFn x) n (sup0 n) := by
  refine ⟨fun x => List.length_ofFn, fun i x y hxy => ?_⟩
  show (List.ofFn x).getD i false = (List.ofFn y).getD i false
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    List.getElem?_ofFn]
  by_cases h : i < n
  · have hx := hxy ⟨i, h⟩ (by simp [sup0, h])
    simp [h, hx]
  · simp [h]

lemma sup0_card (n i : ℕ) : (sup0 n i).card ≤ 1 := by
  unfold sup0
  split <;> simp

lemma bound_step (n : ℕ) (Sup : ℕ → Finset (Fin n)) (k m : ℕ) (T : Finset ℕ)
    (hT : T.card ≤ 2) (h : ∀ Q : Finset ℕ, (Q.biUnion Sup).card ≤ Q.card + k) :
    ∀ Q : Finset ℕ,
      (Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i)).card ≤
        Q.card + (k + 1) := by
  intro Q
  by_cases hm : m ∈ Q
  · have e : Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i) =
        (T ∪ Q.erase m).biUnion Sup := by
      ext j
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
      constructor
      · rintro ⟨i, hi, hj⟩
        by_cases him : i = m
        · rw [ite_eq_left him] at hj
          obtain ⟨t, ht, hjt⟩ := Finset.mem_biUnion.mp hj
          exact ⟨t, Or.inl ht, hjt⟩
        · rw [ite_eq_right him] at hj
          exact ⟨i, Or.inr ⟨him, hi⟩, hj⟩
      · rintro ⟨t, ht | ⟨htm, htQ⟩, hj⟩
        · refine ⟨m, hm, ?_⟩
          rw [ite_eq_left rfl]
          exact Finset.mem_biUnion.mpr ⟨t, ht, hj⟩
        · refine ⟨t, htQ, ?_⟩
          rw [ite_eq_right htm]
          exact hj
    rw [e]
    have h1 := h (T ∪ Q.erase m)
    have h2 := Finset.card_union_le T (Q.erase m)
    have h3 := Finset.card_erase_of_mem hm
    have h4 : 0 < Q.card := Finset.card_pos.mpr ⟨m, hm⟩
    omega
  · have e : Q.biUnion (fun i => if i = m then T.biUnion Sup else Sup i) =
        Q.biUnion Sup := by
      apply Finset.biUnion_congr rfl
      intro i hi
      have him : i ≠ m := fun h' => hm (h' ▸ hi)
      simp [him]
    rw [e]
    have := h Q
    omega

lemma fold_sup (n : ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ (W : (Fin n → Bool) → List Bool) (m : ℕ) (Sup : ℕ → Finset (Fin n)) (k : ℕ),
      St n W m Sup → (∀ Q : Finset ℕ, (Q.biUnion Sup).card ≤ Q.card + k) →
      ∃ Sup' : ℕ → Finset (Fin n),
        (∀ i, Dep n (Sup' i) (fun x => (gs.foldl step (W x)).getD i false)) ∧
        ∀ Q : Finset ℕ, (Q.biUnion Sup').card ≤ Q.card + (k + gs.length) := by
  intro gs
  induction gs with
  | nil =>
    intro _ W m Sup k hSt hb
    exact ⟨Sup, hSt.2, fun Q => by simpa using hb Q⟩
  | cons g gs ih =>
    intro hfan W m Sup k hSt hb
    have hg := hfan g List.mem_cons_self
    have hT : g.inputs.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans hg
    obtain ⟨Sup', hdep, hb'⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      _ (m + 1) _ (k + 1) (st_step n W m Sup hSt g) (bound_step n Sup k m _ hT hb)
    refine ⟨Sup', hdep, fun Q => ?_⟩
    have := hb' Q
    simp only [List.length_cons]
    omega


lemma cast_ne_nat (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro e
  have h := congrArg Fin.val e
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h
  have := p.isLt
  omega

lemma nat_inj (N : ℕ) (m l : Fin N) (e : Fin.natAdd N m = Fin.natAdd N l) : m = l := by
  have h := congrArg Fin.val e
  simp only [Fin.val_natAdd] at h
  exact Fin.ext (by omega)


def linearStep (w : List (Bool × Bool)) (g : Gate) :
    List (Bool × Bool) :=
  w ++ [match g.op with
    | .or => ((g.inputs.map fun i => w.getD i (false, false)).any (·.1),
              (g.inputs.map fun i => w.getD i (false, false)).any (·.2))
    | .and => (g.inputs.map fun i => w.getD i (false, false)).foldl
        (fun a p => (a.1 && p.1, (a.1 && p.2) || (a.2 && p.1))) (true, false)
    | _ => (false, false)]

def related (p : Bool × Bool) (b : Bool) : Prop :=
  (p.1 = true ∨ p.2 = true) → b = true

lemma related_or (a b : Bool × Bool) (x y : Bool)
    (ha : related a x) (hb : related b y) :
    related (a.1 || b.1, a.2 || b.2) (x || y) := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> simp_all [related]

lemma related_and (a b : Bool × Bool) (x y : Bool)
    (ha : related a x) (hb : related b y) :
    related (a.1 && b.1, (a.1 && b.2) || (a.2 && b.1)) (x && y) := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> simp_all [related]

lemma fold_related (gs : List Gate)
    (hlegal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (v : List (Bool × Bool)) (w : List Bool) (hlen : v.length = w.length)
    (hrel : ∀ i, related (v.getD i (false, false)) (w.getD i false)) :
    ∀ i, related ((gs.foldl linearStep v).getD i (false, false))
      ((gs.foldl step w).getD i false) := by
  induction gs generalizing v w with
  | nil => exact hrel
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have ⟨hop, hin⟩ := hlegal g List.mem_cons_self
    have hin : ∃ a b, g.inputs = [a,b] := by
      rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp_all
    obtain ⟨a,b,hin⟩ := hin
    apply ih (fun k hk => hlegal k (List.mem_cons_of_mem _ hk)) _ _
    · simp [linearStep, step, hlen]
    · intro i
      by_cases hi : i < v.length
      · have hw : i < w.length := hlen ▸ hi
        unfold linearStep step
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hw]
        exact hrel i
      · unfold linearStep step
        rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi),
            List.getD_append_right _ _ _ _ (by omega), hlen]
        by_cases he : i = w.length
        · subst i
          rw [Nat.sub_self]
          rcases hop with ho | ho
          · simpa [hin, ho, GateOp.eval] using
              related_and _ _ _ _ (hrel a) (hrel b)
          · simpa [hin, ho, GateOp.eval] using
              related_or _ _ _ _ (hrel a) (hrel b)
        · obtain ⟨k,hk⟩ : ∃ k, i - w.length = k+1 := ⟨i-w.length-1, by omega⟩
          simp [hk, related]

lemma linear_sound (C : Circuit) (x : List Bool) (isPoint : ℕ → Bool)
    (hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    ((PEqualNP.ReadK.linearParts C isPoint x).getD C.output (false, false)).2 = true →
      C.eval x = true := by
  let v := x.zipIdx.map fun (b,i) => if isPoint i then (false,b) else (b,false)
  have hv : v.length = x.length := by simp [v]
  have hr : ∀ i, related (v.getD i (false,false)) (x.getD i false) := by
    intro i
    by_cases hi : i < x.length
    · have hvi : i < v.length := hv.symm ▸ hi
      rw [List.getD_eq_getElem _ _ hvi, List.getD_eq_getElem _ _ hi]
      simp only [v, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      split <;> simp [related]
    · have hv' : v.getD i (false,false) = (false,false) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : v.length ≤ i)]
      rw [hv']
      simp [related]
  intro h
  exact fold_related C.gates hlegal v x hv hr C.output (Or.inr h)

end PEqualNP.Outside.L_meta_3477

open PEqualNP.Outside.L_meta_3477 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3477 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (9 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x14 < x2)) (↑x13.1) (x2 + ↑x13.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro q N I _ C hq hsmall hN hdegree _ hAO hsound
  classical
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hAO.2.2 g hg).le
  obtain ⟨Sup, hdep, hb⟩ := fold_sup (N + N) C.gates hfan _ (N + N)
    (sup0 (N + N)) 0 (st_init (N + N)) (fun Q => by
      have := Finset.card_biUnion_le_card_mul Q (sup0 (N + N)) 1
        (fun a _ => sup0_card (N + N) a)
      omega)
  let S := Sup C.output
  have hS : S.card ≤ C.size + 1 := by
    have h := hb {C.output}
    rw [Finset.singleton_biUnion, Finset.card_singleton] at h
    simpa [S, Circuit.size, Nat.add_comm] using h
  have htrue : ∀ p l : Fin N, PEqualNP.ReadK.lineSingle C (N + N)
      (fun i => decide (i < N)) p.val (N + l.val) = true →
      PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true := by
    intro p l hpl
    let x : Fin (N + N) → Bool := fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
    have hx : List.ofFn x = (List.range (N + N)).map (fun i => i == p.val || i == N + l.val) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, x]
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
          Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
    change C.eval (List.ofFn x) = true
    rw [hx]
    exact linear_sound C _ (fun i => decide (i < N))
      (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) hpl
  have both : ∀ p l : Fin N, PEqualNP.ReadK.lineSingle C (N + N)
      (fun i => decide (i < N)) p.val (N + l.val) = true →
      Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S := by
    intro p l hpl
    let x : Fin (N + N) → Bool := fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
    have hx : PEqualNP.MetaComplexity.circuitFun (N + N) C x = true := htrue p l hpl
    have hd : ∀ y, (∀ i ∈ S, x i = y i) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C y = true := by
      intro y hy
      have he := hdep C.output x y hy
      exact he.symm.trans hx
    constructor
    · by_contra hp
      let y : Fin (N + N) → Bool := fun i => decide (i = Fin.natAdd N l)
      have hty := hd y (by
        intro i hi
        exact decide_eq_decide.mpr ⟨fun h => h.resolve_left (fun he => hp (he ▸ hi)), Or.inr⟩)
      have hcard : Fintype.card {m : Fin N // y (Fin.natAdd N m) = true} ≤ q := by
        rw [Fintype.card_subtype]
        refine (Finset.card_le_card (t := {l}) ?_).trans (by simp; omega)
        intro m hm
        exact Finset.mem_singleton.mpr (nat_inj N m l (of_decide_eq_true (Finset.mem_filter.mp hm).2))
      have noEdge : ¬ ∃ a b : Fin N, I a b ∧ y (Fin.castAdd N a) = true ∧
          y (Fin.natAdd N b) = true := by
        rintro ⟨a, b, _, ha, _⟩
        exact cast_ne_nat N a l (of_decide_eq_true ha)
      rw [hsound y hcard noEdge] at hty
      contradiction
    · by_contra hl
      let y : Fin (N + N) → Bool := fun i => decide (i = Fin.castAdd N p)
      have hty := hd y (by
        intro i hi
        exact decide_eq_decide.mpr ⟨fun h => h.resolve_right (fun he => hl (he ▸ hi)), Or.inl⟩)
      have hcard : Fintype.card {m : Fin N // y (Fin.natAdd N m) = true} ≤ q := by
        rw [Fintype.card_subtype]
        have empty : Finset.univ.filter (fun m : Fin N => y (Fin.natAdd N m) = true) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro m _ hm
          exact cast_ne_nat N p m (of_decide_eq_true hm).symm
        rw [empty]
        simp
      have noEdge : ¬ ∃ a b : Fin N, I a b ∧ y (Fin.castAdd N a) = true ∧
          y (Fin.natAdd N b) = true := by
        rintro ⟨a, b, _, _, hb⟩
        exact cast_ne_nat N p b (of_decide_eq_true hb).symm
      rw [hsound y hcard noEdge] at hty
      contradiction
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2 ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true
  rw [Fintype.card_subtype]
  change E.card ≤ 10 * C.size
  by_cases hE : E.Nonempty
  · obtain ⟨⟨p,l⟩, hpl⟩ := hE
    have hp := (both p l (Finset.mem_filter.mp hpl).2.2).1
    let T := S.erase (Fin.castAdd N p)
    have hT : T.card ≤ C.size := by
      have h := Finset.card_erase_of_mem hp
      simp only [T]
      omega
    refine (Finset.card_le_mul_card_image_of_maps_to
      (f := fun e : Fin N × Fin N => Fin.natAdd N e.2) (s := E) (t := T) ?_ 10 ?_).trans
      (Nat.mul_le_mul_left 10 hT)
    · intro e he
      refine Finset.mem_erase.mpr ⟨(cast_ne_nat N p e.2).symm, ?_⟩
      exact (both e.1 e.2 (Finset.mem_filter.mp he).2.2).2
    · intro j hj
      by_cases hex : ∃ l : Fin N, Fin.natAdd N l = j
      · obtain ⟨m, rfl⟩ := hex
        have hsub : (E.filter fun e => Fin.natAdd N e.2 = Fin.natAdd N m).card ≤
            (Finset.univ.filter fun a : Fin N => I a m).card := by
          apply Finset.card_le_card_of_injOn (fun e => e.1)
          · intro e he
            have hm := Finset.mem_filter.mp he
            have he2 := nat_inj N e.2 m hm.2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he2 ▸ (Finset.mem_filter.mp hm.1).2.1⟩
          · intro a ha b hb heq
            exact Prod.ext heq
              ((nat_inj N a.2 m (Finset.mem_filter.mp ha).2).trans
              (nat_inj N b.2 m (Finset.mem_filter.mp hb).2).symm)
        have hh := hdegree m
        rw [Fintype.card_subtype] at hh
        rw [hh] at hsub
        omega
      · have h₀ : E.filter (fun e => Fin.natAdd N e.2 = j) = ∅ := by
          exact Finset.filter_eq_empty_iff.mpr (fun e _ he => hex ⟨e.2, he⟩)
        rw [h₀]
        simp
  · have h₀ : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    simp [h₀]
