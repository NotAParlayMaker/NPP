import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3262_1_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_length (gs : List Gate) (init : List Bool) :
    (gs.foldl step init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma foldl_step_preserved (gs : List Gate) (init : List Bool) (k : ℕ) (hk : k < init.length) :
    (gs.foldl step init).getD k false = init.getD k false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step init g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma getD_append_last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl w.length)]
  simp

def remapWire (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : n ≤ w ∧ w < n + n then
    n + (σ ⟨w - n, by omega⟩).val
  else w

def remapGate (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire n σ)⟩

def remapCircuit (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (remapGate n σ), remapWire n σ C.output⟩

lemma remapWire_lt_of_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w m : ℕ} (hm : n + n ≤ m)
    (hw : w < m) : remapWire n σ w < m := by
  unfold remapWire
  split_ifs with h
  · have := (σ ⟨w - n, by omega⟩).isLt
    omega
  · exact hw

lemma remapWire_ge_of_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w m : ℕ} (hm : n + n ≤ m)
    (hw : m ≤ w) : remapWire n σ w = w := by
  unfold remapWire
  split_ifs with h
  · omega
  · rfl

lemma remapWire_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin (n + n) → Bool) (w : ℕ)
    (hw : w < n + n) :
    (List.ofFn (fun k : Fin (n + n) =>
      if h : k.val < n then x k
      else x (Fin.natAdd n (σ ⟨k.val - n, by omega⟩)))).getD w false =
    (List.ofFn x).getD (remapWire n σ w) false := by
  have hrw : remapWire n σ w < n + n := remapWire_lt_of_lt σ (le_refl _) hw
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw, dif_pos hrw,
    Option.getD_some]
  by_cases hwn : w < n
  · have hrem : remapWire n σ w = w := by unfold remapWire; rw [dif_neg (by omega)]
    simp only [dif_pos hwn]
    congr 1
    exact Fin.ext hrem.symm
  · have hrem : remapWire n σ w = n + (σ ⟨w - n, by omega⟩).val := by
      unfold remapWire; rw [dif_pos ⟨by omega, hw⟩]
    simp only [dif_neg hwn]
    congr 1
    exact Fin.ext (by simp [Fin.natAdd, hrem])

lemma remapCircuit_wires {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (hRB : ReadsBack (n + n) C) (x : Fin (n + n) → Bool) :
    let y : Fin (n + n) → Bool := fun k =>
      if h : k.val < n then x k
      else x (Fin.natAdd n (σ ⟨k.val - n, by omega⟩))
    ∀ j ≤ C.gates.length, ∀ w < n + n + j,
      ((C.gates.take j).foldl step (List.ofFn y)).getD w false =
      (((C.gates.take j).map (remapGate n σ)).foldl step (List.ofFn x)).getD (remapWire n σ w) false := by
  intro y j
  induction j with
  | zero =>
    intro _ w hw
    simp only [List.take_zero, List.map_nil, List.foldl_nil]
    exact remapWire_perm σ x w hw
  | succ j ih =>
    intro hj_le w hw
    have hj : j < C.gates.length := by omega
    have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
    rw [htake, List.map_append, List.map_singleton, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    set gs1 := (C.gates.take j).foldl step (List.ofFn y)
    set gs2 := ((C.gates.take j).map (remapGate n σ)).foldl step (List.ofFn x)
    have hlen1 : gs1.length = n + n + j := by
      simp [gs1, foldl_step_length, Nat.le_of_lt hj]
    have hlen2 : gs2.length = n + n + j := by
      simp [gs2, foldl_step_length, Nat.le_of_lt hj]
    by_cases hw_lt : w < n + n + j
    · have hw1 : w < gs1.length := by omega
      have hw2 : remapWire n σ w < gs2.length := by
        rw [hlen2]
        exact remapWire_lt_of_lt σ (by omega) hw_lt
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hw1,
        List.getElem?_append_left hw2]
      exact ih (Nat.le_of_lt hj) w hw_lt
    · have hw_eq : w = n + n + j := by omega
      subst hw_eq
      have hrw : remapWire n σ (n + n + j) = n + n + j :=
        remapWire_ge_of_ge σ (m := n + n + j) (by omega) (le_refl _)
      rw [hrw]
      have h1 : (step gs1 C.gates[j]).getD (n + n + j) false =
          C.gates[j].op.eval (C.gates[j].inputs.map fun i => gs1.getD i false) := by
        simp [step, hlen1]
      have h2 : (step gs2 (remapGate n σ C.gates[j])).getD (n + n + j) false =
          C.gates[j].op.eval ((C.gates[j].inputs.map (remapWire n σ)).map fun i => gs2.getD i false) := by
        simp [step, hlen2, remapGate]
      change (step gs1 C.gates[j]).getD (n + n + j) false =
        (step gs2 (remapGate n σ C.gates[j])).getD (n + n + j) false
      rw [h1, h2, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hgate_eq : gateAt C j = C.gates[j] := by
        simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      have hi_lt : i < n + n + j := hRB j hj i (by rw [hgate_eq]; exact hi)
      exact ih (Nat.le_of_lt hj) i hi_lt

lemma remapCircuit_eval {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (hRB : ReadsBack (n + n) C) (x : Fin (n + n) → Bool) :
    let y : Fin (n + n) → Bool := fun k =>
      if h : k.val < n then x k
      else x (Fin.natAdd n (σ ⟨k.val - n, by omega⟩))
    C.eval (List.ofFn y) = (remapCircuit n σ C).eval (List.ofFn x) := by
  intro y
  unfold Circuit.eval
  by_cases ho : C.output < n + n + C.gates.length
  · have h := remapCircuit_wires σ C hRB x C.gates.length (le_refl _) C.output ho
    rw [List.take_length] at h
    exact h
  · have hge : n + n + C.gates.length ≤ C.output := by omega
    have hrw : remapWire n σ C.output = C.output :=
      remapWire_ge_of_ge σ (by omega) hge
    have hlen1 : (C.wires (List.ofFn y)).length = n + n + C.gates.length := by
      unfold Circuit.wires
      change (C.gates.foldl step (List.ofFn y)).length = _
      rw [foldl_step_length, List.length_ofFn]
    have hlen2 : ((remapCircuit n σ C).wires (List.ofFn x)).length = n + n + C.gates.length := by
      unfold Circuit.wires remapCircuit
      change ((C.gates.map (remapGate n σ)).foldl step (List.ofFn x)).length = _
      rw [foldl_step_length, List.length_ofFn, List.length_map]
    simp only [remapCircuit, List.getD_eq_getElem?_getD, hrw]
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simpa [remapCircuit] using hlen2 ▸ hge)]

lemma remapCircuit_isAO2 {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (hA : IsAO2 (n + n) C) : IsAO2 (n + n) (remapCircuit n σ C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [remapCircuit, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact hA.1 g0 hg0
  · intro j hj i hi
    simp only [remapCircuit, List.length_map] at hj
    have hgate : gateAt (remapCircuit n σ C) j = remapGate n σ (gateAt C j) := by
      simp [gateAt, remapCircuit, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj]
    rw [hgate] at hi
    simp only [remapGate, List.mem_map] at hi
    obtain ⟨i0, hi0, rfl⟩ := hi
    exact remapWire_lt_of_lt σ (by omega) (hA.2.1 j hj i0 hi0)
  · intro g hg
    simp only [remapCircuit, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simp [remapGate, hA.2.2 g0 hg0]

def bipGraph (n : ℕ) (B : Finset (Fin n × Fin n)) : SimpleGraph (Fin (n + n)) where
  Adj a b := ∃ i j : Fin n, (i, j) ∈ B ∧
    ((a = Fin.castAdd n i ∧ b = Fin.natAdd n j) ∨
     (a = Fin.natAdd n j ∧ b = Fin.castAdd n i))
  symm := ⟨fun _ _ ⟨i, j, hij, h⟩ => ⟨i, j, hij, by tauto⟩⟩
  loopless := by
    refine ⟨fun a ⟨i, j, _, h⟩ => ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := congrArg Fin.val (h1.symm.trans h2)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · have := congrArg Fin.val (h1.symm.trans h2)
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega

lemma castAdd_ne_natAdd {n : ℕ} (i j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

lemma bipGraph_noFourCycle {n : ℕ} (B : Finset (Fin n × Fin n))
    [DecidableRel (bipGraph n B).Adj]
    (hB : ∀ x5 x6 x7 x8 : Fin n, x5 ≠ x6 → x7 ≠ x8 →
      ¬((x5, x7) ∈ B ∧ (x5, x8) ∈ B ∧ (x6, x7) ∈ B ∧ (x6, x8) ∈ B)) :
    NoFourCycle (bipGraph n B) := by
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hau, hbu⟩ := (Finset.mem_filter.mp hu).2
  obtain ⟨hav, hbv⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨ia, ja, hia, ha⟩ := hau
  obtain ⟨ib, jb, hib, hb⟩ := hbu
  obtain ⟨ia', ja', hia', ha'⟩ := hav
  obtain ⟨ib', jb', hib', hb'⟩ := hbv
  rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · -- a = castAdd n ia, u = natAdd n ja, b = castAdd n ib, u = natAdd n jb
    have hjb_eq : jb = ja := by
      have := congrArg Fin.val (ha2.symm.trans hb2)
      simp only [Fin.val_natAdd] at this
      exact Fin.ext (by omega)
    rcases ha' with ⟨ha1', ha2'⟩ | ⟨ha1', _⟩
    · have hia_eq : ia' = ia := by
        have := congrArg Fin.val (ha1.symm.trans ha1')
        simp only [Fin.val_castAdd] at this
        exact Fin.ext (by omega)
      rcases hb' with ⟨hb1', hb2'⟩ | ⟨hb1', _⟩
      · have hib_eq : ib' = ib := by
          have := congrArg Fin.val (hb1.symm.trans hb1')
          simp only [Fin.val_castAdd] at this
          exact Fin.ext (by omega)
        have hjb'_eq : jb' = ja' := by
          have := congrArg Fin.val (ha2'.symm.trans hb2')
          simp only [Fin.val_natAdd] at this
          exact Fin.ext (by omega)
        have hab_ne : ia ≠ ib := fun h => hab (by rw [ha1, hb1, h])
        by_contra huv
        have hja_ne : ja ≠ ja' := fun h => huv (by rw [ha2, ha2', h])
        exact hB ia ib ja ja' hab_ne hja_ne
          ⟨hia, hia_eq ▸ hia', hjb_eq ▸ hib, hib_eq ▸ hjb'_eq ▸ hib'⟩
      · exfalso; exact castAdd_ne_natAdd ib jb' (hb1.symm.trans hb1')
    · exfalso; exact castAdd_ne_natAdd ia ja' (ha1.symm.trans ha1')
  · exfalso; exact castAdd_ne_natAdd ib ja (hb2.symm.trans ha2)
  · exfalso; exact castAdd_ne_natAdd ia jb (ha2.symm.trans hb2)
  · -- a = natAdd n ja, u = castAdd n ia, b = natAdd n jb, u = castAdd n ib
    have hib_eq : ib = ia := by
      have := congrArg Fin.val (ha2.symm.trans hb2)
      simp only [Fin.val_castAdd] at this
      exact Fin.ext (by omega)
    rcases ha' with ⟨ha1', _⟩ | ⟨ha1', ha2'⟩
    · exfalso; exact castAdd_ne_natAdd ia' ja (ha1'.symm.trans ha1)
    · have hja_eq : ja' = ja := by
        have := congrArg Fin.val (ha1.symm.trans ha1')
        simp only [Fin.val_natAdd] at this
        exact Fin.ext (by omega)
      rcases hb' with ⟨hb1', _⟩ | ⟨hb1', hb2'⟩
      · exfalso; exact castAdd_ne_natAdd ib' jb (hb1'.symm.trans hb1)
      · have hjb_eq : jb' = jb := by
          have := congrArg Fin.val (hb1.symm.trans hb1')
          simp only [Fin.val_natAdd] at this
          exact Fin.ext (by omega)
        have hib'_eq : ib' = ia' := by
          have := congrArg Fin.val (ha2'.symm.trans hb2')
          simp only [Fin.val_castAdd] at this
          exact Fin.ext (by omega)
        have hab_ne : ja ≠ jb := fun h => hab (by rw [ha1, hb1, h])
        by_contra huv
        have hia_ne : ia ≠ ia' := fun h => huv (by rw [ha2, ha2', h])
        exact hB ia ia' ja jb hia_ne hab_ne
          ⟨hia, hib_eq ▸ hib, hja_eq ▸ hia', hib'_eq ▸ hjb_eq ▸ hib'⟩

lemma bipGraph_edgeFinset_card {n : ℕ} (B : Finset (Fin n × Fin n))
    [DecidableRel (bipGraph n B).Adj] :
    (bipGraph n B).edgeFinset.card = B.card := by
  symm
  refine Finset.card_bij (fun p _ => s(Fin.castAdd n p.1, Fin.natAdd n p.2)) ?_ ?_ ?_
  · intro p hp
    rw [SimpleGraph.mem_edgeFinset]
    exact ⟨p.1, p.2, hp, Or.inl ⟨rfl, rfl⟩⟩
  · intro p hp q hq heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Prod.ext
        (Fin.ext (by simpa [Fin.val_castAdd] using congrArg Fin.val h1))
        (Fin.ext (by have := congrArg Fin.val h2; simp only [Fin.val_natAdd] at this; omega))
    · exfalso; exact castAdd_ne_natAdd p.1 q.2 h1
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨i, j, hij, h⟩ := he
      refine ⟨(i, j), hij, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap

end PEqualNP.Outside.R_meta_3262_1_aux

theorem PEqualNP.Outside.R_meta_3262_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C' ∧ PEqualNP.TopForm.TopForm G C' ∧ C'.size ≤ C.size)
    (h2 : ∀ (x1 : ℕ) (G : SimpleGraph (Fin (x1 + x1))) [DecidableRel G.Adj],
      1 ≤ x1 → PEqualNP.TopForm.NoFourCycle G →
      (∀ i j : Fin x1, ¬ G.Adj (Fin.castAdd x1 i) (Fin.castAdd x1 j)) →
      (∀ i j : Fin x1, ¬ G.Adj (Fin.natAdd x1 i) (Fin.natAdd x1 j)) →
      (∀ i : Fin x1, G.Adj (Fin.castAdd x1 i) (Fin.natAdd x1 i)) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        G.edgeFinset.card + x1 ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x2 ∧ (x5, x8) ∈ x2 ∧ (x6, x7) ∈ x2 ∧ (x6, x8) ∈ x2)) → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 h4 hmatch hAO hfun
  by_cases hx1 : x1 = 0
  · subst hx1
    have hx2 : x2 = ∅ := by
      ext p
      exact Fin.elim0 p.1
    simp [hx2]
  · have hx1_pos : 1 ≤ x1 := Nat.pos_of_ne_zero hx1
    let B' : Finset (Fin x1 × Fin x1) := x2.image (fun p => (p.1, x3.symm p.2))
    have hB'_card : B'.card = x2.card := by
      apply Finset.card_image_of_injective
      intro p q hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (x3.symm.injective hpq.2)
    have hB'_4 : ∀ x5 x6 x7 x8 : Fin x1, x5 ≠ x6 → x7 ≠ x8 →
        ¬((x5, x7) ∈ B' ∧ (x5, x8) ∈ B' ∧ (x6, x7) ∈ B' ∧ (x6, x8) ∈ B') := by
      intro x5 x6 x7 x8 h56 h78 ⟨h1', h2', h3', h4'⟩
      simp only [B', Finset.mem_image, Prod.mk.injEq] at h1' h2' h3' h4'
      obtain ⟨⟨a1, b1⟩, hab1, ha1, hb1⟩ := h1'
      obtain ⟨⟨a2, b2⟩, hab2, ha2, hb2⟩ := h2'
      obtain ⟨⟨a3, b3⟩, hab3, ha3, hb3⟩ := h3'
      obtain ⟨⟨a4, b4⟩, hab4, ha4, hb4⟩ := h4'
      dsimp only at ha1 hb1 ha2 hb2 ha3 hb3 ha4 hb4
      have hx3 : x3 x7 ≠ x3 x8 := fun h => h78 (x3.injective h)
      have hb1' : b1 = x3 x7 := by rw [← hb1, Equiv.apply_symm_apply]
      have hb2' : b2 = x3 x8 := by rw [← hb2, Equiv.apply_symm_apply]
      have hb3' : b3 = x3 x7 := by rw [← hb3, Equiv.apply_symm_apply]
      have hb4' : b4 = x3 x8 := by rw [← hb4, Equiv.apply_symm_apply]
      rw [ha1, hb1'] at hab1; rw [ha2, hb2'] at hab2; rw [ha3, hb3'] at hab3; rw [ha4, hb4'] at hab4
      exact h4 x5 x6 (x3 x7) (x3 x8) h56 hx3 ⟨hab1, hab2, hab3, hab4⟩
    let G := PEqualNP.Outside.R_meta_3262_1_aux.bipGraph x1 B'
    classical
    have hG_4 : PEqualNP.TopForm.NoFourCycle G :=
      PEqualNP.Outside.R_meta_3262_1_aux.bipGraph_noFourCycle B' hB'_4
    have hG_match : ∀ i : Fin x1, G.Adj (Fin.castAdd x1 i) (Fin.natAdd x1 i) := by
      intro i
      refine ⟨i, i, ?_, Or.inl ⟨rfl, rfl⟩⟩
      simp only [B', Finset.mem_image]
      exact ⟨(i, x3 i), hmatch i, by simp⟩
    have hG_ne : G.edgeFinset.Nonempty := by
      refine ⟨s(Fin.castAdd x1 ⟨0, hx1_pos⟩, Fin.natAdd x1 ⟨0, hx1_pos⟩), ?_⟩
      rw [SimpleGraph.mem_edgeFinset]
      exact hG_match ⟨0, hx1_pos⟩
    let C' := PEqualNP.Outside.R_meta_3262_1_aux.remapCircuit x1 x3.symm x4
    have hC'_AO : PEqualNP.TopForm.IsAO2 (x1 + x1) C' :=
      PEqualNP.Outside.R_meta_3262_1_aux.remapCircuit_isAO2 x3.symm x4 hAO
    have hC'_size : C'.size = x4.size := by
      simp [C', PEqualNP.Outside.R_meta_3262_1_aux.remapCircuit, PEqualNP.CircuitLowerBounds.Circuit.size]
    have hC'_fun : PEqualNP.MetaComplexity.circuitFun (x1 + x1) C' =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
      funext x
      have hev := PEqualNP.Outside.R_meta_3262_1_aux.remapCircuit_eval x3.symm x4 hAO.2.1 x
      change PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 _ =
        PEqualNP.MetaComplexity.circuitFun (x1 + x1) C' x at hev
      rw [← hev, hfun]
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
      congr 1
      apply propext
      constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        refine ⟨Fin.castAdd x1 i, Fin.natAdd x1 (x3.symm j),
          ⟨i, x3.symm j, Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩, ?_, ?_⟩
        · simpa [Fin.castAdd] using hi
        · simpa [Fin.natAdd] using hj
      · rintro ⟨a, b, ⟨i, j, hij, hab⟩, ha, hb⟩
        simp only [B', Finset.mem_image, Prod.mk.injEq] at hij
        obtain ⟨⟨i0, j0⟩, hij0, rfl, rfl⟩ := hij
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨i0, j0, hij0, ?_, ?_⟩
          · simpa [Fin.castAdd] using ha
          · simpa [Fin.natAdd] using hb
        · refine ⟨i0, j0, hij0, ?_, ?_⟩
          · simpa [Fin.castAdd] using hb
          · simpa [Fin.natAdd] using ha
    obtain ⟨C'', hLeast, hTF, hle⟩ := h1 (x1 + x1) G hG_4 hG_ne C' hC'_AO hC'_fun
    have hL_disj : ∀ i j : Fin x1, ¬ G.Adj (Fin.castAdd x1 i) (Fin.castAdd x1 j) := by
      rintro i j ⟨_, _, _, ⟨_, h⟩ | ⟨h, _⟩⟩
      · exact PEqualNP.Outside.R_meta_3262_1_aux.castAdd_ne_natAdd j _ h
      · exact PEqualNP.Outside.R_meta_3262_1_aux.castAdd_ne_natAdd i _ h
    have hR_disj : ∀ i j : Fin x1, ¬ G.Adj (Fin.natAdd x1 i) (Fin.natAdd x1 j) := by
      rintro i j ⟨_, _, _, ⟨h, _⟩ | ⟨_, h⟩⟩
      · exact PEqualNP.Outside.R_meta_3262_1_aux.castAdd_ne_natAdd _ i h.symm
      · exact PEqualNP.Outside.R_meta_3262_1_aux.castAdd_ne_natAdd _ j h.symm
    have hbound := h2 x1 G hx1_pos hG_4 hL_disj hR_disj hG_match C'' hLeast hTF
    have hcard : G.edgeFinset.card = x2.card := by
      rw [PEqualNP.Outside.R_meta_3262_1_aux.bipGraph_edgeFinset_card B', hB'_card]
    omega
