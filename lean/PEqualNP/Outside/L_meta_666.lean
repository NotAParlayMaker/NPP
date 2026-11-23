import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_666_aux

open PEqualNP.CircuitLowerBounds

-- One step of the wire fold of a circuit.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (gates : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gates, o⟩ x = gates.foldl stepW x := rfl

theorem foldl_length (l : List Gate) :
    ∀ x : List Bool, (l.foldl stepW x).length = x.length + l.length := by
  induction l with
  | nil => intro x; simp
  | cons g l ih =>
    intro x
    simp only [List.foldl]
    rw [ih]
    simp [stepW]
    omega

theorem foldl_prefix (l : List Gate) : ∀ x : List Bool, x <+: l.foldl stepW x := by
  induction l with
  | nil => intro x; simp
  | cons g l ih =>
    intro x
    simp only [List.foldl]
    exact (List.prefix_append x _).trans (ih (stepW x g))

theorem getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) (k : ℕ) (hk : k < l₁.length) :
    l₂.getD k false = l₁.getD k false := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hk

theorem getD_out (l : List Bool) (k : ℕ) (hk : l.length ≤ k) : l.getD k false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
  rfl

theorem take_fold_prefix (gates : List Gate) (x : List Bool) (m : ℕ) :
    (gates.take m).foldl stepW x <+: gates.foldl stepW x := by
  conv_rhs => rw [← List.take_append_drop m gates]
  rw [List.foldl_append]
  exact foldl_prefix _ _

theorem read_eq (gates : List Gate) (x : List Bool) (m : ℕ) (hm : m < gates.length) (j : ℕ) :
    ((gates.take m).foldl stepW x).getD j false =
      if j < x.length + m then (gates.foldl stepW x).getD j false else false := by
  have hlen : ((gates.take m).foldl stepW x).length = x.length + m := by
    rw [foldl_length]
    simp
    omega
  split_ifs with h
  · rw [getD_of_prefix (take_fold_prefix gates x m) j (by omega)]
  · exact getD_out _ _ (by omega)

theorem gate_val (gates : List Gate) (x : List Bool) (m : ℕ) (hm : m < gates.length) :
    (gates.foldl stepW x).getD (x.length + m) false =
      (gates[m]).op.eval ((gates[m]).inputs.map fun j =>
        if j < x.length + m then (gates.foldl stepW x).getD j false else false) := by
  have htake : gates.take (m + 1) = gates.take m ++ [gates[m]] := by
    rw [List.take_add_one]
    simp [List.getElem?_eq_getElem hm]
  have hpre := take_fold_prefix gates x (m + 1)
  rw [htake, List.foldl_concat] at hpre
  have hlen : ((gates.take m).foldl stepW x).length = x.length + m := by
    rw [foldl_length]
    simp
    omega
  rw [getD_of_prefix hpre]
  · simp only [stepW]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hlen, Nat.sub_self, List.getD_cons_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    exact read_eq gates x m hm j
  · simp [stepW, hlen]

theorem input_val (gates : List Gate) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    (gates.foldl stepW x).getD k false = x.getD k false :=
  getD_of_prefix (foldl_prefix gates x) k hk

theorem out_val (gates : List Gate) (x : List Bool) (k : ℕ) (hk : x.length + gates.length ≤ k) :
    (gates.foldl stepW x).getD k false = false :=
  getD_out _ _ (by rw [foldl_length]; omega)

-- The lines of the plane of order 2.
def line (w : Fin 7) : Finset (Fin 7) := ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)

theorem line_card : ∀ w : Fin 7, (line w).card = 3 := by decide

theorem line_inter : ∀ a b : Fin 7, a ≠ b → (line a ∩ line b).card ≤ 1 := by decide

theorem line_union2 : ∀ a b : Fin 7, a ≠ b → 5 ≤ (line a ∪ line b).card := by decide

theorem line_union3 : ∀ a b c : Fin 7, a ≠ b → a ≠ c → b ≠ c →
    6 ≤ (line a ∪ line b ∪ line c).card := by decide

theorem line_image_card : (Finset.univ.image line).card = 7 := by decide

-- A line made by one gate from two sets that are not the line itself.
theorem classify (V : Finset (Finset (Fin 7))) (L A B : Finset (Fin 7)) (hL : L.card = 3)
    (hA : A ∈ V ∨ A.card ≤ 1) (hB : B ∈ V ∨ B.card ≤ 1) (hAL : A ≠ L) (hBL : B ≠ L)
    (h : A ∪ B = L ∨ A ∩ B = L) :
    (∃ P ∈ V, P.card = 2 ∧ P ⊆ L) ∨ (∃ Q ∈ V, Q.card = 4 ∧ L ⊆ Q) ∨
      (∃ A ∈ V, ∃ B ∈ V, A ≠ B ∧ A.card = 5 ∧ B.card = 5 ∧ L ⊆ A ∧ L ⊆ B) := by
  rcases h with h | h
  · left
    have hAs : A ⊆ L := h ▸ Finset.subset_union_left
    have hBs : B ⊆ L := h ▸ Finset.subset_union_right
    have hA3 : A.card < 3 := by
      rcases lt_or_ge A.card 3 with h3 | h3
      · exact h3
      · exact absurd (Finset.eq_of_subset_of_card_le hAs (by omega)) hAL
    have hB3 : B.card < 3 := by
      rcases lt_or_ge B.card 3 with h3 | h3
      · exact h3
      · exact absurd (Finset.eq_of_subset_of_card_le hBs (by omega)) hBL
    have hu := Finset.card_union_le A B
    rw [h, hL] at hu
    by_cases hA2 : A.card = 2
    · exact ⟨A, hA.resolve_right (by omega), hA2, hAs⟩
    · have hB2 : B.card = 2 := by omega
      exact ⟨B, hB.resolve_right (by omega), hB2, hBs⟩
  · right
    have hAs : L ⊆ A := h ▸ Finset.inter_subset_left
    have hBs : L ⊆ B := h ▸ Finset.inter_subset_right
    have hA4 : 4 ≤ A.card := by
      have := Finset.card_le_card hAs
      rcases lt_or_ge A.card 4 with h3 | h3
      · exact absurd (Finset.eq_of_subset_of_card_le hAs (by omega)).symm hAL
      · exact h3
    have hB4 : 4 ≤ B.card := by
      have := Finset.card_le_card hBs
      rcases lt_or_ge B.card 4 with h3 | h3
      · exact absurd (Finset.eq_of_subset_of_card_le hBs (by omega)).symm hBL
      · exact h3
    have hAV : A ∈ V := hA.resolve_right (by omega)
    have hBV : B ∈ V := hB.resolve_right (by omega)
    have hie := Finset.card_union_add_card_inter A B
    have hu : (A ∪ B).card ≤ 7 := by
      have := Finset.card_le_univ (A ∪ B)
      simpa using this
    rw [h, hL] at hie
    by_cases hA4' : A.card = 4
    · exact Or.inl ⟨A, hAV, hA4', hAs⟩
    · by_cases hB4' : B.card = 4
      · exact Or.inl ⟨B, hBV, hB4', hBs⟩
      · right
        refine ⟨A, hAV, B, hBV, ?_, by omega, by omega, hAs, hBs⟩
        rintro rfl
        rw [Finset.inter_self] at h
        exact hAL h

theorem count (V : Finset (Finset (Fin 7))) (hL : ∀ w, line w ∈ V)
    (hstep : ∀ w, ∃ A B : Finset (Fin 7), (A ∈ V ∨ A.card ≤ 1) ∧ (B ∈ V ∨ B.card ≤ 1) ∧
      A ≠ line w ∧ B ≠ line w ∧ (A ∪ B = line w ∨ A ∩ B = line w)) :
    14 ≤ V.card := by
  classical
  have hcl : ∀ w, (∃ P ∈ V, P.card = 2 ∧ P ⊆ line w) ∨ (∃ Q ∈ V, Q.card = 4 ∧ line w ⊆ Q) ∨
      (∃ A ∈ V, ∃ B ∈ V, A ≠ B ∧ A.card = 5 ∧ B.card = 5 ∧ line w ⊆ A ∧ line w ⊆ B) := by
    intro w
    obtain ⟨A, B, hA, hB, hAL, hBL, h⟩ := hstep w
    exact classify V (line w) A B (line_card w) hA hB hAL hBL h
  set S1 := Finset.univ.filter (fun w : Fin 7 => ∃ P ∈ V, P.card = 2 ∧ P ⊆ line w)
  set S4 := Finset.univ.filter (fun w : Fin 7 => ∃ Q ∈ V, Q.card = 4 ∧ line w ⊆ Q)
  set S5 := Finset.univ.filter (fun w : Fin 7 =>
    ∃ A ∈ V, ∃ B ∈ V, A ≠ B ∧ A.card = 5 ∧ B.card = 5 ∧ line w ⊆ A ∧ line w ⊆ B)
  set V2 := V.filter (fun s => s.card = 2)
  set V3 := V.filter (fun s => s.card = 3)
  set V4 := V.filter (fun s => s.card = 4)
  set V5 := V.filter (fun s => s.card = 5)
  have hcover : (Finset.univ : Finset (Fin 7)) ⊆ S1 ∪ S4 ∪ S5 := by
    intro w _
    rcases hcl w with h | h | h
    · simp [S1, h]
    · simp [S4, h]
    · simp [S5, h]
  have h7 : 7 ≤ S1.card + S4.card + S5.card := by
    have h0 := Finset.card_le_card hcover
    rw [Finset.card_univ, Fintype.card_fin] at h0
    have h2 := Finset.card_union_le (S1 ∪ S4) S5
    have h3 := Finset.card_union_le S1 S4
    omega
  have h1 : S1.card ≤ V2.card := by
    apply Finset.card_le_card_of_forall_subsingleton (fun w P => P ⊆ line w)
    · intro w hw
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨P, hP, hP2, hPs⟩ := hw
      exact ⟨P, by simp [V2, hP, hP2], hPs⟩
    · intro P hP a ha b hb
      simp only [V2, Finset.mem_filter] at hP
      by_contra hab
      have := Finset.card_le_card (Finset.subset_inter ha.2 hb.2)
      have := line_inter a b hab
      omega
  have h4 : S4.card ≤ V4.card := by
    apply Finset.card_le_card_of_forall_subsingleton (fun w Q => line w ⊆ Q)
    · intro w hw
      simp only [S4, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨Q, hQ, hQ4, hQs⟩ := hw
      exact ⟨Q, by simp [V4, hQ, hQ4], hQs⟩
    · intro Q hQ a ha b hb
      simp only [V4, Finset.mem_filter] at hQ
      by_contra hab
      have := Finset.card_le_card (Finset.union_subset ha.2 hb.2)
      have := line_union2 a b hab
      omega
  have h5 : S5.card * 2 ≤ V5.card * 2 := by
    apply Finset.card_mul_le_card_mul (fun w F => line w ⊆ F)
    · intro w hw
      simp only [S5, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨A, hA, B, hB, hAB, hA5, hB5, hAs, hBs⟩ := hw
      have : 1 < (Finset.bipartiteAbove (fun w F => line w ⊆ F) V5 w).card := by
        rw [Finset.one_lt_card]
        exact ⟨A, by simp [Finset.bipartiteAbove, V5, hA, hA5, hAs],
          B, by simp [Finset.bipartiteAbove, V5, hB, hB5, hBs], hAB⟩
      omega
    · intro F hF
      simp only [V5, Finset.mem_filter] at hF
      by_contra hlt
      rw [not_le, Finset.two_lt_card] at hlt
      obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hlt
      simp only [Finset.bipartiteBelow, Finset.mem_filter] at ha hb hc
      have hsub : line a ∪ line b ∪ line c ⊆ F :=
        Finset.union_subset (Finset.union_subset ha.2 hb.2) hc.2
      have := Finset.card_le_card hsub
      have := line_union3 a b c hab hac hbc
      omega
  have h3 : 7 ≤ V3.card := by
    have hsub3 : Finset.univ.image line ⊆ V3 := by
      intro s hs
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs
      obtain ⟨w, rfl⟩ := hs
      simp [V3, hL w, line_card w]
    have := Finset.card_le_card hsub3
    rw [line_image_card] at this
    exact this
  have d23 : Disjoint V2 V3 := Finset.disjoint_filter.2 (fun s _ h2 h3 => by omega)
  have d234 : Disjoint (V2.disjUnion V3 d23) V4 := by
    rw [Finset.disjUnion_eq_union, Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_filter.2 (fun s _ h2 h3 => by omega),
      Finset.disjoint_filter.2 (fun s _ h2 h3 => by omega)⟩
  have d2345 : Disjoint ((V2.disjUnion V3 d23).disjUnion V4 d234) V5 := by
    rw [Finset.disjUnion_eq_union, Finset.disjUnion_eq_union, Finset.disjoint_union_left,
      Finset.disjoint_union_left]
    exact ⟨⟨Finset.disjoint_filter.2 (fun s _ h2 h3 => by omega),
      Finset.disjoint_filter.2 (fun s _ h2 h3 => by omega)⟩,
      Finset.disjoint_filter.2 (fun s _ h2 h3 => by omega)⟩
  have hsub : ((V2.disjUnion V3 d23).disjUnion V4 d234).disjUnion V5 d2345 ⊆ V := by
    intro s hs
    simp only [Finset.mem_disjUnion, V2, V3, V4, V5, Finset.mem_filter] at hs
    rcases hs with ((h | h) | h) | h <;> exact h.1
  have hV := Finset.card_le_card hsub
  rw [Finset.card_disjUnion, Finset.card_disjUnion, Finset.card_disjUnion] at hV
  omega

end PEqualNP.Outside.L_meta_666_aux

open PEqualNP.Outside.L_meta_666_aux in
theorem PEqualNP.Outside.L_meta_666 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) → 14 ≤ gates.length := by
  intro gates out hg hc
  classical
  -- the unit inputs
  let e : Fin 7 → Fin 7 → Bool := fun i j => decide (j = i)
  have hlight : ∀ i : Fin 7, ∀ a b : Fin 7, e i a = true → e i b = true → a = b := by
    intro i a b ha hb
    simp only [e, decide_eq_true_eq] at ha hb
    rw [ha, hb]
  let X : Fin 7 → List Bool := fun i => List.ofFn (e i)
  have hX : ∀ i, (X i).length = 7 := by intro i; simp [X]
  let FW : Fin 7 → List Bool := fun i => gates.foldl stepW (X i)
  let val : ℕ → Finset (Fin 7) := fun k => Finset.univ.filter (fun i => (FW i).getD k false = true)
  -- outputs
  have hout : ∀ w, val (out w) = line w := by
    intro w
    ext i
    have h := hc w (e i) (hlight i)
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, wires_eq] at h
    simp only [val, FW, X, Finset.mem_filter, Finset.mem_univ, true_and, h, line]
    simp [e]
  -- input wires
  have hin : ∀ k (hk : k < 7), val k = {⟨k, hk⟩} := by
    intro k hk
    ext i
    simp only [val, FW, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [input_val gates (X i) k (by rw [hX]; exact hk)]
    simp only [X, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [e, hk, Fin.ext_iff, eq_comm]
  -- wires past the end
  have hpast : ∀ k, 7 + gates.length ≤ k → val k = ∅ := by
    intro k hk
    ext i
    simp only [val, FW, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    rw [out_val gates (X i) k (by rw [hX]; exact hk)]
    simp
  let V : Finset (Finset (Fin 7)) := (Finset.range gates.length).image (fun m => val (7 + m))
  have hVcard : V.card ≤ gates.length := by
    have := Finset.card_image_le (s := Finset.range gates.length) (f := fun m => val (7 + m))
    simpa [V] using this
  -- every wire before the end is a gate value, an input or nothing
  have havail : ∀ j, val j ∈ V ∨ (val j).card ≤ 1 := by
    intro j
    rcases lt_or_ge j 7 with hj | hj
    · right
      rw [hin j hj]
      simp
    · rcases lt_or_ge j (7 + gates.length) with hj2 | hj2
      · left
        simp only [V, Finset.mem_image, Finset.mem_range]
        exact ⟨j - 7, by omega, by congr 1; omega⟩
      · right
        rw [hpast j hj2]
        simp
  have key : ∀ w, line w ∈ V ∧ ∃ A B : Finset (Fin 7), (A ∈ V ∨ A.card ≤ 1) ∧
      (B ∈ V ∨ B.card ≤ 1) ∧ A ≠ line w ∧ B ≠ line w ∧
      (A ∪ B = line w ∨ A ∩ B = line w) := by
    intro w
    have hex : ∃ k, val k = line w := ⟨out w, hout w⟩
    let k0 := Nat.find hex
    have hk0 : val k0 = line w := Nat.find_spec hex
    have hmin : ∀ k < k0, val k ≠ line w := fun k hk => Nat.find_min hex hk
    have hl3 := line_card w
    have hk7 : 7 ≤ k0 := by
      by_contra h
      rw [not_le] at h
      have := hin k0 h
      rw [hk0] at this
      rw [this] at hl3
      simp at hl3
    have hklt : k0 < 7 + gates.length := by
      by_contra h
      rw [not_lt] at h
      have := hpast k0 h
      rw [hk0] at this
      rw [this] at hl3
      simp at hl3
    set m := k0 - 7 with hm
    have hmlt : m < gates.length := by omega
    have hkm : k0 = 7 + m := by omega
    have hgm := hg (gates[m]) (List.getElem_mem hmlt)
    -- the value of the gate through the values of the wires it reads
    let rv : ℕ → Finset (Fin 7) := fun j => if j < k0 then val j else ∅
    have hrv : ∀ i j, (i ∈ rv j) ↔
        ((if j < 7 + m then (FW i).getD j false else false) = true) := by
      intro i j
      simp only [rv, ← hkm]
      split_ifs with h
      · simp [val]
      · simp
    have hgate : ∀ i, (i ∈ val k0) ↔ ((gates[m]).op.eval ((gates[m]).inputs.map fun j =>
        if j < 7 + m then (FW i).getD j false else false) = true) := by
      intro i
      have := gate_val gates (X i) m hmlt
      rw [hX] at this
      simp only [val, Finset.mem_filter, Finset.mem_univ, true_and, hkm]
      rw [this]
    have hrvne : ∀ j, rv j ≠ line w := by
      intro j
      simp only [rv]
      split_ifs with h
      · exact hmin j h
      · intro h2
        rw [← h2] at hl3
        simp at hl3
    have hrvav : ∀ j, rv j ∈ V ∨ (rv j).card ≤ 1 := by
      intro j
      simp only [rv]
      split_ifs
      · exact havail j
      · right; simp
    refine ⟨?_, ?_⟩
    · rw [← hk0, hkm]
      simp only [V, Finset.mem_image, Finset.mem_range]
      exact ⟨m, hmlt, rfl⟩
    · obtain ⟨hop, hlen⟩ := hgm
      match hin' : (gates[m]).inputs with
      | [] =>
        exfalso
        rcases hop with hop | hop
        · have : val k0 = Finset.univ := by
            ext i
            rw [hgate i, hin', hop]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          rw [hk0] at this
          rw [this] at hl3
          simp at hl3
        · have : val k0 = ∅ := by
            ext i
            rw [hgate i, hin', hop]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          rw [hk0] at this
          rw [this] at hl3
          simp at hl3
      | [a] =>
        exfalso
        have : val k0 = rv a := by
          ext i
          rw [hgate i, hin', hrv]
          rcases hop with hop | hop <;> simp [hop, PEqualNP.CircuitLowerBounds.GateOp.eval]
        exact hrvne a (this ▸ hk0)
      | [a, b] =>
        refine ⟨rv a, rv b, hrvav a, hrvav b, hrvne a, hrvne b, ?_⟩
        rcases hop with hop | hop
        · right
          rw [← hk0]
          ext i
          rw [Finset.mem_inter, hgate i, hin', hrv, hrv]
          simp [hop, PEqualNP.CircuitLowerBounds.GateOp.eval]
        · left
          rw [← hk0]
          ext i
          rw [Finset.mem_union, hgate i, hin', hrv, hrv]
          simp [hop, PEqualNP.CircuitLowerBounds.GateOp.eval]
      | _ :: _ :: _ :: _ =>
        exfalso
        rw [hin'] at hlen
        simp at hlen
  have h14 := count V (fun w => (key w).1) (fun w => (key w).2)
  omega
