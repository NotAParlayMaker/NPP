import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3017.Retain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

private def slots (S : Finset ℕ) (k : ℕ) : List ℕ :=
  (List.range k).filter fun j => decide (j ∉ S)

private def rank (S : Finset ℕ) (k : ℕ) : ℕ := (slots S k).length

private lemma slots_succ (S : Finset ℕ) (k : ℕ) :
    slots S (k + 1) = slots S k ++ (if k ∈ S then [] else [k]) := by
  by_cases h : k ∈ S <;> simp [slots, List.range_succ, h]

private lemma rank_succ (S : Finset ℕ) (k : ℕ) :
    rank S (k + 1) = rank S k + (if k ∈ S then 0 else 1) := by
  by_cases h : k ∈ S <;> simp [rank, slots_succ, h]

private lemma rank_mono (S : Finset ℕ) : Monotone (rank S) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [rank_succ]
  omega

private lemma rank_lt {S : Finset ℕ} {j k : ℕ} (h : j < k) (hj : j ∉ S) :
    rank S j < rank S k := by
  have hle := rank_mono S (show j + 1 ≤ k by omega)
  rw [rank_succ, ite_eq_right hj] at hle
  omega

private lemma rank_add_card (S : Finset ℕ) (k : ℕ) :
    rank S k + (S ∩ Finset.range k).card = k := by
  induction k with
  | zero => simp [rank, slots]
  | succ k ih =>
    rw [Finset.range_add_one, rank_succ]
    by_cases hk : k ∈ S
    · have he : S ∩ insert k (Finset.range k) = insert k (S ∩ Finset.range k) := by
        ext v
        by_cases hv : v = k <;> simp [hv, hk]
      rw [ite_eq_left hk, he, Finset.card_insert_of_notMem (by simp)]
      omega
    · have he : S ∩ insert k (Finset.range k) = S ∩ Finset.range k := by
        ext v
        by_cases hv : v = k <;> simp [hv, hk]
      rw [ite_eq_right hk, he]
      omega

def rename (n : ℕ) (S : Finset ℕ) (i : ℕ) : ℕ :=
  if i < n then i else n + rank S (i - n)

lemma rename_lt {n k : ℕ} {S : Finset ℕ} {i : ℕ} (hi : i < n + k)
    (hKeep : i < n ∨ i - n ∉ S) : rename n S i < n + rank S k := by
  by_cases h : i < n
  · simp only [rename, ite_eq_left h]
    omega
  · have hz := rank_lt (show i - n < k by omega) (hKeep.resolve_left h)
    simp only [rename, ite_eq_right h]
    omega

lemma rename_mono (n : ℕ) (S : Finset ℕ) : Monotone (rename n S) := by
  intro i j hij
  by_cases hi : i < n <;> by_cases hj : j < n
  · simpa [rename, hi, hj] using hij
  · simp only [rename, ite_eq_left hi, ite_eq_right hj]
    omega
  · omega
  · simp only [rename, ite_eq_right hi, ite_eq_right hj]
    exact Nat.add_le_add_left (rank_mono S (Nat.sub_le_sub_right hij n)) n

lemma rename_strict {n : ℕ} {S : Finset ℕ} {i j : ℕ} (hij : i < j)
    (hiKeep : i < n ∨ i - n ∉ S) : rename n S i < rename n S j := by
  by_cases hi : i < n <;> by_cases hj : j < n
  · simpa [rename, hi, hj] using hij
  · simp only [rename, ite_eq_left hi, ite_eq_right hj]
    omega
  · omega
  · have h := rank_lt (show i - n < j - n by omega) (hiKeep.resolve_left hi)
    simp only [rename, ite_eq_right hi, ite_eq_right hj]
    omega

private def translate (n : ℕ) (S : Finset ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rename n S)⟩

private def selected (n : ℕ) (C : Circuit) (S : Finset ℕ) (k : ℕ) : List Gate :=
  (slots S k).map fun j => translate n S (gateAt C j)

private lemma selected_length (n : ℕ) (C : Circuit) (S : Finset ℕ) (k : ℕ) :
    (selected n C S k).length = rank S k := by simp [selected, rank]

private lemma selected_succ (n : ℕ) (C : Circuit) (S : Finset ℕ) (k : ℕ) :
    selected n C S (k + 1) = selected n C S k ++
      (if k ∈ S then [] else [translate n S (gateAt C k)]) := by
  by_cases h : k ∈ S <;> simp [selected, slots_succ, h]

private lemma selected_origin (n : ℕ) (C : Circuit) (S : Finset ℕ) (k : ℕ) :
    ∀ j < rank S k, ∃ i < k, i ∉ S ∧ rank S i = j ∧
      (selected n C S k).getD j ⟨.or, []⟩ = translate n S (gateAt C i) := by
  induction k with
  | zero => simp [rank, slots]
  | succ k ih =>
    intro j hj
    rw [rank_succ] at hj
    rw [selected_succ]
    by_cases hS : k ∈ S
    · simp only [ite_eq_left hS, Nat.add_zero] at hj
      simp only [ite_eq_left hS, List.append_nil]
      obtain ⟨i, hi, hki, hr, hv⟩ := ih j hj
      exact ⟨i, by omega, hki, hr, hv⟩
    · simp only [ite_eq_right hS] at hj ⊢
      by_cases hlt : j < rank S k
      · obtain ⟨i, hi, hki, hr, hv⟩ := ih j hlt
        rw [List.getD_append _ _ _ _ (by rwa [selected_length])]
        exact ⟨i, by omega, hki, hr, hv⟩
      · have hjk : j = rank S k := by omega
        subst j
        refine ⟨k, by omega, hS, rfl, ?_⟩
        rw [List.getD_append_right _ _ _ _ (by simp [selected_length])]
        simp [selected_length]

private def run (gates : List Gate) (wires : List Bool) : List Bool :=
  gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wires

private lemma run_length (gates : List Gate) (wires : List Bool) :
    (run gates wires).length = wires.length + gates.length := by
  induction gates generalizing wires with
  | nil => simp [run]
  | cons g rest ih =>
    change (run rest (wires ++ [_])).length = _
    rw [ih]
    simp
    omega

private lemma run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run, List.foldl_append]

private lemma at_gate_get (C : Circuit) {k : ℕ} (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk

private lemma prefix_eval (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : IsAO2 n C)
    (hKeep : ∀ k < C.size, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S)
    (x : Fin n → Bool) : ∀ k ≤ C.size, ∀ i < n + k, (i < n ∨ i - n ∉ S) →
      (run (selected n C S k) (List.ofFn x)).getD (rename n S i) false =
        (run (C.gates.take k) (List.ofFn x)).getD i false := by
  intro k
  induction k with
  | zero =>
    intro _ i hi _
    have h : i < n := by omega
    simp [selected, slots, rename, h]
  | succ k ih =>
    intro hk i hi hki
    have hk' : k < C.gates.length := by change k + 1 ≤ C.gates.length at hk; omega
    have hkSize : k < C.size := hk'
    have hTake : C.gates.take (k + 1) = C.gates.take k ++ [gateAt C k] := by
      rw [List.take_succ_eq_append_getElem hk', at_gate_get C hk']
    have hOrigLen : (run (C.gates.take k) (List.ofFn x)).length = n + k := by
      rw [run_length, List.length_ofFn, List.length_take, Nat.min_eq_left hk'.le]
    have hNewLen : (run (selected n C S k) (List.ofFn x)).length = n + rank S k := by
      simp [run_length, selected_length]
    rw [hTake, run_snoc, selected_succ]
    by_cases hiOld : i < n + k
    · rw [List.getD_append _ _ _ _ (by rwa [hOrigLen])]
      by_cases hS : k ∈ S
      · simp only [ite_eq_left hS, List.append_nil]
        exact ih hkSize.le i hiOld hki
      · simp only [ite_eq_right hS]
        rw [run_snoc, List.getD_append _ _ _ _ (by rw [hNewLen]; exact rename_lt hiOld hki)]
        exact ih hkSize.le i hiOld hki
    · have hiEq : i = n + k := by omega
      subst i
      have hS : k ∉ S := by
        have ht := hki.resolve_left (by omega)
        simpa using ht
      have hRen : rename n S (n + k) = n + rank S k := by simp [rename]
      simp only [ite_eq_right hS]
      rw [hRen, run_snoc, List.getD_append_right _ _ _ _ (by rw [hNewLen]),
        List.getD_append_right _ _ _ _ (by rw [hOrigLen]), hOrigLen, hNewLen]
      simp only [Nat.sub_self, List.getD_cons_zero, translate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih hkSize.le a (hAO.2.1 k hk' a ha) (hKeep k hkSize hS a ha)

theorem retain_gates (n : ℕ) (C : Circuit) (S : Finset ℕ) (hAO : IsAO2 n C)
    (hS : S ⊆ Finset.range C.size)
    (hKeep : ∀ k < C.size, k ∉ S → ∀ i ∈ (gateAt C k).inputs, i < n ∨ i - n ∉ S) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + S.card = C.size ∧ ∃ r : ℕ → ℕ,
      ∀ i < n + C.size, (i < n ∨ i - n ∉ S) → r i < n + D.size ∧
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (r i) false =
          (C.wires (List.ofFn x)).getD i false := by
  let D : Circuit := ⟨selected n C S C.size, 0⟩
  have hlen : D.size = rank S C.size := selected_length n C S C.size
  have hmem (g : Gate) (hg : g ∈ D.gates) :
      ∃ i < C.size, g = translate n S (gateAt C i) := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (show g ∈ selected n C S C.size from hg)
    exact ⟨i, (List.mem_range.mp (List.mem_filter.mp hi).1), rfl⟩
  have atMem (i : ℕ) (hi : i < C.size) : gateAt C i ∈ C.gates := by
    rw [at_gate_get C hi]
    exact List.getElem_mem _
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, rename n S, ?_⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := hmem g hg
    simpa [translate] using hAO.1 _ (atMem i hi)
  · intro j hj i hi
    have hj' : j < rank S C.size := by rwa [← hlen]
    obtain ⟨k, hk, hks, hRank, hg⟩ := selected_origin n C S C.size j hj'
    change i ∈ ((selected n C S C.size).getD j ⟨.or, []⟩).inputs at hi
    rw [hg] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    rw [← hRank]
    exact rename_lt (hAO.2.1 k hk a ha) (hKeep k hk hks a ha)
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := hmem g hg
    simpa [translate] using hAO.2.2 _ (atMem i hi)
  · have hCard := congrArg Finset.card (Finset.inter_eq_left.mpr hS)
    rw [hlen, ← hCard]
    exact rank_add_card S C.size
  · intro i hi hiKeep
    refine ⟨by rw [hlen]; exact rename_lt hi hiKeep, ?_⟩
    intro x
    have hv := prefix_eval n C S hAO hKeep x C.size le_rfl i hi hiKeep
    change (run D.gates (List.ofFn x)).getD (rename n S i) false =
      (run C.gates (List.ofFn x)).getD i false
    simpa only [D, Circuit.size, List.take_length] using hv

end PEqualNP.Outside.L_meta_3017.Retain

namespace PEqualNP.Outside.L_meta_3017.Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

def redirect {n : ℕ} (c : ℕ) (s : Fin n) (w : ℕ) : ℕ :=
  if w = n + c then s.val else w

def replace {n : ℕ} (C : Circuit) (c : ℕ) (s : Fin n) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (redirect c s)⟩), C.output⟩

theorem replace_size {n : ℕ} (C : Circuit) (c : ℕ) (s : Fin n) :
    (replace C c s).size = C.size := by simp [replace, Circuit.size]

private lemma replace_at {n : ℕ} (C : Circuit) (c : ℕ) (s : Fin n) {k : ℕ}
    (hk : k < C.gates.length) :
    gateAt (replace C c s) k = ⟨(gateAt C k).op, (gateAt C k).inputs.map (redirect c s)⟩ := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ (by simpa [replace] using hk), List.getD_eq_getElem _ _ hk]
  simp [replace]

theorem replace_AO2 {n : ℕ} {C : Circuit} (c : ℕ) (s : Fin n) (hAO : IsAO2 n C) :
    IsAO2 n (replace C c s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact hAO.1 a ha
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa [replace] using hk
    rw [replace_at C c s hkC] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hlt := hAO.2.1 k hkC i hi
    by_cases h : i = n + c
    · simp only [redirect, ite_eq_left h]
      have hs := s.isLt
      omega
    · simpa only [redirect, ite_eq_right h] using hlt
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    simpa using hAO.2.2 a ha

private lemma cone_subset (n : ℕ) (C : Circuit) {c : ℕ} (hc : c < C.gates.length) :
    PEqualNP.Core.coneSet n C c ⊆ Finset.range C.size := by
  intro j hj
  apply Finset.mem_range.mpr
  rcases Finset.mem_insert.mp hj with rfl | h
  · exact hc
  · exact Finset.mem_range.mp (Finset.mem_filter.mp h).1

theorem prune (n : ℕ) (C C0 : Circuit) (c : ℕ) (s : Fin n)
    (hAO : IsAO2 n C) (hc : c < C.gates.length)
    (hPrivate : ∀ j < C.gates.length, InCone n C j c → ∀ k < C.gates.length,
      n + j ∈ (gateAt C k).inputs → k = c ∨ InCone n C k c)
    (hC0 : C0 = replace C c s)
    (hOutBound : C.output < n + C.size)
    (hOutKeep : C.output < n ∨ C.output - n ∉ PEqualNP.Core.coneSet n C c) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + (PEqualNP.Core.coneSet n C c).card = C.size ∧
      D.output < n + D.size ∧ circuitFun n D = circuitFun n C0 := by
  subst C0
  let S := PEqualNP.Core.coneSet n C c
  have hS : S ⊆ Finset.range (replace C c s).size := by
    rw [replace_size]
    exact cone_subset n C hc
  have hKeep : ∀ k < (replace C c s).size, k ∉ S →
      ∀ w ∈ (gateAt (replace C c s) k).inputs, w < n ∨ w - n ∉ S := by
    intro k hk hkS w hw
    have hkC : k < C.gates.length := by
      change k < C.size
      simpa only [replace_size] using hk
    rw [replace_at C c s hkC] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    by_cases hiEq : i = n + c
    · left
      simpa only [redirect, ite_eq_left hiEq] using s.isLt
    · rw [redirect, ite_eq_right hiEq]
      by_cases hiRaw : i < n
      · exact Or.inl hiRaw
      · right
        intro hiS
        have hiBefore := hAO.2.1 k hkC i hi
        have hj : i - n < C.gates.length := by omega
        rcases Finset.mem_insert.mp hiS with hEq | hCone
        · omega
        · have hIn := (Finset.mem_filter.mp hCone).2
          have hRd : n + (i - n) ∈ (gateAt C k).inputs := by
            rwa [show n + (i - n) = i by omega]
          rcases hPrivate (i - n) hj hIn k hkC hRd with rfl | hKC
          · exact hkS (Finset.mem_insert_self _ _)
          · exact hkS (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr hkC, hKC⟩))
  obtain ⟨D0, hDA, hDsize, r, hr⟩ := PEqualNP.Outside.L_meta_3017.Retain.retain_gates
    n (replace C c s) S (replace_AO2 c s hAO) hS hKeep
  have hBound : C.output < n + (replace C c s).size := by simpa [replace_size] using hOutBound
  obtain ⟨hOut, hEval⟩ := hr C.output hBound hOutKeep
  let D : Circuit := { D0 with output := r C.output }
  refine ⟨D, hDA, ?_, hOut, ?_⟩
  · change D0.size + S.card = C.size
    simpa [replace_size] using hDsize
  · funext x
    exact hEval x

end PEqualNP.Outside.L_meta_3017.Prune

namespace PEqualNP.Outside.L_meta_3017.Cone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount PEqualNP.TopForm

-- Circuit evaluation and strict cone lemmas adapted from L-meta-1499.

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩


theorem memConeIff (n : ℕ) (C : Circuit) (c j : ℕ) :
    j ∈ PEqualNP.Core.coneSet n C c ↔ j = c ∨ InCone n C j c := by
  simp only [PEqualNP.Core.coneSet, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨(inCone_lt n C j c h).1.trans (inCone_lt n C j c h).2, h⟩

theorem coneClosed (n : ℕ) (C : Circuit) (c j w : ℕ) (hRB : ReadsBack n C)
    (hc : c < C.gates.length) (hj : j ∈ PEqualNP.Core.coneSet n C c)
    (hw : w ∈ (gateAt C j).inputs) (hle : n ≤ w) :
    w - n ∈ PEqualNP.Core.coneSet n C c := by
  rcases (memConeIff n C c j).1 hj with hJ | hJ
  · subst j
    have hlt := hRB c hc w hw
    apply (memConeIff n C c _).2
    right
    apply (inCone_iff n C _ c).2
    refine ⟨hc, w - n, by omega, ?_, Or.inl rfl⟩
    rwa [Nat.add_sub_of_le hle]
  · have hjlt := (inCone_lt n C j c hJ).1.trans hc
    have hlt := hRB j hjlt w hw
    have hStep : InCone n C (w - n) j := by
      apply (inCone_iff n C _ j).2
      refine ⟨hjlt, w - n, by omega, ?_, Or.inl rfl⟩
      rwa [Nat.add_sub_of_le hle]
    exact (memConeIff n C c _).2 (Or.inr (inCone_trans n C _ j hStep c hJ))

private theorem gateAtMem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

private theorem aobOfAO {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : AOB n C := by
  intro j hj
  exact ⟨hAO.1 _ (gateAtMem hj), hAO.2.1 j hj⟩

private theorem zeroGate (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ j < C.gates.length, gateVal n C j (fun _ => false) = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    change wv n C (fun _ => false) (n + j) = false
    rw [wv_rec n C _ (aobOfAO hAO) j hj]
    have hMap : (gateAt C j).inputs.map (wv n C (fun _ => false)) =
        (gateAt C j).inputs.map (fun _ => false) := by
      apply List.map_congr_left
      intro w hw
      by_cases hraw : w < n
      · exact wv_input n C (fun _ => false) w hraw
      · have hlt := hAO.2.1 j hj w hw
        have heq : w = n + (w - n) := by omega
        conv_lhs => rw [heq]
        exact ih (w - n) (by omega) (by omega)
    rw [hMap, List.map_const', hAO.2.2 _ (gateAtMem hj)]
    rcases hAO.1 _ (gateAtMem hj) with h | h <;> simp [h, GateOp.eval]

private theorem coneAgreement (n : ℕ) (C : Circuit) (c : ℕ) (hAO : IsAO2 n C)
    (hc : c < C.gates.length) (x y : Fin n → Bool)
    (agree : ∀ j ∈ PEqualNP.Core.coneSet n C c, ∀ w ∈ (gateAt C j).inputs,
      ∀ h : w < n, x ⟨w, h⟩ = y ⟨w, h⟩) :
    gateVal n C c x = gateVal n C c y := by
  have all : ∀ j ∈ PEqualNP.Core.coneSet n C c, gateVal n C j x = gateVal n C j y := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hjlt : j < C.gates.length := by
        rcases (memConeIff n C c j).1 hj with h | h
        · simpa [h] using hc
        · exact (inCone_lt n C j c h).1.trans hc
      change wv n C x (n + j) = wv n C y (n + j)
      rw [wv_rec n C x (aobOfAO hAO) j hjlt, wv_rec n C y (aobOfAO hAO) j hjlt]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_cases hraw : w < n
      · rw [wv_input n C x w hraw, wv_input n C y w hraw]
        exact agree j hj w hw hraw
      · have hlt := hAO.2.1 j hjlt w hw
        have hk := coneClosed n C c j w hAO.2.1 hc hj hw (by omega)
        have heq : w = n + (w - n) := by omega
        rw [heq]
        exact ih (w - n) (by omega) hk
  exact all c ((memConeIff n C c c).2 (Or.inl rfl))

private theorem inputReader (n : ℕ) (C : Circuit) (c : ℕ) (hAO : IsAO2 n C)
    (hc : c < C.gates.length) (p : Fin n) (x y : Fin n → Bool)
    (agree : ∀ q : Fin n, q ≠ p → x q = y q) (different : gateVal n C c x ≠ gateVal n C c y) :
    ∃ j ∈ PEqualNP.Core.coneSet n C c, p.val ∈ (gateAt C j).inputs := by
  by_contra missing
  apply different
  apply coneAgreement n C c hAO hc x y
  intro j hj w hw hraw
  apply agree
  intro heq
  have hVal : w = p.val := congrArg Fin.val heq
  exact missing ⟨j, hj, hVal ▸ hw⟩

theorem count (n : ℕ) (C : Circuit) (c : ℕ) (s : Fin n) (V : Finset (Fin n))
    (hAO : IsAO2 n C) (hc : c < C.gates.length)
    (hsingle : singletonSet n C c = {s}) (hs : s ∉ V)
    (hlost : ∀ y ∈ V, ∃ z : Fin n, z ≠ s ∧ gateVal n C c (pairInput z y) = true) :
    V.card ≤ (PEqualNP.Core.coneSet n C c).card := by
  let K := PEqualNP.Core.coneSet n C c
  let reads := K.biUnion (fun j => (gateAt C j).inputs.toFinset)
  let U := (insert s V).image Fin.val
  let internal := (K.erase c).image (fun j => n + j)
  have hroot : c ∈ K := (memConeIff n C c c).2 (Or.inl rfl)
  have hSingle (p : Fin n) : gateVal n C c (unitInput p) = true ↔ p = s := by
    have h : p ∈ singletonSet n C c ↔ gateVal n C c (unitInput p) = true := by simp [singletonSet]
    rw [hsingle, Finset.mem_singleton] at h
    exact h.symm
  have hInputs (p : Fin n) (hp : p ∈ insert s V) : p.val ∈ reads := by
    have hReader : ∃ j ∈ K, p.val ∈ (gateAt C j).inputs := by
      rcases Finset.mem_insert.mp hp with heq | hp
      · subst p
        apply inputReader n C c hAO hc s (unitInput s) (fun _ => false)
        · intro q hq; simp [unitInput, hq]
        · rw [(hSingle s).2 rfl, zeroGate n C hAO c hc]
          decide
      · obtain ⟨z, hzs, hpair⟩ := hlost p hp
        apply inputReader n C c hAO hc p (pairInput z p) (unitInput z)
        · intro q hq; simp [pairInput, unitInput, hq]
        · have hunit : gateVal n C c (unitInput z) = false :=
            Bool.eq_false_of_not_eq_true (fun h => hzs ((hSingle z).1 h))
          rw [hpair, hunit]
          decide
    obtain ⟨j, hj, hr⟩ := hReader
    exact Finset.mem_biUnion.2 ⟨j, hj, List.mem_toFinset.2 hr⟩
  have hUnion : U ∪ internal ⊆ reads := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      exact hInputs p hp
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hne, hjK⟩ := Finset.mem_erase.mp hj
      have hCone := ((memConeIff n C c j).1 hjK).resolve_left hne
      obtain ⟨r, _, _, hread, hr⟩ := inCone_reader n C j c hCone
      exact Finset.mem_biUnion.2 ⟨r, (memConeIff n C c r).2 hr, List.mem_toFinset.2 hread⟩
  have hDisjoint : Disjoint U internal := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hj
    have hlt := p.isLt
    omega
  have hU : U.card = V.card + 1 := by
    change ((insert s V).image Fin.val).card = _
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_insert_of_notMem hs]
  have hInt : internal.card = K.card - 1 := by
    change ((K.erase c).image (fun j => n + j)).card = _
    rw [Finset.card_image_of_injective _ (fun _ _ => Nat.add_left_cancel), Finset.card_erase_of_mem hroot]
  have hReads : reads.card ≤ K.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro j hj
    have hjlt : j < C.gates.length := by
      rcases (memConeIff n C c j).1 hj with h | h
      · simpa [h] using hc
      · exact (inCone_lt n C j c h).1.trans hc
    exact (List.toFinset_card_le _).trans (hAO.2.2 _ (gateAtMem hjlt)).le
  have hBoth := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hDisjoint, hU, hInt] at hBoth
  change V.card ≤ K.card
  have hKpos := Finset.card_pos.2 ⟨c, hroot⟩
  omega

end PEqualNP.Outside.L_meta_3017.Cone

namespace PEqualNP.Outside.L_meta_3017.Lost

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.SplitCount
open Finset
open Relation (ReflTransGen)

-- The wire and tree lemmas are adapted from L_meta_540 and L_meta_2774.

def stW (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def wV (n : ℕ) (C : Circuit) (x : Fin n->Bool) (w : ℕ) : Bool :=
 (C.wires (List.ofFn x)).getD w false
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
 C.wires x=C.gates.foldl stW x:=rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
 (gs.foldl stW w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons,ih]
  simp [stW]
  omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
 (gs.foldl stW w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  have hlt : i < (stW w g).length:=by simp [stW];omega
  rw [ih (stW w g) hlt]
  simp [stW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length<=i) :
 w.getD i false=false:=by
 simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]
lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n->Bool) :
 (C.wires (List.ofFn x)).length=n+C.gates.length:=by
 rw [wires_eq_foldl,foldl_stepWire_length,List.length_ofFn]
lemma wvO (n : ℕ) (C : Circuit) (x : Fin n->Bool) :
 wV n C x C.output=circuitFun n C x:=rfl
lemma wvI (n : ℕ) (C : Circuit) (x : Fin n->Bool) (i : Fin n) :
 wV n C x i.val=x i:=by
 unfold wV
 rw [wires_eq_foldl,foldl_stepWire_getD_lt C.gates (List.ofFn x) i.val (by simp)]
 simp [List.getD_eq_getElem?_getD]
lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n->Bool) (w : ℕ)
 (hw : n+C.gates.length<=w) : wV n C x w=false:=by
 unfold wV
 exact getD_ge_length _ _ (by rw [wires_length];exact hw)
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
 ∃ (pre post : List Gate) (gj : Gate),
  gs=pre ++ gj :: post/\pre.length=j/\gs[j]'hj=gj:=by
 refine ⟨gs.take j,gs.drop (j+1),gs[j]'hj,?_,by simp;omega,rfl⟩
 rw [List.cons_getElem_drop_succ,List.take_append_drop]
lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
 gateAt C j=C.gates[j]'hj:=by
 simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n->Bool) (j : ℕ)
 (hj : j < C.gates.length) :
 wV n C x (n+j) =
  (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
   if i < n+j then wV n C x i else false):=by
 obtain ⟨pre,post,gj,hgs,hpre_len,hget⟩:=split_gates C.gates j hj
 have hgj : gateAt C j=gj:=by rw [gateAt_eq_getElem C j hj,hget]
 rw [hgj]
 let w0:=pre.foldl stW (List.ofFn x)
 have hW0L : w0.length=n+j:=by
  simp [w0,foldl_stepWire_length,hpre_len]
 have hCj : wV n C x (n+j)=gj.op.eval (gj.inputs.map fun i => w0.getD i false):=by
  unfold wV
  rw [wires_eq_foldl,hgs,List.foldl_append,List.foldl_cons]
  rw [foldl_stepWire_getD_lt post (stW w0 gj) (n+j) (by simp [stW];omega)]
  simp [stW,List.getD_eq_getElem?_getD,hW0L]
 rw [hCj]
 congr 1
 refine List.map_congr_left fun i _ => ?_
 by_cases hi : i < n+j
 . rw [ite_eq_left hi]
   unfold wV
   rw [wires_eq_foldl,hgs,List.foldl_append]
   exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
 . rw [ite_eq_right hi]
   exact getD_ge_length w0 i (by omega)
lemma wvGR (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
 (x : Fin n->Bool) (j : ℕ) (hj : j < C.gates.length) :
 wV n C x (n+j) =
  (gateAt C j).op.eval ((gateAt C j).inputs.map (wV n C x)):=by
 rw [wireVal_gate n C x j hj]
 congr 1
 refine List.map_congr_left fun i hi => ?_
 rw [ite_eq_left (hrb j hj i hi)]

def OrStep (n : ℕ) (C : Circuit) (G : Finset ℕ) (u v : ℕ) : Prop :=
 ∃ j ∈ G,u=n+j/\v ∈ (gateAt C j).inputs
def OrReach (n : ℕ) (C : Circuit) (G : Finset ℕ) : ℕ->ℕ->Prop :=
 Relation.ReflTransGen (OrStep n C G)
lemma rInP (C : Circuit) (G : Finset ℕ) (w : ℕ) :
 0 < readsIn C G w↔∃ j ∈ G,w ∈ (gateAt C j).inputs:=by
 unfold readsIn
 rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
 constructor
 . rintro ⟨j,hj,hpos⟩
   exact ⟨j,hj,List.count_pos_iff.mp hpos⟩
 . rintro ⟨j,hj,hmem⟩
   exact ⟨j,hj,List.count_pos_iff.mpr hmem⟩

lemma otRR {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {w : ℕ} (hw : w ∈ L\/(n<=w/\w - n ∈ G)) :
 OrReach n C G ρ w:=by
 by_cases hEq0 : w=ρ
 . subst hEq0;exact ReflTransGen.refl
 have hbound : w<=n+C.gates.length:=by
  rcases hw with hwL | ⟨hwn,hwG⟩
  . have hr : readsIn C G w=1:=by rw [(ht.2.1 w hwL).2,ite_eq_right hEq0]
    obtain ⟨j,hj,hmem⟩:=(rInP C G w).mp (by omega)
    have:=hrb j (hG j hj) w hmem
    have:=hG j hj
    omega
  . have:=hG (w - n) hwG;omega
 clear hEq0
 generalize hk : n+C.gates.length - w=k
 induction k using Nat.strong_induction_on generalizing w with
 | ind k ih =>
  by_cases hEq : w=ρ
  . subst hEq;exact ReflTransGen.refl
  . have hr : readsIn C G w=1:=by
     rcases hw with hwL | ⟨hwn,hwG⟩
     . rw [(ht.2.1 w hwL).2,ite_eq_right hEq]
     . have hweq : n+(w - n)=w:=by omega
       have h:=ht.2.2.1 (w - n) hwG
       rw [hweq] at h;rw [h,ite_eq_right hEq]
    obtain ⟨j,hj,hmem⟩:=(rInP C G w).mp (by omega)
    have hlt : w < n+j:=hrb j (hG j hj) w hmem
    have hjlt:=hG j hj
    have hreach_j : OrReach n C G ρ (n+j) :=
     ih (n+C.gates.length - (n+j)) (by omega) (Or.inr ⟨by omega,by simpa using hj⟩)
      (by omega) rfl
    exact ReflTransGen.tail hreach_j ⟨j,hj,rfl,hmem⟩
lemma otER {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) (x : Fin n->Bool) {u v : ℕ}
 (hreach : OrReach n C G u v) (hv : wV n C x v=true) :
 wV n C x u=true:=by
 induction hreach with
 | refl => exact hv
 | tail h1 hstep ih =>
  apply ih
  obtain ⟨j,hj,rfl,hmem⟩:=hstep
  rw [wvGR n C hrb x j (hG j hj),(ht.1 j hj).1]
  simp only [GateOp.eval,List.any_eq_true]
  exact ⟨true,List.mem_map.mpr ⟨_,hmem,hv⟩,rfl⟩

-- The cone recurrence is adapted from L_meta_2067.
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩


-- The OR-reach recurrence is adapted from L_meta_1502.
theorem orSets_spec (n : ℕ) (gs : List Gate) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length ∧
    ∀ k < gs.length, ∀ g, g ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] ↔
      g = k ∨ ((gs.getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + k ∧
          g ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g0 ih =>
    obtain ⟨hl, hs⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize gs.foldl (PEqualNP.CleanedNonEdge.orStep n) [] = S at hl hs
    have hpre : ∀ i < gs.length,
        (PEqualNP.CleanedNonEdge.orStep n S g0).getD i [] = S.getD i [] := by
      intro i hi
      unfold PEqualNP.CleanedNonEdge.orStep
      exact List.getD_append _ _ _ _ (by omega)
    have hlast : ∀ g, g ∈ (PEqualNP.CleanedNonEdge.orStep n S g0).getD gs.length [] ↔
        g = gs.length ∨ (g0.op = GateOp.or ∧ ∃ w ∈ g0.inputs, n ≤ w ∧ w < n + gs.length ∧
          g ∈ S.getD (w - n) []) := by
      intro g
      unfold PEqualNP.CleanedNonEdge.orStep
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
      by_cases hop : g0.op = GateOp.or
      · simp [hop, and_assoc]
      · simp [hop]
    refine ⟨by simp [PEqualNP.CleanedNonEdge.orStep, hl], ?_⟩
    intro k hk g
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
    · rw [hpre k hk', List.getD_append _ _ _ _ hk', hs k hk' g]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)]⟩
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)] at h3⟩
    · rw [hlast g, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)]⟩
      · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by rwa [hpre _ (by omega)] at h3⟩

theorem orReaches_def (n : ℕ) (C : Circuit) (w g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C w g ↔
      n ≤ w ∧ g ∈ (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [] :=
  Iff.rfl

theorem orReaches_iff (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        PEqualNP.CleanedNonEdge.OrReaches n C w g) := by
  rw [orReaches_def, Nat.add_sub_cancel_left, (orSets_spec n C.gates).2 k hk g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, h1, h2, (orReaches_def n C w g).2 ⟨h1, h3⟩⟩
  · rintro (h | ⟨hop, w, hw, h1, h2, h3⟩)
    · exact ⟨by omega, Or.inl h⟩
    · exact ⟨by omega, Or.inr ⟨hop, w, hw, h1, h2, ((orReaches_def n C w g).1 h3).2⟩⟩


def redirectedWire (n c : ℕ) (s : Fin n) (w : ℕ) : ℕ :=
  if w = n + c then (s : ℕ) else w

def redirected (n : ℕ) (C : Circuit) (c : ℕ) (s : Fin n) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (redirectedWire n c s)⟩), C.output⟩

lemma redirected_length (n : ℕ) (C : Circuit) (c : ℕ) (s : Fin n) :
    (redirected n C c s).gates.length = C.gates.length := by
  simp [redirected]

lemma gate_redirected {n : ℕ} (C : Circuit) (c : ℕ) (s : Fin n) (k : ℕ)
    (hk : k < C.gates.length) :
    gateAt (redirected n C c s) k =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map (redirectedWire n c s)⟩ := by
  rw [gateAt_eq_getElem _ _ (by simpa [redirected] using hk), gateAt_eq_getElem _ _ hk]
  simp [redirected]

lemma redirected_back {n : ℕ} {C : Circuit} {c : ℕ} {s : Fin n} (hRB : ReadsBack n C) :
    ReadsBack n (redirected n C c s) := by
  intro k hk w hw
  rw [redirected_length] at hk
  rw [gate_redirected _ _ _ _ hk] at hw
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
  by_cases hac : a = n + c
  · simpa [redirectedWire, hac] using (show (s : ℕ) < n + k from by have := s.isLt; omega)
  · simpa [redirectedWire, hac] using hRB k hk a ha

lemma binary_gate {n : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 n C)
    {k : ℕ} (hk : k < C.gates.length) :
    ∃ a b, (gateAt C k).inputs = [a, b] ∧
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) := by
  have hg : gateAt C k ∈ C.gates := by
    rw [gateAt_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hg)
  exact ⟨a, b, hab, hAO.1 _ hg⟩

lemma binary_change (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b a' b' : Bool) (h₁ : op.eval [a, b] = true) (h₂ : op.eval [a', b'] = false) :
    (a = true ∧ a' = false) ∨ (b = true ∧ b' = false) := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp_all [GateOp.eval]

lemma wire_mono {n : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 n C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    wV n C x w = true → wV n C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hraw : w < n
    · exact (wvI n C y ⟨w, hraw⟩).trans (hxy _ ((wvI n C x ⟨w, hraw⟩).symm.trans hw))
    · by_cases hbound : w < n + C.gates.length
      · let j := w - n
        have hj : j < C.gates.length := by dsimp [j]; omega
        have he : w = n + j := by dsimp [j]; omega
        obtain ⟨a, b, hab, hop⟩ := binary_gate hAO hj
        have ha : a ∈ (gateAt C j).inputs := by simp [hab]
        have hb : b ∈ (gateAt C j).inputs := by simp [hab]
        have har := hAO.2.1 j hj a ha
        have hbr := hAO.2.1 j hj b hb
        by_contra hn
        have hn' : wV n C y w = false := Bool.eq_false_iff.mpr hn
        rw [he, wvGR n C hAO.2.1 x j hj, hab] at hw
        rw [he, wvGR n C hAO.2.1 y j hj, hab] at hn'
        simp only [List.map_cons, List.map_nil] at hw hn'
        rcases binary_change _ hop _ _ _ _ hw hn' with ha' | hb'
        · cases (ih a (by omega) ha'.1).symm.trans ha'.2
        · cases (ih b (by omega) hb'.1).symm.trans hb'.2
      · rw [wireVal_ge n C x w (by omega)] at hw
        cases hw

lemma singleton_true {n : ℕ} {C : Circuit} {c : ℕ} {s : Fin n}
    (hS : singletonSet n C c = {s}) :
    wV n C (unitInput s) (n + c) = true := by
  have hs : s ∈ singletonSet n C c := by rw [hS]; simp
  simpa [singletonSet, gateVal, wV] using hs

lemma rewrite_sound {n : ℕ} {C C0 : Circuit} {c : ℕ} {s : Fin n}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hS : singletonSet n C c = {s})
    (hC0 : C0 = redirected n C c s) :
    ∀ x, circuitFun n C0 x = true → circuitFun n C x = true := by
  subst C0
  intro x
  have compare : ∀ w, wV n (redirected n C c s) x w = true → wV n C x w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hnew
      by_cases hraw : w < n
      · exact (wvI n C x ⟨w, hraw⟩).trans
          ((wvI n (redirected n C c s) x ⟨w, hraw⟩).symm.trans hnew)
      · by_cases hw : w < n + C.gates.length
        · let j := w - n
          have hj : j < C.gates.length := by dsimp [j]; omega
          have he : w = n + j := by dsimp [j]; omega
          have hj' : j < (redirected n C c s).gates.length := by simpa [redirected] using hj
          obtain ⟨a, b, hab, hop⟩ := binary_gate hAO hj
          have cmp_read : ∀ r ∈ (gateAt C j).inputs,
              wV n (redirected n C c s) x (redirectedWire n c s r) = true → wV n C x r = true := by
            intro r hr hread
            by_cases hrc : r = n + c
            · have hsx : x s = true := by
                rw [redirectedWire, ite_eq_left hrc, wvI] at hread
                exact hread
              have unit_imp : ∀ i, unitInput s i = true → x i = true := by
                intro i hi
                have h := of_decide_eq_true hi
                subst i
                exact hsx
              rw [hrc]
              exact wire_mono hAO unit_imp _ (singleton_true hS)
            · rw [redirectedWire, ite_eq_right hrc] at hread
              exact ih r (by rw [he]; exact hAO.2.1 j hj r hr) hread
          by_contra hn
          have hold : wV n C x w = false := Bool.eq_false_iff.mpr hn
          rw [he, wvGR n C hAO.2.1 x j hj, hab] at hold
          rw [he, wvGR n _ (redirected_back hAO.2.1) x j hj',
            gate_redirected _ _ _ _ hj, hab] at hnew
          simp only [List.map_cons, List.map_nil] at hold hnew
          rcases binary_change _ hop _ _ _ _ hnew hold with ha | hb
          · cases (cmp_read a (by simp [hab]) ha.1).symm.trans ha.2
          · cases (cmp_read b (by simp [hab]) hb.1).symm.trans hb.2
        · rw [wireVal_ge n _ x w (by rw [redirected_length]; omega)] at hnew
          cases hnew
  exact compare C.output

lemma output_cone_input {n : ℕ} {C : Circuit} {j k : ℕ} (hj : j < k)
    (hk : PEqualNP.Core.InOutputCone n C k) (hr : n + j ∈ (gateAt C k).inputs) :
    PEqualNP.Core.InOutputCone n C j := by
  have hc : InCone n C j k := (inCone_iff _ _ _ _).2 ⟨hk.1, j, hj, hr, Or.inl rfl⟩
  refine ⟨hj.trans hk.1, Or.inr ?_⟩
  rcases hk.2 with he | ⟨he, hk⟩
  · refine ⟨by omega, ?_⟩
    rw [he, Nat.add_sub_cancel_left]
    exact hc
  · exact ⟨he, inCone_trans _ _ _ _ hc _ hk⟩

lemma unit_graph_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Fin n) :
    graphFun G ∅ (unitInput s) = false := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨u, v, ha, hu, hv⟩
  have heu : u = s := of_decide_eq_true hu
  have hev : v = s := of_decide_eq_true hv
  exact G.irrefl (heu ▸ hev ▸ ha)

lemma output_safe {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {c : ℕ} {s : Fin n}
    (hF : circuitFun n C = graphFun G ∅)
    (hO : PEqualNP.Core.InOutputCone n C c)
    (hS : singletonSet n C c = {s}) :
    C.output < n + C.size ∧ C.output - n ∉ PEqualNP.Core.coneSet n C c := by
  have neq : C.output ≠ n + c := by
    intro he
    have ht : circuitFun n C (unitInput s) = true := by
      rw [← wvO, he]
      exact singleton_true hS
    rw [hF, unit_graph_false] at ht
    cases ht
  obtain ⟨hn, hc⟩ := hO.2.resolve_left neq
  obtain ⟨hcl, hlen⟩ := inCone_lt n C c _ hc
  refine ⟨by change C.output < n + C.gates.length; omega, ?_⟩
  simp only [PEqualNP.Core.coneSet, Finset.mem_insert, Finset.mem_filter, Finset.mem_range,
    not_or, not_and]
  exact ⟨by omega, fun _ hbad => by have hh := (inCone_lt n C _ _ hbad).1; omega⟩

lemma leaf_true_output {n : ℕ} {C : Circuit} {T L : Finset ℕ}
    (hRB : ReadsBack n C) (hT : IsOrTree n C T L C.output)
    (x : Fin n → Bool) {w : ℕ} (hw : w ∈ L) (ht : wV n C x w = true) :
    circuitFun n C x = true := by
  have hT' (k : ℕ) (hk : k ∈ T) : k < C.gates.length := by
    by_contra! hall
    have hnone : (gateAt C k).inputs.length = 0 := by
      unfold gateAt
      rw [List.getD_eq_default _ _ hall]
      rfl
    exact (by have := (hT.1 k hk).2.1; omega)
  exact otER hRB hT' hT x (otRR hRB hT' hT (Or.inl hw)) ht

lemma or_reaches_cone {n : ℕ} {C : Circuit} {c : ℕ} :
    ∀ k, k < C.gates.length → OrReaches n C (n + k) c → c = k ∨ InCone n C c k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk h
    rcases (orReaches_iff n C k hk c).1 h with he | ⟨_, w, hw, hwn, hwk, hreach⟩
    · exact Or.inl he
    · let j := w - n
      have he : w = n + j := by dsimp [j]; omega
      have hj : j < k := by omega
      rw [he] at hreach hw
      exact Or.inr ((inCone_iff n C c k).2 ⟨hk, j, hj, hw, ih j hj (hj.trans hk) hreach⟩)

lemma or_reaches_true {n : ℕ} {C : Circuit} {x : Fin n → Bool} {c : ℕ}
    (hRB : ReadsBack n C) (hC : wV n C x (n + c) = true) :
    ∀ w < n + C.gates.length, OrReaches n C w c → wV n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw h
    have hn := h.1
    let k := w - n
    have he : w = n + k := by dsimp [k]; omega
    have hk : k < C.gates.length := by omega
    rw [he] at h ⊢
    rcases (orReaches_iff n C k hk c).1 h with eq | ⟨hop, a, ha, _, hak, hra⟩
    · rw [← eq]
      exact hC
    · have hat := ih a (by omega) (by omega) hra
      rw [wvGR n C hRB x k hk, hop]
      simp only [GateOp.eval, List.any_eq_true]
      exact ⟨true, List.mem_map.mpr ⟨_, ha, hat⟩, rfl⟩

structure LostLeaf (n : ℕ) (C : Circuit) (L : Finset ℕ) (c : ℕ) (x : Fin n → Bool) where
  index : ℕ
  index_lt : index < C.gates.length
  mem : n + index ∈ L
  first : ℕ
  other : ℕ
  inputs : (gateAt C index).inputs = [first, other] ∨ (gateAt C index).inputs = [other, first]
  reaches : OrReaches n C first c
  true_on : wV n C x (n + index) = true

lemma wire_change_trace {n : ℕ} {C : Circuit} {T L : Finset ℕ} {c : ℕ} {s : Fin n}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hT : IsOrTree n C T L C.output)
    (hc : c < C.gates.length)
    (hDesc : ∀ k < C.gates.length, InCone n C c k → PEqualNP.Core.InOutputCone n C k →
      k ∈ T ∨ n + k ∈ L ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ L, ∃ a ∈ (gateAt C (w - n)).inputs, OrReaches n C a k))
    (x : Fin n → Bool) :
    ∀ k, PEqualNP.Core.InOutputCone n C k →
      wV n C x (n + k) = true → wV n (redirected n C c s) x (n + k) = false →
      x s = false ∧ wV n C x (n + c) = true ∧
        (OrReaches n C (n + k) c ∨ Nonempty (LostLeaf n C L c x)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hOut hold hnew
    have hk := hOut.1
    have hk' : k < (redirected n C c s).gates.length := by simpa [redirected] using hk
    obtain ⟨a, b, hab, hop⟩ := binary_gate hAO hk
    have hOld := hold
    rw [wvGR n C hAO.2.1 x k hk, hab] at hold
    rw [wvGR n _ (redirected_back hAO.2.1) x k hk',
      gate_redirected _ _ _ _ hk, hab] at hnew
    simp only [List.map_cons, List.map_nil] at hold hnew
    obtain ⟨r, t, hr, hrOld, hrNew, hrt⟩ :
        ∃ r t, r ∈ (gateAt C k).inputs ∧ wV n C x r = true ∧
          wV n (redirected n C c s) x (redirectedWire n c s r) = false ∧
          ((gateAt C k).inputs = [r,t] ∨ (gateAt C k).inputs = [t,r]) := by
      rcases binary_change _ hop _ _ _ _ hold hnew with hit | hit
      · exact ⟨a,b,by simp [hab],hit.1,hit.2,Or.inl hab⟩
      · exact ⟨b,a,by simp [hab],hit.1,hit.2,Or.inr hab⟩
    have hrBound := hAO.2.1 k hk r hr
    have hrTrace : x s = false ∧ wV n C x (n + c) = true ∧
        (OrReaches n C r c ∨ Nonempty (LostLeaf n C L c x)) := by
      by_cases he : r = n + c
      · rw [redirectedWire, ite_eq_left he, wvI] at hrNew
        rw [he] at hrOld
        exact ⟨hrNew, hrOld, Or.inl (he ▸ (orReaches_iff n C c hc c).2 (Or.inl rfl))⟩
      · rw [redirectedWire, ite_eq_right he] at hrNew
        by_cases hraw : r < n
        · have e1 := wvI n C x ⟨r, hraw⟩
          have e2 := wvI n (redirected n C c s) x ⟨r, hraw⟩
          have heq := (hrOld.symm.trans e1).trans (e2.symm.trans hrNew)
          cases heq
        · let j := r - n
          have hrEq : r = n + j := by dsimp [j]; omega
          have hj : j < k := by omega
          rw [hrEq] at hr hrOld hrNew ⊢
          exact ih j hj (output_cone_input hj hOut hr) hrOld hrNew
    obtain ⟨hsfalse, hcTrue, hreaches | hwitness⟩ := hrTrace
    · refine ⟨hsfalse, hcTrue, ?_⟩
      rcases hop with hand | hor
      · have hrn := hreaches.1
        let j := r - n
        have hrEq : r = n + j := by dsimp [j]; omega
        have hj : j < k := by omega
        have hjC := hj.trans hk
        have cInJ : c = j ∨ InCone n C c j := or_reaches_cone j hjC (hrEq ▸ hreaches)
        have cInK : InCone n C c k :=
          (inCone_iff n C c k).2 ⟨hk, j, hj, hrEq ▸ hr, cInJ⟩
        have hkL : n + k ∈ L := by
          rcases hDesc k hk cInK hOut with hkT | hkL | ⟨hop', _⟩
          · have he := hand.symm.trans (hT.1 k hkT).1
            cases he
          · exact hkL
          · have he := hand.symm.trans hop'
            cases he
        exact Or.inr ⟨⟨k, hk, hkL, r, t, hrt, hreaches, hOld⟩⟩
      · exact Or.inl ((orReaches_iff n C k hk c).2 (Or.inr ⟨hor, r, hr, hreaches.1, hrBound, hreaches⟩))
    · exact ⟨hsfalse, hcTrue, Or.inr hwitness⟩

lemma graph_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graph_true_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have ha' : a = u ∨ a = v := of_decide_eq_true ha
    have hb' : b = u ∨ b = v := of_decide_eq_true hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · exact fun hab => ⟨u, v, hab, by simp [pairInput], by simp [pairInput]⟩

lemma lost_edge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C C0 : Circuit}
    {T L : Finset ℕ} {c : ℕ} {s : Fin n}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : IsOrTree n C T L C.output)
    (hL : ∀ w ∈ L, n ≤ w ∧ (gateAt C (w - n)).op = GateOp.and)
    (hO : PEqualNP.Core.InOutputCone n C c) (hS : singletonSet n C c = {s})
    (hDesc : ∀ k < C.gates.length, InCone n C c k → PEqualNP.Core.InOutputCone n C k →
      k ∈ T ∨ n + k ∈ L ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ L, ∃ a ∈ (gateAt C (w - n)).inputs, OrReaches n C a k))
    (hC0 : C0 = redirected n C c s)
    (hTest : ∀ u v : Fin n, G.Adj u v → circuitFun n C0 (pairInput u v) = false →
      ∀ w ∈ L, gateVal n C (w - n) (pairInput u v) = true →
        ∀ a b : ℕ, ((gateAt C (w - n)).inputs = [a, b] ∨
          (gateAt C (w - n)).inputs = [b, a]) →
        OrReaches n C a c →
          wireVal n C b (unitInput u) = true ∨ wireVal n C b (unitInput v) = true)
    {u v : Fin n} (hAdj : G.Adj u v) (hLoss : circuitFun n C0 (pairInput u v) = false) :
    s ≠ u ∧ s ≠ v ∧ gateVal n C c (pairInput u v) = true ∧ (G.Adj s u ∨ G.Adj s v) := by
  subst C0
  have output := output_safe hF hO hS
  let o := C.output - n
  have output_n : n ≤ C.output := by rcases hO.2 with h | h <;> omega
  have hoEq : C.output = n + o := by dsimp [o]; omega
  have hoLt : o < C.gates.length := by
    have h := output.1
    change C.output < n + C.gates.length at h
    omega
  have hoCone : PEqualNP.Core.InOutputCone n C o := ⟨hoLt, Or.inl hoEq⟩
  have hOld : wV n C (pairInput u v) (n + o) = true := by
    rw [← hoEq, wvO, hF]
    exact (graph_pair_iff G u v).2 hAdj
  have hNew : wV n (redirected n C c s) (pairInput u v) (n + o) = false := by
    rw [← hoEq]
    exact hLoss
  obtain ⟨hsFalse, hcTrue, hr | hw⟩ :=
    wire_change_trace hAO hT hO.1 hDesc (pairInput u v) o hoCone hOld hNew
  · have hSOut : wV n C (unitInput s) (n + o) = true :=
      or_reaches_true hAO.2.1 (singleton_true hS) _ (by omega) hr
    rw [← hoEq, wvO, hF, unit_graph_false] at hSOut
    cases hSOut
  · obtain ⟨w⟩ := hw
    have hne : ¬ (s = u ∨ s = v) := of_decide_eq_false hsFalse
    refine ⟨fun h => hne (Or.inl h), fun h => hne (Or.inr h), hcTrue, ?_⟩
    have hChoice : wireVal n C w.other (unitInput u) = true ∨
        wireVal n C w.other (unitInput v) = true := by
      exact hTest u v hAdj hLoss (n + w.index) w.mem
        (by simpa [gateVal, wV] using w.true_on) w.first w.other
        (by simpa using w.inputs) w.reaches
    have hAdj' (p : Fin n) (ht : wV n C (unitInput p) w.other = true) : G.Adj s p := by
      have imp (q : Fin n) (h : q = s ∨ q = p) (i : Fin n) :
          unitInput q i = true → pairInput s p i = true := by
        intro hi
        have he : i = q := of_decide_eq_true hi
        exact decide_eq_true (he ▸ h)
      have firstTrue : wV n C (pairInput s p) w.first = true := by
        apply or_reaches_true hAO.2.1
          (wire_mono hAO (imp s (Or.inl rfl)) _ (singleton_true hS)) _ _ w.reaches
        have hm : w.first ∈ (gateAt C w.index).inputs := by
          rcases w.inputs with he | he <;> simp [he]
        exact (hAO.2.1 _ w.index_lt _ hm).trans (Nat.add_lt_add_left w.index_lt n)
      have otherTrue : wV n C (pairInput s p) w.other = true :=
        wire_mono hAO (imp p (Or.inr rfl)) _ ht
      have hop : (gateAt C w.index).op = GateOp.and := by
        simpa using (hL _ w.mem).2
      have leafTrue : wV n C (pairInput s p) (n + w.index) = true := by
        rw [wvGR n C hAO.2.1 _ _ w.index_lt, hop]
        rcases w.inputs with he | he <;> simp [he, GateOp.eval, firstTrue, otherTrue]
      have outTrue := leaf_true_output hAO.2.1 hT (pairInput s p) w.mem leafTrue
      rw [hF] at outTrue
      exact (graph_pair_iff G s p).1 outTrue
    exact hChoice.imp (hAdj' u) (hAdj' v)

end PEqualNP.Outside.L_meta_3017.Lost

namespace PEqualNP.Outside.L_meta_3017.Repair

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

private def appendBin (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨op, [a, b]⟩], n + D.size⟩

private theorem wiresLength (D : Circuit) (x : List Bool) :
    (D.wires x).length = x.length + D.size := by
  unfold Circuit.wires Circuit.size
  generalize D.gates = gs
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem wiresAppend (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ) (x : List Bool) :
    (appendBin n D op a b).wires x =
      D.wires x ++ [op.eval [(D.wires x).getD a false, (D.wires x).getD b false]] := by
  simp [appendBin, Circuit.wires, List.foldl_append]

private theorem sizeAppend (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ) :
    (appendBin n D op a b).size = D.size + 1 := by
  simp [appendBin, Circuit.size]

private theorem appendRead (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) (i : ℕ) (hi : i < n + D.size) :
    ((appendBin n D op a b).wires (List.ofFn x)).getD i false =
      (D.wires (List.ofFn x)).getD i false := by
  rw [wiresAppend]
  apply List.getD_append
  simpa [wiresLength] using hi

private theorem evalAppend (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) :
    (appendBin n D op a b).eval (List.ofFn x) =
      op.eval [(D.wires (List.ofFn x)).getD a false, (D.wires (List.ofFn x)).getD b false] := by
  unfold Circuit.eval
  rw [wiresAppend]
  have hlen : (D.wires (List.ofFn x)).length = n + D.size := by
    simp [wiresLength]
  change (_ ++ [_]).getD (n + D.size) false = _
  rw [← hlen]
  simp

private theorem appendAO (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hAO : IsAO2 n D)
    (ha : a < n + D.size) (hb : b < n + D.size) :
    IsAO2 n (appendBin n D op a b) := by
  rcases hAO with ⟨hOps, hReads, hTwo⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendBin, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hOps g hg
    · exact hop
  · intro j hj i hi
    by_cases h : j < D.gates.length
    · have heq : gateAt (appendBin n D op a b) j = gateAt D j := by
        simp only [gateAt, appendBin]
        exact List.getD_append _ _ _ _ h
      rw [heq] at hi
      exact hReads j h i hi
    · have hj' : j = D.gates.length := by
        simp only [appendBin, List.length_append, List.length_singleton] at hj
        omega
      subst j
      simp only [gateAt, appendBin, List.getD_eq_getElem?_getD, List.getElem?_concat_length,
        Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [appendBin, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hTwo g hg
    · rfl

private theorem appendOutput (n : ℕ) (D : Circuit) (op : GateOp) (a b : ℕ) :
    (appendBin n D op a b).output < n + (appendBin n D op a b).size := by
  rw [sizeAppend]
  change n + D.size < n + (D.size + 1)
  omega

private theorem foldPrefix (gates : List Gate) (wires : List Bool) (i : ℕ)
    (hi : i < wires.length) :
    (gates.foldl (fun xs g => xs ++ [g.op.eval (g.inputs.map (fun w => xs.getD w false))])
      wires).getD i false = wires.getD i false := by
  induction gates generalizing wires with
  | nil => rfl
  | cons g gates ih =>
    simp only [List.foldl_cons]
    rw [ih]
    · exact List.getD_append _ _ _ _ hi
    · simp only [List.length_append, List.length_singleton]
      omega

private theorem readInput (n : ℕ) (D : Circuit) (x : Fin n → Bool) (v : Fin n) :
    (D.wires (List.ofFn x)).getD v.val false = x v := by
  unfold Circuit.wires
  rw [foldPrefix D.gates (List.ofFn x) v.val (by simp)]
  simp [List.getD_eq_getElem?_getD, v.isLt]

private theorem foldRawOr (n : ℕ) (D : Circuit) (vs : List (Fin n)) (hD : IsAO2 n D)
    (hout : D.output < n + D.size) :
    ∃ A : Circuit, IsAO2 n A ∧ A.size = D.size + vs.length ∧ A.output < n + A.size ∧
      (∀ (x : Fin n → Bool) (i : ℕ), i < n + D.size →
        (A.wires (List.ofFn x)).getD i false = (D.wires (List.ofFn x)).getD i false) ∧
      ∀ x : Fin n → Bool, A.eval (List.ofFn x) = (D.eval (List.ofFn x) || vs.any x) := by
  induction vs generalizing D with
  | nil => exact ⟨D, hD, by simp, hout, fun _ _ _ => rfl, by simp⟩
  | cons v vs ih =>
    let A := appendBin n D GateOp.or D.output v.val
    have hv : v.val < n + D.size := by have := v.isLt; omega
    have hA := appendAO n D GateOp.or D.output v.val (Or.inr rfl) hD hout hv
    have hAs : A.size = D.size + 1 := sizeAppend ..
    obtain ⟨B, hB, hBs, hBout, hKeep, hEval⟩ := ih A hA (appendOutput ..)
    refine ⟨B, hB, by simp only [List.length_cons]; omega, hBout, ?_, ?_⟩
    · intro x i hi
      have hiA : i < n + A.size := by omega
      exact (hKeep x i hiA).trans (appendRead n D GateOp.or D.output v.val x i hi)
    · intro x
      rw [hEval x]
      change ((appendBin n D GateOp.or D.output v.val).eval (List.ofFn x) || vs.any x) = _
      rw [evalAppend, readInput n D x v]
      simp [GateOp.eval, Circuit.eval, Bool.or_assoc]

private theorem addStar (n : ℕ) (D : Circuit) (center : Fin n) (vs : List (Fin n))
    (hD : IsAO2 n D) (hout : D.output < n + D.size) (hvs : vs ≠ []) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size = D.size + (vs.length + 1) ∧
      E.output < n + E.size ∧ ∀ x : Fin n → Bool,
        E.eval (List.ofFn x) = (D.eval (List.ofFn x) || (x center && vs.any x)) := by
  cases vs with
  | nil => exact (hvs rfl).elim
  | cons v vs =>
    let start : Circuit := ⟨D.gates, v.val⟩
    have hstart : IsAO2 n start := hD
    have startSize : start.size = D.size := rfl
    have startOut : start.output < n + start.size := by
      change v.val < n + D.size
      have := v.isLt
      omega
    obtain ⟨A, hA, hAs, hAout, hKeep, hEval⟩ := foldRawOr n start vs hstart startOut
    let B := appendBin n A GateOp.and center.val A.output
    have centerBound : center.val < n + A.size := by have := center.isLt; omega
    have hB := appendAO n A GateOp.and center.val A.output (Or.inl rfl) hA centerBound hAout
    have hBs : B.size = A.size + 1 := sizeAppend ..
    have hBout : B.output < n + B.size := appendOutput ..
    have houtA : D.output < n + A.size := by omega
    have houtB : D.output < n + B.size := by omega
    let E := appendBin n B GateOp.or D.output B.output
    have hE := appendAO n B GateOp.or D.output B.output (Or.inr rfl) hB houtB hBout
    have hEs : E.size = B.size + 1 := sizeAppend ..
    refine ⟨E, hE, by simp only [List.length_cons]; omega, appendOutput .., ?_⟩
    intro x
    have oldOutput : (B.wires (List.ofFn x)).getD D.output false = D.eval (List.ofFn x) := by
      have hStartBound : D.output < n + start.size := by simpa [startSize] using hout
      change ((appendBin n A GateOp.and center.val A.output).wires
        (List.ofFn x)).getD D.output false = _
      rw [appendRead n A GateOp.and center.val A.output x D.output houtA, hKeep x _ hStartBound]
      rfl
    have startEval : start.eval (List.ofFn x) = x v := readInput n D x v
    have termEval : B.eval (List.ofFn x) = (x center && (v :: vs).any x) := by
      change (appendBin n A GateOp.and center.val A.output).eval (List.ofFn x) = _
      rw [evalAppend, readInput n A x center]
      simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, List.any_cons]
      change (x center && A.eval (List.ofFn x)) = _
      rw [hEval x, startEval]
    change (appendBin n B GateOp.or D.output B.output).eval (List.ofFn x) = _
    rw [evalAppend, oldOutput]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    change (D.eval (List.ofFn x) || B.eval (List.ofFn x)) = _
    simp only [termEval, List.any_cons]

private abbrev Star (n : ℕ) := Fin n × List (Fin n)

private def starValue (n : ℕ) (x : Fin n → Bool) (s : Star n) : Bool :=
  x s.1 && s.2.any x

private def starCost (n : ℕ) (s : Star n) : ℕ := s.2.length + 1

theorem addStars (n : ℕ) (D : Circuit) (stars : List (Star n))
    (hD : IsAO2 n D) (hout : D.output < n + D.size)
    (hvs : ∀ s ∈ stars, s.2 ≠ []) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size = D.size + (stars.map (starCost n)).sum ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) = (D.eval (List.ofFn x) || stars.any (starValue n x)) := by
  induction stars generalizing D with
  | nil => exact ⟨D, hD, by simp, by simp⟩
  | cons s rest ih =>
    obtain ⟨A, hA, hAs, hAout, hEval⟩ := addStar n D s.1 s.2 hD hout (hvs s (by simp))
    obtain ⟨E, hE, hEs, hOut⟩ := ih A hA hAout (fun t ht => hvs t (by simp [ht]))
    refine ⟨E, hE, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, starCost]
      omega
    · intro x
      rw [hOut x, hEval x]
      simp [List.any_cons, starValue, Bool.or_assoc]
theorem repair (n : ℕ) (D : Circuit) (R : Fin n → Fin n → Prop) [DecidableRel R]
    (center : Fin n → Bool) (hD : IsAO2 n D) (hout : D.output < n + D.size)
    (hsymm : ∀ u v, R u v → R v u) (hCross : ∀ u v, R u v → center u ≠ center v)
    (hUnique : ∀ u v y, center u = true → center v = true → R u y → R v y → u = v) :
    ∃ E : Circuit, IsAO2 n E ∧
      E.size ≤ D.size + (Finset.univ.filter fun y => ∃ z, R z y).card ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) = (D.eval (List.ofFn x) ||
        decide (∃ u v, R u v ∧ x u = true ∧ x v = true)) := by
  let ends := Finset.univ.filter fun y => ∃ z, R z y
  let centers := ends.filter fun u => center u = true
  let leaves := fun u => Finset.univ.filter (R u)
  let stars : List (Star n) := centers.toList.map fun u => (u, (leaves u).toList)
  have memEnds (y : Fin n) : y ∈ ends ↔ ∃ z, R z y := by simp [ends]
  have memLeaves (u y : Fin n) : y ∈ leaves u ↔ R u y := by simp [leaves]
  have centerTrue {u : Fin n} (hu : u ∈ centers) : center u = true :=
    (Finset.mem_filter.mp hu).2
  have vertexCenter {u v : Fin n} (h : R u v) (hu : center u = true) : u ∈ centers :=
    Finset.mem_filter.mpr ⟨(memEnds u).mpr ⟨v, hsymm u v h⟩, hu⟩
  have nonempty (s : Star n) (hs : s ∈ stars) : s.2 ≠ [] := by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
    obtain ⟨y, hy⟩ := (memEnds u).mp (Finset.mem_filter.mp (Finset.mem_toList.mp hu)).1
    have hm := Finset.mem_toList.mpr ((memLeaves u y).mpr (hsymm y u hy))
    intro h
    change (leaves u).toList = [] at h
    rw [h] at hm
    exact List.not_mem_nil hm
  have pairDisjoint : (centers : Set (Fin n)).PairwiseDisjoint leaves := by
    intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro y hy hz
    exact hne (hUnique u v y (centerTrue hu) (centerTrue hv)
      ((memLeaves u y).mp hy) ((memLeaves v y).mp hz))
  let allLeaves := centers.biUnion leaves
  have disjoint : Disjoint centers allLeaves := by
    apply Finset.disjoint_left.mpr
    intro y hy hl
    obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.mp hl
    exact hCross u y ((memLeaves u y).mp hyu) ((centerTrue hu).trans (centerTrue hy).symm)
  have cardUnion : (centers ∪ allLeaves).card ≤ ends.card := by
    apply Finset.card_le_card
    intro y hy
    rcases Finset.mem_union.mp hy with hc | hl
    · exact (Finset.mem_filter.mp hc).1
    · obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hl
      exact (memEnds y).mpr ⟨u, (memLeaves u y).mp hu⟩
  have cardLeaves : allLeaves.card = ∑ u ∈ centers, (leaves u).card :=
    Finset.card_biUnion pairDisjoint
  have costBound : (stars.map (starCost n)).sum ≤ ends.card := by
    have hcost : (stars.map (starCost n)).sum = ∑ u ∈ centers, ((leaves u).card + 1) := by
      unfold stars
      rw [List.map_map]
      change (centers.toList.map fun u => (leaves u).toList.length + 1).sum = _
      simp only [Finset.length_toList]
      exact Finset.sum_map_toList centers _
    rw [hcost, Finset.sum_add_distrib, ← cardLeaves]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rw [Nat.add_comm, ← Finset.card_union_of_disjoint disjoint]
    exact cardUnion
  obtain ⟨E, hE, hEs, hEval⟩ := addStars n D stars hD hout nonempty
  refine ⟨E, hE, ?_, ?_⟩
  · change E.size ≤ D.size + ends.card
    omega
  intro x
  have edgeTerm (u v : Fin n) (h : R u v) (hu : center u = true)
      (xu : x u = true) (xv : x v = true) : stars.any (starValue n x) = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u, (leaves u).toList), List.mem_map.mpr ⟨u, Finset.mem_toList.mpr (vertexCenter h hu), rfl⟩, ?_⟩
    change (x u && (leaves u).toList.any x) = true
    rw [Bool.and_eq_true]
    exact ⟨xu, List.any_eq_true.mpr
      ⟨v, Finset.mem_toList.mpr ((memLeaves u v).mpr h), xv⟩⟩
  have reify : stars.any (starValue n x) = decide (∃ u v, R u v ∧ x u = true ∧ x v = true) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨s, hs, hvalue⟩ := List.any_eq_true.mp h
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hs
      change (x u && (leaves u).toList.any x) = true at hvalue
      rw [Bool.and_eq_true] at hvalue
      obtain ⟨xu, hls⟩ := hvalue
      obtain ⟨v, hv, xv⟩ := List.any_eq_true.mp hls
      exact ⟨u, v, (memLeaves u v).mp (Finset.mem_toList.mp hv), xu, xv⟩
    · rintro ⟨u, v, h, xu, xv⟩
      cases hu : center u with
      | true => exact edgeTerm u v h hu xu xv
      | false =>
        have hv : center v = true := by
          cases hv : center v with
          | false => exact (hCross u v h (hu.trans hv.symm)).elim
          | true => rfl
        exact edgeTerm v u (hsymm u v h) hv xv xu
  rw [hEval x, reify]



end PEqualNP.Outside.L_meta_3017.Repair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm in
theorem PEqualNP.Outside.L_meta_3017 :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (col : Fin n → Bool) (C C0 : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (c : ℕ) (s : Fin n),
    (∀ u v : Fin n, G.Adj u v → col u ≠ col v) →
    PEqualNP.TopForm.NoFourCycle G →
    PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
    PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
    PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output →
    (∀ w ∈ L, n ≤ w ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    c < C.gates.length → PEqualNP.Core.InOutputCone n C c →
    PEqualNP.SplitCount.singletonSet n C c = {s} →
    (∀ k < C.gates.length, n + c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (∀ k < C.gates.length, PEqualNP.EdgeOwnership.InCone n C c k → PEqualNP.Core.InOutputCone n C k →
      k ∈ T ∨ n + k ∈ L ∨ ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∃ w ∈ L, ∃ a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs, PEqualNP.CleanedNonEdge.OrReaches n C a k)) →
    (∀ j < C.gates.length, PEqualNP.EdgeOwnership.InCone n C j c → ∀ k < C.gates.length,
      n + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k = c ∨ PEqualNP.EdgeOwnership.InCone n C k c) →
    C0 = ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun ww => if ww = n + c then (s : ℕ) else ww) } : PEqualNP.CircuitLowerBounds.Gate)), output := C.output } : PEqualNP.CircuitLowerBounds.Circuit) →
    (∀ u v : Fin n, G.Adj u v → PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput u v) = false →
      ∀ w ∈ L, PEqualNP.EdgeOwnership.gateVal n C (w - n) (PEqualNP.EdgeOwnership.pairInput u v) = true →
        ∀ a b : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs = [b, a]) →
          PEqualNP.CleanedNonEdge.OrReaches n C a c →
            PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.SplitCount.unitInput u) = true ∨ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.SplitCount.unitInput v) = true) →
    (Finset.univ.filter fun y : Fin n => ∃ z : Fin n, G.Adj z y ∧ PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput z y) = false).card ≤ (PEqualNP.Core.coneSet n C c).card ∧
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' ∧
      PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      C'.size + (PEqualNP.Core.coneSet n C c).card ≤ C.size + (Finset.univ.filter fun y2 : Fin n => ∃ z2 : Fin n, G.Adj z2 y2 ∧ PEqualNP.MetaComplexity.circuitFun n C0 (PEqualNP.EdgeOwnership.pairInput z2 y2) = false).card := by
  intro n G instAdj col C C0 T L c s hBip hFour hAO _hReads hF hT hL hc hO hS
    _hReadOr hDesc hPrivate hC0 hTest
  let R : Fin n → Fin n → Prop := fun u v =>
    G.Adj u v ∧ circuitFun n C0 (pairInput u v) = false
  letI : DecidableRel R := fun u v => by
    change Decidable (G.Adj u v ∧ circuitFun n C0 (pairInput u v) = false)
    infer_instance
  let V : Finset (Fin n) := Finset.univ.filter fun y => ∃ z, R z y
  have pairComm (u v : Fin n) : pairInput u v = pairInput v u := by
    funext k
    simp [pairInput, or_comm]
  have symmetric (u v : Fin n) (hr : R u v) : R v u := by
    exact ⟨G.adj_symm hr.1, (pairComm u v) ▸ hr.2⟩
  have lossFacts (u v : Fin n) (hr : R u v) :
      s ≠ u ∧ s ≠ v ∧ gateVal n C c (pairInput u v) = true ∧
        (G.Adj s u ∨ G.Adj s v) :=
    PEqualNP.Outside.L_meta_3017.Lost.lost_edge hAO hF hT hL hO hS hDesc hC0 hTest hr.1 hr.2
  have sNotLost : s ∉ V := by
    intro hm
    obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hm).2
    exact (lossFacts z s hz).2.1 rfl
  have coneBound : V.card ≤ (PEqualNP.Core.coneSet n C c).card := by
    apply PEqualNP.Outside.L_meta_3017.Cone.count n C c s V hAO hc hS sNotLost
    intro y hy
    obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hy).2
    have h := lossFacts z y hz
    exact ⟨z, h.1.symm, h.2.2.1⟩
  let center : Fin n → Bool := fun u => decide (G.Adj s u)
  have centerAdj (u : Fin n) : center u = true ↔ G.Adj s u := by
    simp [center]
  have cross (u v : Fin n) (hr : R u v) : center u ≠ center v := by
    intro eq
    have adj : G.Adj s u ∧ G.Adj s v := by
      rcases (lossFacts u v hr).2.2.2 with hu | hv
      · exact ⟨hu, (centerAdj v).mp (eq.symm.trans ((centerAdj u).mpr hu))⟩
      · exact ⟨(centerAdj u).mp (eq.trans ((centerAdj v).mpr hv)), hv⟩
    have hsU := hBip s u adj.1
    have hsV := hBip s v adj.2
    have huv := hBip u v hr.1
    cases hs : col s <;> cases hu : col u <;> cases hv : col v <;> simp_all
  have uniqueCenter (u v y : Fin n) (hu : center u = true) (hv : center v = true)
      (huy : R u y) (hvy : R v y) : u = v := by
    by_contra ne
    let common := Finset.univ.filter fun w => G.Adj s w ∧ G.Adj y w
    have huIn : u ∈ common := by simp [common, (centerAdj u).mp hu, G.adj_symm huy.1]
    have hvIn : v ∈ common := by simp [common, (centerAdj v).mp hv, G.adj_symm hvy.1]
    have hmany : 1 < common.card := Finset.one_lt_card.mpr ⟨u, huIn, v, hvIn, ne⟩
    have hfew : common.card ≤ 1 := hFour s y (lossFacts u y huy).2.1
    omega
  have outSafe := PEqualNP.Outside.L_meta_3017.Lost.output_safe hF hO hS
  obtain ⟨D, hD, hDsize, hDout, hDfun⟩ :=
    PEqualNP.Outside.L_meta_3017.Prune.prune n C C0 c s hAO hc hPrivate hC0
      outSafe.1 (Or.inr outSafe.2)
  obtain ⟨E, hE, hEsize, hEval⟩ :=
    PEqualNP.Outside.L_meta_3017.Repair.repair n D R center hD hDout symmetric cross uniqueCenter
  have graphTrue (x : Fin n → Bool) :
      graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simp [graphFun]
  refine ⟨coneBound, E, hE, hE.2.1, ?_, ?_⟩
  · funext x
    change E.eval (List.ofFn x) = graphFun G ∅ x
    apply Bool.eq_iff_iff.mpr
    rw [hEval x, Bool.or_eq_true, decide_eq_true_eq, graphTrue x]
    constructor
    · rintro (hd | ⟨u, v, huv, hu, hv⟩)
      · have h0 : circuitFun n C0 x = true := (congrFun hDfun x).symm.trans hd
        have h1 := PEqualNP.Outside.L_meta_3017.Lost.rewrite_sound hAO hS hC0 x h0
        exact (graphTrue x).mp ((congrFun hF x).symm.trans h1)
      · exact ⟨u, v, huv.1, hu, hv⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      cases hpair : circuitFun n C0 (pairInput u v) with
      | false => exact Or.inr ⟨u, v, ⟨huv, hpair⟩, hu, hv⟩
      | true =>
        apply Or.inl
        have hDpair : circuitFun n D (pairInput u v) = true :=
          (congrFun hDfun _).trans hpair
        have leInput (z : Fin n) (hz : pairInput u v z = true) : x z = true := by
          have eq : z = u ∨ z = v := of_decide_eq_true hz
          rcases eq with rfl | rfl
          · exact hu
          · exact hv
        exact PEqualNP.Outside.L_meta_3017.Lost.wire_mono hD leInput D.output hDpair
  · change E.size + (PEqualNP.Core.coneSet n C c).card ≤ C.size + V.card
    change E.size ≤ D.size + V.card at hEsize
    omega
