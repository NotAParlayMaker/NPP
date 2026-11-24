import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264_aux

open PEqualNP.CircuitLowerBounds

-- One gate appended to the wire values.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  have h' : i < (List.ofFn f).length := by simpa using h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h', Option.getD_some, List.getElem_ofFn]

theorem getD_ofFn_ge {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : n ≤ i) :
    (List.ofFn f).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
  rfl

theorem length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

theorem prefix_fold (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    unfold stepW
    rw [getD_snoc, if_pos hi]

theorem beyond_fold (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl stepW w).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_fold]; exact hi)]
  rfl

-- Wires below `k` stay, every other wire moves up by `N`.
def relabel (k N i : ℕ) : ℕ := if i < k then i else i + N

def relabelGate (k N : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (relabel k N)⟩

theorem sim (k N : ℕ) (gs : List Gate) (w w' : List Bool) (hk : k ≤ w.length)
    (hlen : w'.length = w.length + N)
    (h : ∀ i, w'.getD (relabel k N i) false = w.getD i false) :
    ∀ i, ((gs.map (relabelGate k N)).foldl stepW w').getD (relabel k N i) false =
      (gs.foldl stepW w).getD i false := by
  induction gs generalizing w w' with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [stepW]
      omega
    · simp [stepW]
      omega
    · intro i
      have hv : (relabelGate k N g).op.eval
          ((relabelGate k N g).inputs.map fun i => w'.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [relabelGate, List.map_map, Function.comp_def, h]
      unfold stepW
      rw [hv, getD_snoc, getD_snoc]
      by_cases hi : i < w.length
      · have hr : relabel k N i < w'.length := by unfold relabel; split_ifs <;> omega
        rw [if_pos hr, if_pos hi, h]
      · by_cases he : i = w.length
        · have hr : relabel k N i = w'.length := by unfold relabel; split_ifs <;> omega
          rw [if_neg (by omega), if_pos hr, if_neg hi, if_pos he]
        · have hr : w'.length < relabel k N i := by unfold relabel; split_ifs <;> omega
          rw [if_neg (by omega), if_neg (by omega), if_neg hi, if_neg he]

-- For each pair an AND of its two wires, then an OR into the running output.
def extra (N : ℕ) : ℕ → ℕ → List (Fin N × Fin N) → List Gate
  | _, _, [] => []
  | o, m, p :: L =>
    ⟨GateOp.and, [p.1.val, N + p.2.val]⟩ :: ⟨GateOp.or, [o, m]⟩ :: extra N (m + 1) (m + 2) L

def finalOut {N : ℕ} : ℕ → ℕ → List (Fin N × Fin N) → ℕ
  | o, _, [] => o
  | _, m, _ :: L => finalOut (m + 1) (m + 2) L

theorem extra_length (N : ℕ) (L : List (Fin N × Fin N)) :
    ∀ o m, (extra N o m L).length = 2 * L.length := by
  induction L with
  | nil => intro o m; rfl
  | cons p L ih =>
    intro o m
    simp only [extra, List.length_cons, ih]
    omega

theorem extra_ok (N : ℕ) (L : List (Fin N × Fin N)) :
    ∀ o m, ∀ g ∈ extra N o m L,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction L with
  | nil => intro o m g hg; simp [extra] at hg
  | cons p L ih =>
    intro o m g hg
    simp only [extra, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨Or.inr rfl, rfl⟩
    · exact ih _ _ g hg

theorem extra_reads (N : ℕ) (L : List (Fin N × Fin N)) :
    ∀ o m, o < m → N + N ≤ m →
      ∀ j (hj : j < (extra N o m L).length), ∀ i ∈ ((extra N o m L)[j]).inputs, i < m + j := by
  induction L with
  | nil => intro o m _ _ j hj; simp [extra] at hj
  | cons p L ih =>
    intro o m ho hN j hj i hi
    rcases j with _ | _ | j
    · simp [extra] at hi
      have h1 := p.1.isLt
      have h2 := p.2.isLt
      omega
    · simp [extra] at hi
      omega
    · simp only [extra, List.getElem_cons_succ] at hi
      have hj' : j < (extra N (m + 1) (m + 2) L).length := by
        simp only [extra, List.length_cons] at hj
        omega
      have := ih (m + 1) (m + 2) (by omega) (by omega) j hj' i hi
      omega

theorem extra_val (N : ℕ) (L : List (Fin N × Fin N)) :
    ∀ (o m : ℕ) (W : List Bool), W.length = m → o < m → N + N ≤ m →
      (((extra N o m L).foldl stepW W).getD (finalOut o m L) false = true ↔
        (W.getD o false = true ∨
          ∃ p ∈ L, W.getD p.1.val false = true ∧ W.getD (N + p.2.val) false = true)) := by
  induction L with
  | nil => intro o m W _ _ _; simp [extra, finalOut]
  | cons p L ih =>
    intro o m W hW ho hN
    have hu : p.1.val < m := by have := p.1.isLt; omega
    have hv : N + p.2.val < m := by have := p.2.isLt; omega
    simp only [extra, finalOut, List.foldl_cons]
    have hlen : (stepW (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩)
        ⟨GateOp.or, [o, m]⟩).length = m + 2 := by
      simp [stepW]
      omega
    rw [ih (m + 1) (m + 2) _ hlen (by omega) (by omega)]
    have keep : ∀ i < m, (stepW (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩)
        ⟨GateOp.or, [o, m]⟩).getD i false = W.getD i false := by
      intro i hi
      exact prefix_fold [⟨GateOp.and, [p.1.val, N + p.2.val]⟩, ⟨GateOp.or, [o, m]⟩] W i (by omega)
    have top : (stepW (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩)
        ⟨GateOp.or, [o, m]⟩).getD (m + 1) false =
        (W.getD o false || (W.getD p.1.val false && W.getD (N + p.2.val) false)) := by
      have h1 : (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩).length = m + 1 := by
        simp [stepW]
        omega
      have hm : (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩).getD m false =
          (W.getD p.1.val false && W.getD (N + p.2.val) false) := by
        unfold stepW
        rw [getD_snoc, if_neg (by omega), if_pos hW.symm]
        simp [GateOp.eval]
      have hoo : (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩).getD o false = W.getD o false := by
        unfold stepW
        rw [getD_snoc, if_pos (by omega)]
      show ((stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩) ++
        [GateOp.or.eval ([o, m].map fun i =>
          (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩).getD i false)]).getD (m + 1) false = _
      rw [getD_snoc, if_neg (by omega), if_pos h1.symm]
      show GateOp.or.eval [(stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩).getD o false,
        (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩).getD m false] = _
      rw [hoo, hm]
      simp [GateOp.eval]
    rw [top]
    have rest : (∃ p' ∈ L, (stepW (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩)
          ⟨GateOp.or, [o, m]⟩).getD p'.1.val false = true ∧
        (stepW (stepW W ⟨GateOp.and, [p.1.val, N + p.2.val]⟩)
          ⟨GateOp.or, [o, m]⟩).getD (N + p'.2.val) false = true) ↔
        ∃ p' ∈ L, W.getD p'.1.val false = true ∧ W.getD (N + p'.2.val) false = true := by
      constructor
      · rintro ⟨p', hp', h1, h2⟩
        have a1 := p'.1.isLt
        have a2 := p'.2.isLt
        rw [keep _ (by omega)] at h1
        rw [keep _ (by omega)] at h2
        exact ⟨p', hp', h1, h2⟩
      · rintro ⟨p', hp', h1, h2⟩
        have a1 := p'.1.isLt
        have a2 := p'.2.isLt
        refine ⟨p', hp', ?_, ?_⟩
        · rw [keep _ (by omega)]
          exact h1
        · rw [keep _ (by omega)]
          exact h2
    rw [rest]
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.mem_cons, exists_eq_or_imp]
    tauto

end PEqualNP.Outside.L_meta_3264_aux

theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro k n2 E C hE model hC N x9 x10
  obtain ⟨hAO, hRB, hTwo⟩ := model
  have hout : C.output < k + n2 + C.gates.length := by
    by_contra hcon
    obtain ⟨⟨a, b⟩, hab⟩ := hE
    have h0 : PEqualNP.MetaComplexity.circuitFun (k + n2) C (fun _ => true) = false := by
      show (C.wires _).getD C.output false = false
      rw [PEqualNP.Outside.L_meta_3264_aux.wires_eq]
      exact PEqualNP.Outside.L_meta_3264_aux.beyond_fold _ _ _ (by simp; omega)
    have h1 := hC (fun _ => true)
    rw [h0] at h1
    have h3 : decide (∃ (a' : Fin k) (b' : Fin n2), (a', b') ∈ E ∧
        (fun _ : Fin (k + n2) => true) (Fin.castAdd n2 a') = true ∧
        (fun _ : Fin (k + n2) => true) (Fin.natAdd k b') = true) = true :=
      decide_eq_true ⟨a, b, hab, rfl, rfl⟩
    exact Bool.false_ne_true (h1.trans h3)
  let s := C.gates.length
  let L := x10.toList
  let o := PEqualNP.Outside.L_meta_3264_aux.relabel k (k + n2) C.output
  let m := (k + n2) + (k + n2) + s
  let C' : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (PEqualNP.Outside.L_meta_3264_aux.relabelGate k (k + n2)) ++
      PEqualNP.Outside.L_meta_3264_aux.extra (k + n2) o m L,
      PEqualNP.Outside.L_meta_3264_aux.finalOut o m L⟩
  have ho : o < m := by
    show (if C.output < k then C.output else C.output + (k + n2)) < k + n2 + (k + n2) + s
    split_ifs <;> omega
  have hgateAt : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) (hj : j < D.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt D j = D.gates[j] := by
    intro D j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  refine ⟨C', ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact hAO g0 hg0
    · exact (PEqualNP.Outside.L_meta_3264_aux.extra_ok _ _ _ _ g hg).1
  · intro j hj i hi
    rw [hgateAt C' j hj] at hi
    have hlenC' : C'.gates.length = s + (PEqualNP.Outside.L_meta_3264_aux.extra (k + n2) o m L).length := by
      simp [C', s]
    by_cases hjs : j < s
    · have hjs' : j < (C.gates.map (PEqualNP.Outside.L_meta_3264_aux.relabelGate k (k + n2))).length := by
        simpa using hjs
      have hget : C'.gates[j] = PEqualNP.Outside.L_meta_3264_aux.relabelGate k (k + n2) C.gates[j] := by
        show (_ ++ _)[j] = _
        rw [List.getElem_append_left hjs', List.getElem_map]
      rw [hget] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      have hb := hRB j hjs i0 (by rw [hgateAt C j hjs]; exact hi0)
      unfold PEqualNP.Outside.L_meta_3264_aux.relabel
      split_ifs <;> omega
    · have hjs' : (C.gates.map (PEqualNP.Outside.L_meta_3264_aux.relabelGate k (k + n2))).length ≤ j := by
        simp only [List.length_map]
        omega
      have hje : j - s < (PEqualNP.Outside.L_meta_3264_aux.extra (k + n2) o m L).length := by
        omega
      have hget : C'.gates[j] = (PEqualNP.Outside.L_meta_3264_aux.extra (k + n2) o m L)[j - s] := by
        show (_ ++ _)[j] = _
        rw [List.getElem_append_right hjs']
        simp [s]
      rw [hget] at hi
      have := PEqualNP.Outside.L_meta_3264_aux.extra_reads (k + n2) L o m ho (by omega) (j - s) hje i hi
      omega
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      show (g0.inputs.map _).length = 2
      rw [List.length_map]
      exact hTwo g0 hg0
    · exact (PEqualNP.Outside.L_meta_3264_aux.extra_ok _ _ _ _ g hg).2
  · show (C.gates.map _ ++ PEqualNP.Outside.L_meta_3264_aux.extra (k + n2) o m L).length ≤
      C.gates.length + 2 * x10.card
    rw [List.length_append, List.length_map, PEqualNP.Outside.L_meta_3264_aux.extra_length,
      Finset.length_toList]
  · intro z
    have hrel : ∀ i : Fin (k + n2),
        PEqualNP.Outside.L_meta_3264_aux.relabel k (k + n2) i.val < (k + n2) + (k + n2) := by
      intro i
      have := i.isLt
      unfold PEqualNP.Outside.L_meta_3264_aux.relabel
      split_ifs <;> omega
    let x : Fin (k + n2) → Bool := fun i => z ⟨_, hrel i⟩
    let W := C.gates.foldl PEqualNP.Outside.L_meta_3264_aux.stepW (List.ofFn x)
    let W' := (C.gates.map (PEqualNP.Outside.L_meta_3264_aux.relabelGate k (k + n2))).foldl
      PEqualNP.Outside.L_meta_3264_aux.stepW (List.ofFn z)
    have hsim : ∀ i, W'.getD (PEqualNP.Outside.L_meta_3264_aux.relabel k (k + n2) i) false =
        W.getD i false := by
      have hN : N = k + n2 := rfl
      apply PEqualNP.Outside.L_meta_3264_aux.sim
      · simp
      · simp only [List.length_ofFn, hN]
      · intro i
        by_cases hi : i < k + n2
        · have hr : PEqualNP.Outside.L_meta_3264_aux.relabel k (k + n2) i < (k + n2) + (k + n2) :=
            hrel ⟨i, hi⟩
          rw [PEqualNP.Outside.L_meta_3264_aux.getD_ofFn _ _ hr,
            PEqualNP.Outside.L_meta_3264_aux.getD_ofFn _ _ hi]
        · have hr : (k + n2) + (k + n2) ≤ PEqualNP.Outside.L_meta_3264_aux.relabel k (k + n2) i := by
            unfold PEqualNP.Outside.L_meta_3264_aux.relabel
            split_ifs <;> omega
          rw [PEqualNP.Outside.L_meta_3264_aux.getD_ofFn_ge _ _ hr,
            PEqualNP.Outside.L_meta_3264_aux.getD_ofFn_ge _ _ (by omega)]
    have hW'len : W'.length = m := by
      have hN : N = k + n2 := rfl
      simp only [W', PEqualNP.Outside.L_meta_3264_aux.length_fold, List.length_map,
        List.length_ofFn, hN, m, s]
    have hz1 : ∀ u : Fin (k + n2), W'.getD u.val false = z (Fin.castAdd (k + n2) u) := by
      intro u
      have := u.isLt
      rw [PEqualNP.Outside.L_meta_3264_aux.prefix_fold _ _ _ (by simp; omega),
        PEqualNP.Outside.L_meta_3264_aux.getD_ofFn _ _ (by omega)]
      rfl
    have hz2 : ∀ v : Fin (k + n2), W'.getD (k + n2 + v.val) false = z (Fin.natAdd (k + n2) v) := by
      intro v
      have := v.isLt
      rw [PEqualNP.Outside.L_meta_3264_aux.prefix_fold _ _ _ (by simp; omega),
        PEqualNP.Outside.L_meta_3264_aux.getD_ofFn _ _ (by omega)]
      rfl
    have hx1 : ∀ a : Fin k, x (Fin.castAdd n2 a) = z (Fin.castAdd (k + n2) (Fin.castAdd n2 a)) := by
      intro a
      show z _ = z _
      congr 1
      ext
      simp [PEqualNP.Outside.L_meta_3264_aux.relabel]
    have hx2 : ∀ b : Fin n2, x (Fin.natAdd k b) = z (Fin.natAdd (k + n2) (Fin.natAdd k b)) := by
      intro b
      show z _ = z _
      congr 1
      ext
      simp [PEqualNP.Outside.L_meta_3264_aux.relabel]
      omega
    have hoval : W'.getD o false = true ↔
        ∃ (a : Fin k) (b : Fin n2), (a, b) ∈ E ∧
          z (Fin.castAdd (k + n2) (Fin.castAdd n2 a)) = true ∧
          z (Fin.natAdd (k + n2) (Fin.natAdd k b)) = true := by
      rw [hsim C.output]
      have hcf := hC x
      have hcf' : W.getD C.output false = PEqualNP.MetaComplexity.circuitFun (k + n2) C x := rfl
      rw [hcf', hcf, decide_eq_true_iff]
      simp only [hx1, hx2]
    have hval : PEqualNP.MetaComplexity.circuitFun (k + n2 + (k + n2)) C' z =
        ((PEqualNP.Outside.L_meta_3264_aux.extra (k + n2) o m L).foldl
          PEqualNP.Outside.L_meta_3264_aux.stepW W').getD
          (PEqualNP.Outside.L_meta_3264_aux.finalOut o m L) false := by
      show (C'.wires (List.ofFn z)).getD C'.output false = _
      rw [PEqualNP.Outside.L_meta_3264_aux.wires_eq]
      exact congrArg (fun l => List.getD l (PEqualNP.Outside.L_meta_3264_aux.finalOut o m L) false)
        (List.foldl_append (f := PEqualNP.Outside.L_meta_3264_aux.stepW) (b := List.ofFn z)
          (l := C.gates.map (PEqualNP.Outside.L_meta_3264_aux.relabelGate k (k + n2)))
          (l' := PEqualNP.Outside.L_meta_3264_aux.extra (k + n2) o m L))
    rw [hval]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff,
      PEqualNP.Outside.L_meta_3264_aux.extra_val (k + n2) L o m W' hW'len ho (by omega), hoval]
    constructor
    · rintro (⟨a, b, hab, ha, hb⟩ | ⟨p, hp, h1, h2⟩)
      · exact ⟨Fin.castAdd n2 a, Fin.natAdd k b,
          Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩), ha, hb⟩
      · rw [hz1] at h1
        rw [hz2] at h2
        exact ⟨p.1, p.2, Finset.mem_union_right _ (Finset.mem_toList.mp hp), h1, h2⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases Finset.mem_union.mp huv with h | h
      · obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact Or.inl ⟨a, b, hab, hu, hv⟩
      · refine Or.inr ⟨(u, v), Finset.mem_toList.mpr h, ?_, ?_⟩
        · rw [hz1]
          exact hu
        · rw [hz2]
          exact hv
