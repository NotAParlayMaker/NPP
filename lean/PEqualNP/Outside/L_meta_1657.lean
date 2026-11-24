import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1657

-- Evaluation and replacement lemmas follow L_meta_1513 and L_meta_986.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

def patchC (gates : List Gate) (j : ℕ) : Circuit :=
  ⟨gates.set j ⟨GateOp.or, []⟩, 0⟩

lemma patchC_size (gates : List Gate) (j : ℕ) : (patchC gates j).size = gates.length := by
  simp [patchC, Circuit.size]

lemma patchC_good (gates : List Gate) (j : Fin gates.length)
    (valid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (unique : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j) :
    ∀ g ∈ (patchC gates j.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [patchC] using hk
  by_cases hkj : j.val = k
  · simp [patchC, hkj]
  · have same : (patchC gates j.val).gates[k] = gates[k] := by simp [patchC, hkj]
    rw [same]
    obtain ⟨hop, hfan⟩ := valid gates[k] (List.getElem_mem _)
    refine ⟨?_, hfan⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (unique ⟨k, hk'⟩ hop)).symm hkj

lemma patchC_false {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool) :
    value (patchC gates j.val) x (n + j.val) = false := by
  have h := gate_value (patchC gates j.val) x (n + j.val) (by omega)
    (by rw [patchC_size]; omega)
  simp only at h
  rw [h]
  simp [patchC, GateOp.eval]

lemma patchC_other {n : ℕ} (gates : List Gate) (j : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + j) :
    value (patchC gates j) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (patchC gates j) x r else false) := by
  have h := gate_value (patchC gates j) x w hn (by rw [patchC_size]; exact hw)
  simp only at h
  rw [h]
  have same : (patchC gates j).gates[w - n]'(by simp [patchC]; omega) =
      gates[w - n]'(by omega) := by
    simp only [patchC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [same]

lemma originalGateValue {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma patchEvalCongr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

lemma patchC_eq {n : ℕ} (gates : List Gate) (j : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (hjFalse : value ⟨gates, o⟩ x (n + j.val) = false) (w : ℕ) :
    value (patchC gates j.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h₁ := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h₂ := input_value (patchC gates j.val) x ⟨w, hn⟩
      simp only at h₁ h₂
      rw [h₁, h₂]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + j.val
      · rw [hne, hjFalse]
        exact patchC_false gates j x
      · rw [originalGateValue gates o x w (by omega) hw,
          patchC_other gates j.val x w (by omega) hw hne]
        apply patchEvalCongr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (patchC gates j.val) x w (by rw [patchC_size]; omega)]

lemma not_false_of_input_true {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (o : ℕ) (x : Fin n → Bool)
    (hop : (gates.get j).op = GateOp.not) (hlt : h < j)
    (hread : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r)
    (hhTrue : value ⟨gates, o⟩ x (n + h.val) = true) :
    value ⟨gates, o⟩ x (n + j.val) = false := by
  obtain ⟨r, hr⟩ := hread
  have hj : n + j.val < n + gates.length := by omega
  have hw : n + h.val < n + j.val := by exact Nat.add_lt_add_left hlt n
  have he := originalGateValue gates o x (n + j.val) (by omega) hj
  simp only [Nat.add_sub_cancel_left] at he
  rw [he]
  change (gates.get j).op.eval ((gates.get j).inputs.map fun w =>
    if w < n + j.val then value ⟨gates, o⟩ x w else false) = false
  rw [hop, hr]
  simp [hw, hhTrue, GateOp.eval]

lemma repl_eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx r hr => h r hr (hx r hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact fun ⟨r, hr, hx⟩ => ⟨r, hr, h r hr hx⟩

lemma comparePatch {n} (gs : List Gate) (j : Fin gs.length) (x : Fin n → Bool)
    (ops : ∀ k : Fin gs.length, k ≠ j → (gs.get k).op = GateOp.and ∨ (gs.get k).op = GateOp.or)
    (w : ℕ) : value (patchC gs j) x w = true → value ⟨gs,0⟩ x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · exact (input_value (patchC gs j) x ⟨w,hn⟩).trans (input_value ⟨gs,0⟩ x ⟨w,hn⟩).symm ▸ id
    by_cases hw : w < n + gs.length
    · by_cases hj : w = n+j.val
      · subst w
        simp [patchC_false]
      · rw [patchC_other gs j x w (by omega) hw hj, originalGateValue gs 0 x w (by omega) hw]
        apply repl_eval_mono _ (ops ⟨w-n, by omega⟩ (fun e => hj (by have := congrArg Fin.val e; simp at this; omega)))
        intro r hr
        by_cases h : r < w
        · simpa [h] using ih r h
        · simp [h]
    · rw [missing_value (patchC gs j) x w (by rw [patchC_size]; omega)]
      simp

lemma noChange {n} (gs : List Gate) (j : Fin gs.length) (x : Fin n → Bool)
    (off : ∀ i : Fin gs.length, n+j.val ∈ (gs.get i).inputs → value ⟨gs,0⟩ x (n+i.val) = false)
    (leq : ∀ w, value (patchC gs j) x w = true → value ⟨gs,0⟩ x w = true)
    (w : ℕ) : w ≠ n+j.val → value (patchC gs j) x w = value ⟨gs,0⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hj
    by_cases hn : w < n
    · exact (input_value (patchC gs j) x ⟨w,hn⟩).trans (input_value ⟨gs,0⟩ x ⟨w,hn⟩).symm
    by_cases hw : w < n + gs.length
    · let k : Fin gs.length := ⟨w-n,by omega⟩
      have eqw : n+k.val = w := by dsimp [k]; omega
      by_cases read : n+j.val ∈ (gs.get k).inputs
      · have z := off k read
        rw [eqw] at z
        cases e : value (patchC gs j) x w
        · exact z.symm
        · exact (leq w e).symm
      · rw [patchC_other gs j x w (by omega) hw hj, originalGateValue gs 0 x w (by omega) hw]
        apply patchEvalCongr
        intro r hr
        by_cases lt : r < w
        · simp only [lt, ↓reduceIte]
          apply ih r lt
          rintro rfl
          exact read hr
        · simp [lt]
    · rw [missing_value (patchC gs j) x w (by rw [patchC_size]; omega),
          missing_value ⟨gs,0⟩ x w (by simp only [Circuit.size]; omega)]

end PEqualNP.Outside.L_meta_1657
open PEqualNP.Outside.L_meta_1657 in
theorem PEqualNP.Outside.L_meta_1657 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    ∀ ev ev' : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w⟩ (List.ofFn x)) →
    (∀ p : Fin N, ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true) ∧ (∀ (w : ℕ) (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ev' w x = ev w x) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false) ∧
    (∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false → ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true) ∧
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun uu : Fin N => decide (uu = v)) = true := by
  intro q N L a b c sa sb sc hq hN card _ _ _ _ _ _ _ _ _ gs o j h legal back hn uniq hlt read correct readers ev ev' orig patch tri _
  have ops (k : Fin gs.length) (ne : k ≠ j) : (gs.get k).op = GateOp.and ∨ (gs.get k).op = GateOp.or := by
    rcases (legal _ (List.get_mem gs k)).1 with z | z | z
    · exact Or.inl z
    · exact Or.inr z
    · exact (ne (uniq k z)).elim
  have lower (w x) : ev' w x = true → ev w x = true := by
    rw [patch, orig]
    exact comparePatch gs j x ops w
  have same (w x) (hot : ev (N+h.val) x = true) : ev' w x = ev w x := by
    rw [patch,orig]
    rw [orig] at hot
    exact patchC_eq gs j 0 x (not_false_of_input_true gs j h 0 x hn hlt read hot) w
  have zero (i : Fin gs.length) (x : Fin N → Bool) (hi : N+j.val ∈ (gs.get i).inputs) : ev' (N+i.val) x = false := by
    have ne : N+i.val ≠ N+j.val := by have := back i _ hi; omega
    rw [patch]
    change value (patchC gs j) x (N+i.val) = false
    rw [patchC_other gs j x _ (by omega) (by omega) ne]
    simp only [Nat.add_sub_cancel_left]
    change (gs.get i).op.eval _ = false
    rw [readers i hi]
    by_contra! hh
    have hot : (GateOp.and.eval ((gs.get i).inputs.map fun r => if r < N+i.val then value (patchC gs j) x r else false)) = true := by simpa using hh
    simp only [GateOp.eval,List.all_eq_true,id_eq] at hot
    have zz := hot _ (List.mem_map.mpr ⟨_,hi,rfl⟩)
    simp [back i _ hi,patchC_false] at zz
  have vertex (t P) : ev (o t) (fun v => decide (v=P)) = decide (P ∈ L t) := by
    rw [orig,correct]
    simp
  have notOut (t : Fin N) : o t ≠ N+j.val := by
    intro eqo
    have sub : Finset.univ ⊆ L t ∪ ({a,b,c} : Finset (Fin N)) := by
      intro p _
      by_contra hp
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      have cold : ev (N+h.val) (fun v => decide (v=p)) = false := by
        cases e : ev (N+h.val) (fun v => decide (v=p))
        · rfl
        · have := (tri p).mp e
          tauto
      obtain ⟨r,hr⟩ := read
      have vv := originalGateValue gs 0 (fun v : Fin N => decide (v=p)) (N+j.val) (by omega) (by omega)
      simp only [Nat.add_sub_cancel_left] at vv
      change value ⟨gs,0⟩ _ _ = (gs.get j).op.eval _ at vv
      have z := vertex t p
      rw [eqo,orig] at z
      rw [orig] at cold
      change value ⟨gs,0⟩ _ _ = false at cold
      change value ⟨gs,0⟩ _ _ = _ at z
      change gs[j.val].inputs = _ at hr
      rw [vv,hn,hr] at z
      simp [GateOp.eval,Nat.add_lt_add_left hlt N,cold,hp.1] at z
    have h1 := Finset.card_le_card sub
    have h2 := Finset.card_union_le (L t) ({a,b,c} : Finset (Fin N))
    have h3 : ({a,b,c} : Finset (Fin N)).card ≤ 3 := by
      have := Finset.card_insert_le a ({b,c} : Finset (Fin N))
      have := Finset.card_insert_le b ({c} : Finset (Fin N))
      simp only [Finset.card_singleton] at *
      omega
    rw [Finset.card_univ,Fintype.card_fin] at h1
    rw [card] at h2
    nlinarith
  refine ⟨lower,same,zero,?_,?_⟩
  · intro t P hP lost
    by_contra! no
    let x : Fin N → Bool := fun v => decide (v=P)
    have off (i : Fin gs.length) (hi : N+j.val ∈ (gs.get i).inputs) : value ⟨gs,0⟩ x (N+i.val) = false := by
      have z := no i hi
      rw [orig] at z
      change value ⟨gs,0⟩ x (N+i.val) ≠ true at z
      simpa using z
    have z := noChange gs j x off (comparePatch gs j x ops) (o t) (notOut t)
    change ev' (o t) x = false at lost
    rw [patch] at lost
    change value (patchC gs j) x (o t) = false at lost
    rw [z] at lost
    have v := vertex t P
    rw [orig] at v
    change value ⟨gs,0⟩ x (o t) = _ at v
    simp [hP,lost] at v
  · intro t v hv hit
    rw [same,vertex]
    · simp [hit]
    · apply (tri v).mpr
      simpa using hv
