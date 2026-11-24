import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1657_aux

-- Evaluation and replacement lemmas follow the checked L-meta-1513 and L-meta-1460.

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

lemma eval_gate_mono (g : Gate) (f k : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = true → k r = true)
    (ho : g.op = .and ∨ g.op = .or) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map k) = true := by
  rcases ho with ha | ha
  · simp only [ha,GateOp.eval,List.all_map,List.all_eq_true,Function.comp,id]
    exact fun hf r hr => h r hr (hf r hr)
  · simp only [ha,GateOp.eval,List.any_map,List.any_eq_true,Function.comp,id]
    exact fun ⟨r,hr,hv⟩ => ⟨r,hr,h r hr hv⟩

lemma lower {n : ℕ} (gs : List Gate) (j : Fin gs.length)
    (good : ∀ i : Fin gs.length, i ≠ j → (gs.get i).op = .and ∨ (gs.get i).op = .or)
    (x : Fin n → Bool) (w : ℕ) : value (patchC gs j) x w = true → value ⟨gs,0⟩ x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hin : w < n
    · let p : Fin n := ⟨w,hin⟩
      change value _ x p = true → value _ x p = true
      simp only [input_value,imp_self]
    by_cases hbound : w < n + gs.length
    · by_cases hcut : w = n + j.val
      · subst w
        simp [patchC_false]
      · let i : Fin gs.length := ⟨w-n,by omega⟩
        have hne : i ≠ j := by intro e; have ee := congrArg Fin.val e; dsimp [i] at ee; omega
        rw [patchC_other gs j.val x w (by omega) hbound hcut,
          originalGateValue gs 0 x w (by omega) hbound]
        apply eval_gate_mono _ _ _ _ (good i hne)
        intro r _
        by_cases ht : r < w
        · simpa [ht] using ih r ht
        · simp [ht]
    · rw [missing_value (patchC gs j) x w (by rw [patchC_size]; omega)]
      simp

lemma read_false {n : ℕ} (gs : List Gate) (j i : Fin gs.length)
    (jnot : (gs.get j).op = .not) (iand : (gs.get i).op = .and)
    (read : n+j.val ∈ (gs.get i).inputs) (x : Fin n → Bool) :
    value (patchC gs j) x (n+i.val) = false := by
  have hij : i ≠ j := by intro eq; subst i; rw [jnot] at iand; contradiction
  have ne : n+i.val ≠ n+j.val := by intro eq; apply hij; apply Fin.ext; omega
  rw [patchC_other gs j.val x (n+i.val) (by omega) (by have := i.isLt; omega) ne]
  simp only [Nat.add_sub_cancel_left]
  change (gs.get i).op.eval ((gs.get i).inputs.map _) = false
  rw [iand]
  apply Bool.eq_false_iff.mpr
  simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp,id]
  intro hh
  have hx := List.all_eq_true.mp hh (n+j.val) read
  change (if n+j.val < n+i.val then value (patchC gs j) x (n+j.val) else false) = true at hx
  simp [patchC_false] at hx

lemma agree_off_readers {n : ℕ} (gs : List Gate) (j : Fin gs.length) (x : Fin n → Bool)
    (low : ∀ w, value (patchC gs j) x w = true → value ⟨gs,0⟩ x w = true)
    (off : ∀ i : Fin gs.length, n+j.val ∈ (gs.get i).inputs →
      value ⟨gs,0⟩ x (n+i.val) ≠ true)
    (w : ℕ) (hcut : w ≠ n+j.val) : value (patchC gs j) x w = value ⟨gs,0⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w,hn⟩
      change value _ x p = value _ x p
      simp only [input_value]
    by_cases hb : w < n+gs.length
    · let i : Fin gs.length := ⟨w-n,by omega⟩
      have eq : n+i.val=w := by dsimp [i]; omega
      by_cases read : n+j.val ∈ (gs.get i).inputs
      · have hfalse := off i read
        rw [eq] at hfalse
        cases e : value (patchC gs j) x w <;> cases eo : value (Circuit.mk gs 0) x w <;> simp_all
      · rw [patchC_other gs j.val x w (by omega) hb hcut,originalGateValue gs 0 x w (by omega) hb]
        apply patchEvalCongr
        intro r hr
        by_cases lt : r < w
        · have neq : r ≠ n+j.val := fun e => read (e ▸ hr)
          simpa [lt] using ih r lt neq
        · simp [lt]
    · rw [missing_value (patchC gs j) x w (by rw [patchC_size]; omega),
          missing_value ⟨gs,0⟩ x w (by change n + gs.length ≤ w; omega)]

lemma outside {N q : ℕ} (L : Finset (Fin N)) (a b c : Fin N) (hq : 3 ≤ q)
    (hn : N = q^2+q+1) (hl : L.card = q+1) : ∃ p : Fin N, p ∉ L ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c := by
  classical
  by_contra! h
  have sub : Finset.univ ⊆ insert a (insert b (insert c L)) := by
    intro v _
    by_cases hv : v ∈ L
    · simp [hv]
    · by_contra! hh
      simp at hh
      exact hh.1 (by by_contra e; exact hh.2.2.1 (h v hv e hh.2.1))
  have sz := Finset.card_le_card sub
  have ha := Finset.card_insert_le a (insert b (insert c L))
  have hb := Finset.card_insert_le b (insert c L)
  have hc := Finset.card_insert_le c L
  simp only [Finset.card_univ,Fintype.card_fin] at sz
  nlinarith [Nat.mul_le_mul hq hq]

end PEqualNP.Outside.L_meta_1657_aux

open PEqualNP.Outside.L_meta_1657_aux in
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
  intro q N L va vb vc sa sb sc hq hn hcard _ _ _ _ _ _ _ _ _ gs o j h legal _
    jnot unique hj hread correct reads ev patched sev spat vertices _
  let C : Circuit := ⟨gs,0⟩
  let D := patchC gs j.val
  have orig (w : ℕ) (x : Fin N → Bool) : ev w x = value C x w := sev w x
  have cut (w : ℕ) (x : Fin N → Bool) : patched w x = value D x w := spat w x
  have mono (w : ℕ) (x : Fin N → Bool) : patched w x = true → ev w x = true := by
    rw [orig,cut]
    apply lower gs j _ x w
    intro i ne
    have ho := (legal (gs.get i) (List.get_mem ..)).1
    rcases ho with ha | ho | hh
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (ne (unique i hh)).elim
  have same (w : ℕ) (x : Fin N → Bool) (hit : ev (N+h.val) x = true) : patched w x = ev w x := by
    rw [orig] at hit
    rw [orig,cut]
    apply patchC_eq gs j 0 x _ w
    exact not_false_of_input_true gs j h 0 x jnot hj hread hit
  have output_not (t : Fin N) : o t ≠ N+j.val := by
    intro eq
    obtain ⟨p,hp,pa,pb,pc⟩ := outside (L t) va vb vc hq hn (hcard t)
    let x := fun v : Fin N => decide (v=p)
    have ht : value C x (N+h.val) = false := by
      apply Bool.eq_false_iff.mpr
      intro hv
      have hv' : ev (N+h.val) x = true := (orig _ _).trans hv
      exact ((vertices p).mp hv').elim pa (fun h' => h'.elim pb pc)
    have hev : value C x (N+j.val) = true := by
      obtain ⟨r,hr⟩ := hread
      rw [originalGateValue gs 0 x (N+j.val) (by omega) (by have := j.isLt; omega)]
      simp only [Nat.add_sub_cancel_left]
      change (gs.get j).op.eval ((gs.get j).inputs.map _) = true
      rw [jnot,hr]
      have lt : N+h.val < N+j.val := Nat.add_lt_add_left hj N
      simp [GateOp.eval,lt,show value ⟨gs,0⟩ x (N+h.val) = false from ht]
    have no : value C x (o t) = false := by
      change (Circuit.mk gs (o t)).eval (List.ofFn x) = false
      rw [correct]
      simp [x,hp]
    rw [eq,hev] at no
    contradiction
  refine ⟨mono,same,?_,?_,?_⟩
  · intro i x hr
    rw [cut]
    exact read_false gs j i jnot (reads i hr) hr x
  · intro t p hp hp0
    by_contra! none
    let x := fun v : Fin N => decide (v=p)
    have z : value D x (o t) = false := (cut _ _).symm.trans hp0
    have otrue : value C x (o t) = true := by
      change (Circuit.mk gs (o t)).eval (List.ofFn x) = true
      rw [correct]
      exact decide_eq_true ⟨p,hp,by simp [x]⟩
    have ho := agree_off_readers gs j x (fun w hv => (orig w x).symm.trans (mono w x ((cut w x).trans hv)))
      (fun i hr hv => none i hr ((orig _ x).trans hv)) (o t) (output_not t)
    exact Bool.noConfusion (z.symm.trans (ho.trans otrue))
  · intro t v hv hvt
    have hhv : ev (N+h.val) (fun u : Fin N => decide (u=v)) = true :=
      (vertices v).mpr (by simpa [Finset.mem_insert,Finset.mem_singleton] using hv)
    rw [same _ _ hhv,sev,correct]
    exact decide_eq_true ⟨v,hvt,by simp⟩
