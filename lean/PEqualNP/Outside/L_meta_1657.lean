import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1657

open PEqualNP.CircuitLowerBounds

def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map (fun w => xs.getD w false))]

def wire (gs : List Gate) (xs : List Bool) (w : ℕ) : Bool :=
  (gs.foldl step xs).getD w false

lemma extend (gs : List Gate) (xs : List Bool) :
    ∃ ys, gs.foldl step xs = xs ++ ys ∧ ys.length = gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨ys, hy, hl⟩ := ih (step xs g)
    refine ⟨g.op.eval (g.inputs.map (fun w => xs.getD w false)) :: ys, ?_, by simp [hl]⟩
    simpa [step, List.foldl_cons, List.append_assoc] using hy

lemma original (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    wire gs xs w = xs.getD w false := by
  obtain ⟨ys, hy, _⟩ := extend gs xs
  simp [wire, hy, List.getD, List.getElem?_append, hw]

lemma outside (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : xs.length + gs.length ≤ w) :
    wire gs xs w = false := by
  obtain ⟨ys, hy, hl⟩ := extend gs xs
  have hk : (xs ++ ys).length ≤ w := by simpa [hl] using hw
  simp [wire, hy, List.getD, List.getElem?_eq_none hk]

lemma atGate (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < gs.length)
    (valid : ∀ a ∈ gs[i].inputs, a < xs.length + i) :
    wire gs xs (xs.length + i) = gs[i].op.eval (gs[i].inputs.map (wire gs xs)) := by
  induction gs generalizing xs i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at valid ⊢
      have he : g.inputs.map (wire (g :: gs) xs) = g.inputs.map (fun w => xs.getD w false) :=
        List.map_congr_left (fun w hw => original _ _ _ (valid w hw))
      rw [he]
      change wire gs (step xs g) xs.length = _
      rw [original _ _ _ (by simp [step])]
      simp [step, List.getD]
    | succ k =>
      have hk : k < gs.length := by simpa using hi
      have hv : ∀ a ∈ gs[k].inputs, a < (step xs g).length + k := by
        intro a ha
        have hh := valid a ha
        simpa [step, Nat.add_assoc, Nat.add_comm 1 k] using hh
      have hres := ih (step xs g) k hk hv
      change wire gs (step xs g) (xs.length + (k + 1)) = gs[k].op.eval (gs[k].inputs.map (wire gs (step xs g)))
      have hlen : (step xs g).length + k = xs.length + (k + 1) := by simp [step]; omega
      rw [hlen] at hres
      exact hres

lemma missingPoint (q N : ℕ) (hq : 3 ≤ q) (hN : N = q ^ 2 + q + 1)
    (s : Finset (Fin N)) (hs : s.card = q + 1) (a b c : Fin N) :
    ∃ p : Fin N, p ∉ s ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c := by
  classical
  by_contra! hn
  have ht : (Finset.univ : Finset (Fin N)) ⊆ insert a (insert b (insert c s)) := by
    intro p _
    by_cases hp : p ∈ s
    · simp [hp]
    · by_contra hm
      simp only [Finset.mem_insert, not_or] at hm
      exact hm.2.2.1 (hn p hp hm.1 hm.2.1)
  have hcard := Finset.card_le_card ht
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have h1 := Finset.card_insert_le a (insert b (insert c s))
  have h2 := Finset.card_insert_le b (insert c s)
  have h3 := Finset.card_insert_le c s
  have hq2 : 9 ≤ q ^ 2 := by nlinarith [Nat.mul_self_le_mul_self hq]
  omega

lemma wireInd {gs : List Gate} {N : ℕ} (R : ℕ → Prop)
    (valid : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < N + i.val)
    (base : ∀ w, (w < N ∨ N + gs.length ≤ w) → R w)
    (next : ∀ i : Fin gs.length, (∀ a ∈ (gs.get i).inputs, R a) → R (N + i.val)) :
    ∀ w, R w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlo : w < N
    · exact base _ (Or.inl hlo)
    by_cases hhi : N + gs.length ≤ w
    · exact base _ (Or.inr hhi)
    let i : Fin gs.length := ⟨w - N, by omega⟩
    have he : N + i.val = w := by dsimp [i]; omega
    rw [← he]
    exact next i (fun a ha => ih a (he ▸ valid i a ha))

lemma monoGate (g : Gate) (f k : ℕ → Bool) (hb : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ w ∈ g.inputs, f w = true → k w = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map k) = true := by
  rcases hb with hb | hb
  · simpa [hb, GateOp.eval, List.all_eq_true] using
      (fun (u : ∀ w ∈ g.inputs, f w = true) w hw => h w hw (u w hw))
  · simp [hb, GateOp.eval, List.any_eq_true]
    intro w hw hh
    exact ⟨w, hw, h w hw hh⟩

lemma evalGate {N : ℕ} (gs : List Gate) (i : Fin gs.length) (x : Fin N → Bool)
    (valid : ∀ a ∈ (gs.get i).inputs, a < N + i.val) :
    Circuit.eval ⟨gs,N+i.val⟩ (List.ofFn x) = (gs.get i).op.eval
      ((gs.get i).inputs.map (fun a => Circuit.eval ⟨gs,a⟩ (List.ofFn x))) := by
  have res := atGate gs (List.ofFn x) i.val i.isLt (by simpa using valid)
  change wire gs (List.ofFn x) (N + i.val) = gs[i.val].op.eval (gs[i.val].inputs.map (wire gs (List.ofFn x)))
  simpa only [List.length_ofFn] using res

end PEqualNP.Outside.L_meta_1657

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
  intro q N L va vb vc sa sb sc hq hN hcard _ _ _ _ _ _ _ _ _ gs o j h hb wf hj uniq _ hin comp readers e f he hf tri _
  let z := N + j.val
  let modified := gs.set j.val (⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ : PEqualNP.CircuitLowerBounds.Gate)
  have glen : modified.length = gs.length := by simp [modified]
  have ix (i : Fin gs.length) : i.val < modified.length := glen.symm ▸ i.isLt
  have old (i : Fin gs.length) (x : Fin N → Bool) :
      e (N+i.val) x = (gs.get i).op.eval ((gs.get i).inputs.map (fun a => e a x)) := by
    simp only [he]
    exact PEqualNP.Outside.L_meta_1657.evalGate gs i x (wf i)
  have fresh (i : Fin gs.length) (x : Fin N → Bool) (hv : ∀ a ∈ modified[i.val].inputs, a < N + i.val) :
      f (N+i.val) x = modified[i.val].op.eval (modified[i.val].inputs.map (fun a => f a x)) := by
    simp only [hf]
    exact PEqualNP.Outside.L_meta_1657.evalGate modified ⟨i.val,ix i⟩ x hv
  have editj : modified[j.val] = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by simp [modified]
  have other (i : Fin gs.length) (hi : i ≠ j) : modified[i.val] = gs.get i := by
    have hne : j.val ≠ i.val := fun hh => hi (Fin.ext hh.symm)
    simp [modified, hne, List.get_eq_getElem]
  have newj (x : Fin N → Bool) : f z x = false := by
    have r := fresh j x (by rw [editj]; simp)
    simpa [editj, PEqualNP.CircuitLowerBounds.GateOp.eval, z] using r
  have normal (i : Fin gs.length) (hi : i ≠ j) (x : Fin N → Bool) :
      f (N+i.val) x = (gs.get i).op.eval ((gs.get i).inputs.map (fun a => f a x)) := by
    have r := fresh i x (by rw [other i hi]; exact wf i)
    rwa [other i hi] at r
  obtain ⟨tail, htail⟩ := hin
  have oldj (x : Fin N → Bool) : e z x = !(e (N+h.val) x) := by
    have r := old j x
    rw [hj, htail] at r
    exact r
  have base (w : ℕ) (x : Fin N → Bool) (hw : w < N ∨ N + gs.length ≤ w) : f w x = e w x := by
    rw [hf, he]
    change PEqualNP.Outside.L_meta_1657.wire modified (List.ofFn x) w = PEqualNP.Outside.L_meta_1657.wire gs (List.ofFn x) w
    rcases hw with hl | hh
    · rw [PEqualNP.Outside.L_meta_1657.original _ _ _ (by simpa using hl), PEqualNP.Outside.L_meta_1657.original _ _ _ (by simpa using hl)]
    · rw [PEqualNP.Outside.L_meta_1657.outside _ _ _ (by simpa only [List.length_ofFn,glen] using hh),
          PEqualNP.Outside.L_meta_1657.outside _ _ _ (by simpa only [List.length_ofFn] using hh)]
  have eqInputs (i : Fin gs.length) (hi : i ≠ j) (x : Fin N → Bool)
      (ha : ∀ a ∈ (gs.get i).inputs, f a x = e a x) : f (N+i.val) x = e (N+i.val) x := by
    rw [normal i hi, old i]
    rw [List.map_congr_left ha]
  have mono (w : ℕ) (x : Fin N → Bool) : f w x = true → e w x = true := by
    apply PEqualNP.Outside.L_meta_1657.wireInd (fun a => f a x = true → e a x = true) wf _ _ w
    · intro a ha
      rw [base a x ha]
      exact id
    · intro i ih
      by_cases hij : i = j
      · subst i
        rw [show f (N+j.val) x = false from newj x]
        simp
      have hops := (hb (gs.get i) (List.get_mem gs i)).1
      have hn := fun hnot => hij (uniq i hnot)
      rw [normal i hij, old i]
      apply PEqualNP.Outside.L_meta_1657.monoGate _ _ _ _ ih
      tauto
  have same (w : ℕ) (x : Fin N → Bool) (hh : e (N+h.val) x = true) : f w x = e w x := by
    apply PEqualNP.Outside.L_meta_1657.wireInd (fun a => f a x = e a x) wf (fun a ha => base a x ha) _ w
    intro i ih
    by_cases hij : i = j
    · subst i
      change f z x = e z x
      rw [newj, oldj, hh]
      rfl
    exact eqInputs i hij x ih
  have reader (i : Fin gs.length) (x : Fin N → Bool) (mem : z ∈ (gs.get i).inputs) : f (N+i.val) x = false := by
    have hi : i ≠ j := by intro hij; subst i; have bad := wf j z mem; exact (Nat.lt_irrefl _ bad)
    rw [normal i hi, readers i mem]
    change ((gs.get i).inputs.map (fun a => f a x)).all id = false
    have hm : false ∈ (gs.get i).inputs.map (fun a => f a x) := List.mem_map.mpr ⟨z, mem, newj x⟩
    simpa [List.all_eq_false] using hm
  have singleton (t p : Fin N) : e (o t) (fun v => decide (v = p)) = decide (p ∈ L t) := by
    rw [he, comp]
    simp
  have neq (t : Fin N) : o t ≠ z := by
    intro ho
    obtain ⟨p,hp,ha,hb',hc⟩ := PEqualNP.Outside.L_meta_1657.missingPoint q N hq hN (L t) (hcard t) va vb vc
    have hn : e (N+h.val) (fun v => decide (v = p)) = false := by
      cases hv : e (N+h.val) (fun v => decide (v = p)) with
      | false => rfl
      | true => exact False.elim (by simpa [ha,hb',hc] using (tri p).mp hv)
    have hh := singleton t p
    rw [ho, oldj, hn] at hh
    simp [hp] at hh
  refine ⟨mono, same, reader, ?_, ?_⟩
  · intro t p hp hfalse
    classical
    by_contra! noReader
    let x : Fin N → Bool := fun v => decide (v = p)
    have away (w : ℕ) : w ≠ z → f w x = e w x := by
      apply PEqualNP.Outside.L_meta_1657.wireInd (fun a => a ≠ z → f a x = e a x) wf (fun a ha _ => base a x ha) _ w
      intro i ih hw
      have hi : i ≠ j := fun eij => hw (eij ▸ rfl)
      by_cases hm : z ∈ (gs.get i).inputs
      · rw [reader i x hm]
        symm
        simpa [x] using noReader i hm
      · exact eqInputs i hi x (fun a ha => ih a ha (fun haz => hm (haz ▸ ha)))
    have hh := away (o t) (neq t)
    rw [show e (o t) x = true by simpa [hp,x] using singleton t p] at hh
    exact Bool.noConfusion (hh.symm.trans hfalse)
  · intro t v hv hp
    have hv' : v = va ∨ v = vb ∨ v = vc := by simpa using hv
    rw [same _ _ ((tri v).mpr hv'), singleton]
    simp [hp]
