import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4673_43
    (trim : ∀ n (C : Circuit) (u : Nat), IsAO2 n C → C.output < n+C.size → u < n+C.size → ∃ (D : Circuit) (v : Nat), IsAO2 n D ∧ D.size ≤ C.size ∧ D.output < n+D.size ∧ v < n+D.size ∧ (∀ i < D.size, (gateAt D i).inputs.Nodup ∧ (n+i=D.output ∨ n+i=v ∨ ∃ j<D.size, n+i ∈ (gateAt D j).inputs)) ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) ∧ (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn x)).getD u false)
    (synth : ∃ (C : Circuit) (u : Nat), IsAO2 21 C ∧ C.size ≤ 45 ∧
      let F := fun x : Fin 21 → Bool => ∃ (p : Fin 9) (l : Fin 12), (([1,3,4,5,6,7,9,10,11] : List Nat).getD p.val 0 + l.val + 15)%13 ∈ ([0,1,3,9] : List Nat) ∧ x (Fin.castAdd 12 p) = true ∧ x (Fin.natAdd 9 l) = true
      let M := fun x : Fin 21 → Bool => (x 9 || x 11 || x 17) = true
      let w := fun (x : Fin 21 → Bool) (i : Nat) => (C.wires (List.ofFn x)).getD i false
      ∀ x, (Minimal F x → w x C.output = true) ∧ (Maximal (fun y => ¬ F y) x → w x C.output = false) ∧ (Minimal M x → w x u = true) ∧ (Maximal (fun y => ¬ F y ∧ ¬ M y) x → w x u = false)) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 (21 : ℕ) x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (21 : ℕ) + x1.size ∧ x2 < (21 : ℕ) + x1.size ∧ (∀ x3 < x1.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).inputs.Nodup ∧ ((21 : ℕ) + x3 = x1.output ∨ (21 : ℕ) + x3 = x2 ∨ ∃ x5 < x1.size, (21 : ℕ) + x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).inputs)) ∧ ∀ (x3 : Fin (21 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (9 : ℕ)) (x5 : Fin (12 : ℕ)), ([(1 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ)].getD ↑x4 (0 : ℕ) + ↑x5 + (15 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x3 (Fin.castAdd (12 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (9 : ℕ) x5) = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (9 : Fin (21 : ℕ)) || x3 (11 : Fin (21 : ℕ)) || x3 (17 : Fin (21 : ℕ)))) := by
  have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let run (gs : List Gate) (w : List Bool) := gs.foldl (fun z g => z ++ [g.op.eval (g.inputs.map fun j => z.getD j false)]) w
  have runMono (gs : List Gate) (h : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (w t : List Bool)
      (len : w.length=t.length) (inc : ∀ j, w.getD j false=true → t.getD j false=true) :
      ∀ j, (run gs w).getD j false=true → (run gs t).getD j false=true := by
    induction gs generalizing w t with
    | nil => exact inc
    | cons g gs ih =>
      apply ih (fun g' hg => h g' (List.mem_cons_of_mem _ hg)) _ _ (by simp [len]); intro i
      by_cases lt : i<w.length
      · rw [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (lt.trans_eq len)]; exact inc i
      by_cases eq : i=w.length
      · subst i; simp only [List.getD_eq_getElem?_getD,List.getElem?_concat_length,Option.getD_some]
        rw [len]; simp only [List.getElem?_concat_length,Option.getD_some]
        rcases h _ List.mem_cons_self with op|op
        · simp only [op,andEval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]; exact fun hh a ha => inc a (hh a ha)
        · simp only [op,orEval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]; rintro ⟨a,ha,hh⟩; exact ⟨a,ha,inc a hh⟩
      · rw [List.getD_eq_default _ _ (by simp; omega)]; simp
  have transfer {α : Type} [PartialOrder α] [Finite α] (F M : α → Prop) (A B : α → Bool) (ma : Monotone A) (mb : Monotone B)
      (pos : ∀ x, Minimal F x → A x = true)
      (neg : ∀ x, Maximal (fun y => ¬ F y) x → A x = false)
      (mp : ∀ x, Minimal M x → B x = true)
      (mn : ∀ x, Maximal (fun y => ¬ F y ∧ ¬ M y) x → B x = false) (x : α) :
      (A x = true ↔ F x) ∧ (A x = false → (B x = true ↔ M x)) := by
    classical
    have high (pf : F x) : A x = true := by
      obtain ⟨z,zx,hz⟩ := exists_minimal_le_of_wellFoundedLT F x pf
      exact Bool.le_iff_imp.mp (ma zx) (pos z hz)
    have low (pf : ¬ F x) : A x = false := by
      obtain ⟨z,xz,hz⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => ¬F y) x pf
      cases hx : A x with
      | false => rfl
      | true => have := Bool.le_iff_imp.mp (ma xz) hx; simp [neg z hz] at this
    constructor
    · exact ⟨fun h => by by_contra e; simp [low e] at h,high⟩
    · intro ax
      have nf : ¬ F x := fun f => by simp [high f] at ax
      constructor
      · intro bx; by_contra nm
        obtain ⟨z,xz,hz⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => ¬ F y ∧ ¬ M y) x ⟨nf,nm⟩
        have := Bool.le_iff_imp.mp (mb xz) bx; simp [mn z hz] at this
      · intro m; obtain ⟨z,zx,hz⟩ := exists_minimal_le_of_wellFoundedLT M x m
        exact Bool.le_iff_imp.mp (mb zx) (mp z hz)
  obtain ⟨C,u,ao,sz,cases⟩ := synth
  let F := fun x : Fin 21 → Bool => ∃ (p : Fin 9) (l : Fin 12), (([1,3,4,5,6,7,9,10,11] : List Nat).getD p.val 0 + l.val + 15)%13 ∈ ([0,1,3,9] : List Nat) ∧ x (Fin.castAdd 12 p) = true ∧ x (Fin.natAdd 9 l) = true
  let M := fun x : Fin 21 → Bool => (x 9 || x 11 || x 17) = true
  let w := fun (j : Nat) (x : Fin 21 → Bool) => (C.wires (List.ofFn x)).getD j false
  have len (gs : List Gate) (v : List Bool) : (run gs v).length = v.length + gs.length := by
    induction gs generalizing v with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (v ++ [_])).length = _
      rw [ih]; simp; omega
  have bound (j : Nat) (x : Fin 21 → Bool) (hj : w j x = true) : j < 21+C.size := by
    by_contra! e
    have le : (run C.gates (List.ofFn x)).length ≤ j := by rw [len,List.length_ofFn]; change 21+C.size ≤ j; exact e
    change (run C.gates (List.ofFn x)).getD j false = true at hj
    rw [List.getD_eq_default _ _ le] at hj; contradiction
  have ftop : F (fun _ => true) := ⟨0,0,by decide,rfl,rfl⟩
  obtain ⟨p,_,hp⟩ := exists_minimal_le_of_wellFoundedLT F (fun _ => true) ftop
  obtain ⟨m,_,hm⟩ := exists_minimal_le_of_wellFoundedLT M (fun _ => true) (show M (fun _ => true) from rfl)
  obtain ⟨D,v,dao,dsz,dout,dvb,live,pres⟩ :=
    trim 21 C u ao (bound _ p ((cases p).1 hp)) (bound _ m ((cases m).2.2.1 hm))
  refine ⟨D,v,dao,dsz.trans sz,dout,dvb,live,?_⟩
  have mono (j : Nat) : Monotone (w j) := by
    intro x y xy; apply Bool.le_iff_imp.mpr
    apply runMono C.gates ao.1 (List.ofFn x) (List.ofFn y) (by simp) _ j
    intro i; by_cases hi : i<21
    · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
      simpa only [List.getElem_ofFn] using Bool.le_iff_imp.mp (xy ⟨i,hi⟩)
    · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]; simp
  intro x
  have h := transfer F M (w C.output) (w u) (mono _) (mono _) (fun y => (cases y).1) (fun y => (cases y).2.1) (fun y => (cases y).2.2.1) (fun y => (cases y).2.2.2) x
  rw [(pres x).1,(pres x).2]
  refine ⟨h.1,fun hx => ?_⟩
  exact Bool.eq_iff_iff.mpr (h.2 hx)
