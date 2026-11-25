import Mathlib.Data.List.GetD
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_3614_722
 (blur : ∀ (C : Circuit) (n i w : ℕ) (u v : List Bool), u.length = n → v.length = n →
    (∀ j, j ≠ i → u.getD j false = v.getD j false) →
    (∀ g ∈ C.gates.take (w+1-n), i ∉ g.inputs) →
    ∀ j ≤ w, j ≠ i → (C.wires u).getD j false = (C.wires v).getD j false)
 (peel : ∀ (C : Circuit) (n w : ℕ), FanInTwo C → n ≤ w → w < C.output →
    C.output < n+C.size → ∃ (P : Circuit) (t b : Bool) (S : List ℕ),
    FanInTwo P ∧ P.size < C.size ∧ w < n+P.size ∧
    P.gates.take (w+1-n) = C.gates.take (w+1-n) ∧
    S.length ≤ 2 ∧ (t ≠ b → S.length ≤ 1) ∧ ∀ u : List Bool, u.length = n →
      (P.wires u).getD w false = (C.wires u).getD w false ∧
      (C.eval u = t ↔ ∀ j ∈ S, (P.wires u).getD j false = b))
 (geometry : let F := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))
    let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
    ∀ (i : Fin 9) (k : ℕ) (b t d : Bool), k < 10 → i ≠ 0 → i ≠ 6 →
    (∀ x, (x i = b ∨ F x ≠ F (Function.update x i b)) → F x = t →
      (row x).getD k false = d) → k = i.val ∧ t = b ∧ d = b)
 (boundary : let F := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))
    let row := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
    ∀ (i : Fin 9) (P : Circuit) (w : ℕ) (b t d : Bool) (S : List ℕ),
    let V := fun (x : Fin 9 → Bool) (j : ℕ) => (P.wires (row x)).getD j false
    i ≠ 0 → i ≠ 6 → FanInTwo P → P.size ≤ 12 → 10 ≤ w → w < 10+P.size →
    (∀ g ∈ P.gates.take (w+1-10), i.val ∉ g.inputs) →
    S.length ≤ 2 → (t ≠ d → S.length ≤ 1) →
    (∀ j ∈ S, j < 10 → j = i.val ∧ t = b ∧ d = b) →
    (∀ x, F x ≠ F (Function.update x i b) → V x w ≠ b) →
    ∃ x, (x i = b ∨ V x w ≠ b) ∧ ¬(F x = t ↔ ∀ j ∈ S, V x j = d)) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < (10 : ℕ) + x4.size →               (∀ x13 ∈ List.take (x5 + (1 : ℕ) - (10 : ℕ)) x4.gates, ↑x3 ∉ x13.inputs) →                 (∀ (x14 x15 : Fin (9 : ℕ) → Bool), (∀ (x16 : Fin (9 : ℕ)), x16 ≠ x3 → x14 x16 = x15 x16) → x1 x14 ≠ x1 x15 → (x4.wires (x2 x14)).getD x5 Bool.false = !x6) →                   ∃ (x15 : Fin (9 : ℕ) → Bool),                     have x16 : Bool := (x4.wires (x2 x15)).getD x5 Bool.false;                     x4.eval ((x2 x15).set (↑x3) (if x6 = Bool.true then x15 x3 || x16 else x15 x3 && x16)) ≠ x1 x15 := by
  intro F row i C w b i0 i6 fan sz lb ub clean sens
  classical
  by_contra! agree
  have fixed (x : Fin 9 → Bool) (h : x i = b ∨ (C.wires (row x)).getD w false ≠ b) :
      C.eval (row x) = F x := by
    have val := Classical.not_not.mp (agree x)
    have mask : (if b = true then x i || (C.wires (row x)).getD w false else x i && (C.wires (row x)).getD w false) = x i := by
      revert h
      cases b <;> cases x i <;> cases (C.wires (row x)).getD w false <;> decide
    change C.eval ((row x).set i.val _) = F x at val
    rw [mask] at val
    have hrow : (row x)[i.val]? = some (x i) := by
      simp only [row,List.getElem?_append_left (by simp : i.val < (List.ofFn x).length),List.getElem?_ofFn,dite_eq_left i.isLt]
    have he : i.val < (row x).length := by simpa only [row,List.length_append,List.length_ofFn,List.length_singleton] using (Nat.lt_trans i.isLt (by decide : 9 < 9+1))
    have ee : (row x)[i.val] = x i := by simpa [List.getElem?_eq_getElem he] using hrow
    rw [←ee,List.set_getElem_self he] at val
    exact val
  have primal : ∃ u v : Fin 9 → Bool, (∀ j, j ≠ i → u j = v j) ∧ F u ≠ F v := by
    obtain ⟨k,e⟩ := (show ∀ a : Fin 9, ∃ k : Fin 9,
      F (fun j => decide (j = k)) ≠ F (fun j => decide (j = k ∨ j = a)) by decide +kernel) i
    exact ⟨fun j => decide (j=k),fun j => decide (j=k ∨ j=i),fun j h => by simp [h],e⟩
  obtain ⟨u,v,diff,opp⟩ := primal
  have fu := fixed u (Or.inr (by rw [sens u v diff opp]; cases b <;> decide))
  have fv := fixed v (Or.inr (by rw [sens v u (fun j h => (diff j h).symm) opp.symm]; cases b <;> decide))
  have rows (x : Fin 9 → Bool) : (row x).length = 10 := by simp [row]
  have length (L : List Gate) (z : List Bool) : ((Circuit.mk L 0).wires z).length = z.length+L.length := by
    induction L generalizing z with
    | nil => rfl
    | cons g L ih =>
      change ((Circuit.mk L 0).wires (z ++ [_])).length = _
      rw [ih]; simp; omega
  have preserve (L : List Gate) (z : List Bool) (j : ℕ) (h : j < z.length) :
      ((Circuit.mk L 0).wires z).getD j false = z.getD j false := by
    induction L generalizing z with
    | nil => rfl
    | cons g L ih =>
      change ((Circuit.mk L 0).wires (z ++ [_])).getD j false = _
      rw [ih _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]
  have inputWire (D : Circuit) (x : Fin 9 → Bool) (j : Fin 9) :
      (D.wires (row x)).getD j.val false = x j := by
    rw [show (D.wires (row x)).getD j.val false = _ from preserve D.gates _ _ (by rw [rows]; exact Nat.lt_trans j.isLt (by decide))]
    simp only [row,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp : j.val < (List.ofFn x).length),List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some]
  have outOfRange (D : Circuit) (u v : List Bool) (hu : u.length = 10) (hv : v.length = 10)
      (e : 10+D.size ≤ D.output) : D.eval u = D.eval v := by
    have a : (D.wires u).length = 10+D.size := (length D.gates u).trans (by rw [hu]; rfl)
    have c : (D.wires v).length = 10+D.size := (length D.gates v).trans (by rw [hv]; rfl)
    exact (List.getD_eq_default _ false (a.trans_le e)).trans (List.getD_eq_default _ false (c.trans_le e)).symm
  have early : C.output ≠ i.val := by
    obtain ⟨x,hx,hF⟩ := (show ∀ (i : Fin 9) (b : Bool), ∃ c : Bool,
      let x := fun j : Fin 9 => if j = i then b else c
      x i = b ∧ F x ≠ b by decide +kernel) i b
    let z := fun j : Fin 9 => if j = i then b else x
    have hz := fixed z (Or.inl hx)
    intro e
    have input : (C.wires (row z)).getD i.val false = z i := by
      exact inputWire C z i
    change (C.wires (row z)).getD C.output false = F z at hz
    rw [e,input,show z i = b from hx] at hz
    exact hF hz.symm
  have index : ∀ j, j ≠ i.val → (row u).getD j false = (row v).getD j false := by
    intro j hj
    by_cases small : j < 9
    · let a : Fin 9 := ⟨j,small⟩
      have eq := diff a (by intro h; exact hj (congrArg Fin.val h))
      simpa only [row,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using small : j < (List.ofFn u).length),
        List.getElem?_append_left (by simpa using small : j < (List.ofFn v).length),List.getElem?_ofFn,dite_eq_left small,Option.getD_some,a] using eq
    · have a := diff 0 i0.symm
      have b' := diff 6 i6.symm
      simp only [row,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simpa using Nat.le_of_not_gt small : (List.ofFn u).length ≤ j),
        List.getElem?_append_right (by simpa using Nat.le_of_not_gt small : (List.ofFn v).length ≤ j),List.length_ofFn,a,b']
  have past : w < C.output := by
    by_contra! e
    exact opp (fu.symm.trans ((blur C 10 i.val w _ _ (rows u) (rows v) index clean _ e early).trans fv))
  have legal : C.output < 10+C.size := by
    by_contra! e
    exact opp (fu.symm.trans ((outOfRange C _ _ (rows u) (rows v) e).trans fv))
  obtain ⟨P,t,d,S,pfan,count,tap,pre,arity,unary,sem⟩ := peel C 10 w fan lb past legal
  have neutral (x : Fin 9 → Bool) (h : F x ≠ F (Function.update x i b)) :
      (C.wires (row x)).getD w false ≠ b := by
    rw [sens x _ (fun j hj => by simp [Function.update_of_ne hj]) h]
    cases b <;> decide
  have pinRule (j : ℕ) (mem : j ∈ S) (base : j < 10) : j = i.val ∧ t = b ∧ d = b := by
    apply geometry i j b t d base i0 i6
    intro x active target
    change F x = t at target
    have obs := fixed x (active.imp_right (neutral x))
    have h := ((sem _ (rows x)).2.mp (obs.trans target)) j mem
    exact (preserve P.gates (row x) j (by rw [rows]; exact base)).symm.trans h
  obtain ⟨x,hx,bad⟩ := boundary i P w b t d S i0 i6 pfan (by omega) lb tap (pre ▸ clean) arity unary pinRule (by
    intro x hx
    change (P.wires (row x)).getD w false ≠ b
    rw [(sem _ (rows x)).1,sens x _ _ hx]
    · cases b <;> decide
    · intro j hj
      simp [Function.update_of_ne hj])
  change x i = b ∨ (P.wires (row x)).getD w false ≠ b at hx
  change ¬(F x = t ↔ ∀ j ∈ S, (P.wires (row x)).getD j false = d) at bad
  have obs := fixed x (by simpa only [(sem _ (rows x)).1] using hx)
  apply bad
  rw [←obs]
  exact (sem _ (rows x)).2
