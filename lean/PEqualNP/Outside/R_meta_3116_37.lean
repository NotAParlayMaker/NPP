import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_3116_37
    (raw : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 13)
    (deleted : ∀ s : ℕ, HasCircuitSize 8 (fun y : Fin 8 → Bool => ([(0,1),(0,5),(1,2),(1,6),(2,3),(2,7),(4,6),(4,7),(5,7)] : List (Fin 8 × Fin 8)).any (fun e => y e.1 && y e.2)) s → 12 ≤ s)
    (unread : ∀ (C : Circuit) (a b : List Bool) (i : ℕ),
      a.length = b.length → i < a.length → C.output ≠ i →
      (∀ k, k ≠ i → a.getD k false = b.getD k false) →
      (∀ j : Fin C.size, let g := C.gates.get j
        ¬ (i ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some i))) →
      C.eval a = C.eval b)
    (restrict : ∀ (C : Circuit) (n m : ℕ) (w : (Fin n → Bool) → List Bool)
      (S : Finset (Fin C.size)),
      let read (i : ℕ) (j : Fin C.size) := let g := C.gates.get j
        i ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some i)
      let col (i : ℕ) (x : Fin n → Bool) := (w x).getD i false
      FanInTwo C → m ≤ C.output → (∀ x, (w x).length = m) →
      (∀ i < m, (∃ j, read i j) →
        (∃ b : Bool, ∀ x, col i x = b) ∨ (∃ p : Fin n, ∀ x, col i x = x p)) →
      (∀ j ∈ S, ∃ i < m, read i j ∧ ∃ b : Bool, ∀ x, col i x = b) →
      (∃ x y, C.eval (w x) ≠ C.eval (w y)) →
      HasCircuitSize n (fun x => C.eval (w x)) (C.size - S.card)) :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!(x 0 && x 3)]) =
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) → 14 ≤ C.size := by
  classical
  intro C fan computes
  by_contra! short
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let H := fun y : Fin 8 → Bool => ([(0,1),(0,5),(1,2),(1,6),(2,3),(2,7),(4,6),(4,7),(5,7)] : List (Fin 8 × Fin 8)).any (fun e => y e.1 && y e.2)
  let w (x : Fin 9 → Bool) :=
    [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 0 && x 3,!(x 0 && x 3)]
  have encode : ∀ x : Fin 9 → Bool,
      List.ofFn x ++ [x 0 && x 3] ++ [!(x 0 && x 3)] = w x := by decide +kernel
  have correct (x : Fin 9 → Bool) : C.eval (w x) = F x := by
    rw [← encode x]
    exact computes x
  let read (i : ℕ) (j : Fin C.size) := let g := C.gates.get j
    i ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some i)
  let step (a : List Bool) (g : Gate) := a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]
  have keep (gs : List Gate) (a : List Bool) (i : ℕ) (hi : i < a.length) :
      (gs.foldl step a).getD i false = a.getD i false := by
    induction gs generalizing a with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  have high : 11 ≤ C.output := by
    by_contra! h
    have rows : ∀ i : Fin 11, ∃ x : Fin 9 → Bool, (w x).getD i.val false ≠ F x := by decide +kernel
    obtain ⟨x,hx⟩ := rows ⟨C.output,h⟩
    exact hx ((keep C.gates (w x) C.output (by simpa [w] using h)).symm.trans (correct x))
  by_cases used : ∃ (j : Fin C.size) (p : Fin 11), 9 ≤ p.val ∧ read p.val j
  · obtain ⟨j,p,hp,hj⟩ := used
    have need (v : Fin 11) (hv : v = 0 ∨ v = 3) : ∃ k : Fin C.size, read v.val k := by
      have wit : ∃ a b : Fin 9 → Bool, F a ≠ F b ∧
          ∀ i : Fin 11, i ≠ v → (w a).getD i.val false = (w b).getD i.val false := by
        rcases hv with rfl | rfl
        · exact ⟨![false,true,false,false,false,false,false,false,false],
            ![true,true,false,false,false,false,false,false,false], by decide +kernel⟩
        · exact ⟨![false,false,true,false,false,false,false,false,false],
            ![false,false,true,true,false,false,false,false,false], by decide +kernel⟩
      obtain ⟨a,b,hab,off⟩ := wit
      by_contra noRead
      have eq := unread C (w a) (w b) v.val (by simp [w]) (by simpa [w] using v.isLt)
        (by omega) (fun k hk => by
          by_cases h : k < 11
          · exact off ⟨k,h⟩ (fun e => hk (congrArg Fin.val e))
          · rw [List.getD_eq_default _ false (by simp only [w, List.length_cons, List.length_nil]; omega),
                List.getD_eq_default _ false (by simp only [w, List.length_cons, List.length_nil]; omega)]) (fun k hr => noRead ⟨k,hr⟩)
      exact hab ((correct a).symm.trans (eq.trans (correct b)))
    obtain ⟨a,ha⟩ := need 0 (Or.inl rfl)
    obtain ⟨b,hb⟩ := need 3 (Or.inr rfl)
    have choice : ∃ (v : Fin 9) (k : Fin C.size),
        (v = 0 ∨ v = 3) ∧ k ≠ j ∧ read v.val k := by
      by_cases h0 : a = j
      · by_cases h3 : b = j
        · subst a
          subst b
          have lim := (fan _ (List.get_mem C.gates j)).2
          have r0 : 0 ∈ (C.gates.get j).inputs := ha.1
          have r3 : 3 ∈ (C.gates.get j).inputs := hb.1
          have rp : p.val ∈ (C.gates.get j).inputs := hj.1
          generalize (C.gates.get j).inputs = l at lim r0 r3 rp
          rcases l with _ | ⟨s, _ | ⟨t, _ | ⟨u,rest⟩⟩⟩ <;>
            simp_all only [List.length_nil, List.length_cons, List.not_mem_nil,
              List.mem_cons, or_false] <;> omega
        · exact ⟨3,b,Or.inr rfl,h3,hb⟩
      · exact ⟨0,a,Or.inl rfl,h0,ha⟩
    obtain ⟨v,k,hv,hkj,hk⟩ := choice
    let lift (v : Fin 9) (y : Fin 8 → Bool) : Fin 9 → Bool :=
      if v = 0 then ![false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7]
      else ![y 2,y 1,y 0,false,y 3,y 7,y 6,y 5,y 4]
    have graph : ∀ (z : Fin 9), z = 0 ∨ z = 3 → ∀ y, F (lift z y) = H y := by decide +kernel
    have cols : ∀ (z : Fin 9) (i : Fin 11),
        (∃ b : Bool, ∀ y, (w (lift z y)).getD i.val false = b) ∨
        (∃ t : Fin 8, ∀ y, (w (lift z y)).getD i.val false = y t) := by decide +kernel
    have fixedCol : ∀ (z : Fin 9), z = 0 ∨ z = 3 → ∀ (i : Fin 11),
        i.val = z.val ∨ 9 ≤ i.val → ∃ b : Bool, ∀ y, (w (lift z y)).getD i.val false = b := by
      decide +kernel
    have projected (y : Fin 8 → Bool) : C.eval (w (lift v y)) = H y :=
      (correct _).trans (graph v hv y)
    have changes : C.eval (w (lift v (fun _ => false))) ≠ C.eval (w (lift v (fun _ => true))) := by
      rw [projected,projected]
      decide +kernel
    have reduced := restrict C 8 11 (fun y => w (lift v y)) {k,j} fan high (by simp [w])
      (fun i hi _ => cols v ⟨i,hi⟩) (fun d hd => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact ⟨v.val,by omega,hk,fixedCol v hv ⟨v.val,by omega⟩ (Or.inl rfl)⟩
        · exact ⟨p.val,p.isLt,hj,fixedCol v hv p (Or.inr hp)⟩) ⟨_,_,changes⟩
    rw [show (fun y => C.eval (w (lift v y))) = H from funext projected] at reduced
    have lb := deleted _ reduced
    simp [hkj] at lb
    omega
  · have cols : ∀ (i : Fin 9), ∀ x, (w x).getD i.val false = x i := by decide +kernel
    have changes : C.eval (w (fun _ => false)) ≠ C.eval (w (fun _ => true)) := by
      rw [correct,correct]
      decide +kernel
    have reduced := restrict C 9 11 w ∅ fan high (by simp [w]) (fun i hi hread => by
      obtain ⟨j,hj⟩ := hread
      by_cases h : i < 9
      · exact Or.inr ⟨⟨i,h⟩,cols ⟨i,h⟩⟩
      · exact False.elim (used ⟨j,⟨i,hi⟩,by omega,hj⟩)) (by simp) ⟨_,_,changes⟩
    rw [show (fun y => C.eval (w y)) = F from funext correct] at reduced
    obtain ⟨D,hf,hs,he⟩ := reduced
    exact raw ⟨D,hf,by simp only [Finset.card_empty, Nat.sub_zero] at hs; omega,he⟩
