import Mathlib
import PEqualNP.Defs
open Classical PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2114_419
    (normalize :
      let f : (Fin 9 → Bool) → Bool := fun x => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun t => x (Fin.ofNat 9 (t/9)) && x (Fin.ofNat 9 t))
      ∀ C : Circuit, FanInTwo C → C.size ≤ 15 → circuitFun 9 C = f →
        (∀ j : Fin C.size, let g := C.gates.get j
          (∀ w ∈ g.inputs, w < 9+j.val) ∧ g.inputs.Nodup ∧ g.inputs ≠ [] ∧ (g.inputs.length = 1 ↔ g.op=.not)) →
        (∀ g ∈ C.gates, ∀ v ∈ ([4,6,7] : List ℕ), v ∈ g.inputs → g.op=.or) →
        ∃ (a m b : List Gate) (g r : Gate) (v : Fin 9),
          C.gates = a ++ g :: (m ++ r :: b) ∧ v.val ∈ ([4,6,7] : List ℕ) ∧ r.op=.or ∧
          (r.inputs=[v.val,9+a.length] ∨ r.inputs=[9+a.length,v.val]) ∧
          (∀ t ∈ a ++ g :: m, ∀ u ∈ ([4,6,7] : List ℕ), u ∈ t.inputs → ∀ z ∈ t.inputs, z<9))
    (core :
      let f : (Fin 9 → Bool) → Bool := fun x => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun t => x (Fin.ofNat 9 (t/9)) && x (Fin.ofNat 9 t))
      ∀ (A M B : Circuit) (g : Gate) (v : Fin 9), v.val ∈ ([4,6,7] : List ℕ) →
        A.size + M.size + B.size ≤ 13 → FanInTwo ⟨A.gates ++ g :: (M.gates ++ B.gates),0⟩ →
        (∀ t ∈ A.gates ++ g :: M.gates, ∀ u ∈ ([4,6,7] : List ℕ), u ∈ t.inputs → t.op=.or ∧ ∀ z ∈ t.inputs, z<9) →
        (∀ t ∈ B.gates, ∀ u ∈ ([4,6,7] : List ℕ), u ∈ t.inputs → t.op=.or) →
        ∃ x : Fin 9 → Bool, let w := A.wires (List.ofFn x)
          let q := g.op.eval (g.inputs.map (fun i => w.getD i false))
          B.eval (M.wires (w ++ [q]) ++ [x v || q]) ≠ f x) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x7 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x7).card = (2 : ℕ)) → False := by
  classical
  dsimp only
  intro C hc hor _
  obtain ⟨hmin,sz,hf,hcl,_⟩ := hc
  let target : (Fin 9 → Bool) → Bool := fun x => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun t => x (Fin.ofNat 9 (t/9)) && x (Fin.ofNat 9 t))
  have fn : target = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    simp only [target,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  have allOr : ∀ g ∈ C.gates, ∀ v ∈ ([4,6,7] : List ℕ), v ∈ g.inputs → g.op=.or := by
    intro g hg v hv hin
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    have lt : v<9 := by simp at hv; omega
    let u : Fin 9 := ⟨v,lt⟩
    have hu : u ∈ ([4,6,7] : List (Fin 9)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv ⊢
      rcases hv with h|h|h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    exact hor u hu ⟨j,hj⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hin⟩)
  obtain ⟨a,m,b,g,r,v,seq,hv,rop,rin,prior⟩ := normalize C hmin.1 sz (hf.trans fn.symm) (by
    intro j
    have hj := hcl j
    refine ⟨hj.1,hj.2.1,?_,?_⟩
    · intro h; rcases hj.2.2 with h1|h2 <;> simp [h] at *
    rcases hj.2.2 with ⟨op,len⟩|⟨op,len⟩ <;> simp [len,op]) allOr
  let A : Circuit := ⟨a,0⟩
  let M : Circuit := ⟨m,0⟩
  let B : Circuit := ⟨b,C.output⟩
  have f2 := hmin.1
  have cost : A.size + M.size + B.size ≤ 13 := by
    change C.gates.length ≤ 15 at sz
    rw [seq] at sz; simp only [List.length_append,List.length_cons] at sz
    change a.length + m.length + b.length ≤ 13; omega
  obtain ⟨x,bad⟩ := core A M B g v hv cost (by
    intro t ht
    apply f2 t
    rw [seq]; change t ∈ a ++ g :: (m ++ b) at ht; simp only [List.mem_append,List.mem_cons] at ht ⊢; tauto) (by
    intro t ht u hu hin
    refine ⟨allOr t (by rw [seq]; change t ∈ a ++ g :: m at ht; simp only [List.mem_append,List.mem_cons] at ht ⊢; tauto) u hu hin,prior t ht u hu hin⟩) (by
    intro t ht u hu hin
    exact allOr t (by rw [seq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ht)))) u hu hin)
  let w := A.wires (List.ofFn x)
  let q := g.op.eval (g.inputs.map fun i => w.getD i false)
  let z := M.wires (w ++ [q])
  change B.eval (z ++ [x v || q]) ≠ _ at bad
  let step := fun (ws : List Bool) (t : Gate) => ws ++ [t.op.eval (t.inputs.map fun i => ws.getD i false)]
  have keep (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i<ws.length) :
      (gs.foldl step ws).getD i false = ws.getD i false := by
    induction gs generalizing ws with
    | nil => rfl
    | cons t gs ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
  have len (gs : List Gate) (ws : List Bool) : (gs.foldl step ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons t gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have lw : w.length = 9+a.length := by
    change (a.foldl step (List.ofFn x)).length=_
    rw [len,List.length_ofFn]
  have xv : z.getD v.val false = x v := by
    change (m.foldl step (w++[q])).getD _ _=_
    have lt : v.val<w.length := by rw [lw]; omega
    rw [keep _ _ _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]
    change (a.foldl step (List.ofFn x)).getD v.val false = x v
    rw [keep _ _ _ (by simpa using v.isLt)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos v.isLt,Option.getD_some]
  have qt : z.getD (9+a.length) false = q := by
    change (m.foldl step (w++[q])).getD _ _=_
    rw [←lw,keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have rd : r.op.eval (r.inputs.map fun i => z.getD i false) = (x v || q) := by
    rcases rin with hr|hr
    · rw [rop,hr]
      change (z.getD v.val false || (z.getD (9+a.length) false || false)) = _
      rw [xv,qt,Bool.or_false]
    · rw [rop,hr]
      change (z.getD (9+a.length) false || (z.getD v.val false || false)) = _
      rw [xv,qt,Bool.or_false,Bool.or_comm]
  apply bad
  have hh := congrFun hf x
  change (C.gates.foldl step (List.ofFn x)).getD C.output false = _ at hh
  rw [seq,List.foldl_append,List.foldl_cons,List.foldl_append,List.foldl_cons] at hh
  change (b.foldl step (z ++ [r.op.eval (r.inputs.map fun i => z.getD i false)])).getD C.output false = _ at hh
  rw [rd] at hh
  exact hh.trans (congrFun fn.symm x)
