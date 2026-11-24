import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fix a false input and record which incidence tests each wire accepts.
-- A false AND inherits an operand bound. A false OR takes the union of two such sets.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2377_105
    (privateBound : ∀ (ι : Type) (W : Finset ι) (F : Set (Set ι)) (R : List (Set ι × Set ι)),
      (∀ s ∈ F, (s ∩ (W : Set ι)).Subsingleton) →
      let step := fun (G : Set (Set ι)) (r : Set ι × Set ι) =>
        G ∪ {s | r.1 ∈ G ∧ r.2 ∈ G ∧ s ⊆ r.1 ∪ r.2}
      ∀ s ∈ R.foldl step F, sᶜ ∈ R.foldl step F → W.card ≤ R.length + 2)
    (obstruction : let left := fun e : Fin 21 × Fin 5 => Fin.castAdd 21 e.1
      let right := fun e : Fin 21 × Fin 5 =>
        Fin.natAdd 21 (e.1 + Fin.ofNat 21 (([20, 0, 5, 7, 17] : List ℕ).getD e.2.val 0))
      ∀ (P : List (Set (Fin 21 × Fin 5) × Set (Fin 21 × Fin 5))) (T : Finset (Set (Fin 21 × Fin 5))),
        32 ≤ P.length → P.length + T.card ≤ 103 →
        (∀ r ∈ P, Disjoint r.1 r.2 ∧ r.1 ∪ r.2 ≠ Set.univ) →
        ∃ U : Finset (Fin 42), Minimal (fun V : Finset (Fin 42) =>
          ∀ e, left e ∈ V ∨ right e ∈ V) U ∧
          let seed : Set (Set (Fin 21 × Fin 5)) :=
            {s | s = ∅ ∨ ∃ v ∈ U, ∀ e ∈ s, v = left e ∨ v = right e}
          let step := fun (F : Set (Set (Fin 21 × Fin 5))) (r : Set (Fin 21 × Fin 5) × _) =>
            F ∪ {s | r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
          ∀ s ∈ T, ¬ (s ∈ P.foldl step seed ∧ sᶜ ∈ P.foldl step seed)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  have extractRules : ∀ (ι : Type) (n : ℕ) (pos : ι → Fin n → Bool) (C : Circuit), Monotone2 C →
        ∃ R : List (Set ι × Set ι), R.length ≤ PEqualNP.ReadTwo.nOr C ∧
          ∀ x : Fin n → Bool, C.eval (List.ofFn x) = false →
            let seed : Set (Set ι) := {s | s = ∅ ∨ ∃ v, x v = false ∧ ∀ e ∈ s, pos e v = true}
            let step := fun (F : Set (Set ι)) (r : Set ι × Set ι) =>
              F ∪ {s | r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
            {e | C.eval (List.ofFn (pos e)) = true} ∈ R.foldl step seed := by
    classical
    intro ι n pos C hm
    let X := Fin n → Bool
    let z : X → Bool := fun _ => false
    let read := fun (w : List (X → Bool)) (i : ℕ) => w.getD i z
    let value := fun (w : List (X → Bool)) (g : Gate) (y : X) =>
      g.op.eval (g.inputs.map fun i => read w i y)
    let extend := fun (w : List (X → Bool)) (g : Gate) => w ++ [value w g]
    let tr := fun (f : X → Bool) => {e : ι | f (pos e) = true}
    let step := fun (F : Set (Set ι)) (r : Set ι × Set ι) =>
      F ∪ {s | r.1 ∈ F ∧ r.2 ∈ F ∧ s ⊆ r.1 ∪ r.2}
    let good := fun (w : List (X → Bool)) (x : X) (F : Set (Set ι)) =>
      ∀ f ∈ w, f x = false → tr f ∈ F
    have atWire (w : List (X → Bool)) (x : X) (F : Set (Set ι))
        (none : (∅ : Set ι) ∈ F) (ok : good w x F) (i : ℕ) :
        read w i x = false → tr (read w i) ∈ F := by
      dsimp only [read]
      by_cases hi : i < w.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact ok _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        intro _
        simpa [tr, z] using none
    have lowerStep (F : Set (Set ι)) (r : Set ι × Set ι) (lower : IsLowerSet F) :
        IsLowerSet (step F r) := by
      intro a b hab hb
      rcases hb with h | ⟨h₁, h₂, h⟩
      · exact Or.inl (lower hab h)
      · exact Or.inr ⟨h₁,h₂,hab.trans h⟩
    let count := fun gs : List Gate => (gs.filter (fun g => decide (g.op = GateOp.or))).length
    have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have compile (gs : List Gate) (legal : ∀ g ∈ gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) (w : List (X → Bool)) :
        ∃ R : List (Set ι × Set ι), R.length = count gs ∧
          ∀ (x : X) (F : Set (Set ι)), IsLowerSet F → (∅ : Set ι) ∈ F → good w x F →
            good (gs.foldl extend w) x (R.foldl step F) ∧ (∅ : Set ι) ∈ R.foldl step F := by
      induction gs generalizing w with
      | nil => exact ⟨[], rfl, fun _ _ _ empty h => ⟨h,empty⟩⟩
      | cons g gs ih =>
        obtain ⟨R, cost, finish⟩ := ih (fun q hq => legal q (List.mem_cons_of_mem _ hq)) (extend w g)
        obtain ⟨op, arity⟩ := legal g List.mem_cons_self
        rcases op with hop | hop
        · refine ⟨R, by simpa [count, hop] using cost, ?_⟩
          intro x F lower empty ok
          apply finish x F lower empty
          intro f hf off
          rcases List.mem_append.mp hf with old | new
          · exact ok f old off
          · have eqf : f = value w g := List.mem_singleton.mp new
            subst f
            have hmiss : ∃ i ∈ g.inputs, read w i x = false := by
              simpa [value, hop, evalAnd, List.all_map, Function.comp_def] using off
            obtain ⟨i, hi, hix⟩ := hmiss
            refine lower (show tr (value w g) ⊆ tr (read w i) from ?_) (atWire w x F empty ok i hix)
            intro e he
            change value w g (pos e) = true at he
            have all : ∀ j ∈ g.inputs, read w j (pos e) = true := by
              simpa [value, hop, evalAnd, List.all_map, Function.comp_def] using he
            exact all i hi
        · let args := g.inputs.map (read w)
          let a := read args 0
          let b := read args 1
          let r := (tr a, tr b)
          have gate (y : X) : value w g y = (a y || b y) := by
            rcases h : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
            · simp [value, hop, evalOr, h, a,b,read,args,z]
            · simp [value, hop, evalOr, h, a,b,read,args,z]
            · simp [value, hop, evalOr, h, a,b,read,args,z]
            · simp [h] at arity
          refine ⟨r :: R, by simp [count, hop] at cost ⊢; omega, ?_⟩
          intro x F lower empty ok
          apply finish x (step F r) (lowerStep F r lower) (Or.inl empty)
          intro f hf off
          rcases List.mem_append.mp hf with old | new
          · exact Or.inl (ok f old off)
          · have eqf : f = value w g := List.mem_singleton.mp new
            subst f
            have both := Bool.or_eq_false_iff.mp ((gate x).symm.trans off)
            have okArgs : good args x F := by
              intro sig hs
              obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
              exact atWire w x F empty ok i
            refine Or.inr ⟨atWire args x F empty okArgs 0 both.1,
              atWire args x F empty okArgs 1 both.2, ?_⟩
            intro e he
            apply Bool.or_eq_true_iff.mp
            exact (gate (pos e)).symm.trans he
    let inputs : List (X → Bool) := List.ofFn fun v : Fin n => fun y : X => y v
    have legal (g : Gate) (hg : g ∈ C.gates) :
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      hm g hg
    obtain ⟨R,cost,runs⟩ := compile C.gates legal inputs
    have readMap (w : List (X → Bool)) (i : ℕ) (y : X) :
        read w i y = (w.map (fun f => f y)).getD i false := by
      simp only [read,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases w[i]? <;> rfl
    have simulate (gs : List Gate) (w : List (X → Bool)) (y : X) :
        (gs.foldl extend w).map (fun f => f y) =
          gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map fun i => vs.getD i false)])
            (w.map fun f => f y) := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, List.foldl_cons, ih]
        simp only [extend, List.map_append, List.map_cons, List.map_nil, value, readMap]
    let out := read (C.gates.foldl extend inputs) C.output
    have output (y : X) : out y = C.eval (List.ofFn y) := by
      rw [show out y = _ from readMap (C.gates.foldl extend inputs) C.output y, simulate]
      change _ = (C.gates.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map fun i => vs.getD i false)]) (List.ofFn y)).getD C.output false
      simp [inputs, List.map_ofFn, Function.comp_def]
    refine ⟨R, ?_, ?_⟩
    · exact le_of_eq (cost.trans (by unfold PEqualNP.ReadTwo.nOr count; congr! 3; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]))
    intro x off
    let F : Set (Set ι) := {s | s = ∅ ∨ ∃ v, x v = false ∧ ∀ e ∈ s, pos e v = true}
    have lower : IsLowerSet F := by
      intro a b hab hb
      rcases hb with rfl | ⟨v,hv,h⟩
      · exact Or.inl (Set.subset_empty_iff.mp hab)
      · exact Or.inr ⟨v,hv,fun e he => h e (hab he)⟩
    have ok : good inputs x F := by
      intro f hf
      obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hf
      exact fun h => Or.inr ⟨v,h,fun _ he => he⟩
    obtain ⟨final, empty⟩ := runs x F lower (Or.inl rfl) ok
    have h := atWire _ x _ empty final C.output ((output x).trans off)
    change tr out ∈ R.foldl step F at h
    simpa only [tr, output] using h
  have stage : ∀ (ι : Type) (R : List (Set ι × Set ι)),
        let step := fun (G : Set (Set ι)) (r : Set ι × Set ι) =>
          G ∪ {s | r.1 ∈ G ∧ r.2 ∈ G ∧ s ⊆ r.1 ∪ r.2}
        ∃ (P : List (Set ι × Set ι)) (T : Finset (Set ι)),
          P.length + T.card ≤ R.length ∧
          (∀ r ∈ P, Disjoint r.1 r.2 ∧ r.1 ∪ r.2 ≠ Set.univ) ∧
          ∀ F : Set (Set ι), IsLowerSet F → Set.univ ∉ F → Set.univ ∈ R.foldl step F →
            ∃ s ∈ T, s ∈ P.foldl step F ∧ sᶜ ∈ P.foldl step F := by
    classical
    intro ι R
    let step := fun (G : Set (Set ι)) (r : Set ι × Set ι) =>
      G ∪ {s | r.1 ∈ G ∧ r.2 ∈ G ∧ s ⊆ r.1 ∪ r.2}
    let split := fun (r : Set ι × Set ι) => (r.1, r.2 \ r.1)
    have sum (r : Set ι × Set ι) : (split r).1 ∪ (split r).2 = r.1 ∪ r.2 := by
      ext x
      simp only [split, Set.mem_union, Set.mem_sdiff]
      tauto
    have lowerStep (F : Set (Set ι)) (r : Set ι × Set ι) (lower : IsLowerSet F) :
        IsLowerSet (step F r) := by
      intro a b hab hb
      rcases hb with h | ⟨h₁,h₂,h⟩
      · exact Or.inl (lower hab h)
      · exact Or.inr ⟨h₁,h₂,hab.trans h⟩
    have grow (L : List (Set ι × Set ι)) (F : Set (Set ι)) : F ⊆ L.foldl step F := by
      induction L generalizing F with
      | nil => exact fun _ h => h
      | cons r rs ih => exact fun _ h => ih (step F r) (Or.inl h)
    have more (L : List (Set ι × Set ι)) (F G : Set (Set ι)) (h : F ⊆ G) (lower : IsLowerSet G) :
        L.foldl step F ⊆ (L.map split).foldl step G := by
      induction L generalizing F G with
      | nil => exact h
      | cons r rs ih =>
        apply ih (step F r) (step G (split r)) _ (lowerStep _ _ lower)
        intro s hs
        rcases hs with old | ⟨a,b,c⟩
        · exact Or.inl (h old)
        · exact Or.inr ⟨h a, lower (Set.sdiff_subset : r.2 \ r.1 ⊆ r.2) (h b), (sum r) ▸ c⟩
    let proper := fun (r : Set ι × Set ι) => decide (r.1 ∪ r.2 ≠ Set.univ)
    let prep := fun L : List (Set ι × Set ι) => L.filter proper
    let top := fun L : List (Set ι × Set ι) => (L.filter (fun r => !proper r)).map Prod.fst
    have budget (L : List (Set ι × Set ι)) : (prep L).length + (top L).length = L.length := by
      induction L with
      | nil => rfl
      | cons r rs ih =>
        cases hp : proper r <;> simp [prep, top, hp] at ih ⊢ <;> omega
    have finish (L : List (Set ι × Set ι)) (F : Set (Set ι)) (lower : IsLowerSet F)
        (small : Set.univ ∉ F) (full : Set.univ ∈ L.foldl step F) :
        ∃ s ∈ top L, s ∈ (prep L).foldl step F ∧ sᶜ ∈ (prep L).foldl step F := by
      induction L generalizing F with
      | nil => exact (small full).elim
      | cons r rs ih =>
        by_cases isProper : r.1 ∪ r.2 ≠ Set.univ
        · have hp : proper r = true := decide_eq_true isProper
          have ssmall : Set.univ ∉ step F r := by
            rintro (old | ⟨_,_,sub⟩)
            · exact small old
            · exact isProper (Set.univ_subset_iff.mp sub)
          obtain ⟨s,hs,ha,hb⟩ := ih (step F r) (lowerStep _ _ lower) ssmall full
          exact ⟨s, by simpa [top,hp] using hs, by simpa [prep,hp] using ha,
            by simpa [prep,hp] using hb⟩
        · have eq : r.1 ∪ r.2 = Set.univ := not_not.mp isProper
          have hp : proper r = false := by simp [proper,eq]
          by_cases both : r.1 ∈ F ∧ r.2 ∈ F
          · have hc : r.1ᶜ ⊆ r.2 := by
              intro e hn
              have he : e ∈ r.1 ∪ r.2 := eq.symm ▸ Set.mem_univ e
              exact he.resolve_left hn
            refine ⟨r.1, by simp [top,hp], ?_, ?_⟩
            · simpa [prep,hp] using grow (prep rs) F both.1
            · simpa [prep,hp] using grow (prep rs) F (lower hc both.2)
          · have same : step F r = F := by
              ext s
              exact ⟨fun H => H.elim id (fun H => (both ⟨H.1,H.2.1⟩).elim), Or.inl⟩
            change Set.univ ∈ rs.foldl step (step F r) at full
            rw [same] at full
            obtain ⟨s,hs,ha,hb⟩ := ih F lower small full
            exact ⟨s, by simpa only [top, List.filter_cons, hp, Bool.not_false, ite_true, List.map_cons, List.mem_cons] using Or.inr (a := s = r.1) hs, by simpa [prep,hp] using ha,
              by simpa [prep,hp] using hb⟩
    let L := R.map split
    refine ⟨prep L, (top L).toFinset, ?_, ?_, ?_⟩
    · have bound := List.toFinset_card_le (top L)
      have len : L.length = R.length := by simp [L]
      have := budget L
      omega
    · intro r hr
      obtain ⟨h, hp⟩ := List.mem_filter.mp hr
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
      exact ⟨Set.disjoint_sdiff_right, of_decide_eq_true hp⟩
    · intro F low small full
      obtain ⟨s, hs, ha, hb⟩ := finish L F low small (more R F F (fun _ h => h) low full)
      exact ⟨s,List.mem_toFinset.mpr hs,ha,hb⟩
  classical
  intro C hm computes
  let left := fun e : Fin 21 × Fin 5 => Fin.castAdd 21 e.1
  let right := fun e : Fin 21 × Fin 5 =>
    Fin.natAdd 21 (e.1 + Fin.ofNat 21 (([20, 0, 5, 7, 17] : List ℕ).getD e.2.val 0))
  let pos := fun (e : Fin 21 × Fin 5) (v : Fin 42) => decide (v = left e ∨ v = right e)
  let edges := (List.range 21).flatMap (fun i =>
    [(i, 21 + (i + 20) % 21), (i, 21 + i), (i, 21 + (i + 5) % 21),
     (i, 21 + (i + 7) % 21), (i, 21 + (i + 17) % 21)])
  have row : ∀ i : Fin 21,
      [(i.val, 21 + (i.val + 20) % 21), (i.val, 21 + i.val), (i.val, 21 + (i.val + 5) % 21),
       (i.val, 21 + (i.val + 7) % 21), (i.val, 21 + (i.val + 17) % 21)] =
        (List.finRange 5).map (fun j => ((left (i,j)).val, (right (i,j)).val)) := by
    decide +kernel
  have table (p l : Fin 42) : (p.val, l.val) ∈ edges ↔
      ∃ e : Fin 21 × Fin 5, left e = p ∧ right e = l := by
    constructor
    · intro h
      obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp h
      let a : Fin 21 := ⟨i, List.mem_range.mp hi⟩
      have ew := (row a).symm ▸ he
      obtain ⟨j, _, eq⟩ := List.mem_map.mp ew
      exact ⟨(a,j), Fin.ext (congrArg Prod.fst eq), Fin.ext (congrArg Prod.snd eq)⟩
    · rintro ⟨⟨a,j⟩,rfl,rfl⟩
      apply List.mem_flatMap.mpr
      refine ⟨a.val, List.mem_range.mpr a.isLt, ?_⟩
      rw [row a]
      exact List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩
  obtain ⟨R, cost, run⟩ := extractRules _ 42 pos C hm
  have en : PEqualNP.ReadTwo.nOr C = {i : Fin C.gates.length |
      (C.gates.get i).op = GateOp.or}.ncard := by
    let pred := fun i : Fin C.gates.length => (C.gates.get i).op = GateOp.or
    change _ = (Set.ofPred pred).ncard
    rw [Set.ncard_eq_toFinset_card']
    rw [show (Set.ofPred pred).toFinset = Finset.univ.filter pred by ext; simp]
    have h := (List.nodup_finRange C.gates.length).card_eq_countP (P := pred)
    rw [show (List.finRange C.gates.length).toFinset = Finset.univ by ext; simp] at h
    rw [h, List.countP_eq_length_filter]
    unfold PEqualNP.ReadTwo.nOr
    have mapget : (List.finRange C.gates.length).map C.gates.get = C.gates := by
      rw [← List.ofFn_eq_map, List.ofFn_get]
    conv_lhs => rw [← mapget]
    rw [List.filter_map, List.length_map]
    congr 2
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, decide_eq_true_eq, pred]
  by_contra! small
  obtain ⟨P,T,budget,proper,finish⟩ := stage _ R
  let step := fun (G : Set (Set (Fin 21 × Fin 5))) (r : Set (Fin 21 × Fin 5) × _) =>
    G ∪ {s | r.1 ∈ G ∧ r.2 ∈ G ∧ s ⊆ r.1 ∪ r.2}
  let seed := fun U : Finset (Fin 42) =>
    {s : Set (Fin 21 × Fin 5) | s = ∅ ∨ ∃ v ∈ U, ∀ e ∈ s, v = left e ∨ v = right e}
  have avoids : ∀ v : Fin 42, ∃ e : Fin 21 × Fin 5, v ≠ left e ∧ v ≠ right e := by
    decide +kernel
  have finishes (U : Finset (Fin 42)) (cover : ∀ e, left e ∈ U ∨ right e ∈ U) :
      ∃ s ∈ T, s ∈ P.foldl step (seed U) ∧ sᶜ ∈ P.foldl step (seed U) := by
    apply finish (seed U)
    · intro a b hab hb
      rcases hb with rfl | ⟨v,hv,h⟩
      · exact Or.inl (Set.subset_empty_iff.mp hab)
      · exact Or.inr ⟨v,hv,fun e he => h e (hab he)⟩
    · rintro (empty | ⟨v,_,touch⟩)
      · exact Set.univ_nonempty.ne_empty empty
      · obtain ⟨e,hl,hr⟩ := avoids v
        exact (touch e (Set.mem_univ e)).elim hl hr
    · let x := fun v : Fin 42 => decide (v ∉ U)
      have negative : C.eval (List.ofFn x) = false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        obtain ⟨p,l,edge,hp,hl⟩ := (computes x).mp yes
        obtain ⟨e,hp',hl'⟩ := (table p l).mp edge
        rcases cover e with h | h
        · exact (of_decide_eq_true hp) (hp' ▸ h)
        · exact (of_decide_eq_true hl) (hl' ▸ h)
      have positive : {e | C.eval (List.ofFn (pos e)) = true} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro e
        apply (computes _).mpr
        exact ⟨left e, right e, (table _ _).mpr ⟨e, rfl, rfl⟩, by simp [pos], by simp [pos]⟩
      have gen := run x negative
      dsimp only at gen
      rw [positive] at gen
      simpa only [x, pos, seed, decide_eq_false_iff_not, not_not, decide_eq_true_eq] using gen
  -- Each of the 34 vertices in this cover has an incidence whose other endpoint is outside it.
  let U : Finset (Fin 42) := ({0,1,4,14,23,33,36,37} : Finset (Fin 42))ᶜ
  let W : Finset (Fin 21 × Fin 5) :=
    {(2,1),(3,0),(5,3),(6,4),(7,2),(8,3),(9,3),(10,2),(11,2),(12,1),(13,0),
     (15,1),(16,0),(17,0),(18,2),(19,4),(20,4),(0,1),(1,1),(4,0),(4,1),(0,2),
     (1,2),(0,3),(1,3),(4,2),(14,4),(4,3),(14,0),(14,1),(0,4),(1,4),(14,2),(0,0)}
  have cover : ∀ e, left e ∈ U ∨ right e ∈ U := by decide +kernel
  have sizeW : W.card = 34 := by decide +kernel
  have privateEdges : ∀ v : Fin 42, v ∈ U →
      (W.filter (fun e => v = left e ∨ v = right e)).card ≤ 1 := by decide +kernel
  have one (s : Set (Fin 21 × Fin 5)) (hs : s ∈ seed U) : (s ∩ (W : Set _)).Subsingleton := by
    rcases hs with rfl | ⟨v,hv,h⟩
    · simp
    · intro a ha b hb
      exact Finset.card_le_one.mp (privateEdges v hv) a (Finset.mem_filter.mpr ⟨ha.2,h a ha.1⟩)
        b (Finset.mem_filter.mpr ⟨hb.2,h b hb.1⟩)
  obtain ⟨s,_,ha,hb⟩ := finishes U cover
  have necessary := privateBound _ W (seed U) P one s ha hb
  obtain ⟨V,hV,blocked⟩ := obstruction P T (by omega) (by omega) proper
  obtain ⟨cut,hcut,conditions⟩ := finishes V hV.1
  exact blocked cut hcut conditions
