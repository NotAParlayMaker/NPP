import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1629_704
    (privatePoint : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      (∀ l, Fintype.card {p : Fin N // I p l}=q+1) →
      (∀ p p', p≠p' → ∃! l, I p l ∧ I p' l) →
      ∀ (S : Finset (Fin N)) (l : Fin N), S.card≤q → l∉S →
      ∃ p, I p l ∧ ∀ t∈S, ¬I p t)
    (subsetLower : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2≤q → N=q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l}=q+1) →
      (∀ p p', p≠p' → ∃! l, I p l ∧ I p' l) → Monotone2 C →
      (∀ S T : Finset (Fin N), S.card≤q → T.card≤q →
        (circuitFun (N+N) C (Fin.addCases (fun p => decide (∀ l∈S, ¬I p l))
          (fun l => decide (l∈T)))=true ↔ ¬T⊆S)) → N*q≤100*C.size) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 100 * C.size := by
  classical
  intro q N I _ C hq hn hline hpair hm on off
  have lineSize (l : Fin N) : Fintype.card {p : Fin N // I p l} = q+1 := by
    simpa only [Fintype.card_subtype] using hline l
  apply subsetLower q N I C hq hn lineSize hpair hm
  intro S T hs ht
  let z : Fin (N+N) → Bool := Fin.addCases (fun p => decide (∀ l∈S, ¬I p l)) (fun l => decide (l∈T))
  change circuitFun (N+N) C z=true ↔ ¬T⊆S
  have zp (p : Fin N) : z (Fin.castAdd N p)=true ↔ ∀ l∈S, ¬I p l := by
    simp only [z, Fin.addCases_left, decide_eq_true_eq]
  have zl (l : Fin N) : z (Fin.natAdd N l)=true ↔ l∈T := by
    simp only [z, Fin.addCases_right, decide_eq_true_eq]
  constructor
  · intro hot sub
    have count : (Finset.univ.filter fun l => z (Fin.natAdd N l)=true)=T := by
      ext l; simp only [Finset.mem_filter,Finset.mem_univ,true_and,zl]
    have h0 := off z (by rw [count]; exact ht) (by
      rintro ⟨p,l,inc,hp,hl⟩
      exact (zp p).mp hp l (sub ((zl l).mp hl)) inc)
    simp [hot] at h0
  · intro sub
    obtain ⟨l,htl,hsl⟩ := Finset.not_subset.mp sub
    obtain ⟨p,inc,hp⟩ := privatePoint q N I lineSize hpair S l hs hsl
    let a : Fin (N+N) → Bool := fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)
    have ab (i) (h : a i = true) : z i = true := by
      rcases of_decide_eq_true h with rfl | rfl
      · exact (zp p).mpr hp
      · exact (zl l).mpr htl
    let LE (x y : List Bool) : Prop := ∀ i, x.getD i false=true → y.getD i false=true
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have gateMono (op : GateOp) (hop : op=.and ∨ op=.or) (ls : List ℕ) (x y : List Bool)
        (le : LE x y) : op.eval (ls.map fun i => x.getD i false)=true →
          op.eval (ls.map fun i => y.getD i false)=true := by
      rcases hop with rfl | rfl
      · change (ls.map (fun i => x.getD i false)).all id=true → (ls.map (fun i => y.getD i false)).all id=true
        simp only [List.all_eq_true,List.mem_map,id]
        intro h b hb
        obtain ⟨i,hi,rfl⟩ := hb
        exact le i (h _ ⟨i,hi,rfl⟩)
      · change (ls.map (fun i => x.getD i false)).any id=true → (ls.map (fun i => y.getD i false)).any id=true
        simp only [List.any_eq_true,List.mem_map,id]
        rintro ⟨b,⟨i,hi,rfl⟩,hit⟩
        exact ⟨_,⟨i,hi,rfl⟩,le i hit⟩
    have foldMono (gs : List Gate) (hg : ∀ g∈gs, g.op=.and ∨ g.op=.or) :
        ∀ x y : List Bool, x.length=y.length → LE x y → LE (gs.foldl step x) (gs.foldl step y) := by
      induction gs with
      | nil => intro x y _ h; exact h
      | cons g gs ih =>
        intro x y hlen le
        rw [List.foldl_cons,List.foldl_cons]
        apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
        · simp [step,hlen]
        · intro i hi
          by_cases h : i < x.length
          · rw [show step x g = _ from rfl, List.getD_append _ _ _ _ h] at hi
            change (y ++ _).getD i false=true
            rw [List.getD_append _ _ _ _ (by omega)]; exact le i hi
          · change (x ++ _).getD i false=true at hi
            change (y ++ _).getD i false=true
            rw [List.getD_append_right _ _ _ _ (by omega)] at hi
            rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
            by_cases he : i-x.length=0
            · rw [he] at hi ⊢
              simp only [List.getD_cons_zero] at hi ⊢
              exact gateMono g.op (hg g List.mem_cons_self) _ _ _ le hi
            · obtain ⟨m,H⟩ : ∃ m, i-x.length=m+1 := ⟨i-x.length-1,by omega⟩
              rw [H] at hi; simp at hi
    apply foldMono C.gates (fun g hg => by simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using (hm g hg).1)
      (List.ofFn a) (List.ofFn z) (by simp) _ C.output (on p l inc)
    intro i hi
    by_cases h : i<N+N
    · simp [List.getD_eq_getElem?_getD,h] at hi ⊢
      exact ab _ hi
    · simp [List.getD_eq_getElem?_getD,h] at hi
