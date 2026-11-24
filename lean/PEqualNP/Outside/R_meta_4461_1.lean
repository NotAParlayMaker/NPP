import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Fintype.EquivFin
import PEqualNP.Defs

-- Restrict to the complement of the isolated set. Two deletions there are exactly the
-- same restrictions on the original edge function. The pure case is L-meta-3997.
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.R_meta_4461_1
    (moore :
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H.Colorable 2 →
        (∀ v, (H.neighborSet v).ncard = 3) →
        (∀ v (w : H.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∃ u v, H.Adj u v) → 30 ≤ m)
    (pureDeletion :
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (f : (Fin m → Bool) → Bool),
        30 ≤ m → Even m → H.Colorable 2 →
        (∀ v, (H.neighborSet v).ncard = 3) →
        (∀ v (w : H.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∃ u v, H.Adj u v) →
        (∀ x, f x = true ↔ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
        ∀ s, s + 1 < 2 * m → HasCircuitSize m f s →
          ∃ a b : Fin m, a ≠ b ∧ ¬ H.Adj a b ∧
            ∃ t, t + 8 ≤ s ∧ HasCircuitSize m
              (fun y => f (Function.update (Function.update y a false) b false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x10 → x10 < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x4 ∧ x14 ∉ x4 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  have rewire (n m : ℕ) (port : Fin n → Option (Fin m)) (f : (Fin n → Bool) → Bool)
      (s : ℕ) (small : HasCircuitSize n f s) :
      HasCircuitSize m (fun x => f (fun i => ((port i).map x).getD false)) s := by
    obtain ⟨C, valid, size, computes⟩ := small
    let unavailable := m + C.gates.length
    let rename := fun i : ℕ => if h : i < n then
      ((port ⟨i,h⟩).map Fin.val).getD unavailable else i - n + m
    let move := fun g : PEqualNP.CircuitLowerBounds.Gate =>
      (⟨g.op, g.inputs.map rename⟩ : PEqualNP.CircuitLowerBounds.Gate)
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map move, rename C.output⟩
    let run := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let Rel := fun (u v : List Bool) =>
      n ≤ u.length ∧ v.length + n = u.length + m ∧ v.length ≤ unavailable ∧
        ∀ i, v.getD (rename i) false = u.getD i false
    have belongs {k : ℕ} (x : Fin k → Bool) (i : Fin k) :
        (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have starts (x : Fin m → Bool) :
        Rel (List.ofFn fun i => ((port i).map x).getD false) (List.ofFn x) := by
      refine ⟨by simp, by simp; omega, by simp [unavailable], ?_⟩
      intro i
      let old := fun j : Fin n => ((port j).map x).getD false
      change (List.ofFn x).getD (rename i) false = (List.ofFn old).getD i false
      by_cases hi : i < n
      · have eq := belongs old (⟨i,hi⟩ : Fin n)
        rw [eq]
        cases chosen : port ⟨i,hi⟩ with
        | none =>
          have sent : rename i = unavailable := by simp [rename,hi,chosen]
          rw [sent, List.getD_eq_default _ _ (by simp [unavailable])]
          simp [old,chosen]
        | some j =>
          have atj : rename i = j.val := by simp [rename,hi,chosen]
          rw [atj, belongs]
          simp [old,chosen]
      · have large : n ≤ i := Nat.le_of_not_gt hi
        rw [show rename i = i - n + m from dite_eq_right hi]
        rw [List.getD_eq_default _ _ (by simp <;> omega),
          List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using large)]
    have step (u v : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate)
        (h : Rel u v) (room : v.length < unavailable) : Rel (run u g) (run v (move g)) := by
      obtain ⟨lower, len, cap, vals⟩ := h
      have gate : (move g).op.eval ((move g).inputs.map fun i => v.getD i false) =
          g.op.eval (g.inputs.map fun i => u.getD i false) := by
        simp only [move,List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => vals i)
      refine ⟨by simp [run]; omega, by simp [run]; omega, by simp [run]; omega, ?_⟩
      intro i
      simp only [run,gate]
      by_cases hi : i < n
      · have old : i < u.length := by omega
        cases chosen : port ⟨i,hi⟩ with
        | none =>
          have sent : rename i = unavailable := by simp [rename,hi,chosen]
          have emptyRead := vals i
          rw [sent, List.getD_eq_default _ _ cap] at emptyRead
          rw [List.getD_append _ _ _ _ old, sent,
            List.getD_eq_default _ _ (by simp; omega)]
          exact emptyRead
        | some j =>
          have atj : rename i = j.val := by simp [rename,hi,chosen]
          have inside : rename i < v.length := by
            rw [atj]
            have := j.isLt
            omega
          rw [List.getD_append _ _ _ _ inside, List.getD_append _ _ _ _ old]
          exact vals i
      · have mapIndex : rename i = i - n + m := dite_eq_right hi
        rcases Nat.lt_trichotomy i u.length with inside | ending | outside
        · have fits : rename i < v.length := by omega
          rw [List.getD_append _ _ _ _ fits, List.getD_append _ _ _ _ inside]
          exact vals i
        · have last : rename i = v.length := by omega
          rw [last, ending]
          simp
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
    have finish (gs : List PEqualNP.CircuitLowerBounds.Gate) (u v : List Bool)
        (related : Rel u v) (room : v.length + gs.length ≤ unavailable) :
        Rel (gs.foldl run u) ((gs.map move).foldl run v) := by
      induction gs generalizing u v with
      | nil => exact related
      | cons g tail ih =>
        have free : v.length < unavailable := by simp at room; omega
        exact ih _ _ (step u v g related free) (by simp [run] at ⊢; simp at room; omega)
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hg
      exact ⟨(valid old ho).1, by simpa only [move,List.length_map] using (valid old ho).2⟩
    · change (C.gates.map move).length ≤ s
      change C.gates.length ≤ s at size
      simpa only [List.length_map] using size
    · intro x
      have values := (finish C.gates _ _ (starts x) (by simp [unavailable])).2.2.2 C.output
      exact values.trans (computes (fun i => ((port i).map x).getD false))
  classical
  intro n G inst A color degrees paths isolated edge s cs bound
  let S : Finset (Fin n) := Aᶜ
  let m := n - A.card
  have count : Fintype.card (↥S) = m := by simp [S, m, Finset.card_compl]
  let index := Fintype.equivFinOfCardEq count
  let incl : Fin m → Fin n := fun i => (index.symm i).val
  have injIncl : Function.Injective incl := Subtype.val_injective.comp index.symm.injective
  have on (i : Fin m) : incl i ∉ A := by
    have hit : incl i ∈ S := (index.symm i).property
    simpa [S] using hit
  have covered (v : Fin n) (h : v ∉ A) : ∃ i, incl i = v := by
    let a : S := ⟨v, by simpa [S] using h⟩
    exact ⟨index a, congrArg Subtype.val (index.symm_apply_apply a)⟩
  let H := G.comap incl
  letI : DecidableRel H.Adj := fun i j => Classical.propDecidable (H.Adj i j)
  let hom : H →g G := SimpleGraph.Hom.comap incl G
  have colorH : H.Colorable 2 := SimpleGraph.Colorable.of_hom hom color
  have neighbors (i : Fin m) : incl '' H.neighborSet i = G.neighborSet (incl i) := by
    change incl '' (incl ⁻¹' G.neighborSet (incl i)) = G.neighborSet (incl i)
    apply Set.image_preimage_eq_of_subset
    intro v hv
    have adj : G.Adj (incl i) v := hv
    exact covered v (isolated _ _ adj.symm)
  have degreesH (i : Fin m) : (H.neighborSet i).ncard = 3 := by
    rw [← Set.ncard_image_of_injective _ injIncl, neighbors]
    exact degrees (incl i) (on i)
  have pathsH (i : Fin m) (w : H.Walk i i) (hw : w.IsCycle) : 7 ≤ w.length := by
    have mapped : (w.map hom).IsCycle := hw.map (show Function.Injective hom from injIncl)
    have lengthPreserved {j k : Fin m} (p : H.Walk j k) :
        (p.map hom).length = p.length := by
      induction p with
      | nil => rfl
      | cons _ _ ih => exact congrArg Nat.succ ih
    exact (paths (incl i) (w.map hom) mapped).trans_eq (lengthPreserved w)
  have edgeH : ∃ u v, H.Adj u v := by
    obtain ⟨u, v, uv⟩ := edge
    obtain ⟨a, ai⟩ := covered u (isolated _ _ uv)
    obtain ⟨b, bi⟩ := covered v (isolated _ _ uv.symm)
    refine ⟨a,b,?_⟩
    change G.Adj (incl a) (incl b)
    rwa [ai, bi]
  have minVertices := moore m H colorH degreesH pathsH edgeH
  have parity : Even m := by
    have deg (i : Fin m) : H.degree i = 3 := by
      rw [← H.ncard_neighborSet]
      exact degreesH i
    have sum : 3 * m = 2 * H.edgeFinset.card := by
      calc
        3 * m = ∑ v : Fin m, H.degree v := by simp [deg, nsmul_eq_mul, Nat.mul_comm]
        _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    exact ⟨H.edgeFinset.card - m, by omega⟩
  have graphTruth (k : ℕ) (K : SimpleGraph (Fin k)) [DecidableRel K.Adj] (x : Fin k → Bool) :
      graphFun K ∅ x = true ↔ ∃ a b, K.Adj a b ∧ x a = true ∧ x b = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin k)), x a = true) ||
      decide (∃ a b, K.Adj a b ∧ x a = true ∧ x b = true)) = true ↔ _
    simp
  have equivInputs (x : Fin n → Bool) : graphFun G ∅ x = graphFun H ∅ (x ∘ incl) := by
    apply Bool.eq_iff_iff.mpr
    change graphFun G ∅ x = true ↔ graphFun H ∅ (x ∘ incl) = true
    rw [graphTruth, graphTruth]
    constructor
    · rintro ⟨a, b, ab, ha, hb⟩
      obtain ⟨u, uEq⟩ := covered a (isolated _ _ ab)
      obtain ⟨v, vEq⟩ := covered b (isolated _ _ ab.symm)
      exact ⟨u, v, by change G.Adj (incl u) (incl v); rwa [uEq,vEq],
        by simpa only [Function.comp_apply,uEq] using ha,
        by simpa only [Function.comp_apply,vEq] using hb⟩
    · rintro ⟨u,v,adj,hu,hv⟩
      exact ⟨incl u,incl v,adj,hu,hv⟩
  let remove : Fin n → Option (Fin m) := fun i =>
    if h : i ∈ S then some (index ⟨i,h⟩) else none
  have pull (x : Fin m → Bool) :
      (fun i => ((remove (incl i)).map x).getD false) = x := by
    funext i
    have mem : incl i ∈ S := (index.symm i).property
    simp only [remove, dite_eq_left mem, Option.map_some, Option.getD_some]
    exact congrArg x (index.apply_symm_apply i)
  have reduced : HasCircuitSize m (graphFun H ∅) s := by
    have moved := rewire n m remove (graphFun G ∅) s cs
    have same :
        (fun x : Fin m → Bool => graphFun G ∅ (fun i => ((remove i).map x).getD false)) =
          graphFun H ∅ := by
      funext x
      rw [equivInputs]
      change graphFun H ∅ (fun i => ((remove (incl i)).map x).getD false) = graphFun H ∅ x
      rw [pull x]
    rwa [same] at moved
  have limit : s + 1 < 2 * m := by dsimp [m]; omega
  obtain ⟨a,b,distinct,apart,t,save,pinned⟩ :=
    pureDeletion m H (graphFun H ∅) minVertices parity colorH degreesH pathsH edgeH
      (graphTruth m H) s limit reduced
  have updatePull (x : Fin n → Bool) (i : Fin m) :
      Function.update x (incl i) false ∘ incl = Function.update (x ∘ incl) i false := by
    funext j
    by_cases he : j = i
    · subst j
      simp [Function.comp_apply]
    · have moved : incl j ≠ incl i := fun eq => he (injIncl eq)
      simp only [Function.comp_apply, Function.update_of_ne moved, Function.update_of_ne he]
  refine ⟨incl a, incl b, on a, on b, fun h => distinct (injIncl h), apart, t, save, ?_⟩
  have expanded := rewire m n (fun i => some (incl i))
    (fun y => graphFun H ∅ (Function.update (Function.update y a false) b false)) t pinned
  have same :
      (fun x : Fin n → Bool =>
        graphFun H ∅ (Function.update (Function.update (x ∘ incl) a false) b false)) =
      (fun x : Fin n → Bool =>
        graphFun G ∅ (Function.update (Function.update x (incl a) false) (incl b) false)) := by
    funext x
    rw [equivInputs, updatePull, updatePull]
  change HasCircuitSize n
    (fun x => graphFun H ∅ (Function.update (Function.update (x ∘ incl) a false) b false)) t at expanded
  rwa [same] at expanded
