import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4461_276
    (transport : ∀ (n m s : ℕ) (f : (Fin n → Bool) → Bool) (r : Fin n → Option (Fin m)),
      PEqualNP.MetaComplexity.HasCircuitSize n f s →
      PEqualNP.MetaComplexity.HasCircuitSize m (fun x => f (fun i => (r i).elim false x)) s)
    (regular : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.Colorable 2 →
      (∀ v, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∃ u v, G.Adj u v) →
      ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n
        (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) s →
        s < 2 * n - 1 →
        ∃ u v, u ≠ v ∧ ¬ G.Adj u v ∧
          ∃ t, t + 8 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n
            (fun x => PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
              (Function.update (Function.update x u false) v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x10 → x10 < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x4 ∧ x14 ∉ x4 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro n G dec A hcolor hdegree hgirth hA hedge s hs hsize
  let B : Finset (Fin n) := Finset.univ \ A
  let m := B.card
  let E : Fin m ≃ B := B.equivFin.symm
  let e : Fin m ↪ Fin n := E.toEmbedding.trans (Function.Embedding.subtype _)
  have he (i : Fin m) : e i ∉ A := (Finset.mem_sdiff.mp (E i).property).2
  have hback {i : Fin n} (hi : i ∉ A) : i ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
  let r (i : Fin n) : Option (Fin m) :=
    if hi : i ∈ B then some (E.symm ⟨i, hi⟩) else none
  have hr (i : Fin m) : r (e i) = some i := by
    change r (E i).val = some i
    simp [r, (E i).property]
  have her (i : Fin n) (hi : i ∉ A) : e (E.symm ⟨i, hback hi⟩) = i := by
    change (E (E.symm ⟨i, hback hi⟩)).val = i
    simp
  have hm : m = n - A.card := by simp [m, B, Finset.card_sdiff]
  let K := G.comap e
  let : DecidableRel K.Adj := fun a b => dec (e a) (e b)
  let F : K ↪g G := SimpleGraph.Embedding.comap e G
  have hKcolor : K.Colorable 2 := hcolor.of_hom F.toHom
  have hKdegree (i : Fin m) : (K.neighborSet i).ncard = 3 := by
    have himage : e '' K.neighborSet i = G.neighborSet (e i) := by
      ext v
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact hj
      · intro hv
        have hAdj : G.Adj (e i) v := hv
        have hvA := hA v (e i) hAdj.symm
        let j := E.symm ⟨v, hback hvA⟩
        have hj : e j = v := her v hvA
        exact ⟨j, by change G.Adj (e i) (e j); rwa [hj], hj⟩
    rw [← Set.ncard_image_of_injective _ e.injective, himage]
    exact hdegree (e i) (he i)
  have hKgirth (i : Fin m) (w : K.Walk i i) (h : w.IsCycle) : 7 ≤ w.length := by
    rw [← SimpleGraph.Walk.length_map F.toHom w]
    exact hgirth (e i) (w.map F.toHom) (h.map e.injective)
  have hKedge : ∃ i j, K.Adj i j := by
    obtain ⟨a, b, hab⟩ := hedge
    have ha := hA a b hab
    have hb := hA b a hab.symm
    refine ⟨E.symm ⟨a, hback ha⟩, E.symm ⟨b, hback hb⟩, ?_⟩
    change G.Adj (e (E.symm ⟨a, hback ha⟩)) (e (E.symm ⟨b, hback hb⟩))
    rwa [her, her]
  have hGraph (x : Fin n → Bool) :
      PEqualNP.MetaComplexity.NestedCover.graphFun K ∅ (x ∘ e) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
    delta PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Finset.notMem_empty, false_and,
      exists_false, decide_false, Bool.false_or, Function.comp_apply]
    rw [decide_eq_decide]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨e i, e j, hij, hi, hj⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      have haA := hA a b hab
      have hbA := hA b a hab.symm
      let i := E.symm ⟨a, hback haA⟩
      let j := E.symm ⟨b, hback hbA⟩
      have hi : e i = a := her a haA
      have hj : e j = b := her b hbA
      refine ⟨i, j, ?_, hi ▸ ha, hj ▸ hb⟩
      change G.Adj (e i) (e j)
      rwa [hi, hj]
  have hInput (y : Fin m → Bool) : (fun i => (r i).elim false y) ∘ e = y := by
    funext i
    simp [Function.comp_apply, hr]
  have hSmall : PEqualNP.MetaComplexity.HasCircuitSize m
      (PEqualNP.MetaComplexity.NestedCover.graphFun K ∅) s := by
    have h := transport n m s _ r hs
    have hEq : (fun y => PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
        (fun i => (r i).elim false y)) = PEqualNP.MetaComplexity.NestedCover.graphFun K ∅ := by
      funext y
      rw [← hGraph, hInput]
    exact hEq ▸ h
  have hmSize : s < 2 * m - 1 := by simpa only [hm] using hsize
  obtain ⟨u, v, huv, hnot, t, ht, hD⟩ :=
    regular m K hKcolor hKdegree hKgirth hKedge s hSmall hmSize
  have hUpdate (x : Fin n → Bool) (i : Fin m) :
      (Function.update x (e i) false) ∘ e = Function.update (x ∘ e) i false := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · have he' : e j ≠ e i := fun heq => h (e.injective heq)
      simp [Function.update_of_ne, h, he']
  have hD' := transport m n t _ (fun j => some (e j)) hD
  refine ⟨e u, e v, he u, he v, fun h => huv (e.injective h), hnot, t, ht, ?_⟩
  have hOut : (fun (x : Fin n → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun K ∅
      (Function.update (Function.update (x ∘ e) u false) v false)) =
      fun x => PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
        (Function.update (Function.update x (e u) false) (e v) false) := by
    funext x
    rw [← hGraph, hUpdate, hUpdate]
  exact hOut ▸ hD'
