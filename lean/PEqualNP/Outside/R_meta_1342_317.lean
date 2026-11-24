import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1342_317
    (boundary : let p (k : Fin 11) := BitVec.ofNat 40 (([2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146] : List ℕ).getD k.val 0)
    ∀ C : Circuit, Monotone2 C →
      (∀ r : Fin 40, C.eval (List.ofFn fun k => (p k).getLsbD r.val) = decide (r.val < 16)) →
      ∀ x : Fin 11 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 11, (u.val,v.val) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)
    (reify : ∀ (p : Fin 11 → BitVec 40) (fs : List (Bool × BitVec 40)) (ts : List (BitVec 40 × BitVec 40)), ts ≠ [] →
    (∀ j : Fin fs.length, let w := List.ofFn p ++ (fs.take j.val).map Prod.snd
      ∃ a ∈ w, ∃ b ∈ w, (fs.get j).2 = (if (fs.get j).1 then a &&& b else a ||| b)) →
    (∀ t ∈ ts, t.1 ∈ List.ofFn p ++ fs.map Prod.snd ∧ t.2 ∈ List.ofFn p ++ fs.map Prod.snd) →
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 = fs.length + 2*ts.length ∧
      ∀ r : Fin 40, C.eval (List.ofFn fun k => (p k).getLsbD r.val) =
        ts.any (fun t => (t.1 &&& t.2).getLsbD r.val))
    (search : let p (k : Fin 11) := BitVec.ofNat 40 (([2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146] : List ℕ).getD k.val 0)
    ∃ (fs : List (Bool × BitVec 40)) (ts : List (BitVec 40 × BitVec 40)), ts ≠ [] ∧ ts.length ≤ 9 ∧
      fs.length + 2*ts.length ≤ 22 ∧ 3 ≤ fs.countP Prod.fst ∧
      (∀ z ∈ fs, 65536 ≤ z.2.toNat) ∧
      (∀ j : Fin fs.length, let w := List.ofFn p ++ (fs.take j.val).map Prod.snd
      ∃ a ∈ w, ∃ b ∈ w, (fs.get j).2 = (if (fs.get j).1 then a &&& b else a ||| b)) ∧
      (∀ t ∈ ts, t.1 ∈ List.ofFn p ++ fs.map Prod.snd ∧ t.2 ∈ List.ofFn p ++ fs.map Prod.snd) ∧
      ∀ r : Fin 40, ts.any (fun t => (t.1 &&& t.2).getLsbD r.val) = decide (r.val < 16)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  let p (k : Fin 11) := BitVec.ofNat 40 (([2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146] : List ℕ).getD k.val 0)
  obtain ⟨fs,ts,ne,_,budget,_,_,gates,pairs,accept⟩ := search
  obtain ⟨C,mono,size,read⟩ := reify p fs ts ne gates pairs
  exact ⟨C,mono,boundary C mono (fun r => (read r).trans (accept r)),by omega⟩
