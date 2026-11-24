import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK

-- Convert a rectangle program into a circuit using the same gate budget,
-- then apply the two single-occurrence bounds of L-meta-2970 and L-meta-2972.
theorem PEqualNP.Outside.R_meta_5086_1
    (lineOnce : ∀ (n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      (∀ p r l u, p ≠ r → l ≠ u → ¬ (I p l ∧ I r l ∧ I p u ∧ I r u)) →
      IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ 1 →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧
        lineSingle C (n+n) (fun k => decide (n ≤ k)) e.1.val (n+e.2.val) = true} ≤ 10 * C.size)
    (pointOnce : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧
        lineSingle C (n+n) (fun k => decide (k < n)) e.1.val (n+e.2.val) = true} ≤ 10 * C.size)
    (bothRepeated : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      250 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      (∀ p l, I p l → circuitFun (n+n) C
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) →
      Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧
        lineSingle C (n+n) (fun k => decide (n ≤ k)) e.1.val (n+e.2.val) = false ∧
        lineSingle C (n+n) (fun k => decide (k < n)) e.1.val (n+e.2.val) = false} ≤ 80 * C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Fin x2 × Fin x2) × Set (Finset (Fin x2))),             have x12 : ℕ → Set ((Fin x2 × Fin x2) × Finset (Fin x2)) := fun (x12 : ℕ) => (x11 x12).1 ×ˢ (x11 x12).2;             x10 < x2 + x2 + x9 → (∀ (x14 : Fin (x2 + x2)) (x15 x16 : Fin x2) (x17 : Finset (Fin x2)), ((x15, x16), x17) ∈ x12 ↑x14 → (x14 = Fin.castAdd x2 x15 ∧ ∃ x19 ∈ x17, x3 x15 x19) ∨ x14 = Fin.natAdd x2 x16 ∧ x16 ∉ x17) → (∀ x15 < x9, ∃ (x17 : ℕ) (x18 : ℕ), x17 < x18 ∧ x18 < x2 + x2 + x15 ∧ x12 (x2 + x2 + x15) ⊆ x12 x17 ∪ x12 x18) → {x16 : Fin x2 × Fin x2 | x3 x16.1 x16.2} ×ˢ {x16 : Finset (Fin x2) | x16.card ≤ x1} ⊆ x12 x10 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q n I inst hq hn degree unique s o R rect out raw parents cover
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have stepExpr (w : List Bool) (g : Gate) :
      step w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl
  have wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

  have fold_prefix (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
      induction gs with
      | nil => intro w; exact ⟨[], by simp, rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨t, ht, hl⟩ := ih (step w g)
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
        rw [List.foldl_cons, ht]; simp [step]

  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := fold_prefix gs w
      rw [ht]; simp [hl]

  have fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
      obtain ⟨t, ht, _⟩ := fold_prefix gs w
      rw [ht, List.getD_append _ _ _ _ h]

  let rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
    if i < g then (C.wires x).getD i false else false

  have wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
      (C.wires x).getD i false = x.getD i false := fold_getD_lt _ _ _ h

  have wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
      (C.wires x).getD (x.length + j) false
        = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
      have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
        simp
      set A := (C.gates.take j).foldl step x with hA
      have hAl : A.length = x.length + j := by
        rw [hA, fold_length]; simp; omega
      have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
        rw [wires_eq]
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
        intro i
        unfold rd
        by_cases hi : i < x.length + j
        · rw [ite_eq_left hi, hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), stepExpr,
            List.getD_append _ _ _ _ (by omega)]
        · rw [ite_eq_right hi, List.getD_eq_default]; omega
      rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), stepExpr,
        List.getD_append_right _ _ _ _ (by omega)]
      simp only [hAl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      congr 1
      exact List.map_congr_left (fun i _ => hreadA i)

  have splitRectangle {A B : Type} {P P₀ P₁ : Set A} {Q Q₀ Q₁ : Set B}
      (nonP : P.Nonempty) (nonQ : Q.Nonempty)
      (covered : P ×ˢ Q ⊆ P₀ ×ˢ Q₀ ∪ P₁ ×ˢ Q₁) :
      (P ⊆ P₀ ∧ Q ⊆ Q₀) ∨ (P ⊆ P₁ ∧ Q ⊆ Q₁) ∨
        (P ⊆ P₀ ∪ P₁ ∧ Q ⊆ Q₀ ∧ Q ⊆ Q₁ ∧ P₀.Nonempty ∧ P₁.Nonempty) ∨
        (P ⊆ P₀ ∧ P ⊆ P₁ ∧ Q ⊆ Q₀ ∪ Q₁ ∧ Q₀.Nonempty ∧ Q₁.Nonempty) := by
      have cross (a : A) (b : B) (ha : a ∈ P) (hb : b ∈ Q) :=
        covered (show (a,b) ∈ P ×ˢ Q from ⟨ha,hb⟩)
      obtain ⟨a,ha⟩ := nonP
      obtain ⟨b,hb⟩ := nonQ
      by_cases hP₀ : P ⊆ P₀
      · by_cases hQ₀ : Q ⊆ Q₀
        · exact Or.inl ⟨hP₀,hQ₀⟩
        · obtain ⟨b₀,hb₀,hb₀out⟩ := Set.not_subset.mp hQ₀
          have hP₁ : P ⊆ P₁ := by
            intro a ha
            exact ((cross a b₀ ha hb₀).resolve_left (fun h => hb₀out h.2)).1
          by_cases hQ₁ : Q ⊆ Q₁
          · exact Or.inr (Or.inl ⟨hP₁,hQ₁⟩)
          · obtain ⟨b₁,hb₁,hb₁out⟩ := Set.not_subset.mp hQ₁
            have b₀in := ((cross a b₀ ha hb₀).resolve_left (fun h => hb₀out h.2)).2
            have b₁in := ((cross a b₁ ha hb₁).resolve_right (fun h => hb₁out h.2)).2
            exact Or.inr (Or.inr (Or.inr ⟨hP₀,hP₁,
              fun b h => (cross a b ha h).imp And.right And.right,⟨b₁,b₁in⟩,⟨b₀,b₀in⟩⟩))
      · obtain ⟨a₀,ha₀,ha₀out⟩ := Set.not_subset.mp hP₀
        have hQ₁ : Q ⊆ Q₁ := by
          intro b hb
          exact ((cross a₀ b ha₀ hb).resolve_left (fun h => ha₀out h.1)).2
        by_cases hP₁ : P ⊆ P₁
        · exact Or.inr (Or.inl ⟨hP₁,hQ₁⟩)
        · obtain ⟨a₁,ha₁,ha₁out⟩ := Set.not_subset.mp hP₁
          have hQ₀ : Q ⊆ Q₀ := by
            intro b hb
            exact ((cross a₁ b ha₁ hb).resolve_right (fun h => ha₁out h.1)).2
          have a₀in := ((cross a₀ b ha₀ hb).resolve_left (fun h => ha₀out h.1)).1
          have a₁in := ((cross a₁ b ha₁ hb).resolve_right (fun h => ha₁out h.1)).1
          exact Or.inr (Or.inr (Or.inl ⟨fun a h => (cross a b h hb).imp And.left And.left,
            hQ₀,hQ₁,⟨a₁,a₁in⟩,⟨a₀,a₀in⟩⟩))

  have rectanglesToCircuit (A B : Type) [Nonempty A] [Nonempty B] (d s o : ℕ)
      (P : A → Fin d → Bool) (Q : B → Fin d → Bool) (R : ℕ → Set A × Set B)
      (out : o < d+s)
      (raw : ∀ (i : Fin d) (a : A) (b : B), (a,b) ∈ (R i.val).1 ×ˢ (R i.val).2 →
        P a i = true ∧ Q b i = false)
      (parents : ∀ j < s, ∃ a b, a < b ∧ b < d+j ∧
        (R (d+j)).1 ×ˢ (R (d+j)).2 ⊆ (R a).1 ×ˢ (R a).2 ∪ (R b).1 ×ˢ (R b).2)
      (root : Set.univ ×ˢ Set.univ ⊆ (R o).1 ×ˢ (R o).2) :
      ∃ C : Circuit, IsAO2 d C ∧ C.size = s ∧
        (∀ a, circuitFun d C (P a) = true) ∧ ∀ b, circuitFun d C (Q b) = false := by
      let valid (w : ℕ) (f : A → Bool) (g : B → Bool) :=
        ((R w).2.Nonempty → ∀ a ∈ (R w).1, f a = true) ∧
          ((R w).1.Nonempty → ∀ b ∈ (R w).2, g b = false)
      have orEval (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
        cases a <;> cases b <;> rfl
      have andEval (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by
        cases a <;> cases b <;> rfl
      have choices (j : Fin s) : ∃ (op : GateOp) (a b : ℕ), a < d+j.val ∧ b < d+j.val ∧
          (op = .and ∨ op = .or) ∧
          ∀ (f : A → ℕ → Bool) (g : B → ℕ → Bool),
            valid a (fun x => f x a) (fun y => g y a) →
            valid b (fun x => f x b) (fun y => g y b) →
            valid (d+j.val) (fun x => op.eval [f x a, f x b])
              (fun y => op.eval [g y a, g y b]) := by
        obtain ⟨u,v,uv,hv,cover⟩ := parents j.val j.isLt
        have hu := uv.trans hv
        by_cases healthy : (R (d+j.val)).1.Nonempty ∧ (R (d+j.val)).2.Nonempty
        · have copyChild (w : ℕ) (hw : w < d+j.val)
              (a : (R (d+j.val)).1 ⊆ (R w).1) (b : (R (d+j.val)).2 ⊆ (R w).2) :
              ∀ (f : A → ℕ → Bool) (g : B → ℕ → Bool),
                valid w (fun x => f x w) (fun y => g y w) →
                valid (d+j.val) (fun x => GateOp.or.eval [f x w,f x w])
                  (fun y => GateOp.or.eval [g y w,g y w]) := by
            intro f g h
            constructor
            · intro hQ x hx
              dsimp only
              rw [orEval, Bool.or_self]
              exact h.1 (hQ.mono b) x (a hx)
            · intro hP y hy
              dsimp only
              rw [orEval, Bool.or_self]
              exact h.2 (hP.mono a) y (b hy)
          rcases splitRectangle healthy.1 healthy.2 cover with h | h | h | h
          · exact ⟨.or,u,u,hu,hu,Or.inr rfl,fun f g good _ => copyChild u hu h.1 h.2 f g good⟩
          · exact ⟨.or,v,v,hv,hv,Or.inr rfl,fun f g good _ => copyChild v hv h.1 h.2 f g good⟩
          · obtain ⟨pos,nu,nv,pu,pv⟩ := h
            refine ⟨.or,u,v,hu,hv,Or.inr rfl,?_⟩
            intro f g uok vok
            constructor
            · intro hQ x hx
              dsimp only
              rw [orEval, Bool.or_eq_true]
              exact (pos hx).imp (uok.1 (hQ.mono nu) x) (vok.1 (hQ.mono nv) x)
            · intro _ y hy
              dsimp only
              rw [orEval]
              exact Bool.or_eq_false_iff.mpr ⟨uok.2 pu y (nu hy), vok.2 pv y (nv hy)⟩
          · obtain ⟨pu,pv,neg,nu,nv⟩ := h
            refine ⟨.and,u,v,hu,hv,Or.inl rfl,?_⟩
            intro f g uok vok
            constructor
            · intro _ x hx
              dsimp only
              rw [andEval, Bool.and_eq_true]
              exact ⟨uok.1 nu x (pu hx), vok.1 nv x (pv hx)⟩
            · intro hP y hy
              dsimp only
              rw [andEval]
              rcases neg hy with h | h
              · have hf : g y u = false := uok.2 (hP.mono pu) y h
                rw [hf]
                rfl
              · have hf : g y v = false := vok.2 (hP.mono pv) y h
                rw [hf, Bool.and_false]
        · refine ⟨.or,u,v,hu,hv,Or.inr rfl,?_⟩
          intro f g _ _
          exact ⟨fun hQ a ha => (healthy ⟨⟨a,ha⟩,hQ⟩).elim,
            fun hP b hb => (healthy ⟨hP,⟨b,hb⟩⟩).elim⟩
      choose op a b ha hb basis good using choices
      let gate (j : Fin s) : Gate := ⟨op j,[a j,b j]⟩
      let C : Circuit := ⟨List.ofFn gate,o⟩
      have sizeC : C.size = s := by
        change (List.ofFn gate).length = s
        simp
      have lookup (j : Fin s) : gateAt C j.val = gate j := by
        have h : j.val < C.gates.length := by simp [C]
        rw [show gateAt C j.val = C.gates[j.val] from List.getD_eq_getElem _ _ h]
        exact List.getElem_ofFn ..
      have fan : IsAO2 d C := by
        have member (g : Gate) (hg : g ∈ C.gates) : ∃ j, gate j = g := by
          change g ∈ List.ofFn gate at hg
          simpa only [List.mem_ofFn] using hg
        refine ⟨?_,?_,?_⟩
        · intro g hg
          obtain ⟨j,rfl⟩ := member g hg
          exact basis j
        · intro j hj w hw
          have hj' : j < s := by simpa [C] using hj
          rw [lookup ⟨j,hj'⟩] at hw
          change w ∈ [a ⟨j,hj'⟩,b ⟨j,hj'⟩] at hw
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
          rcases hw with rfl | rfl
          · exact ha _
          · exact hb _
        · intro g hg
          obtain ⟨_,rfl⟩ := member g hg
          rfl
      have read (x : Fin d → Bool) (j : Fin s) :
          wireValue C (List.ofFn x) (d+j.val) =
            (op j).eval [wireValue C (List.ofFn x) (a j),wireValue C (List.ofFn x) (b j)] := by
        have hj : j.val < C.gates.length := by simp [C]
        have he := wires_gate C (List.ofFn x) j.val hj
        rw [List.length_ofFn, ← show gateAt C j.val = C.gates[j.val] from List.getD_eq_getElem _ _ hj,
          lookup] at he
        change wireValue C (List.ofFn x) (d+j.val) = (op j).eval
          [rd C (List.ofFn x) (d+j.val) (a j),rd C (List.ofFn x) (d+j.val) (b j)] at he
        refine he.trans ?_
        change (op j).eval
          [rd C (List.ofFn x) (d+j.val) (a j), rd C (List.ofFn x) (d+j.val) (b j)] =
          (op j).eval [(C.wires (List.ofFn x)).getD (a j) false,
            (C.wires (List.ofFn x)).getD (b j) false]
        simp [rd,ha j,hb j]
      have holds (w : ℕ) (hw : w < d+s) :
          valid w (fun x => wireValue C (List.ofFn (P x)) w)
            (fun y => wireValue C (List.ofFn (Q y)) w) := by
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          by_cases inside : w < d
          · let i : Fin d := ⟨w,inside⟩
            have input (x : Fin d → Bool) : wireValue C (List.ofFn x) w = x i := by
              change (C.wires (List.ofFn x)).getD w false = _
              rw [wires_input C (List.ofFn x) w (by simpa using inside),
                List.getD_eq_getElem _ _ (by simpa using inside), List.getElem_ofFn]
            constructor
            · rintro ⟨b,hb'⟩ x hx
              dsimp only
              rw [input]
              exact (raw i x b ⟨hx,hb'⟩).1
            · rintro ⟨a,ha'⟩ y hy
              dsimp only
              rw [input]
              exact (raw i a y ⟨ha',hy⟩).2
          · let j : Fin s := ⟨w-d,by omega⟩
            have eq : d+j.val = w := by dsimp [j]; omega
            have v := good j (fun x k => wireValue C (List.ofFn (P x)) k)
              (fun y k => wireValue C (List.ofFn (Q y)) k)
              (ih _ (eq ▸ ha j) (by have := ha j; omega))
              (ih _ (eq ▸ hb j) (by have := hb j; omega))
            simpa only [← read,eq] using v
      obtain ⟨a₀⟩ := ‹Nonempty A›
      obtain ⟨b₀⟩ := ‹Nonempty B›
      have rootP (a : A) : a ∈ (R o).1 :=
        (root (show (a,b₀) ∈ (Set.univ : Set A) ×ˢ (Set.univ : Set B) from ⟨trivial,trivial⟩)).1
      have rootQ (b : B) : b ∈ (R o).2 :=
        (root (show (a₀,b) ∈ (Set.univ : Set A) ×ˢ (Set.univ : Set B) from ⟨trivial,trivial⟩)).2
      exact ⟨C,fan,sizeC,fun x => (holds o out).1 ⟨b₀,rootQ b₀⟩ x (rootP x),
        fun y => (holds o out).2 ⟨a₀,rootP a₀⟩ y (rootQ y)⟩
  let E := {e : Fin n × Fin n // I e.1 e.2}
  let Sets := {Y : Finset (Fin n) // Y.card ≤ q}
  let pair (p l : Fin n) (i : Fin (n+n)) :=
    decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)
  let neg (Y : Finset (Fin n)) (i : Fin (n+n)) : Bool := Fin.addCases
    (fun p : Fin n => decide (∀ l ∈ Y, ¬ I p l))
    (fun l : Fin n => decide (l ∈ Y)) i
  let positive (e : E) := pair e.val.1 e.val.2
  let negative (Y : Sets) := neg Y.val
  let pulled (w : ℕ) : Set E × Set Sets :=
    (Subtype.val ⁻¹' (R w).1, Subtype.val ⁻¹' (R w).2)
  have npos : 0 < n := by omega
  let l : Fin n := ⟨0,npos⟩
  have positiveDegree : 0 < Fintype.card {p : Fin n // I p l} := by rw [degree]; omega
  obtain ⟨p⟩ := Fintype.card_pos_iff.mp positiveDegree
  let _ : Nonempty E := ⟨⟨(p.val,l),p.property⟩⟩
  let _ : Nonempty Sets := ⟨⟨∅,by simp⟩⟩
  have rawBits (i : Fin (n+n)) (e : E) (Y : Sets)
      (h : (e,Y) ∈ (pulled i.val).1 ×ˢ (pulled i.val).2) :
      positive e i = true ∧ negative Y i = false := by
    rcases raw i e.val.1 e.val.2 Y.val h with ⟨eq,hit⟩ | ⟨eq,miss⟩
    · subst i
      obtain ⟨j,hj,incident⟩ := hit
      constructor
      · simp [positive,pair]
      · simp only [negative, neg, Fin.addCases_left]
        exact decide_eq_false_iff_not.mpr (fun h => h j hj incident)
    · subst i
      constructor
      · simp [positive,pair]
      · simp only [negative, neg, Fin.addCases_right]
        exact decide_eq_false_iff_not.mpr miss
  have pulledParents (j : ℕ) (hj : j < s) :
      ∃ a b, a < b ∧ b < n+n+j ∧
        (pulled (n+n+j)).1 ×ˢ (pulled (n+n+j)).2 ⊆
          (pulled a).1 ×ˢ (pulled a).2 ∪ (pulled b).1 ×ˢ (pulled b).2 := by
    obtain ⟨a,b,ab,back,h⟩ := parents j hj
    refine ⟨a,b,ab,back,?_⟩
    rintro ⟨e,Y⟩ hz
    exact h (show (e.val,Y.val) ∈ rect (n+n+j) from hz)
  have pulledRoot : Set.univ ×ˢ Set.univ ⊆ (pulled o).1 ×ˢ (pulled o).2 := by
    rintro ⟨e,Y⟩ _
    exact cover (show (e.val,Y.val) ∈
      {e : Fin n × Fin n | I e.1 e.2} ×ˢ {Y : Finset (Fin n) | Y.card ≤ q} from
      ⟨e.property,Y.property⟩)
  obtain ⟨D,hD,dsize,accepts,rejects⟩ :=
    rectanglesToCircuit E Sets (n+n) s o positive negative pulled out rawBits pulledParents pulledRoot
  have acceptD (p l : Fin n) (h : I p l) : circuitFun (n+n) D
      (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true :=
    accepts ⟨(p,l),h⟩
  let leBits (a b : List Bool) := ∀ i, a.getD i false = true → b.getD i false = true
  have evalMono (op : GateOp) (hop : op = .and ∨ op = .or) (s : List ℕ)
      (a b : List Bool) (h : leBits a b) :
      op.eval (s.map (fun i => a.getD i false)) = true →
      op.eval (s.map (fun i => b.getD i false)) = true := by
    rcases hop with rfl | rfl
    · change (s.map _).all id = true → (s.map _).all id = true
      simp only [List.all_eq_true, List.mem_map, id_eq]
      intro H v hv
      obtain ⟨i, hi, rfl⟩ := hv
      exact h i (H _ ⟨i,hi,rfl⟩)
    · change (s.map _).any id = true → (s.map _).any id = true
      simp only [List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
      exact ⟨_, ⟨i,hi,rfl⟩, h i hv⟩
  have foldMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ a b : List Bool, a.length = b.length → leBits a b →
        leBits (gs.foldl step a) (gs.foldl step b) := by
    induction gs with
    | nil => intro a b _ h; exact h
    | cons g gs ih =>
      intro a b len h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))
      · simp [step, len]
      · intro i hi
        change (a ++ [_]).getD i false = true at hi
        change (b ++ [_]).getD i false = true
        by_cases earlier : i < a.length
        · rw [List.getD_append _ _ _ _ earlier] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega), ← len]
          by_cases next : i - a.length = 0
          · rw [next] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            exact evalMono g.op (ops g List.mem_cons_self) _ a b h hi
          · obtain ⟨k, eq⟩ : ∃ k, i - a.length = k+1 :=
              ⟨i-a.length-1, by omega⟩
            rw [eq] at hi
            simp at hi
  have cardSubtype {α : Type} [Fintype α] (S : Finset α) (P : α → Prop)
      [DecidablePred P] (mem : ∀ a, a ∈ S ↔ P a) :
      S.card = Fintype.card (Subtype P) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight mem)
  have rejectD (x : Fin (n+n) → Bool)
      (small : Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q)
      (miss : ¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) :
      circuitFun (n+n) D x = false := by
    let Y := Finset.univ.filter (fun l : Fin n => x (Fin.natAdd n l) = true)
    have yCard : Y.card ≤ q := by
      rw [cardSubtype Y (fun l => x (Fin.natAdd n l) = true) (by simp [Y])]
      exact small
    have dominated (i : Fin (n+n)) (hx : x i = true) : neg Y i = true := by
      revert hx
      refine Fin.addCases ?_ ?_ i
      · intro p hp
        have none : ∀ l ∈ Y, ¬ I p l := by
          intro l hl h
          exact miss ⟨p, l, h, hp, (Finset.mem_filter.mp hl).2⟩
        change Fin.addCases _ _ (Fin.castAdd n p) = true
        rw [Fin.addCases_left]
        exact decide_eq_true none
      · intro l hl
        change Fin.addCases _ _ (Fin.natAdd n l) = true
        rw [Fin.addCases_right, decide_eq_true_eq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
    have lists : leBits (List.ofFn x) (List.ofFn (neg Y)) := by
      intro i hi
      by_cases inside : i < n+n
      · rw [List.getD_eq_getElem _ _ (by simp [inside]), List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ (by simp [inside]), List.getElem_ofFn]
        exact dominated ⟨i, inside⟩ hi
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt inside)] at hi
        contradiction
    cases h : circuitFun (n+n) D x with
    | false => rfl
    | true =>
      have reaches : circuitFun (n+n) D (neg Y) = true :=
        foldMono D.gates hD.1 _ _ (by simp) lists D.output h
      have rejected : circuitFun (n+n) D (neg Y) = false := rejects ⟨Y,yCard⟩
      rw [rejected] at reaches
      contradiction
  have fourFree (p r l u : Fin n) (neP : p ≠ r) (neL : l ≠ u) :
      ¬ (I p l ∧ I r l ∧ I p u ∧ I r u) := by
    rintro ⟨a,b,c,d⟩
    obtain ⟨v, _, only⟩ := unique p r neP
    exact neL ((only l ⟨a,b⟩).trans (only u ⟨c,d⟩).symm)
  let incidences : Finset (Fin n × Fin n) := Finset.univ.filter (fun e => I e.1 e.2)
  let lx (e : Fin n × Fin n) := lineSingle D (n+n) (fun k => decide (n ≤ k)) e.1.val (n+e.2.val)
  let px (e : Fin n × Fin n) := lineSingle D (n+n) (fun k => decide (k < n)) e.1.val (n+e.2.val)
  let A := incidences.filter (fun e => lx e = true)
  let B := incidences.filter (fun e => px e = true)
  let T := incidences.filter (fun e => lx e = false ∧ px e = false)
  have Acount : A.card ≤ 10 * D.size := by
    rw [cardSubtype A (fun e => I e.1 e.2 ∧ lx e = true) (by simp [A,incidences])]
    exact lineOnce n I D fourFree hD (fun x small miss => rejectD x (by omega) miss)
  have Bcount : B.card ≤ 10 * D.size := by
    rw [cardSubtype B (fun e => I e.1 e.2 ∧ px e = true) (by simp [B,incidences])]
    exact pointOnce q n I D (by omega) hn degree unique hD rejectD
  have Tcount : T.card ≤ 80 * D.size := by
    rw [cardSubtype T (fun e => I e.1 e.2 ∧ lx e = false ∧ px e = false)
      (by simp [T,incidences])]
    exact bothRepeated q n I D hq hn degree unique hD rejectD acceptD
  have covers : incidences ⊆ A ∪ (B ∪ T) := by
    intro e he
    cases hl : lx e
    · cases hp : px e
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨he,hl,hp⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨he,hp⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,hl⟩)
  let fibers : ∀ l : Fin n, Type := fun l => {p : Fin n // I p l}
  have incCount : incidences.card = n * (q+1) := by
    rw [← Fintype.card_coe]
    let e : ↥incidences ≃ (Σ l : Fin n, fibers l) :=
      { toFun := fun z => ⟨z.val.2, ⟨z.val.1, (Finset.mem_filter.mp z.property).2⟩⟩
        invFun := fun z => ⟨(z.2.val,z.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.2.property⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp [fibers, degree]
  have lb := ((Finset.card_le_card covers).trans (Finset.card_union_le A (B ∪ T)))
  rw [incCount] at lb
  have bc := Finset.card_union_le B T
  have incidence : n*q ≤ n*(q+1) := Nat.mul_le_mul_left n (Nat.le_succ q)
  omega
